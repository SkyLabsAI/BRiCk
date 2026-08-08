/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilder.hpp"
#include "LocationEmitter.hpp"
#include "RocqEmitter.hpp"
#include "Sharing.hpp"

#include <iostream>
#include <map>
#include <string>
#include <vector>

#include <clang/AST/DeclTemplate.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/MemoryBuffer.h>

namespace {
class Finder : public clang::RecursiveASTVisitor<Finder> {
public:
    bool VisitNamedDecl(clang::NamedDecl *declaration) {
        if (const auto *identifier = declaration->getIdentifier())
            if (!declaration->isImplicit())
                declarations.emplace(identifier->getName().str(), declaration);
        return true;
    }
    const clang::NamedDecl *named(llvm::StringRef name) const {
        auto found = declarations.find(name.str());
        return found == declarations.end() ? nullptr : found->second;
    }
    const clang::VarDecl *variable(llvm::StringRef name) const {
        const clang::NamedDecl *declaration = named(name);
        if (const auto *templ =
                llvm::dyn_cast_or_null<clang::VarTemplateDecl>(declaration))
            return templ->getTemplatedDecl();
        return llvm::dyn_cast_or_null<clang::VarDecl>(declaration);
    }
    std::map<std::string, clang::NamedDecl *> declarations;
};

bool fail(const std::string &message) {
    std::cerr << "sharing builder probe: " << message << '\n';
    return false;
}
} // namespace

int main(int argc, char **argv) {
    if (argc != 2) {
        std::cerr << "usage: cpp2v-sharing-builder-probe SOURCE\n";
        return 2;
    }
    auto buffer = llvm::MemoryBuffer::getFile(argv[1]);
    if (!buffer) {
        std::cerr << "cannot read " << argv[1] << '\n';
        return 2;
    }
    auto ast = clang::tooling::buildASTFromCodeWithArgs(
        (*buffer)->getBuffer(), {"-std=c++17"}, argv[1]);
    if (!ast)
        return fail("could not build AST") ? 0 : 1;
    Finder finder;
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    const auto *first = finder.variable("first_occurrence");
    const auto *second = finder.variable("second_occurrence");
    const auto *qualified = finder.variable("qualified_occurrence");
    const auto *templateOnly = finder.variable("template_only_type");
    const auto *function = finder.named("shared_function");
    const auto *meta = finder.named("MetaOnly");
    if (!first || !second || !qualified || !templateOnly || !function || !meta)
        return fail("fixture declarations were not found") ? 0 : 1;

    std::vector<ir::PointerUse<clang::NamedDecl>> names{
        {function, ir::SemanticMode::Static},
        {function, ir::SemanticMode::Template},
        {meta, ir::SemanticMode::Template},
        {first, ir::SemanticMode::Static}};
    std::vector<ir::PointerUse<clang::TypeSourceInfo>> types{
        {first->getTypeSourceInfo(), ir::SemanticMode::Static},
        {second->getTypeSourceInfo(), ir::SemanticMode::Static},
        {templateOnly->getTypeSourceInfo(), ir::SemanticMode::Template},
        {first->getTypeSourceInfo(), ir::SemanticMode::Template},
        {qualified->getTypeSourceInfo(), ir::SemanticMode::Static}};
    ir::BuildSelection selection{names, types, {}, {}, {}, {}, {}};
    auto artifact = ir::IRBuilder::build(ast->getASTContext(), selection);
    if (!artifact) {
        std::cerr << llvm::toString(artifact.takeError()) << '\n';
        return 1;
    }
    if (artifact->names.size() != 4 || artifact->types.size() != 5)
        return fail("builder returned the wrong selected values") ? 0 : 1;

    auto firstNode = artifact->unit->nodes().get(artifact->types[0]);
    auto secondNode = artifact->unit->nodes().get(artifact->types[1]);
    auto templateNode = artifact->unit->nodes().get(artifact->types[2]);
    auto sameTemplateType = artifact->unit->nodes().get(artifact->types[3]);
    auto qualifiedNode = artifact->unit->nodes().get(artifact->types[4]);
    auto staticName = artifact->unit->nodes().get(artifact->names[0]);
    auto templateName = artifact->unit->nodes().get(artifact->names[1]);
    auto templateOnlyName = artifact->unit->nodes().get(artifact->names[2]);
    auto variableName = artifact->unit->nodes().get(artifact->names[3]);
    if (!firstNode || !secondNode || !templateNode || !sameTemplateType ||
        !qualifiedNode || !staticName || !templateName || !templateOnlyName ||
        !variableName || !(*firstNode)->shareClass ||
        !(*secondNode)->shareClass || !(*templateNode)->shareClass ||
        !(*sameTemplateType)->shareClass || !(*qualifiedNode)->shareClass ||
        !(*staticName)->shareClass || !(*templateName)->shareClass ||
        !(*templateOnlyName)->shareClass || !(*variableName)->shareClass)
        return fail("builder omitted owned sharing metadata") ? 0 : 1;
    if (artifact->types[0] == artifact->types[1] ||
        (*firstNode)->origins == (*secondNode)->origins ||
        (*firstNode)->shareClass != (*secondNode)->shareClass)
        return fail("equal occurrences did not remain distinct in one class")
                   ? 0
                   : 1;
    if (artifact->names[0] == artifact->names[1] ||
        (*staticName)->shareClass != (*templateName)->shareClass)
        return fail("static/template name occurrences do not share identity")
                   ? 0
                   : 1;
    if ((*firstNode)->shareClass == (*sameTemplateType)->shareClass)
        return fail("static/template canonical types reused one class") ? 0 : 1;
    auto qualifiedChildren =
        artifact->unit->nodes().children(artifact->types[4]);
    if (!qualifiedChildren || qualifiedChildren->size() != 1)
        return fail("qualified pointer lost its child") ? 0 : 1;
    auto qualifier = artifact->unit->nodes().get(qualifiedChildren->front());
    auto qualifierChildren =
        qualifier
            ? artifact->unit->nodes().children(qualifiedChildren->front())
            : llvm::Expected<std::vector<ir::NodeId>>(qualifier.takeError());
    if (!qualifier || (*qualifier)->shareClass || !qualifierChildren ||
        qualifierChildren->size() != 1)
        return fail("qualified wrapper unexpectedly owns a sharing class") ? 0
                                                                           : 1;
    auto unqualified = artifact->unit->nodes().get(qualifierChildren->front());
    if (!unqualified || !(*unqualified)->shareClass)
        return fail("unqualified child lacks its sharing class") ? 0 : 1;

    std::vector<ir::SharingSeed> seeds{
        {ir::SharingSeedKind::TemplateOnly, artifact->types[2],
         artifact->names[2]},
        // Legacy VisitVarDecl seeds only the value/type dependencies.
        {ir::SharingSeedKind::Ordinary, artifact->types[0], std::nullopt},
        {ir::SharingSeedKind::Ordinary, artifact->types[4], std::nullopt},
        {ir::SharingSeedKind::Ordinary, artifact->types[0],
         artifact->names[0]}};
    auto plan = ir::IRSharing::analyze(*artifact->unit, seeds);
    if (!plan) {
        std::cerr << llvm::toString(plan.takeError()) << '\n';
        return 1;
    }
    const std::vector<ir::SharingDefinition> &definitions = plan->definitions();
    const std::vector<std::string> expectedNames{"n1", "t1", "t2", "t3", "n2"};
    if (definitions.size() != expectedNames.size())
        return fail("sharing plan has the wrong definition count") ? 0 : 1;
    for (std::size_t index = 0; index < definitions.size(); ++index)
        if (definitions[index].localName != expectedNames[index])
            return fail("sharing order is not child/type before function name")
                       ? 0
                       : 1;
    if (plan->lookup(*(*templateNode)->shareClass) ||
        plan->lookup(*(*templateOnlyName)->shareClass) ||
        plan->lookup(*(*variableName)->shareClass))
        return fail("unseeded/template-only name created a definition") ? 0 : 1;

    ir::SemanticRocqEmitter shared;
    ir::SemanticRocqEmitter inlineEmitter({false});
    auto prelude = shared.emitSharingDefinitions(*artifact->unit, *plan);
    auto disabledPrelude =
        inlineEmitter.emitSharingDefinitions(*artifact->unit, *plan);
    auto inlineType =
        inlineEmitter.renderNode(*artifact->unit, artifact->types[1], *plan);
    auto sharedType =
        shared.renderNode(*artifact->unit, artifact->types[1], *plan);
    auto staticFunction =
        shared.renderNode(*artifact->unit, artifact->names[0], *plan);
    auto templateFunction =
        shared.renderNode(*artifact->unit, artifact->names[1], *plan);
    auto templateInline =
        shared.renderNode(*artifact->unit, artifact->types[2], *plan);
    if (!prelude || !disabledPrelude || !disabledPrelude->empty() ||
        !inlineType || !sharedType || !staticFunction || !templateFunction ||
        !templateInline || *sharedType != "t2" || *staticFunction != "n2" ||
        *templateFunction != "n2" || *templateInline == "t1" ||
        *templateInline == "t2")
        return fail("semantic sharing rendering is inconsistent") ? 0 : 1;

    ir::LocationRocqEmitter sharedLocations({true});
    ir::LocationRocqEmitter inlineLocations({false});
    auto sharedTree =
        sharedLocations.renderTree(*artifact->unit, artifact->types[1]);
    auto inlineTree =
        inlineLocations.renderTree(*artifact->unit, artifact->types[1]);
    if (!sharedTree || !inlineTree || *sharedTree != *inlineTree)
        return fail("sharing changed location bytes or shape") ? 0 : 1;

    std::cout << *prelude;
    std::cout << "INLINE_TYPE " << *inlineType << '\n';
    std::cout << "SHARED_TYPE " << *sharedType << '\n';
    std::cout << "STATIC_NAME " << *staticFunction << '\n';
    std::cout << "TEMPLATE_NAME " << *templateFunction << '\n';
    std::cout << "TEMPLATE_ONLY " << *templateInline << '\n';
    return 0;
}
