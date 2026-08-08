/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilder.hpp"
#include "ModuleBuilder.hpp"
#include "RocqEmitter.hpp"
#include "Sharing.hpp"

#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Sema/Sema.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/Casting.h>

#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <optional>
#include <string>
#include <type_traits>
#include <vector>

namespace {

class Finder : public clang::RecursiveASTVisitor<Finder> {
public:
    bool shouldVisitImplicitCode() const { return true; }
    bool shouldVisitTemplateInstantiations() const { return true; }

    bool VisitVarDecl(clang::VarDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit() &&
            !declaration->isImplicit())
            variables[declaration->getNameAsString()] = declaration;
        return true;
    }

    bool VisitFunctionDecl(clang::FunctionDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit() &&
            !declaration->isImplicit() &&
            !declaration->isTemplateInstantiation()) {
            functions[declaration->getNameAsString()] = declaration;
            if (declaration->getName() == "redeclared_function")
                redeclaredFunctions.push_back(declaration);
        }
        return true;
    }

    bool VisitCXXRecordDecl(clang::CXXRecordDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit() &&
            !declaration->isImplicit() && !declaration->getName().empty() &&
            !declaration->getDescribedClassTemplate())
            records[declaration->getNameAsString()] = declaration;
        if (declaration->getName() == "RedeclaredRecord" &&
            !declaration->isImplicit())
            redeclaredRecords.push_back(declaration);
        if (const auto *specialization =
                llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
                    declaration))
            if (specialization->getSpecializedTemplate()->getName() == "Box" &&
                specialization->getSpecializationKind() ==
                    clang::TSK_ImplicitInstantiation)
                boxSpecialization = declaration;
        return true;
    }

    bool VisitCXXMethodDecl(clang::CXXMethodDecl *declaration) {
        if (declaration->getParent()->getName() == "ImplicitOnly" &&
            declaration->isImplicit()) {
            if (const auto *constructor =
                    llvm::dyn_cast<clang::CXXConstructorDecl>(declaration)) {
                if (constructor->isDefaultConstructor())
                    implicitDefaultConstructor = constructor;
                else if (constructor->isCopyConstructor())
                    implicitCopyConstructor = constructor;
                else if (constructor->isMoveConstructor())
                    implicitMoveConstructor = constructor;
            } else if (const auto *destructor =
                           llvm::dyn_cast<clang::CXXDestructorDecl>(
                               declaration)) {
                implicitDestructor = destructor;
            } else if (declaration->isCopyAssignmentOperator()) {
                implicitCopyAssignment = declaration;
            } else if (declaration->isMoveAssignmentOperator()) {
                implicitMoveAssignment = declaration;
            }
            return true;
        }
        if (declaration->getParent()->getName() == "ExceptionHolder" &&
            declaration->isImplicit()) {
            if (const auto *constructor =
                    llvm::dyn_cast<clang::CXXConstructorDecl>(declaration)) {
                if (constructor->isDefaultConstructor())
                    exceptionDefaultConstructor = constructor;
                else if (constructor->isCopyConstructor())
                    exceptionCopyConstructor = constructor;
            } else if (const auto *destructor =
                           llvm::dyn_cast<clang::CXXDestructorDecl>(
                               declaration)) {
                exceptionDestructor = destructor;
            }
            return true;
        }
        if (declaration->isImplicit() ||
            declaration->getParent()->getName() != "Record")
            return true;
        if (llvm::isa<clang::CXXConstructorDecl>(declaration))
            constructor = llvm::cast<clang::CXXConstructorDecl>(declaration);
        else if (llvm::isa<clang::CXXDestructorDecl>(declaration))
            destructor = llvm::cast<clang::CXXDestructorDecl>(declaration);
        else
            methods[declaration->getNameAsString()] = declaration;
        return true;
    }

    bool VisitEnumDecl(clang::EnumDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit() &&
            declaration->getName() == "AuditEnum")
            enumeration = declaration;
        if (declaration->getName() == "Concrete")
            templatedEnumeration = declaration;
        return true;
    }

    bool VisitEnumConstantDecl(clang::EnumConstantDecl *declaration) {
        if (declaration->getDeclContext() == enumeration)
            enumerators.push_back(declaration);
        if (declaration->getName() == "Suppressed")
            templatedEnumerator = declaration;
        return true;
    }

    bool VisitTypeAliasDecl(clang::TypeAliasDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit() &&
            declaration->getName() == "Alias")
            alias = declaration;
        if (declaration->getName() == "AliasTemplate" &&
            declaration->getDescribedAliasTemplate())
            aliasTemplate = declaration;
        return true;
    }

    bool VisitNamespaceAliasDecl(clang::NamespaceAliasDecl *declaration) {
        namespaceAliases[declaration->getNameAsString()] = declaration;
        if (declaration->getName() == "alias_namespace")
            namespaceAlias = declaration;
        return true;
    }

    bool VisitNamespaceDecl(clang::NamespaceDecl *declaration) {
        if (declaration->getName() == "inline_namespace" &&
            declaration->isInline())
            inlineNamespace = declaration;
        return true;
    }

    bool VisitStaticAssertDecl(clang::StaticAssertDecl *declaration) {
        if (declaration->getDeclContext()->isTranslationUnit())
            staticAssertion = declaration;
        return true;
    }

    bool VisitClassTemplateDecl(clang::ClassTemplateDecl *declaration) {
        if (declaration->getName() == "Box")
            box = declaration;
        if (declaration->getName() == "EnumScope")
            enumScope = declaration;
        if (declaration->getName() == "RedeclaredTemplate")
            redeclaredTemplates.push_back(declaration);
        return true;
    }

    bool VisitFunctionTemplateDecl(clang::FunctionTemplateDecl *declaration) {
        if (declaration->getName() == "templated_function")
            functionTemplate = declaration;
        return true;
    }

    std::map<std::string, clang::VarDecl *> variables;
    std::map<std::string, clang::FunctionDecl *> functions;
    std::vector<clang::FunctionDecl *> redeclaredFunctions;
    std::map<std::string, clang::CXXRecordDecl *> records;
    std::vector<clang::CXXRecordDecl *> redeclaredRecords;
    std::map<std::string, clang::CXXMethodDecl *> methods;
    clang::CXXConstructorDecl *constructor = nullptr;
    clang::CXXDestructorDecl *destructor = nullptr;
    const clang::CXXConstructorDecl *implicitDefaultConstructor = nullptr;
    const clang::CXXConstructorDecl *implicitCopyConstructor = nullptr;
    const clang::CXXConstructorDecl *implicitMoveConstructor = nullptr;
    const clang::CXXMethodDecl *implicitCopyAssignment = nullptr;
    const clang::CXXMethodDecl *implicitMoveAssignment = nullptr;
    const clang::CXXDestructorDecl *implicitDestructor = nullptr;
    const clang::CXXConstructorDecl *exceptionDefaultConstructor = nullptr;
    const clang::CXXConstructorDecl *exceptionCopyConstructor = nullptr;
    const clang::CXXDestructorDecl *exceptionDestructor = nullptr;
    clang::EnumDecl *enumeration = nullptr;
    std::vector<clang::EnumConstantDecl *> enumerators;
    clang::EnumDecl *templatedEnumeration = nullptr;
    clang::EnumConstantDecl *templatedEnumerator = nullptr;
    clang::TypeAliasDecl *alias = nullptr;
    clang::TypeAliasDecl *aliasTemplate = nullptr;
    std::map<std::string, clang::NamespaceAliasDecl *> namespaceAliases;
    clang::NamespaceAliasDecl *namespaceAlias = nullptr;
    clang::NamespaceDecl *inlineNamespace = nullptr;
    clang::StaticAssertDecl *staticAssertion = nullptr;
    clang::ClassTemplateDecl *box = nullptr;
    clang::ClassTemplateDecl *enumScope = nullptr;
    std::vector<clang::ClassTemplateDecl *> redeclaredTemplates;
    clang::CXXRecordDecl *boxSpecialization = nullptr;
    clang::FunctionTemplateDecl *functionTemplate = nullptr;
};

std::optional<std::string> readFile(const std::string &path) {
    std::ifstream input(path);
    if (!input)
        return std::nullopt;
    return std::string(std::istreambuf_iterator<char>(input),
                       std::istreambuf_iterator<char>());
}

template <typename T>
T *lookup(const std::map<std::string, T *> &values, const char *name) {
    const auto found = values.find(name);
    return found == values.end() ? nullptr : found->second;
}

void emitTypedPairs(
    const char *name, const char *keyType, const char *valueType,
    const std::vector<std::pair<std::string, std::string>> &values) {
    std::cout << "Definition " << name << " : list (" << keyType << " * "
              << valueType << ") :=\n  ";
    for (const auto &[key, value] : values)
        std::cout << "(" << key << ", " << value << ") ::\n  ";
    std::cout << "nil.\n\n";
}

void emitPairs(const char *name, const char *type,
               const std::vector<std::pair<std::string, std::string>> &values) {
    emitTypedPairs(name, "name", type, values);
}

std::string rocqString(llvm::StringRef value) {
    std::string result = "\"";
    for (const char byte : value) {
        if (byte == '"')
            result += "\"\"";
        else
            result += byte;
    }
    result += '"';
    return result;
}

std::optional<std::uint64_t>
spellingOffset(const clang::SourceManager &sourceManager,
               clang::SourceLocation location) {
    if (location.isInvalid())
        return std::nullopt;
    location = sourceManager.getSpellingLoc(location);
    if (location.isInvalid())
        return std::nullopt;
    return sourceManager.getFileOffset(location);
}

bool originKindBeginsAt(const ir::BuildArtifact &artifact, ir::NodeId node,
                        source::OriginKind kind,
                        const clang::SourceManager &sourceManager,
                        clang::SourceLocation location) {
    const auto expected = spellingOffset(sourceManager, location);
    auto value = artifact.unit->nodes().get(node);
    if (!expected || !value)
        return false;
    for (source::OriginId originId : (*value)->origins) {
        const source::Origin &origin =
            artifact.unit->sources().origins[originId.value()];
        if (origin.kind == kind && origin.spelling && origin.spelling->begin &&
            origin.spelling->begin->byteOffset == *expected)
            return true;
    }
    return false;
}

bool firstOriginAnchorBeginsAt(const ir::BuildArtifact &artifact,
                               ir::NodeId node, source::OriginKind originKind,
                               source::OriginKind anchorKind,
                               const clang::SourceManager &sourceManager,
                               clang::SourceLocation location) {
    const auto expected = spellingOffset(sourceManager, location);
    auto value = artifact.unit->nodes().get(node);
    if (!expected || !value || (*value)->origins.empty())
        return false;
    const source::Origin &origin =
        artifact.unit->sources().origins[(*value)->origins.front().value()];
    if (origin.kind != originKind || !origin.anchor)
        return false;
    const source::Origin &anchor =
        artifact.unit->sources().origins[origin.anchor->value()];
    return anchor.kind == anchorKind && anchor.spelling &&
           anchor.spelling->begin &&
           anchor.spelling->begin->byteOffset == *expected;
}

bool hasOrderedTransformedDerivation(const ir::BuildArtifact &artifact,
                                     ir::NodeId node) {
    auto value = artifact.unit->nodes().get(node);
    if (!value || (*value)->origins.size() < 2)
        return false;
    const source::OriginId directId = (*value)->origins[0];
    const source::OriginId transformedId = (*value)->origins[1];
    const source::Origin &direct =
        artifact.unit->sources().origins[directId.value()];
    const source::Origin &transformed =
        artifact.unit->sources().origins[transformedId.value()];
    return direct.kind == source::OriginKind::Explicit &&
           transformed.kind == source::OriginKind::ClangTransformed &&
           transformed.derivedFrom.size() == 1 &&
           transformed.derivedFrom.front() == directId;
}

bool firstOriginAnchorsNodeOrigin(const ir::BuildArtifact &artifact,
                                  ir::NodeId generated, ir::NodeId anchorNode) {
    auto generatedValue = artifact.unit->nodes().get(generated);
    auto anchorValue = artifact.unit->nodes().get(anchorNode);
    if (!generatedValue || !anchorValue || (*generatedValue)->origins.empty())
        return false;
    const source::Origin &origin =
        artifact.unit->sources()
            .origins[(*generatedValue)->origins.front().value()];
    if (!origin.anchor)
        return false;
    return std::find((*anchorValue)->origins.begin(),
                     (*anchorValue)->origins.end(),
                     *origin.anchor) != (*anchorValue)->origins.end();
}

} // namespace

int main(int argc, char **argv) {
    if (argc < 3) {
        std::cerr << "usage: declaration-probe FILE MODULE [-- CLANG-ARGS]\n";
        return 2;
    }
    const std::string path = argv[1];
    const std::string module = argv[2];
    std::vector<std::string> arguments;
    bool clangArguments = false;
    for (int index = 3; index < argc; ++index) {
        if (std::string(argv[index]) == "--") {
            clangArguments = true;
            continue;
        }
        if (clangArguments)
            arguments.emplace_back(argv[index]);
    }
    auto source = readFile(path);
    if (!source) {
        std::cerr << "could not read " << path << '\n';
        return 2;
    }
    auto ast = clang::tooling::buildASTFromCodeWithArgs(
        *source, arguments, path, "cpp2v-declaration-probe");
    if (!ast) {
        std::cerr << "could not parse fixture\n";
        return 1;
    }
    Finder finder;
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    clang::VarDecl *external = lookup(finder.variables, "external_value");
    clang::VarDecl *plain = lookup(finder.variables, "plain_value");
    clang::VarDecl *initialized = lookup(finder.variables, "initialized_value");
    clang::FunctionDecl *function = lookup(finder.functions, "free_function");
    clang::CXXRecordDecl *forward = lookup(finder.records, "Forward");
    clang::CXXRecordDecl *fallbackOnly = lookup(finder.records, "FallbackOnly");
    clang::CXXRecordDecl *implicitOnly = lookup(finder.records, "ImplicitOnly");
    clang::CXXRecordDecl *base = lookup(finder.records, "Base");
    clang::CXXRecordDecl *pureOverride = lookup(finder.records, "PureOverride");
    clang::CXXRecordDecl *record = lookup(finder.records, "Record");
    clang::CXXRecordDecl *choice = lookup(finder.records, "Choice");
    clang::NamespaceAliasDecl *zetaAlias =
        lookup(finder.namespaceAliases, "zeta_alias");
    clang::NamespaceAliasDecl *middleAlias =
        lookup(finder.namespaceAliases, "middle_alias");
    clang::NamespaceAliasDecl *alphaAlias =
        lookup(finder.namespaceAliases, "alpha_alias");
    clang::CXXMethodDecl *method = lookup(finder.methods, "method");
    clang::CXXMethodDecl *staticMethod =
        lookup(finder.methods, "static_method");
    clang::CXXMethodDecl *virtualMethod =
        lookup(finder.methods, "virtual_method");
    if (!external || !plain || !initialized || !function || !forward ||
        !fallbackOnly || !implicitOnly || !base || !pureOverride || !record ||
        !choice || !zetaAlias || !middleAlias || !alphaAlias ||
        !finder.constructor || !finder.destructor || !method || !staticMethod ||
        !virtualMethod || !finder.enumeration ||
        finder.enumerators.size() != 2 || !finder.templatedEnumeration ||
        !finder.templatedEnumerator || !finder.alias || !finder.aliasTemplate ||
        !finder.namespaceAlias || !finder.inlineNamespace ||
        !finder.staticAssertion || !finder.box || !finder.enumScope ||
        !finder.boxSpecialization || !finder.functionTemplate ||
        !finder.implicitDefaultConstructor || !finder.implicitCopyConstructor ||
        !finder.implicitMoveConstructor || !finder.implicitCopyAssignment ||
        !finder.implicitMoveAssignment || !finder.implicitDestructor ||
        !finder.exceptionDefaultConstructor ||
        !finder.exceptionCopyConstructor || !finder.exceptionDestructor ||
        finder.redeclaredRecords.size() != 2 ||
        finder.redeclaredTemplates.size() != 2) {
        std::cerr << "fixture declarations were not found\n";
        return 1;
    }
    if (finder.exceptionCopyConstructor->getExceptionSpecType() !=
        clang::EST_Unevaluated) {
        std::cerr << "exception fixture did not preserve an unevaluated spec: "
                  << finder.exceptionCopyConstructor->getExceptionSpecType()
                  << '\n';
        return 1;
    }

    clang::Sema *sema = &ast->getSema();

    const std::vector<ir::RootDeclarationUse> fallbackRoots{
        {fallbackOnly, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
         false, true, true}};
    ir::BuildSelection fallbackSelection;
    fallbackSelection.rootDeclarations = fallbackRoots;
    auto fallbackArtifact =
        ir::IRBuilder::build(ast->getASTContext(), fallbackSelection, sema);
    if (!fallbackArtifact) {
        std::cerr << llvm::toString(fallbackArtifact.takeError()) << '\n';
        return 1;
    }
    const auto fallbackSeeds =
        ir::IRSharing::productionSeeds(*fallbackArtifact->unit);
    if (fallbackArtifact->unit->rootEvents().size() != 7 ||
        fallbackSeeds.size() != 1) {
        std::cerr << "implicit fallback root/seed mismatch\n";
        return 1;
    }

    const std::vector<ir::RootDeclarationUse> duplicateRoots{
        {finder.redeclaredRecords[0], ir::SemanticMode::Static,
         ir::DeclarationFamily::Global, false, true},
        {finder.redeclaredRecords[1], ir::SemanticMode::Static,
         ir::DeclarationFamily::Global, false, true}};
    ir::BuildSelection duplicateSelection;
    duplicateSelection.rootDeclarations = duplicateRoots;
    auto duplicateArtifact =
        ir::IRBuilder::build(ast->getASTContext(), duplicateSelection, sema);
    if (!duplicateArtifact ||
        duplicateArtifact->unit->rootEvents().size() != 2) {
        if (!duplicateArtifact)
            std::cerr << llvm::toString(duplicateArtifact.takeError()) << '\n';
        else
            std::cerr << "duplicate root cardinality mismatch\n";
        return 1;
    }

    const std::vector<ir::RootDeclarationUse> templateDuplicateRoots{
        {finder.redeclaredTemplates[0]->getTemplatedDecl(),
         ir::SemanticMode::Template, ir::DeclarationFamily::Global, true, true},
        {finder.redeclaredTemplates[1]->getTemplatedDecl(),
         ir::SemanticMode::Template, ir::DeclarationFamily::Global, true,
         true}};
    ir::BuildSelection templateDuplicateSelection;
    templateDuplicateSelection.rootDeclarations = templateDuplicateRoots;
    auto templateDuplicateArtifact = ir::IRBuilder::build(
        ast->getASTContext(), templateDuplicateSelection, sema);
    if (!templateDuplicateArtifact ||
        templateDuplicateArtifact->unit->rootEvents().size() != 2) {
        if (!templateDuplicateArtifact)
            std::cerr << llvm::toString(templateDuplicateArtifact.takeError())
                      << '\n';
        else
            std::cerr << "template duplicate root cardinality mismatch\n";
        return 1;
    }

    const std::vector<ir::RootDeclarationUse> exceptionRoots{
        {finder.exceptionCopyConstructor, ir::SemanticMode::Static,
         ir::DeclarationFamily::Object, false, true}};
    ir::BuildSelection exceptionSelection;
    exceptionSelection.rootDeclarations = exceptionRoots;
    auto missingSema =
        ir::IRBuilder::build(ast->getASTContext(), exceptionSelection);
    if (missingSema) {
        std::cerr << "unevaluated exception spec built without Sema\n";
        return 1;
    }
    const std::string missingSemaMessage =
        llvm::toString(missingSema.takeError());
    if (missingSemaMessage.find("live Sema") == std::string::npos) {
        std::cerr << missingSemaMessage << '\n';
        return 1;
    }
    auto exceptionResolutionArtifact =
        ir::IRBuilder::build(ast->getASTContext(), exceptionSelection, sema);
    if (!exceptionResolutionArtifact ||
        exceptionResolutionArtifact->unit->rootEvents().size() != 1) {
        if (!exceptionResolutionArtifact)
            std::cerr << llvm::toString(exceptionResolutionArtifact.takeError())
                      << '\n';
        else
            std::cerr << "exception resolution root cardinality mismatch\n";
        return 1;
    }
    const ir::RootEvent &resolvedExceptionRoot =
        exceptionResolutionArtifact->unit->rootEvents().front();
    auto resolvedOuterChildren =
        exceptionResolutionArtifact->unit->nodes().children(
            resolvedExceptionRoot.semanticValue);
    auto resolvedRecord =
        resolvedOuterChildren && resolvedOuterChildren->size() == 1
            ? exceptionResolutionArtifact->unit->nodes().get(
                  resolvedOuterChildren->front())
            : llvm::Expected<const ir::Node *>(
                  llvm::createStringError(std::errc::invalid_argument,
                                          "malformed resolved exception root"));
    const auto *resolvedException =
        resolvedRecord && (*resolvedRecord)->arguments.size() > 4
            ? std::get_if<ir::ScalarTerm>(
                  &(*resolvedRecord)->arguments[4].payload)
            : nullptr;
    if (!resolvedException ||
        resolvedException->text != "exception_spec.NoThrow") {
        if (!resolvedOuterChildren)
            llvm::consumeError(resolvedOuterChildren.takeError());
        if (!resolvedRecord)
            llvm::consumeError(resolvedRecord.takeError());
        std::cerr << "unevaluated exception spec did not resolve\n";
        return 1;
    }

    sema->DefineImplicitCopyConstructor(
        finder.exceptionCopyConstructor->getLocation(),
        const_cast<clang::CXXConstructorDecl *>(
            finder.exceptionCopyConstructor));
    if (!finder.exceptionCopyConstructor->getBody()) {
        std::cerr << "implicit copy constructor elaboration failed\n";
        return 1;
    }
    auto exceptionArtifact =
        ir::IRBuilder::build(ast->getASTContext(), exceptionSelection, sema);
    if (!exceptionArtifact ||
        exceptionArtifact->unit->rootEvents().size() != 1) {
        if (!exceptionArtifact)
            std::cerr << llvm::toString(exceptionArtifact.takeError()) << '\n';
        else
            std::cerr << "elaborated exception root cardinality mismatch\n";
        return 1;
    }

    sema->DefineImplicitDestructor(
        finder.implicitDestructor->getLocation(),
        const_cast<clang::CXXDestructorDecl *>(finder.implicitDestructor));
    if (!finder.implicitDestructor->getBody()) {
        std::cerr << "implicit destructor elaboration failed\n";
        return 1;
    }

    const std::vector<ir::RootDeclarationUse> suppressedEnumRoots{
        {finder.templatedEnumerator, ir::SemanticMode::Template,
         ir::DeclarationFamily::Global, true, true}};
    ir::BuildSelection suppressedEnumSelection;
    suppressedEnumSelection.rootDeclarations = suppressedEnumRoots;
    auto suppressedEnumArtifact = ir::IRBuilder::build(
        ast->getASTContext(), suppressedEnumSelection, sema);
    if (!suppressedEnumArtifact ||
        !suppressedEnumArtifact->unit->rootEvents().empty()) {
        if (!suppressedEnumArtifact)
            std::cerr << llvm::toString(suppressedEnumArtifact.takeError())
                      << '\n';
        else
            std::cerr << "templated enum constant was not suppressed\n";
        return 1;
    }

    auto cAst = clang::tooling::buildASTFromCodeWithArgs(
        "struct CRecord { int value; }; union CUnion { int value; };",
        {"-x", "c", "-std=c17"}, "c-record.c", "cpp2v-declaration-c-probe");
    if (!cAst) {
        std::cerr << "could not parse C record fixture\n";
        return 1;
    }
    std::vector<const clang::RecordDecl *> cRecords;
    for (const clang::Decl *declaration :
         cAst->getASTContext().getTranslationUnitDecl()->decls())
        if (const auto *record = llvm::dyn_cast<clang::RecordDecl>(declaration))
            if (record->isCompleteDefinition() && record->getIdentifier())
                cRecords.push_back(record);
    if (cRecords.size() != 2) {
        std::cerr << "C record declarations were not found\n";
        return 1;
    }
    for (const clang::RecordDecl *cRecord : cRecords) {
        const std::vector<ir::RootDeclarationUse> cRoots{
            {cRecord, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
             false, true}};
        ir::BuildSelection cSelection;
        cSelection.rootDeclarations = cRoots;
        auto rejected = ir::IRBuilder::build(cAst->getASTContext(), cSelection,
                                             &cAst->getSema());
        if (rejected) {
            std::cerr << "C record definition unexpectedly built\n";
            return 1;
        }
        const std::string message = llvm::toString(rejected.takeError());
        if (message.find("outside the C++17 IR scope") == std::string::npos) {
            std::cerr << message << '\n';
            return 1;
        }
    }

    std::vector<ir::PointerUse<clang::NamedDecl>> objectUses{
        {external, ir::SemanticMode::Static},
        {plain, ir::SemanticMode::Static},
        {initialized, ir::SemanticMode::Static},
        {function, ir::SemanticMode::Static},
        {finder.constructor, ir::SemanticMode::Static},
        {finder.destructor, ir::SemanticMode::Static},
        {method, ir::SemanticMode::Static},
        {staticMethod, ir::SemanticMode::Static},
        {virtualMethod, ir::SemanticMode::Static},
        {finder.functionTemplate->getTemplatedDecl(),
         ir::SemanticMode::Template}};
    const std::vector<const clang::NamedDecl *> implicitMembers{
        finder.implicitDefaultConstructor, finder.implicitCopyConstructor,
        finder.implicitMoveConstructor,    finder.implicitCopyAssignment,
        finder.implicitMoveAssignment,     finder.implicitDestructor};
    for (const clang::NamedDecl *member : implicitMembers)
        objectUses.push_back({member, ir::SemanticMode::Static});
    std::vector<ir::PointerUse<clang::NamedDecl>> globalUses{
        {forward, ir::SemanticMode::Static},
        {implicitOnly, ir::SemanticMode::Static},
        {base, ir::SemanticMode::Static},
        {record, ir::SemanticMode::Static},
        {choice, ir::SemanticMode::Static},
        {finder.enumeration, ir::SemanticMode::Static},
        {finder.enumerators[0], ir::SemanticMode::Static},
        {finder.enumerators[1], ir::SemanticMode::Static},
        {finder.alias, ir::SemanticMode::Static},
        {finder.box->getTemplatedDecl(), ir::SemanticMode::Template},
        {finder.templatedEnumeration, ir::SemanticMode::Template},
        {pureOverride, ir::SemanticMode::Static}};
    std::vector<ir::PointerUse<clang::Decl>> parameterUses{
        {finder.box->getTemplatedDecl(), ir::SemanticMode::Template},
        {finder.functionTemplate->getTemplatedDecl(),
         ir::SemanticMode::Template}};
    std::vector<ir::RootDeclarationUse> roots{
        {external, ir::SemanticMode::Static, ir::DeclarationFamily::Object,
         false, false},
        {plain, ir::SemanticMode::Static, ir::DeclarationFamily::Object, false,
         false},
        {initialized, ir::SemanticMode::Static, ir::DeclarationFamily::Object,
         false, false},
        {function, ir::SemanticMode::Static, ir::DeclarationFamily::Object,
         false, true},
        {finder.constructor, ir::SemanticMode::Static,
         ir::DeclarationFamily::Object, false, true},
        {finder.destructor, ir::SemanticMode::Static,
         ir::DeclarationFamily::Object, false, true},
        {method, ir::SemanticMode::Static, ir::DeclarationFamily::Object, false,
         true},
        {staticMethod, ir::SemanticMode::Static, ir::DeclarationFamily::Object,
         false, true},
        {virtualMethod, ir::SemanticMode::Static, ir::DeclarationFamily::Object,
         false, true},
        {forward, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
         false, true},
        {implicitOnly, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
         false, true},
        {base, ir::SemanticMode::Static, ir::DeclarationFamily::Global, false,
         true},
        {record, ir::SemanticMode::Static, ir::DeclarationFamily::Global, false,
         true},
        {choice, ir::SemanticMode::Static, ir::DeclarationFamily::Global, false,
         true},
        {finder.enumeration, ir::SemanticMode::Static,
         ir::DeclarationFamily::Global, false, true},
        {finder.enumerators[0], ir::SemanticMode::Static,
         ir::DeclarationFamily::Global, false, true},
        {finder.enumerators[1], ir::SemanticMode::Static,
         ir::DeclarationFamily::Global, false, true},
        {finder.alias, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
         false, true},
        {finder.functionTemplate->getTemplatedDecl(),
         ir::SemanticMode::Template, ir::DeclarationFamily::Object, true, true},
        {finder.box->getTemplatedDecl(), ir::SemanticMode::Template,
         ir::DeclarationFamily::Global, true, true},
        {finder.templatedEnumeration, ir::SemanticMode::Template,
         ir::DeclarationFamily::Global, true, true},
        {pureOverride, ir::SemanticMode::Static, ir::DeclarationFamily::Global,
         false, true}};
    auto implicitRootPosition = roots.begin() + 9;
    for (const clang::NamedDecl *member : implicitMembers) {
        implicitRootPosition = roots.insert(
            implicitRootPosition, {member, ir::SemanticMode::Static,
                                   ir::DeclarationFamily::Object, false, true});
        ++implicitRootPosition;
    }
    std::vector<ir::NamespaceAliasUse> namespaceAliases{
        {zetaAlias, zetaAlias->getNamespace(), zetaAlias->getAliasedNamespace(),
         ir::SemanticMode::Static},
        {middleAlias, middleAlias->getNamespace(),
         middleAlias->getAliasedNamespace(), ir::SemanticMode::Static},
        {finder.namespaceAlias, finder.namespaceAlias->getNamespace(),
         finder.namespaceAlias->getAliasedNamespace(),
         ir::SemanticMode::Static},
        {alphaAlias, alphaAlias->getNamespace(),
         alphaAlias->getAliasedNamespace(), ir::SemanticMode::Static},
        {finder.inlineNamespace, nullptr, finder.inlineNamespace,
         ir::SemanticMode::Static}};
    std::vector<ir::PointerUse<clang::Decl>> staticAssertions{
        {finder.staticAssertion, ir::SemanticMode::Static}};
    std::vector<ir::PointerUse<clang::NamedDecl>> templateAliases{
        {finder.aliasTemplate, ir::SemanticMode::Template}};
    std::vector<ir::PointerUse<clang::NamedDecl>> templateInstances{
        {finder.boxSpecialization, ir::SemanticMode::Template}};

    std::vector<ir::PointerUse<clang::NamedDecl>> selectedNames{
        {finder.templatedEnumerator, ir::SemanticMode::Template}};

    ir::BuildSelection selection;
    selection.names = selectedNames;
    selection.objectDeclarations = objectUses;
    selection.globalDeclarations = globalUses;
    selection.declarationTemplateParameters = parameterUses;
    selection.rootDeclarations = roots;
    selection.namespaceAliases = namespaceAliases;
    selection.staticAssertions = staticAssertions;
    selection.templateAliases = templateAliases;
    selection.templateInstances = templateInstances;
    auto artifact = ir::IRBuilder::build(ast->getASTContext(), selection, sema);
    if (!artifact) {
        std::cerr << llvm::toString(artifact.takeError()) << '\n';
        return 1;
    }
    if (!artifact->unit || !artifact->unit->finished() ||
        artifact->objectValues.size() != objectUses.size() ||
        artifact->globalDeclarations.size() != globalUses.size() ||
        artifact->declarationTemplateParameters.size() !=
            parameterUses.size() ||
        artifact->unit->rootEvents().size() < roots.size() ||
        artifact->unit->nonRootEvents().size() != 8) {
        std::cerr << "declaration artifact cardinality mismatch\n";
        return 1;
    }

    auto node = [&](ir::NodeId id) -> const ir::Node * {
        auto value = artifact->unit->nodes().get(id);
        if (!value) {
            llvm::consumeError(value.takeError());
            return nullptr;
        }
        return *value;
    };
    if (node(artifact->objectValues[7])->constructor !=
            ir::Constructor::ObjectFunction ||
        node(artifact->globalDeclarations[6])->constructor !=
            ir::Constructor::GlobalConstant ||
        node(artifact->globalDeclarations[7])->constructor !=
            ir::Constructor::GlobalConstant) {
        std::cerr << "eager declaration helper reduction mismatch\n";
        return 1;
    }
    const ir::Node *pureGlobal = node(artifact->globalDeclarations[11]);
    const auto *pureStructRef =
        pureGlobal && pureGlobal->arguments.size() == 1
            ? std::get_if<ir::NodeRef>(&pureGlobal->arguments[0].payload)
            : nullptr;
    const ir::Node *pureStruct =
        pureStructRef ? node(pureStructRef->value) : nullptr;
    const auto *pureOverrides =
        pureStruct && pureStruct->arguments.size() > 3
            ? std::get_if<ir::SequenceValue>(&pureStruct->arguments[3].payload)
            : nullptr;
    if (!pureGlobal ||
        pureGlobal->constructor != ir::Constructor::GlobalStruct ||
        !pureStruct || !pureOverrides || !pureOverrides->elements.empty()) {
        std::cerr << "pure virtual override filtering mismatch\n";
        return 1;
    }
    auto verifyTree = [&](ir::NodeId root, bool rejectMethods,
                          bool requireLayout) {
        std::vector<ir::NodeId> pending{root};
        std::vector<bool> seen(artifact->unit->nodes().size(), false);
        bool sawLayout = false;
        while (!pending.empty()) {
            const ir::NodeId current = pending.back();
            pending.pop_back();
            if (seen[current.value()])
                return false;
            seen[current.value()] = true;
            const ir::Node *currentNode = node(current);
            if (!currentNode || (rejectMethods &&
                                 currentNode->category == ir::Category::Method))
                return false;
            if (currentNode->category == ir::Category::LayoutInfo) {
                sawLayout = true;
                if (currentNode->origins.empty())
                    return false;
                const source::Origin &origin =
                    artifact->unit->sources()
                        .origins[currentNode->origins.front().value()];
                if (origin.kind != source::OriginKind::Cpp2vSynthesized ||
                    !origin.anchor)
                    return false;
            }
            auto children = artifact->unit->nodes().children(current);
            if (!children) {
                llvm::consumeError(children.takeError());
                return false;
            }
            pending.insert(pending.end(), children->begin(), children->end());
        }
        return !requireLayout || sawLayout;
    };
    if (!verifyTree(artifact->objectValues[7], true, false) ||
        !verifyTree(artifact->globalDeclarations[3], false, true) ||
        !verifyTree(artifact->globalDeclarations[6], false, false) ||
        !verifyTree(artifact->globalDeclarations[7], false, false)) {
        std::cerr << "declaration shape/provenance tree mismatch\n";
        return 1;
    }

    const clang::SourceManager &sourceManager = ast->getSourceManager();
    auto onlyChild = [&](ir::NodeId parent) -> std::optional<ir::NodeId> {
        auto children = artifact->unit->nodes().children(parent);
        if (!children || children->size() != 1)
            return std::nullopt;
        return children->front();
    };
    const auto recordStructId = onlyChild(artifact->globalDeclarations[3]);
    auto recordChildren =
        recordStructId
            ? artifact->unit->nodes().children(*recordStructId)
            : llvm::Expected<std::vector<ir::NodeId>>(llvm::createStringError(
                  std::errc::invalid_argument, "missing record value"));
    const clang::CXXBaseSpecifier &writtenBase = *record->bases_begin();
    const clang::SourceLocation baseBegin =
        writtenBase.getTypeSourceInfo()
            ? writtenBase.getTypeSourceInfo()->getTypeLoc().getBeginLoc()
            : writtenBase.getBeginLoc();
    if (!recordStructId || !recordChildren || recordChildren->size() < 2 ||
        !originKindBeginsAt(*artifact, (*recordChildren)[0],
                            source::OriginKind::Explicit, sourceManager,
                            baseBegin) ||
        !firstOriginAnchorBeginsAt(*artifact, (*recordChildren)[1],
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   baseBegin) ||
        !firstOriginAnchorsNodeOrigin(*artifact, (*recordChildren)[1],
                                      (*recordChildren)[0])) {
        if (!recordChildren)
            llvm::consumeError(recordChildren.takeError());
        std::cerr << "base written/layout provenance mismatch\n";
        return 1;
    }

    const ir::Node *recordStruct = node(*recordStructId);
    const auto *destructorNameRef =
        recordStruct && recordStruct->arguments.size() > 4
            ? std::get_if<ir::NodeRef>(&recordStruct->arguments[4].payload)
            : nullptr;
    auto destructorNameChildren =
        destructorNameRef
            ? artifact->unit->nodes().children(destructorNameRef->value)
            : llvm::Expected<std::vector<ir::NodeId>>(llvm::createStringError(
                  std::errc::invalid_argument, "missing destructor name"));
    if (!destructorNameRef || !destructorNameChildren ||
        destructorNameChildren->empty() ||
        !firstOriginAnchorBeginsAt(*artifact, destructorNameRef->value,
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   record->getBeginLoc()) ||
        !firstOriginAnchorBeginsAt(*artifact, destructorNameChildren->back(),
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   record->getBeginLoc())) {
        if (!destructorNameChildren)
            llvm::consumeError(destructorNameChildren.takeError());
        std::cerr << "generated destructor-name provenance mismatch\n";
        return 1;
    }

    auto returnTypeLocation = [](const clang::FunctionDecl &declaration) {
        const clang::TypeSourceInfo *written = declaration.getTypeSourceInfo();
        if (!written)
            return clang::SourceLocation{};
        clang::FunctionTypeLoc functionLocation =
            written->getTypeLoc().getAs<clang::FunctionTypeLoc>();
        return functionLocation ? functionLocation.getReturnLoc().getBeginLoc()
                                : clang::SourceLocation{};
    };
    const auto functionRecordId = onlyChild(artifact->objectValues[3]);
    const auto staticFunctionRecordId = onlyChild(artifact->objectValues[7]);
    auto functionChildren =
        functionRecordId
            ? artifact->unit->nodes().children(*functionRecordId)
            : llvm::Expected<std::vector<ir::NodeId>>(llvm::createStringError(
                  std::errc::invalid_argument, "missing function record"));
    auto staticFunctionChildren =
        staticFunctionRecordId
            ? artifact->unit->nodes().children(*staticFunctionRecordId)
            : llvm::Expected<std::vector<ir::NodeId>>(
                  llvm::createStringError(std::errc::invalid_argument,
                                          "missing static function record"));
    const auto enumTypeId = onlyChild(artifact->globalDeclarations[5]);
    if (!functionRecordId || !staticFunctionRecordId || !functionChildren ||
        functionChildren->empty() || !staticFunctionChildren ||
        staticFunctionChildren->empty() || !enumTypeId ||
        !originKindBeginsAt(*artifact, functionChildren->front(),
                            source::OriginKind::Explicit, sourceManager,
                            returnTypeLocation(*function)) ||
        !originKindBeginsAt(*artifact, staticFunctionChildren->front(),
                            source::OriginKind::Explicit, sourceManager,
                            returnTypeLocation(*staticMethod)) ||
        !originKindBeginsAt(*artifact, *enumTypeId,
                            source::OriginKind::Explicit, sourceManager,
                            finder.enumeration->getIntegerTypeSourceInfo()
                                ->getTypeLoc()
                                .getBeginLoc()) ||
        !hasOrderedTransformedDerivation(*artifact,
                                         artifact->objectValues[7]) ||
        !hasOrderedTransformedDerivation(*artifact, *staticFunctionRecordId)) {
        if (!functionChildren)
            llvm::consumeError(functionChildren.takeError());
        if (!staticFunctionChildren)
            llvm::consumeError(staticFunctionChildren.takeError());
        std::cerr << "declaration written/transformed provenance mismatch\n";
        return 1;
    }

    auto constantChildren =
        artifact->unit->nodes().children(artifact->globalDeclarations[6]);
    auto castChildren =
        constantChildren && constantChildren->size() == 2
            ? artifact->unit->nodes().children(constantChildren->back())
            : llvm::Expected<std::vector<ir::NodeId>>(llvm::createStringError(
                  std::errc::invalid_argument, "malformed enum constant"));
    auto literalChildren =
        castChildren && castChildren->size() == 2
            ? artifact->unit->nodes().children(castChildren->back())
            : llvm::Expected<std::vector<ir::NodeId>>(llvm::createStringError(
                  std::errc::invalid_argument, "malformed enum constant cast"));
    const clang::SourceLocation constantBegin =
        finder.enumerators.front()->getBeginLoc();
    const clang::SourceLocation underlyingBegin =
        finder.enumeration->getIntegerTypeSourceInfo()
            ->getTypeLoc()
            .getBeginLoc();
    if (!constantChildren || constantChildren->size() != 2 || !castChildren ||
        castChildren->size() != 2 || !literalChildren ||
        literalChildren->size() != 1 ||
        !firstOriginAnchorBeginsAt(*artifact, constantChildren->back(),
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   constantBegin) ||
        !firstOriginAnchorBeginsAt(*artifact, castChildren->front(),
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   constantBegin) ||
        !firstOriginAnchorBeginsAt(*artifact, castChildren->back(),
                                   source::OriginKind::Cpp2vSynthesized,
                                   source::OriginKind::Explicit, sourceManager,
                                   constantBegin) ||
        !firstOriginAnchorsNodeOrigin(*artifact, constantChildren->back(),
                                      artifact->globalDeclarations[6]) ||
        !firstOriginAnchorsNodeOrigin(*artifact, castChildren->front(),
                                      artifact->globalDeclarations[6]) ||
        !firstOriginAnchorsNodeOrigin(*artifact, castChildren->back(),
                                      artifact->globalDeclarations[6]) ||
        !originKindBeginsAt(*artifact, literalChildren->front(),
                            source::OriginKind::Explicit, sourceManager,
                            underlyingBegin)) {
        if (!constantChildren)
            llvm::consumeError(constantChildren.takeError());
        if (!castChildren)
            llvm::consumeError(castChildren.takeError());
        if (!literalChildren)
            llvm::consumeError(literalChildren.takeError());
        std::cerr << "enum helper provenance mismatch\n";
        return 1;
    }
    for (const ir::RootEvent &root : fallbackArtifact->unit->rootEvents()) {
        if (root.kind != ir::RootKind::Symbol)
            continue;
        auto value = fallbackArtifact->unit->nodes().get(root.semanticValue);
        if (!value || (*value)->origins.empty()) {
            if (!value)
                llvm::consumeError(value.takeError());
            std::cerr << "implicit fallback has no direct origin\n";
            return 1;
        }
        const source::Origin &origin =
            fallbackArtifact->unit->sources()
                .origins[(*value)->origins.front().value()];
        if (origin.kind != source::OriginKind::Implicit || !origin.anchor) {
            std::cerr << "implicit fallback origin kind/anchor mismatch\n";
            return 1;
        }
    }
    for (const ir::NonRootEvent &event : artifact->unit->nonRootEvents()) {
        const bool hasOrigin = std::visit(
            [](const auto &typed) { return !typed.origins.empty(); }, event);
        if (!hasOrigin) {
            std::cerr << "non-root event lost its declaration origin\n";
            return 1;
        }
    }

    ::Module productionModule(Trace::NONE);
    const ::Module::Flags ordinary{false, false};
    const ::Module::Flags templated{true, false};
    const ::Module::Flags specialized{false, true};
    productionModule.add_declaration(*external, ordinary);
    productionModule.add_definition(*function, ordinary);
    productionModule.add_definition(*fallbackOnly, ordinary);
    productionModule.add_definition(*finder.boxSpecialization, specialized);
    productionModule.add_declaration(*finder.aliasTemplate, templated);
    productionModule.add_definition(
        *finder.functionTemplate->getTemplatedDecl(), templated);
    productionModule.add_namespace_alias(alphaAlias);
    productionModule.add_namespace_alias(finder.namespaceAlias);
    productionModule.add_namespace_alias(zetaAlias);
    productionModule.add_inline_namespace(finder.inlineNamespace);
    productionModule.add_namespace_alias(middleAlias);
    productionModule.add_assert(*finder.staticAssertion);
    productionModule.add_declaration(*finder.templatedEnumeration, templated);
    productionModule.add_declaration(*finder.templatedEnumerator, templated);
    auto productionArtifact = ir::IRBuilder::buildModule(
        ast->getASTContext(), productionModule, sema);
    if (!productionArtifact) {
        std::cerr << llvm::toString(productionArtifact.takeError()) << '\n';
        return 1;
    }
    const auto productionSeeds =
        ir::IRSharing::productionSeeds(*productionArtifact->unit);
    if (!productionArtifact->unit->finished() ||
        productionArtifact->unit->rootEvents().size() != 15 ||
        productionArtifact->unit->nonRootEvents().size() != 8 ||
        productionArtifact->unit->orderedEvents().size() != 23 ||
        productionSeeds.size() != 6) {
        std::cerr << "ModuleBuilder partition adapter mismatch: roots="
                  << productionArtifact->unit->rootEvents().size()
                  << " nonroots="
                  << productionArtifact->unit->nonRootEvents().size()
                  << " ordered="
                  << productionArtifact->unit->orderedEvents().size()
                  << " seeds=" << productionSeeds.size() << '\n';
        return 1;
    }
    const auto &ordered = productionArtifact->unit->orderedEvents();
    if (ordered.empty() || ordered.front().kind != ir::OrderedEventKind::Root ||
        ordered.back().kind != ir::OrderedEventKind::Root) {
        std::cerr << "ordered module event stream mismatch:";
        for (const ir::OrderedEventRef &event : ordered)
            std::cerr << ' '
                      << (event.kind == ir::OrderedEventKind::Root ? 'R' : 'N');
        std::cerr << '\n';
        return 1;
    }
    unsigned templateEnums = 0;
    unsigned templateEnumConstants = 0;
    for (const ir::RootEvent &root : productionArtifact->unit->rootEvents()) {
        if (root.kind != ir::RootKind::TemplateType)
            continue;
        auto children =
            productionArtifact->unit->nodes().children(root.semanticValue);
        if (!children || children->empty()) {
            if (!children)
                llvm::consumeError(children.takeError());
            std::cerr << "malformed template global root\n";
            return 1;
        }
        auto value = productionArtifact->unit->nodes().get(children->back());
        if (!value) {
            std::cerr << llvm::toString(value.takeError()) << '\n';
            return 1;
        }
        templateEnums +=
            (*value)->constructor == ir::Constructor::GlobalEnum ? 1 : 0;
        templateEnumConstants +=
            (*value)->constructor == ir::Constructor::GlobalConstant ? 1 : 0;
    }
    if (templateEnums != 1 || templateEnumConstants != 0) {
        std::cerr << "templated enum root suppression mismatch\n";
        return 1;
    }

    const auto seeds = ir::IRSharing::productionSeeds(*artifact->unit);
    if (seeds.size() != roots.size() || seeds[0].semanticName ||
        seeds[1].semanticName || seeds[2].semanticName ||
        !seeds[3].semanticName ||
        seeds[24].kind != ir::SharingSeedKind::TemplateOnly ||
        seeds[25].kind != ir::SharingSeedKind::TemplateOnly ||
        seeds[26].kind != ir::SharingSeedKind::TemplateOnly) {
        std::cerr << "production sharing seed mismatch\n";
        return 1;
    }
    auto sharing = ir::IRSharing::analyze(*artifact->unit, seeds);
    if (!sharing) {
        std::cerr << llvm::toString(sharing.takeError()) << '\n';
        return 1;
    }

    for (const ir::RootEvent &root : artifact->unit->rootEvents()) {
        auto value = artifact->unit->nodes().get(root.semanticValue);
        auto name = artifact->unit->nodes().get(root.semanticName);
        if (!value || !name || (*name)->category != ir::Category::Name ||
            (*value)->origins.empty()) {
            std::cerr << "root provenance/category mismatch\n";
            return 1;
        }
        auto children = artifact->unit->nodes().children(root.semanticValue);
        if (!children) {
            std::cerr << llvm::toString(children.takeError()) << '\n';
            return 1;
        }
    }

    ir::SemanticRocqEmitter emitter;
    auto renderIn = [&](const ir::TranslationUnitIR &unit,
                        ir::NodeId value) -> std::optional<std::string> {
        auto result = emitter.renderNode(unit, value);
        if (!result) {
            std::cerr << llvm::toString(result.takeError()) << '\n';
            return std::nullopt;
        }
        return *result;
    };
    auto render = [&](ir::NodeId value) {
        return renderIn(*artifact->unit, value);
    };
    std::vector<std::pair<std::string, std::string>> ordinaryObjects;
    std::vector<std::pair<std::string, std::string>> ordinaryGlobals;
    std::vector<std::pair<std::string, std::string>> templateObjects;
    std::vector<std::pair<std::string, std::string>> templateGlobals;
    for (const ir::RootEvent &root : artifact->unit->rootEvents()) {
        auto nameText = render(root.semanticName);
        auto valueText = render(root.semanticValue);
        if (!nameText || !valueText)
            return 1;
        switch (root.kind) {
        case ir::RootKind::Symbol:
            ordinaryObjects.emplace_back(*nameText, *valueText);
            break;
        case ir::RootKind::Type:
            ordinaryGlobals.emplace_back(*nameText, *valueText);
            break;
        case ir::RootKind::TemplateSymbol:
            templateObjects.emplace_back(*nameText, *valueText);
            break;
        case ir::RootKind::TemplateType:
            templateGlobals.emplace_back(*nameText, *valueText);
            break;
        }
    }

    std::vector<std::pair<std::string, std::string>> exceptionObjects;
    for (const ir::RootEvent &root : exceptionArtifact->unit->rootEvents()) {
        auto nameText = renderIn(*exceptionArtifact->unit, root.semanticName);
        auto valueText = renderIn(*exceptionArtifact->unit, root.semanticValue);
        if (!nameText || !valueText)
            return 1;
        exceptionObjects.emplace_back(*nameText, *valueText);
        auto outerChildren =
            exceptionArtifact->unit->nodes().children(root.semanticValue);
        if (!outerChildren || outerChildren->size() != 1) {
            if (!outerChildren)
                llvm::consumeError(outerChildren.takeError());
            std::cerr << "malformed exception object root\n";
            return 1;
        }
        auto record =
            exceptionArtifact->unit->nodes().get(outerChildren->front());
        if (!record) {
            std::cerr << llvm::toString(record.takeError()) << '\n';
            return 1;
        }
        const std::size_t exceptionIndex =
            (*record)->constructor == ir::Constructor::ConstructorRecord ? 4
                                                                         : 2;
        const auto *exception =
            (*record)->arguments.size() > exceptionIndex
                ? std::get_if<ir::ScalarTerm>(
                      &(*record)->arguments[exceptionIndex].payload)
                : nullptr;
        if (!exception || exception->text != "exception_spec.NoThrow") {
            std::cerr << "unevaluated exception spec did not resolve\n";
            return 1;
        }
    }

    std::vector<std::pair<std::string, std::string>> duplicateObjects;
    for (const ir::RootEvent &root : duplicateArtifact->unit->rootEvents()) {
        auto nameText =
            emitter.renderNode(*duplicateArtifact->unit, root.semanticName);
        auto valueText =
            emitter.renderNode(*duplicateArtifact->unit, root.semanticValue);
        if (!nameText || !valueText) {
            if (!nameText)
                std::cerr << llvm::toString(nameText.takeError()) << '\n';
            if (!valueText)
                std::cerr << llvm::toString(valueText.takeError()) << '\n';
            return 1;
        }
        duplicateObjects.emplace_back(*nameText, *valueText);
    }
    if (duplicateObjects.size() != 2 ||
        duplicateObjects[0].first != duplicateObjects[1].first ||
        duplicateObjects[0].second == duplicateObjects[1].second) {
        std::cerr << "ordered compatible duplicate roots mismatch\n";
        return 1;
    }

    std::vector<std::pair<std::string, std::string>> duplicateTemplateGlobals;
    for (const ir::RootEvent &root :
         templateDuplicateArtifact->unit->rootEvents()) {
        auto nameText = emitter.renderNode(*templateDuplicateArtifact->unit,
                                           root.semanticName);
        auto valueText = emitter.renderNode(*templateDuplicateArtifact->unit,
                                            root.semanticValue);
        if (!nameText || !valueText) {
            if (!nameText)
                std::cerr << llvm::toString(nameText.takeError()) << '\n';
            if (!valueText)
                std::cerr << llvm::toString(valueText.takeError()) << '\n';
            return 1;
        }
        duplicateTemplateGlobals.emplace_back(*nameText, *valueText);
    }
    if (duplicateTemplateGlobals.size() != 2 ||
        duplicateTemplateGlobals[0].first !=
            duplicateTemplateGlobals[1].first ||
        duplicateTemplateGlobals[0].second ==
            duplicateTemplateGlobals[1].second) {
        std::cerr << "ordered template duplicate roots mismatch\n";
        return 1;
    }

    std::vector<std::pair<std::string, std::string>> fallbackObjects;
    for (const ir::RootEvent &root : fallbackArtifact->unit->rootEvents()) {
        if (root.kind != ir::RootKind::Symbol)
            continue;
        auto nameText =
            emitter.renderNode(*fallbackArtifact->unit, root.semanticName);
        auto valueText =
            emitter.renderNode(*fallbackArtifact->unit, root.semanticValue);
        if (!nameText || !valueText) {
            if (!nameText)
                std::cerr << llvm::toString(nameText.takeError()) << '\n';
            if (!valueText)
                std::cerr << llvm::toString(valueText.takeError()) << '\n';
            return 1;
        }
        fallbackObjects.emplace_back(*nameText, *valueText);
    }
    if (fallbackObjects.size() != 6) {
        std::cerr << "implicit fallback object count mismatch\n";
        return 1;
    }

    std::vector<std::pair<std::string, std::string>> aliasEvents;
    std::vector<std::string> assertionEvents;
    std::vector<std::pair<std::string, std::string>> aliasTemplateEvents;
    std::vector<std::pair<std::string, std::string>> instanceEvents;
    for (const ir::NonRootEvent &event : artifact->unit->nonRootEvents()) {
        bool ok = std::visit(
            [&](const auto &typed) -> bool {
                using T = std::decay_t<decltype(typed)>;
                if constexpr (std::is_same_v<T, ir::NamespaceAliasEvent>) {
                    std::string from = "None";
                    if (typed.from) {
                        auto value = render(*typed.from);
                        if (!value)
                            return false;
                        from = "(Some " + *value + ")";
                    }
                    auto to = render(typed.to);
                    if (!to)
                        return false;
                    aliasEvents.emplace_back(std::move(from), *to);
                } else if constexpr (std::is_same_v<T, ir::StaticAssertEvent>) {
                    auto condition = render(typed.condition);
                    if (!condition)
                        return false;
                    const std::string message =
                        typed.message ? rocqString(typed.message->text)
                                      : "\"\"";
                    assertionEvents.push_back("(Build_StaticAssert " + message +
                                              " " + *condition + ")");
                } else if constexpr (std::is_same_v<T,
                                                    ir::TemplateAliasEvent>) {
                    auto name = render(typed.semanticName);
                    auto value = render(typed.templateValue);
                    if (!name || !value)
                        return false;
                    aliasTemplateEvents.emplace_back(*name, *value);
                } else {
                    auto name = render(typed.canonicalKey);
                    auto value = render(typed.value);
                    if (!name || !value)
                        return false;
                    instanceEvents.emplace_back(*name, *value);
                }
                return true;
            },
            event);
        if (!ok)
            return 1;
    }

    std::vector<std::pair<std::string, std::string>> productionAliasEvents;
    for (const ir::OrderedEventRef &reference : ordered) {
        if (reference.kind != ir::OrderedEventKind::NonRoot)
            continue;
        const ir::NonRootEvent &event =
            productionArtifact->unit->nonRootEvents()[reference.index];
        const auto *alias = std::get_if<ir::NamespaceAliasEvent>(&event);
        if (!alias)
            continue;
        std::string from = "None";
        if (alias->from) {
            auto value = renderIn(*productionArtifact->unit, *alias->from);
            if (!value)
                return 1;
            from = "(Some " + *value + ")";
        }
        auto to = renderIn(*productionArtifact->unit, alias->to);
        if (!to)
            return 1;
        productionAliasEvents.emplace_back(std::move(from), *to);
    }
    if (productionAliasEvents != aliasEvents) {
        std::cerr << "production namespace alias ordering mismatch\nexpected:";
        for (const auto &[from, to] : aliasEvents)
            std::cerr << " [" << from << " -> " << to << ']';
        std::cerr << "\nactual:";
        for (const auto &[from, to] : productionAliasEvents)
            std::cerr << " [" << from << " -> " << to << ']';
        std::cerr << '\n';
        return 1;
    }
    if (artifact->names.size() != 1) {
        std::cerr << "suppressed enum name selection mismatch\n";
        return 1;
    }
    auto suppressedEnumName = render(artifact->names.front());
    if (!suppressedEnumName)
        return 1;

    std::cout << "Require Import skylabs.lang.cpp.mparser.\n"
                 "#[local] Open Scope pstring_scope.\n\n"
              << "Module " << module << ".\n\n";
    emitPairs("ordinary_objects", "ObjValue", ordinaryObjects);
    emitPairs("duplicate_globals", "GlobDecl", duplicateObjects);
    emitPairs("duplicate_template_globals", "template GlobDecl",
              duplicateTemplateGlobals);
    emitPairs("fallback_objects", "ObjValue", fallbackObjects);
    emitPairs("exception_holder_objects", "ObjValue", exceptionObjects);
    emitPairs("ordinary_globals", "GlobDecl", ordinaryGlobals);
    emitPairs("template_objects", "template ObjValue", templateObjects);
    emitPairs("template_globals", "template GlobDecl", templateGlobals);
    emitTypedPairs("namespace_alias_events", "option name", "name",
                   aliasEvents);
    emitTypedPairs("production_namespace_alias_events", "option name", "name",
                   productionAliasEvents);
    std::cout
        << "Definition static_assertion_events : list StaticAssert :=\n  ";
    for (const std::string &event : assertionEvents)
        std::cout << event << " ::\n  ";
    std::cout << "nil.\n\n";
    emitPairs("template_alias_events", "template type", aliasTemplateEvents);
    emitPairs("template_instance_events", "tpreinst", instanceEvents);
    std::cout << "Definition suppressed_template_enum_constant_name : name := "
              << *suppressedEnumName << ".\n"
              << "Definition production_template_enum_count : nat := "
              << templateEnums << ".\n"
              << "Definition production_template_enum_constant_count : nat := "
              << templateEnumConstants << ".\n"
              << "Definition production_seed_count : nat := " << seeds.size()
              << ".\n"
              << "Definition sharing_definition_count : nat := "
              << sharing->definitions().size() << ".\n\n"
              << "End " << module << ".\n";
    return 0;
}
