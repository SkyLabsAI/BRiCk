/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilder.hpp"
#include "RocqEmitter.hpp"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/MemoryBuffer.h>

namespace {

class Finder : public clang::RecursiveASTVisitor<Finder> {
public:
    bool shouldVisitImplicitCode() const { return true; }
    bool VisitNamedDecl(clang::NamedDecl *declaration) {
        all.push_back(declaration);
        return true;
    }
    const clang::NamedDecl *named(llvm::StringRef name) const {
        for (const clang::NamedDecl *declaration : all)
            if (const clang::IdentifierInfo *identifier =
                    declaration->getIdentifier())
                if (identifier->getName() == name && !declaration->isImplicit())
                    return declaration;
        return nullptr;
    }
    const clang::NamespaceDecl *anonymousNamespace() const {
        for (const clang::NamedDecl *declaration : all)
            if (const auto *space =
                    llvm::dyn_cast<clang::NamespaceDecl>(declaration))
                if (space->isAnonymousNamespace())
                    return space;
        return nullptr;
    }
    const clang::RecordDecl *anonymousRecord(bool withField) const {
        for (const clang::NamedDecl *declaration : all) {
            const auto *record = llvm::dyn_cast<clang::RecordDecl>(declaration);
            if (!record || record->getIdentifier() || record->isImplicit())
                continue;
            bool hasNamedField = false;
            for (const clang::FieldDecl *field : record->fields())
                hasNamedField |= field->getIdentifier() != nullptr;
            if (hasNamedField == withField && record->getDeclContext() &&
                (record->getDeclContext()->isTranslationUnit() ||
                 llvm::isa<clang::RecordDecl>(record->getDeclContext())))
                return record;
        }
        return nullptr;
    }
    const clang::RecordDecl *recordWithTypedef(llvm::StringRef name) const {
        for (const clang::NamedDecl *declaration : all)
            if (const auto *record =
                    llvm::dyn_cast<clang::RecordDecl>(declaration))
                if (const auto *typeName = record->getTypedefNameForAnonDecl())
                    if (typeName->getName() == name)
                        return record;
        return nullptr;
    }
    const clang::RecordDecl *recordWithField(llvm::StringRef name) const {
        for (const clang::NamedDecl *declaration : all)
            if (const auto *record =
                    llvm::dyn_cast<clang::RecordDecl>(declaration))
                for (const clang::FieldDecl *field : record->fields())
                    if (field->getName() == name)
                        return record;
        return nullptr;
    }
    const clang::CXXRecordDecl *implicitRecord(llvm::StringRef name) const {
        for (const clang::NamedDecl *declaration : all)
            if (const auto *record =
                    llvm::dyn_cast<clang::CXXRecordDecl>(declaration))
                if (record->isImplicit() && record->getName() == name)
                    return record;
        return nullptr;
    }

    std::vector<clang::NamedDecl *> all;
};

bool fail(const std::string &message) {
    std::cerr << "name-builder probe: " << message << '\n';
    return false;
}

} // namespace

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr << "usage: cpp2v-name-builder-probe SOURCE [-- ARGS...]\n";
        return 2;
    }
    auto buffer = llvm::MemoryBuffer::getFile(argv[1]);
    if (!buffer) {
        std::cerr << "cannot read " << argv[1] << '\n';
        return 2;
    }
    std::vector<std::string> arguments{"-std=c++17"};
    bool afterDash = false;
    for (int i = 2; i < argc; ++i) {
        if (std::string(argv[i]) == "--")
            afterDash = true;
        else if (afterDash)
            arguments.emplace_back(argv[i]);
        else {
            std::cerr << "unknown argument " << argv[i] << '\n';
            return 2;
        }
    }
    auto ast = clang::tooling::buildASTFromCodeWithArgs((*buffer)->getBuffer(),
                                                        arguments, argv[1]);
    if (!ast) {
        std::cerr << "could not build AST\n";
        return 1;
    }
    Finder finder;
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    const auto *global = finder.named("global_value");
    const auto *space = finder.named("scope");
    const auto *scoped = finder.named("scoped_value");
    const auto *record = finder.named("Record");
    const auto *member = finder.named("member_value");
    const auto *anonymousSpace = finder.anonymousNamespace();
    const auto *firstDecl = finder.anonymousRecord(true);
    const auto *typedefRecord = finder.recordWithTypedef("Alias");
    const auto *globalAnonymous = finder.recordWithField("leaked_field");
    const auto *implicitRecord = finder.implicitRecord("Record");
    const clang::RecordDecl *anonymousIndex = nullptr;
    const clang::RecordDecl *firstChild = nullptr;
    for (clang::NamedDecl *declaration : finder.all) {
        const auto *candidate = llvm::dyn_cast<clang::RecordDecl>(declaration);
        if (!candidate || candidate->getIdentifier() || candidate->isImplicit())
            continue;
        if (const auto *parent = llvm::dyn_cast<clang::RecordDecl>(
                candidate->getDeclContext())) {
            if (parent->getName() != "Holder")
                continue;
            bool hasField = false;
            for (const auto *field : candidate->fields())
                hasField |= field->getIdentifier() != nullptr;
            (hasField ? firstChild : anonymousIndex) = candidate;
        }
    }
    const auto *firstDeclarationSource = finder.named("by_decl");
    const auto *firstChildSource = finder.named("child");
    const auto *typedefSource = finder.named("Alias");
    const auto *function = finder.named("unported_function");
    if (!global || !space || !scoped || !record || !member || !anonymousSpace ||
        !firstDecl || !anonymousIndex || !firstChild || !typedefRecord ||
        !globalAnonymous || !implicitRecord || !firstDeclarationSource ||
        !firstChildSource || !typedefSource || !function)
        return fail("fixture declarations were not found") ? 0 : 1;

    std::vector<const clang::NamedDecl *> requested{
        global,     space,          scoped,    record,
        member,     anonymousSpace, firstDecl, anonymousIndex,
        firstChild, typedefRecord,  global,    function};
    auto artifact = ir::IRBuilder::buildNames(ast->getASTContext(), requested);
    if (!artifact) {
        std::cerr << llvm::toString(artifact.takeError()) << '\n';
        return 1;
    }
    if (!artifact->unit || !artifact->unit->finished() ||
        artifact->names.size() != requested.size())
        return fail("builder did not return a finished owned artifact") ? 0 : 1;
    if (artifact->names.front() == artifact->names[10])
        return fail("equal requested names reused an occurrence") ? 0 : 1;

    ir::SemanticRocqEmitter emitter;
    const std::vector<std::string> expected{
        "(Nglobal (Nid \"global_value\"))",
        "(Nglobal (Nid \"scope\"))",
        "(Nscoped (Nglobal (Nid \"scope\")) (Nid \"scoped_value\"))",
        "(Nglobal (Nid \"Record\"))",
        "(Nscoped (Nglobal (Nid \"Record\")) (Nid \"member_value\"))",
        "(Nglobal (Nanonymous))",
        "(Nglobal (Nfirst_decl \"by_decl\"))",
        "(Nscoped (Nglobal (Nid \"Holder\")) (Nanon 0))",
        "(Nscoped (Nglobal (Nid \"Holder\")) (Nfirst_child \"child\"))",
        "(Nglobal (Nid \"Alias\"))",
        "(Nglobal (Nid \"global_value\"))",
        "(Nglobal (core.Nfunction function_qualifiers.N \"unported_function\" "
        "nil))"};
    for (std::size_t i = 0; i < artifact->names.size(); ++i) {
        auto rendered = emitter.renderNode(*artifact->unit, artifact->names[i]);
        if (!rendered) {
            std::cerr << llvm::toString(rendered.takeError()) << '\n';
            return 1;
        }
        if (*rendered != expected[i])
            return fail("semantic term mismatch: " + *rendered) ? 0 : 1;
        std::cout << *rendered << '\n';
        auto nameNode = artifact->unit->nodes().get(artifact->names[i]);
        if (!nameNode || (*nameNode)->origins.empty())
            return fail("name occurrence lacks its written origin") ? 0 : 1;
        const source::Origin &written =
            artifact->unit->sources()
                .origins[(*nameNode)->origins.front().value()];
        if (written.kind != source::OriginKind::Explicit)
            return fail("name's first origin is not its written declaration")
                       ? 0
                       : 1;
        auto children = artifact->unit->nodes().children(artifact->names[i]);
        const std::size_t wantedChildren =
            (*nameNode)->constructor == ir::Constructor::NameScoped ? 2 : 1;
        if (!children || children->size() != wantedChildren)
            return fail("name child order/arity mismatch") ? 0 : 1;
        if ((*nameNode)->constructor == ir::Constructor::NameScoped) {
            auto scopeNode = artifact->unit->nodes().get((*children)[0]);
            auto atomicNode = artifact->unit->nodes().get((*children)[1]);
            if (!scopeNode || !atomicNode ||
                (*scopeNode)->category != ir::Category::Name ||
                (*atomicNode)->category != ir::Category::AtomicName)
                return fail("Nscoped children are not scope then atomic") ? 0
                                                                          : 1;
        }
    }
    const clang::SourceManager &sourceManager =
        ast->getASTContext().getSourceManager();
    const std::vector<std::pair<std::size_t, const clang::Decl *>> heuristics{
        {6, firstDeclarationSource}, {8, firstChildSource}, {9, typedefSource}};
    for (const auto &entry : heuristics) {
        auto children =
            artifact->unit->nodes().children(artifact->names[entry.first]);
        if (!children)
            return fail("could not inspect heuristic name") ? 0 : 1;
        auto atomic = artifact->unit->nodes().get(children->back());
        if (!atomic || (*atomic)->origins.size() != 2)
            return fail("heuristic atomic name lacks exact provenance") ? 0 : 1;
        const source::OriginId direct = (*atomic)->origins[0];
        const source::Origin &transformed =
            artifact->unit->sources().origins[(*atomic)->origins[1].value()];
        if (transformed.kind != source::OriginKind::ClangTransformed ||
            transformed.derivedFrom != std::vector<source::OriginId>{direct} ||
            !transformed.spelling || !transformed.spelling->begin)
            return fail("heuristic derivation is not direct and exact") ? 0 : 1;
        const clang::SourceLocation sourceBegin =
            sourceManager.getSpellingLoc(entry.second->getBeginLoc());
        if (sourceBegin.isInvalid() ||
            transformed.spelling->begin->byteOffset !=
                sourceManager.getFileOffset(sourceBegin))
            return fail("heuristic origin uses the wrong source declaration")
                       ? 0
                       : 1;
    }

    auto implicit =
        ir::IRBuilder::buildNames(ast->getASTContext(), {implicitRecord});
    if (!implicit || implicit->names.size() != 1)
        return fail("implicit record name did not build") ? 0 : 1;
    auto implicitName = implicit->unit->nodes().get(implicit->names.front());
    if (!implicitName || (*implicitName)->origins.size() != 1 ||
        implicit->unit->sources()
                .origins[(*implicitName)->origins.front().value()]
                .kind != source::OriginKind::Implicit)
        return fail("implicit declaration was not labeled implicit") ? 0 : 1;

    auto unsupportedGlobal =
        ir::IRBuilder::buildNames(ast->getASTContext(), {globalAnonymous});
    if (!unsupportedGlobal || unsupportedGlobal->names.size() != 1)
        return fail("global anonymous record did not build legacy unsupported")
                   ? 0
                   : 1;
    auto globalTerm = emitter.renderNode(*unsupportedGlobal->unit,
                                         unsupportedGlobal->names.front());
    if (!globalTerm ||
        *globalTerm != "(Nglobal (Nunsupported_atomic \"record\"))")
        return fail("global anonymous record differs from legacy unsupported")
                   ? 0
                   : 1;

    return 0;
}
