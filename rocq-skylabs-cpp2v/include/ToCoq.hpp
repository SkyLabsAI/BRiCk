/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "Trace.hpp"
#include <clang/AST/ASTConsumer.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTMutationListener.h>
#include <optional>
#include <string>

namespace clang {
class TranslationUnitDecl;
}

class CoqPrinter;

namespace clang {
class CompilerInstance;
}

using namespace clang;

class ToCoqConsumer : public clang::ASTConsumer, clang::ASTMutationListener {
public:
    using path = std::optional<std::string>;
    explicit ToCoqConsumer(
        clang::CompilerInstance *compiler, const path output_file,
        const path notations_file, const path templates_file,
        const path name_test_file, Trace::Mask trace, bool comment,
        bool sharing, bool type_check, bool elaborate = true,
        bool typedefs = false,
        std::optional<std::string> &&interactive = std::optional<std::string>(),
        std::optional<std::string> &&attributes = std::optional<std::string>())
        : compiler_(compiler), output_file_(output_file),
          notations_file_(notations_file), templates_file_(templates_file),
          name_test_file_(name_test_file), trace_(trace), comment_{comment},
          sharing_{sharing}, elaborate_(elaborate), check_types_{type_check},
          typedefs_{typedefs}, interactive_{std::move(interactive)},
          attributes_{std::move(attributes)} {}

public:
    // Implementation of `clang::ASTConsumer`
    virtual void HandleTranslationUnit(clang::ASTContext &Context) override;

    virtual void HandleTagDeclDefinition(TagDecl *decl) override;
    virtual bool HandleTopLevelDecl(DeclGroupRef decl) override;
    virtual void HandleInlineFunctionDefinition(FunctionDecl *decl) override;
    virtual void
    HandleCXXImplicitFunctionInstantiation(FunctionDecl *decl) override;
    virtual ASTMutationListener *GetASTMutationListener() override {
        return this;
    }

public:
    // Implementation of clang::ASTMutationListener
    virtual void AddedCXXTemplateSpecialization(
        const ClassTemplateDecl *TD,
        const ClassTemplateSpecializationDecl *D) override {
        // TODO [const_cast] is a code-smell.
        // The implementation calls this method from a non-`const` method.
        // it is not clear why this method should take a
        // `const ClassTemplateSpecializationDecl` rather than a non-`const`
        // See question:
        // https://stackoverflow.com/questions/76085015/using-clangs-astconsumer-to-force-generation-of-implicit-members
        elab(const_cast<ClassTemplateSpecializationDecl *>(D), true);
    }

private:
    void toCoqModule(clang::ASTContext *ctxt, clang::TranslationUnitDecl *decl);
    void elab(Decl *, bool rec = false);

private:
    clang::CompilerInstance *compiler_;
    const path output_file_;
    const path notations_file_;
    const path templates_file_;
    const path name_test_file_;
    const Trace::Mask trace_;
    const bool comment_;
    const bool sharing_;
    const bool elaborate_;
    const bool check_types_;
    const bool typedefs_;
    const std::optional<std::string> interactive_;
    const std::optional<std::string> attributes_;
};
