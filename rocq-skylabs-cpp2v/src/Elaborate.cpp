/*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "FromClang.hpp"
#include "Location.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "ToCoq.hpp"
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>

using namespace clang;

static raw_ostream &warning(loc::loc loc, const ASTContext &context,
                            StringRef msg) {
    auto &os = logging::unsupported();
    os << loc::prefix(loc, context) << "warning: " << msg << "\n";
    logging::debug() << loc::dump(loc, context);
    return os;
}

using Flags = ::Module::Flags;

class Elaborate : public DeclVisitorArgs<Elaborate, void, Flags> {
private:
    using Visitor = DeclVisitorArgs<Elaborate, void, Flags>;

    clang::CompilerInstance *const ci_;
    std::set<int64_t> visited_;
    const bool templates_;
    const bool trace_;
    bool recursive_;

    const ASTContext &getContext() const { return ci_->getASTContext(); }

    void warning(const Decl *decl, StringRef msg) {
        ::warning(loc::of(decl), getContext(), msg);
    }

    void trace(StringRef what, const Decl &decl) {
        auto loc = loc::of(decl);
        if (loc::can_trace(loc)) {
            auto &os = llvm::errs();
            auto &context = decl.getASTContext();
            os << "[Elaborate] " << what << " " << loc::trace(loc, context)
               << "\n";
        }
    }

public:
    Elaborate(clang::CompilerInstance *ci, bool templates, Trace::Mask trace,
              bool rec = false)
        : ci_(ci), templates_(templates), trace_(trace & Trace::Elaborate),
          recursive_(rec) {}

    void Visit(Decl *d, Flags flags) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            Visitor::Visit(d, flags);
        }
    }

    void VisitDecl(const Decl *decl, Flags) {
        warning(decl, "cannot elaborate declaration");
    }

#define IGNORE(D)                                                              \
    void Visit##D(const D *, Flags) {}

    IGNORE(AccessSpecDecl)
    IGNORE(EmptyDecl)
    IGNORE(EnumConstantDecl)
    IGNORE(EnumDecl)
    IGNORE(FieldDecl)
    IGNORE(FileScopeAsmDecl)
    IGNORE(IndirectFieldDecl)
    IGNORE(StaticAssertDecl)
    IGNORE(TemplateTypeParmDecl)
    IGNORE(UsingDecl)
    IGNORE(UsingDirectiveDecl)
    IGNORE(UsingShadowDecl)

    // TODO: These may impact structured names
    IGNORE(NamespaceAliasDecl)

    // Clang expands aliases, rather than specialize them
    IGNORE(TypeAliasTemplateDecl)
    IGNORE(TypedefNameDecl)

    // TODO (Discuss): Consider descending to elaborate structures
    // inside function bodies.
    IGNORE(FunctionTemplateDecl)
    IGNORE(FunctionDecl)

    // TODO (Discuss): If we ignore variables, why do we descend into
    // variable templates?
    IGNORE(VarDecl)

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, Flags flags) {
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl,
                                  Flags flags) {
        always_assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void GenerateImplicitMembers(CXXRecordDecl *decl, bool deprecated) {
        if (trace_ && decl)
            trace("special methods", *decl);
        Sema &sema = ci_->getSema();
        if (deprecated) {
            sema.ForceDeclarationOfImplicitMembers(decl);
            return;
        }
        GenerateUndeprecatedImplicitMembers(decl, sema);
    }

    void VisitCXXRecordDecl(CXXRecordDecl *decl, Flags flags) {
        if (decl->isImplicit()) {
            return;
        }
        if (isa<ClassTemplatePartialSpecializationDecl>(decl)) {
            return;
        }

        if (decl->isCompleteDefinition()) {
            // Do *not* generate deprecated members
            GenerateImplicitMembers(decl, false);
        }

        if (recursive_) {
            // find any static functions or fields
            for (auto i : decl->decls()) {
                Visit(i, flags);
            }
        }
    }

    void VisitCXXMethodDecl(CXXMethodDecl *decl, Flags) {
        if (decl->isDeleted() || (!templates_ && decl->isDependentContext()))
            return;

        if (not decl->getBody() && decl->isDefaulted()) {
            if (decl->isMoveAssignmentOperator()) {
                if (trace_)
                    trace("move assignment", *decl);

                ci_->getSema().DefineImplicitMoveAssignment(decl->getLocation(),
                                                            decl);

            } else if (decl->isCopyAssignmentOperator()) {
                if (trace_)
                    trace("copy assignment", *decl);

                ci_->getSema().DefineImplicitCopyAssignment(decl->getLocation(),
                                                            decl);
            } else {
                warning(decl, "cannot generate body for defaulted method");
            }
        }
    }

    void VisitNamespaceDecl(const NamespaceDecl *decl, Flags flags) {
        always_assert(flags.none());

        for (auto d : decl->decls()) {
            this->Visit(d, flags);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, Flags flags) {
        // TODO: This assertion would be off should we wind up
        // descending into function bodies.
        always_assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void VisitCXXConstructorDecl(CXXConstructorDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        if (not decl->getBody() && decl->isDefaulted()) {
            if (decl->isDefaultConstructor()) {
                if (trace_)
                    trace("constructor", *decl);
                ci_->getSema().DefineImplicitDefaultConstructor(
                    decl->getLocation(), decl);
            } else if (decl->isCopyConstructor()) {
                if (trace_)
                    trace("copy constructor", *decl);
                ci_->getSema().DefineImplicitCopyConstructor(
                    decl->getLocation(), decl);
            } else if (decl->isMoveConstructor()) {
                if (trace_)
                    trace("move constructor", *decl);
                ci_->getSema().DefineImplicitMoveConstructor(
                    decl->getLocation(), decl);
            } else {
                warning(decl, "unknown defaulted constructor");
            }
        }
    }

    void VisitCXXDestructorDecl(CXXDestructorDecl *decl, Flags) {
        if (decl->isDeleted())
            return;

        if (not decl->hasBody() && decl->isDefaulted()) {
            if (trace_)
                trace("destructor", *decl);
            ci_->getSema().DefineImplicitDestructor(decl->getLocation(), decl);
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, Flags flags) {
        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitFriendDecl(const FriendDecl *decl, Flags flags) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), flags);
        }
    }
};

void ToCoqConsumer::elab(Decl *d, bool rec) {
    Flags f{false, false};
    if (auto dc = dyn_cast<DeclContext>(d)) {
        f.in_template = dc->isDependentContext();
    }
    if (not f.in_template) {
        Elaborate(compiler_, templates_file_.has_value(), trace_, rec)
            .Visit(d, f);
    }
}

bool ToCoqConsumer::HandleTopLevelDecl(DeclGroupRef decl) {
    if (elaborate_) {
        for (auto i : decl) {
            elab(i, true);
        }
    }
    return true;
}

void ToCoqConsumer::HandleCXXImplicitFunctionInstantiation(FunctionDecl *decl) {
    if (elaborate_)
        elab(decl);
}

void ToCoqConsumer::HandleInlineFunctionDefinition(FunctionDecl *decl) {
    if (elaborate_)
        elab(decl);
}

void ToCoqConsumer::HandleTagDeclDefinition(TagDecl *decl) {
    if (elaborate_) {
        elab(decl);
    }
}
