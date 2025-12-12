/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ModuleBuilder.hpp"
#include "Assert.hpp"
#include "CommentScanner.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "FromClang.hpp"
#include "Location.hpp"
#include "Logging.hpp"
#include "SpecCollector.hpp"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>

using namespace clang;

static void unsupported_decl(raw_ostream &os, const Decl *decl,
                             const ASTContext &context) {
    os << loc::prefix(loc::of(decl), context)
       << "warning: ModuleBuilder dropping unsupported declaration\n";
}

using Flags = ::Module::Flags;

bool EvaluateRequiresClause(const clang::FunctionDecl *FD,
                            clang::Sema &SemaRef) {
    auto with_template_args =
        [&](ArrayRef<clang::TemplateArgument> TemplateArgs) {
            // 3. Location for diagnostics
            clang::SourceLocation Loc = FD->getLocation();

            // 4. Use CheckInstantiatedFunctionTemplateConstraints to
            // evaluate the constraints
            ConstraintSatisfaction Satisfaction;
            bool Satisfied =
                !SemaRef.CheckInstantiatedFunctionTemplateConstraints(
                    Loc, // Location for diagnostics
                    const_cast<clang::FunctionDecl *>(
                        FD),       // The function declaration
                    TemplateArgs,  // Template arguments
                    Satisfaction); // Will contain unsatisfied constraints

            return Satisfied && Satisfaction.IsSatisfied;
        };

    auto specialization_info = FD->getTemplateSpecializationInfo();
    if (specialization_info != nullptr) {
        if (auto *FTSI = dyn_cast<clang::FunctionTemplateSpecializationInfo>(
                specialization_info)) {
            return with_template_args(FTSI->TemplateArguments->asArray());
        }
    }
    // You might need to build template arguments from context
    // This is more complex and depends on your situation
    return true;
}

class BuildModule : public ConstDeclVisitorArgs<BuildModule, void, Flags> {
private:
    using Visitor = ConstDeclVisitorArgs<BuildModule, void, Flags>;

    ::Module &module_;
    Filter &filter_;
    const bool templates_;
    SpecCollector &specs_;
    clang::ASTContext *const context_;
    std::set<int64_t> visited_;
    clang::Sema *sema_;

    const ASTContext &getContext() const { return *context_; }

private:
    Filter::What go(const NamedDecl *decl, Flags flags,
                    bool definition = true) {
        auto what = filter_.shouldInclude(decl);
        switch (what) {
        case Filter::What::DEFINITION:
            if (definition) {
                module_.add_definition(*decl, flags);
                return what;
            } else {
                module_.add_declaration(*decl, flags);
                return Filter::What::DECLARATION;
            }
        case Filter::What::DECLARATION:
            module_.add_declaration(*decl, flags);
            return Filter::What::DECLARATION;
        default:
            return Filter::What::NOTHING;
        }
    }

public:
    BuildModule(::Module &m, Filter &filter, bool templates,
                clang::ASTContext *context, SpecCollector &specs,
                clang::CompilerInstance *ci)
        : module_(m), filter_(filter), templates_(templates), specs_(specs),
          context_(context), sema_(&ci->getSema()) {}

    void Visit(const Decl *d, Flags flags) {
        if (visited_.find(d->getID()) == visited_.end()) {
            visited_.insert(d->getID());
            Visitor::Visit(d, flags);
        }
    }

    void VisitDecl(const Decl *d, Flags) {
        unsupported_decl(logging::debug(), d, getContext());
    }

#define IGNORE(D)                                                              \
    void Visit##D(const D *, Flags) {}

    IGNORE(EmptyDecl)
    IGNORE(CXXDeductionGuideDecl)
    IGNORE(UsingDecl)
    IGNORE(UsingDirectiveDecl)
    IGNORE(UsingShadowDecl)
    IGNORE(AccessSpecDecl)

    IGNORE(FieldDecl)
    IGNORE(IndirectFieldDecl)

    IGNORE(BuiltinTemplateDecl)
    IGNORE(ClassTemplatePartialSpecializationDecl)
    IGNORE(VarTemplatePartialSpecializationDecl)

    void VisitNamespaceAliasDecl(const NamespaceAliasDecl *decl, Flags) {
        module_.add_namespace_alias(decl);
    }

    void VisitStaticAssertDecl(const StaticAssertDecl *decl, Flags) {
        // NOTE: This might need some more work because of declarations that
        // have requires clauses; however, these should be in dependent
        // contexts.
        if (not decl->getDeclContext()->isDependentContext())
            module_.add_assert(*decl);
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl,
                                  Flags flags) {
        always_assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }
    }

    void VisitTypeDecl(const TypeDecl *type, Flags) {
        unsupported_decl(logging::verbose(), type, getContext());
    }

    static bool isCanonical(const TypedefNameDecl *decl) {
        return decl && decl == decl->getCanonicalDecl();
    }

    void VisitTypedefNameDecl(const TypedefNameDecl *decl, Flags flags) {
        if (decl->getAnonDeclWithTypedefName(true)) {
            // these [typedef]s become the name of the anonymous struct, so we
            // ignore them.
            return;
        }
        if (not decl->isCanonicalDecl())
            return;
        go(decl, flags);
    }

    void VisitTypeAliasTemplateDecl(const TypeAliasTemplateDecl *decl,
                                    Flags flags) {
        if (templates_)
            Visit(decl->getTemplatedDecl(), flags.set_template());
    }

    void VisitTagDecl(const TagDecl *decl, Flags flags) {
        auto defn = decl->getDefinition();
        if (defn == decl) {
            go(decl, flags, true);
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            go(decl, flags, false);
        }
    }

    void VisitDeclContext(const DeclContext *dc, Flags flags) {
        // For namespaces: Find anything.
        // For structures: Find static functions or fields.
        for (auto i : dc->decls()) {
            Visit(i, flags);
        }
    }

    void VisitCXXRecordDecl(const CXXRecordDecl *decl, Flags flags) {
        if (decl->isImplicit() and not decl->isLambda())
            return;
        if (not decl->isDependentContext() or templates_) {
            VisitTagDecl(decl, flags);
            VisitDeclContext(decl, flags);
        }
    }

    void VisitClassTemplateDecl(const ClassTemplateDecl *decl, Flags flags) {
        if (templates_)
            Visit(decl->getTemplatedDecl(), flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitCXXMethodDecl(const CXXMethodDecl *decl, Flags flags) {
        if (decl->isDeleted())
            return;

        // this goes to [VisitFunctionDecl]
        this->ConstDeclVisitorArgs::VisitCXXMethodDecl(decl, flags);
    }

    void VisitFunctionDecl(const FunctionDecl *decl, Flags flags) {
        if (decl->isDependentContext() and not templates_)
            return;

        // TODO: in some instances, clang does not link all definitions together
        // which can cause both 'defn == decl' and 'first-decl' to succeed on
        // what is, effectively, the same declaration. It would be good to
        // figure out why this happens and fix it, but, for the time being we
        // fix this within Coq by de-duplicating the definition.
        auto debug = [=](const char *info) {
#ifdef DEBUG
            llvm::errs() << info << ": ";
            decl->getNameForDiagnostic(
                llvm::errs(), PrintingPolicy(context_->getLangOpts()), true);
            llvm::errs() << ' ' << (void *)decl->getCanonicalDecl() << "\n";
#endif
        };

        if (not EvaluateRequiresClause(decl, *sema_))
            return;

        using namespace comment;
        auto defn = decl->getDefinition();
        if (defn == decl) {
            debug("defn == decl");
            if (auto c = context_->getRawCommentForDeclNoCache(decl)) {
                this->specs_.add_specification(decl, c, *context_);
            }

            auto what = go(decl, flags, true);
            if (what >= Filter::What::DEFINITION) {
                // search for definitions that need to be lifted, e.g.
                // static local variables, classes, functions, etc.
                for (auto i : decl->decls()) {
                    if (auto d = dyn_cast<VarDecl>(i)) {
                        if (d->isStaticLocal() or d->hasExternalStorage()) {
                            Visit(d, flags);
                        }
                    } else {
                        Visit(i, flags);
                    }
                }
            }
        } else if (defn == nullptr && decl->getPreviousDecl() == nullptr) {
            debug("first-decl");
            go(decl, flags, false);
        } else {
            debug("skipped");
        }
    }

    void VisitFunctionTemplateDecl(const FunctionTemplateDecl *decl,
                                   Flags flags) {
        if (templates_)
            this->Visit(decl->getTemplatedDecl(), flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitEnumConstantDecl(const EnumConstantDecl *decl, Flags flags) {
        go(decl, flags);
    }

    void VisitVarDecl(const VarDecl *decl, Flags flags) {
        if (decl->isTemplated() and not templates_)
            return;

        if (auto defn = decl->getDefinition()) {
            if (defn == decl)
                go(decl, flags);
        } else if (decl == decl->getCanonicalDecl())
            go(decl, flags);
    }

    void VisitVarTemplateDecl(const VarTemplateDecl *decl, Flags flags) {
        if (templates_)
            Visit(decl->getTemplatedDecl(), flags.set_template());

        for (auto i : decl->specializations()) {
            this->Visit(i, flags.set_specialization());
        }
    }

    void VisitNamespaceDecl(const NamespaceDecl *decl, Flags flags) {
        // namespaces can not be located inside of templates
        always_assert(flags.none());

        if (decl->isInlineNamespace()) {
            module_.add_inline_namespace(decl);
        }

        VisitDeclContext(decl, flags);
    }

    void VisitEnumDecl(const EnumDecl *decl, Flags flags) {
        if (not decl->isCanonicalDecl())
            return;

        go(decl, flags);
        for (auto i : decl->enumerators()) {
            go(i, flags);
        }
    }

    void VisitLinkageSpecDecl(const LinkageSpecDecl *decl, Flags flags) {
        always_assert(flags.none());

        VisitDeclContext(decl, flags);
    }

    void VisitFriendDecl(const FriendDecl *decl, Flags flags) {
        if (decl->getFriendDecl()) {
            this->Visit(decl->getFriendDecl(), flags);
        }
    }
};

void build_module(clang::TranslationUnitDecl *tu, ::Module &mod, Filter &filter,
                  SpecCollector &specs, clang::CompilerInstance *ci,
                  bool elaborate, bool templates) {
    auto &ctxt = tu->getASTContext();
    BuildModule(mod, filter, templates, &ctxt, specs, ci)
        .VisitTranslationUnitDecl(tu, {});
}

void ::Module::add_assert(const clang::StaticAssertDecl &d) {
    asserts_.push_back(&d);
}

using DeclList = ::Module::DeclList;

void ::Module::add_decl(StringRef indef, DeclList &decls, DeclList &tdecls,
                        const NamedDecl &decl, Flags flags) {
    auto save = [&](StringRef intemp, DeclList &list) {
        if (trace_) {
            auto loc = loc::of(decl);
            if (loc::can_trace(loc)) {
                auto &os = llvm::errs();
                auto &context = decl.getASTContext();
                os << "[ModuleBuilder] " << indef << intemp << " "
                   << loc::trace(loc, context) << "\n";
            }
        }
        list.push_back(&decl);
    };
    if (flags.in_template) {
        save("1", tdecls);
    } else {
        save("0", decls);
        if (flags.in_specialization) {
            save("1", tdecls);
        }
    }
}

void ::Module::add_definition(const clang::NamedDecl &d, Flags flags) {
    add_decl("1", definitions_, template_definitions_, d, flags);
}

void ::Module::add_declaration(const clang::NamedDecl &d, Flags flags) {
    add_decl("0", declarations_, template_declarations_, d, flags);
}
