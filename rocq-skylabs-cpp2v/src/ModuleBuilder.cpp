/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ModuleBuilder.hpp"
#include "Assert.hpp"
#include "ClangCompat.hpp"
#include "CommentScanner.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "FromClang.hpp"
#include "Location.hpp"
#include "Logging.hpp"
#include "SpecCollector.hpp"
#include "Template.hpp"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <set>
#include <vector>

using namespace clang;

static void unsupported_decl(raw_ostream &os, const Decl *decl,
                             const ASTContext &context) {
    os << loc::prefix(loc::of(decl), context)
       << "warning: ModuleBuilder dropping unsupported declaration\n";
}

using Flags = ::Module::Flags;

namespace {

// Keep declarations written in the main file and the complete declaration
// subgraphs they reference. Reaching a record deliberately retains all of its
// members; this is conservative and avoids reproducing the printer's detailed
// dependency logic here.
class ReachableDecls : public clang::RecursiveASTVisitor<ReachableDecls> {
private:
    using Visitor = clang::RecursiveASTVisitor<ReachableDecls>;

    const SourceManager &source_manager_;
    const bool templates_;
    std::set<int64_t> reachable_;
    std::set<int64_t> queued_;
    std::set<int64_t> traversed_;
    std::vector<Decl *> worklist_;
    bool has_main_declarations_ = false;

    static const Decl *canonical(const Decl *decl) {
        return decl->getCanonicalDecl();
    }

    static Decl *definition(Decl *decl) {
        if (auto function = dyn_cast<FunctionDecl>(decl)) {
            if (auto defn = function->getDefinition())
                return defn;
        } else if (auto tag = dyn_cast<TagDecl>(decl)) {
            if (auto defn = tag->getDefinition())
                return defn;
        } else if (auto var = dyn_cast<VarDecl>(decl)) {
            if (auto defn = var->getDefinition())
                return defn;
        }
        return decl;
    }

    bool isInMainFile(const Decl *decl) const {
        auto loc = decl->getLocation();
        if (loc.isInvalid())
            loc = decl->getBeginLoc();
        return loc.isValid() && source_manager_.isWrittenInMainFile(
                                    source_manager_.getExpansionLoc(loc));
    }

    void select(const Decl *decl) {
        if (decl)
            reachable_.insert(canonical(decl)->getID());
    }

    void selectContexts(const Decl *decl) {
        for (auto context = decl->getDeclContext();
             context && !context->isTranslationUnit();
             context = context->getParent()) {
            auto owner = dyn_cast<Decl>(context);
            if (!owner)
                continue;
            if (isa<NamespaceDecl>(owner)) {
                select(owner);
            } else if (isa<RecordDecl>(owner) || isa<EnumDecl>(owner)) {
                enqueue(owner);
            }
        }
    }

    void selectTemplateDependencies(const Decl *decl) {
        if (!templates_)
            return;
        if (auto pattern = recoverPattern(*decl))
            enqueue(pattern);
        if (auto specialization = recoverSpecialization(*decl))
            enqueue(&specialization->temp);
    }

    void discover(const Decl *decl, bool queue) {
        if (!decl)
            return;

        select(decl);

        if (queue) {
            auto key = canonical(decl)->getID();
            if (!queued_.insert(key).second)
                return;
            worklist_.push_back(definition(const_cast<Decl *>(decl)));
        }

        // Mark the declaration as queued before following dependencies. Clang
        // 22 can report a variable template specialization as its own
        // instantiation pattern, and template relationships can contain other
        // cycles as well.
        selectContexts(decl);
        selectTemplateDependencies(decl);
    }

    void enqueue(const Decl *decl) { discover(decl, true); }

    void enqueueAllocationFunction(const FunctionDecl *function) {
        if (!function)
            return;

        enqueue(function);
        if (!function->isOverloadedOperator())
            return;

        auto op = function->getOverloadedOperator();
        if ((op != OO_Delete && op != OO_Array_Delete) ||
            !function->isReplaceableGlobalAllocationFunction())
            return;

        auto context = function->getDeclContext();
        if (!context->isTranslationUnit())
            return;

        // Clang may select the sized replaceable global deallocation function
        // while clients still need the unsized form (and conversely).
        for (auto decl : context->decls()) {
            auto overload = dyn_cast<FunctionDecl>(decl);
            if (overload && overload->isOverloadedOperator() &&
                overload->getOverloadedOperator() == op &&
                overload->isReplaceableGlobalAllocationFunction())
                enqueue(overload);
        }
    }

    void seedMainFile(const DeclContext *context) {
        for (auto decl : context->decls()) {
            if (isInMainFile(decl)) {
                has_main_declarations_ = true;
                if (isa<NamespaceDecl>(decl) || isa<LinkageSpecDecl>(decl))
                    discover(decl, false);
                else
                    enqueue(decl);
            }

            if (auto ns = dyn_cast<NamespaceDecl>(decl)) {
                seedMainFile(ns);
            } else if (auto linkage = dyn_cast<LinkageSpecDecl>(decl)) {
                seedMainFile(linkage);
            }
        }
    }

public:
    ReachableDecls(TranslationUnitDecl *tu, bool templates)
        : source_manager_(tu->getASTContext().getSourceManager()),
          templates_(templates) {
        seedMainFile(tu);
        for (size_t i = 0; i < worklist_.size(); ++i) {
            auto decl = worklist_[i];
            auto key = canonical(decl)->getID();
            if (traversed_.insert(key).second)
                Visitor::TraverseDecl(definition(decl));
        }
    }

    bool hasMainDeclarations() const { return has_main_declarations_; }

    bool contains(const Decl *decl) const {
        return decl &&
               reachable_.find(canonical(decl)->getID()) != reachable_.end();
    }

    bool shouldVisitImplicitCode() const { return true; }

    bool VisitDecl(Decl *decl) {
        discover(decl, false);
        return true;
    }

    bool VisitType(Type *type) {
        if (auto tag = type->getAsTagDecl())
            enqueue(tag);
        if (auto typedef_type = dyn_cast<TypedefType>(type))
            enqueue(typedef_type->getDecl());
        return true;
    }

    bool VisitTemplateSpecializationType(TemplateSpecializationType *type) {
        if (auto decl = type->getTemplateName().getAsTemplateDecl())
            enqueue(decl);
        return true;
    }

    bool VisitRecordDecl(RecordDecl *decl) {
        for (auto member : decl->decls())
            enqueue(member);
        return true;
    }

    bool VisitDeclRefExpr(DeclRefExpr *expr) {
        enqueue(expr->getDecl());
        return true;
    }

    bool VisitMemberExpr(MemberExpr *expr) {
        enqueue(expr->getMemberDecl());
        return true;
    }

    bool VisitCallExpr(CallExpr *expr) {
        enqueue(expr->getCalleeDecl());
        return true;
    }

    bool VisitOverloadExpr(OverloadExpr *expr) {
        for (auto decl : expr->decls())
            enqueue(decl);
        return true;
    }

    bool VisitCXXConstructExpr(CXXConstructExpr *expr) {
        enqueue(expr->getConstructor());
        return true;
    }

    bool VisitCXXInheritedCtorInitExpr(CXXInheritedCtorInitExpr *expr) {
        enqueue(expr->getConstructor());
        return true;
    }

    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *expr) {
        enqueue(expr->getMethodDecl());
        return true;
    }

    bool VisitCXXNewExpr(CXXNewExpr *expr) {
        enqueueAllocationFunction(expr->getOperatorNew());
        enqueueAllocationFunction(expr->getOperatorDelete());
        return true;
    }

    bool VisitCXXDeleteExpr(CXXDeleteExpr *expr) {
        enqueueAllocationFunction(expr->getOperatorDelete());
        return true;
    }

    bool VisitLambdaExpr(LambdaExpr *expr) {
        enqueue(expr->getLambdaClass());
        return true;
    }

    bool VisitCXXDestructorDecl(CXXDestructorDecl *decl) {
        enqueueAllocationFunction(decl->getOperatorDelete());
        return true;
    }
};

class ReachableFilter : public Filter {
private:
    Filter &filter_;
    const ReachableDecls &reachable_;

public:
    ReachableFilter(Filter &filter, const ReachableDecls &reachable)
        : filter_(filter), reachable_(reachable) {}

    What shouldInclude(const Decl *decl) override {
        return reachable_.contains(decl) ? filter_.shouldInclude(decl)
                                         : What::NOTHING;
    }
};

} // namespace

bool EvaluateRequiresClause(const clang::FunctionDecl *FD,
                            clang::Sema &SemaRef) {
    auto with_template_args =
        [&](ArrayRef<clang::TemplateArgument> TemplateArgs) {
            // 3. Location for diagnostics
            clang::SourceLocation Loc = FD->getLocation();

            // 4. Use CheckInstantiatedFunctionTemplateConstraints to
            // evaluate the constraints
            ConstraintSatisfaction Satisfaction;
#if CLANG_VERSION_MAJOR < 21
            bool Satisfied =
                !SemaRef.CheckInstantiatedFunctionTemplateConstraints(
                    Loc, // Location for diagnostics
                    const_cast<clang::FunctionDecl *>(
                        FD),       // The function declaration
                    TemplateArgs,  // Template arguments
                    Satisfaction); // Will contain unsatisfied constraints
#else
            bool Satisfied =
                !SemaRef.CheckFunctionConstraints(FD, Satisfaction, Loc);
#endif

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
            // Declarations in the scope of template parameters are patterns,
            // also when they are reached outside of their template, e.g.
            // through the out-of-line definition of a member of a class
            // template. [TemplateDecl]s set the flag for their own patterns
            // and not for their specializations.
            if (not isa<TemplateDecl>(d) and d->isTemplated())
                flags = flags.set_template();
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
    IGNORE(UnresolvedUsingTypenameDecl)
    IGNORE(AccessSpecDecl)

    IGNORE(FieldDecl)
    IGNORE(IndirectFieldDecl)

    IGNORE(BuiltinTemplateDecl)
    IGNORE(ClassTemplatePartialSpecializationDecl)
    IGNORE(VarTemplatePartialSpecializationDecl)

    void VisitNamespaceAliasDecl(const NamespaceAliasDecl *decl, Flags) {
        if (filter_.shouldInclude(decl) != Filter::What::NOTHING)
            module_.add_namespace_alias(decl);
    }

    void VisitStaticAssertDecl(const StaticAssertDecl *decl, Flags) {
        // NOTE: This might need some more work because of declarations that
        // have requires clauses; however, these should be in dependent
        // contexts.
        if (filter_.shouldInclude(decl) != Filter::What::NOTHING &&
            not decl->getDeclContext()->isDependentContext())
            module_.add_assert(*decl);
    }

    void VisitTranslationUnitDecl(const TranslationUnitDecl *decl,
                                  Flags flags) {
        always_assert(flags.none());

        for (auto i : decl->decls()) {
            this->Visit(i, flags);
        }

        // Clang creates std::align_val_t for its implicit aligned allocation
        // functions, but does not add the EnumDecl to a declaration context.
        if (auto align_val_t = sema_->getStdAlignValT())
            Visit(align_val_t->getCanonicalDecl(), flags);
    }

    void VisitTypeDecl(const TypeDecl *type, Flags) {
        unsupported_decl(logging::verbose(), type, getContext());
    }

    static bool isCanonical(const TypedefNameDecl *decl) {
        return decl && decl == decl->getCanonicalDecl();
    }

    static const TagDecl *selfTypedefTag(const TypedefNameDecl &decl) {
        if (!decl.getIdentifier())
            return nullptr;

        const Type *type = decl.getUnderlyingType().getTypePtrOrNull();
        const auto *tag = type ? type->getAsTagDecl() : nullptr;
        if (!tag || !isa<RecordDecl>(tag) || !tag->getIdentifier())
            return nullptr;

        if (decl.getName() == tag->getName())
            return tag;
        return nullptr;
    }

    void VisitTypedefNameDecl(const TypedefNameDecl *decl, Flags flags) {
        if (decl->getAnonDeclWithTypedefName(true)) {
            // these [typedef]s become the name of the anonymous struct, so we
            // ignore them.
            return;
        }
        if (auto tag = selfTypedefTag(*decl)) {
            // C commonly uses [typedef struct C C] to make the tag name
            // available as a type name. In cpp2v both declarations have the
            // same key, so emit the record and suppress the redundant alias.
            Visit(tag, flags);
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

    void VisitRecordDecl(const RecordDecl *decl, Flags flags) {
        if (isa<CXXRecordDecl>(decl))
            return;
        VisitTagDecl(decl, flags);
        VisitDeclContext(decl, flags);
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
            auto decl_flags =
                decl->isDependentContext() ? flags.set_template() : flags;
            VisitTagDecl(decl, decl_flags);
            VisitDeclContext(decl, decl_flags);
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
        auto decl_flags = decl->isDependentContext() ? flags.set_template() : flags;

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
            if (auto c = clang_compat::getRawCommentNoCache(*context_, decl)) {
                this->specs_.add_specification(decl, c, *context_);
            }

            auto what = go(decl, decl_flags, true);
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
            go(decl, decl_flags, false);
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

        auto decl_flags = decl->isTemplated() ? flags.set_template() : flags;
        if (auto defn = decl->getDefinition()) {
            if (defn == decl)
                go(decl, decl_flags);
        } else if (decl == decl->getCanonicalDecl())
            go(decl, decl_flags);
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

        if (decl->isInlineNamespace() &&
            filter_.shouldInclude(decl) != Filter::What::NOTHING) {
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
    ReachableDecls reachable(tu, templates);
    if (reachable.hasMainDeclarations()) {
        ReachableFilter reachable_filter(filter, reachable);
        BuildModule(mod, reachable_filter, templates, &ctxt, specs, ci)
            .VisitTranslationUnitDecl(tu, {});
    } else {
        // Include-only translation units are used to expose header APIs. With
        // no main-file declarations to seed reachability, retain the original
        // filter behavior rather than emitting an empty module.
        BuildModule(mod, filter, templates, &ctxt, specs, ci)
            .VisitTranslationUnitDecl(tu, {});
    }
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
