/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Version.inc"

using namespace clang;

class PrintStmt : public ConstStmtVisitor<PrintStmt, void, CoqPrinter &,
                                          ClangPrinter &, ASTContext &> {
private:
    PrintStmt() {}

public:
    static PrintStmt printer;

    /// Whether `stmt` declares a local variable with
    /// `__attribute__((cleanup(f)))`, which calls `f(&var)` when the variable
    /// goes out of scope. BRiCk has no such scope-exit call, so the whole
    /// statement is unsupported rather than printed without the call.
    static bool declaresCleanupVar(const Stmt &stmt) {
        auto cleanup = [](const VarDecl *vd) {
            return vd && vd->hasAttr<CleanupAttr>();
        };
        if (auto ds = dyn_cast<DeclStmt>(&stmt))
            return llvm::any_of(ds->decls(), [&](const Decl *d) {
                return cleanup(dyn_cast<VarDecl>(d));
            });
        if (auto s = dyn_cast<IfStmt>(&stmt))
            return cleanup(s->getConditionVariable());
        if (auto s = dyn_cast<WhileStmt>(&stmt))
            return cleanup(s->getConditionVariable());
        if (auto s = dyn_cast<ForStmt>(&stmt))
            return cleanup(s->getConditionVariable());
        if (auto s = dyn_cast<SwitchStmt>(&stmt))
            return cleanup(s->getConditionVariable());
        if (auto s = dyn_cast<CXXForRangeStmt>(&stmt))
            return cleanup(s->getLoopVariable());
        return false;
    }

    void Visit(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint,
               ASTContext &ctxt) {
        if (stmt == nullptr) [[unlikely]] {
            guard::ctor _{print, "Sunsupported"};
            print.str("empty statement");
            return;
        }
        if (variablyModifiedConditionVar(stmt))
            return unsupportedStmt(
                stmt, print, cprint,
                "condition variable of a variably modified type");
        if (declaresCleanupVar(*stmt)) {
            cprint.error_prefix(logging::unsupported(), loc::of(stmt))
                << "warning: unsupported cleanup attribute\n";
            guard::ctor _{print, "Sunsupported"};
            print.str("variable with a cleanup attribute");
            return;
        }
        ConstStmtVisitor<PrintStmt, void, CoqPrinter &, ClangPrinter &,
                         ASTContext &>::Visit(stmt, print, cprint, ctxt);
    }

    // Clang evaluates the array bounds of a variably modified type where a
    // variable of that type is declared, also for a condition variable
    // (`if (int (*p)[n++] = q)`). A condition is a single declaration, with
    // no place for the bounds, so the statement is unsupported.
    static bool variablyModifiedConditionVar(const Stmt *stmt) {
        const VarDecl *var = nullptr;
        if (auto s = dyn_cast<IfStmt>(stmt))
            var = s->getConditionVariable();
        else if (auto s = dyn_cast<SwitchStmt>(stmt))
            var = s->getConditionVariable();
        else if (auto s = dyn_cast<WhileStmt>(stmt))
            var = s->getConditionVariable();
        else if (auto s = dyn_cast<ForStmt>(stmt))
            var = s->getConditionVariable();
        return var && !ClangPrinter::varVlaBounds(*var).empty();
    }

    // Statements without a printer (e.g. coroutines, computed `goto`, MS
    // `asm`, SEH) become [Sunsupported], so that the rest of the translation
    // unit is still available.
    void VisitStmt(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &) {
        cprint.error_prefix(logging::unsupported(), loc::of(stmt))
            << "warning: unsupported statement " << stmt->getStmtClassName()
            << "\n";
        guard::ctor _{print, "Sunsupported"};
        print.str(std::string("unsupported statement: ") +
                  stmt->getStmtClassName());
    }

    // A statement cpp2v has a printer for but cannot print faithfully: the
    // printer would drop part of its meaning.
    void unsupportedStmt(const Stmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, const std::string &msg) {
        cprint.error_prefix(logging::unsupported(), loc::of(stmt))
            << "warning: unsupported " << msg << "\n";
        guard::ctor _{print, "Sunsupported"};
        print.str(msg);
    }

    // Labels are printed by name ([Slabeled], [Sgoto]), and the logic
    // assumes that a name identifies one label in a function. A GNU local
    // label (<<__label__ L;>>) breaks that assumption: an inner [L] can shadow
    // an outer [L] of the same function. The rejection that counts is the one
    // of the `__label__` declaration statement, which opens the label's block.
    // The tests of [isGnuLocal] on label statements and `goto`s are
    // best-effort, for a better message: clang does not report the labels of
    // a template instantiation as local. The support report's check that no
    // function body defines a label name twice is the backstop.
    static constexpr const char *gnu_local_label =
        "GNU local label (__label__)";

    static bool isGnuLocalLabel(const LabelDecl *decl) {
        return decl != nullptr && decl->isGnuLocal();
    }

    void unsupportedGnuLocalLabel(const Stmt *stmt, CoqPrinter &print,
                                  ClangPrinter &cprint) {
        unsupportedStmt(stmt, print, cprint, gnu_local_label);
    }

    // The local declarations [printLocalDecl] prints: variables, including
    // static locals, and structured bindings.
    static bool printedLocalDecl(const Decl *d) {
        if (d->isInvalidDecl() || isa<DecompositionDecl>(d))
            return true;
        return d->getKind() == Decl::Var &&
               !cast<VarDecl>(d)->hasExternalStorage();
    }

    // The local declarations that have no runtime effect, so that leaving
    // them out of the [Sdecl] loses nothing: they only introduce names
    // that the printed code refers to by their resolved meaning. A typedef
    // is one of them up to the array bounds of a variably modified type,
    // which [VisitDeclStmt] prints (see [declVlaBounds]).
    static bool localDeclWithoutEffect(const Decl *d) {
        // `extern int x;` refers to a variable defined elsewhere.
        if (auto vd = dyn_cast<VarDecl>(d))
            return d->getKind() == Decl::Var && vd->hasExternalStorage();
        return isa<TypedefNameDecl,          // typedef, alias declaration
                   TagDecl,                  // local class or enumeration
                   StaticAssertDecl,         // checked at compile time
                   UsingDecl, UsingEnumDecl, // name lookup only
                   UsingDirectiveDecl, NamespaceAliasDecl,
                   UnresolvedUsingValueDecl, // dependent using-declarations
                   UnresolvedUsingTypenameDecl,
                   FunctionDecl,             // block-scope function prototype
                   EmptyDecl>(d);
    }

    // A typedef or alias declaration of a variably modified type (GNU VLA
    // extension) evaluates the array bounds when it is reached:
    // `typedef int A[(x = 1)];` assigns to `x`. So does the declaration of
    // a variable of such a type, before its initializer and also when the
    // variable is a static local: `int (*p)[(x = 1)] = nullptr;`.
    static ClangPrinter::VlaBounds declVlaBounds(const Decl *d) {
        ClangPrinter::VlaBounds vla;
        if (auto td = dyn_cast<TypedefNameDecl>(d))
            ClangPrinter::vlaBounds(td->getUnderlyingType(), vla,
                                    d->getASTContext());
        else if (auto vd = dyn_cast<VarDecl>(d))
            vla = ClangPrinter::varVlaBounds(*vd);
        return vla;
    }

    // Fail closed: any other local declaration (e.g. OpenMP `threadprivate`,
    // `declare reduction`, `allocate`) would be dropped from the [Sdecl]
    // together with its meaning, so the statement is unsupported instead.
    void VisitDeclStmt(const DeclStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        for (auto d : stmt->decls()) {
            if (isa<LabelDecl>(d))
                return unsupportedGnuLocalLabel(stmt, print, cprint);
            if (auto why = declVlaBounds(d).unsupported)
                return unsupportedStmt(stmt, print, cprint, *why);
            if (!printedLocalDecl(d) && !localDeclWithoutEffect(d))
                return unsupportedStmt(
                    stmt, print, cprint,
                    std::string("unsupported local declaration: ") +
                        d->getDeclKindName());
        }
        print.ctor("Sdecl");
        print.begin_list();
        for (auto d : stmt->decls()) {
            // The bounds come first: a variable evaluates them before its
            // initializer.
            auto vla = declVlaBounds(d);
            if (!vla.bounds.empty()) {
                cprint.printVlaBounds(print, vla.bounds);
                print.cons();
            }
            bool printed =
                cprint.printLocalDecl(print, d, /*vla_bounds_printed*/ true);
            always_assert(printed == printedLocalDecl(d) &&
                          "printedLocalDecl out of sync with printLocalDecl");
            if (printed)
                print.cons();
        }
        print.end_list();
        print.end_ctor();
    }

    // The body of a function definition whose parameter types have array
    // bounds to evaluate (see [ClangPrinter::paramVlaBounds]). Clang
    // evaluates them on entry, in parameter order: before the member
    // initializers of a constructor and outside a function-try-block. The
    // logic can only run them as the first statement of a body that is a
    // block, so other definitions are unsupported.
    void printBodyWithParamBounds(const FunctionDecl &decl, const Stmt *body,
                                  const ClangPrinter::VlaBounds &vla,
                                  CoqPrinter &print, ClangPrinter &cprint,
                                  ASTContext &ctxt) {
        auto block = dyn_cast<CompoundStmt>(body);
        auto why = vla.unsupported;
        if (!why && isa<CXXConstructorDecl>(decl))
            why = "constructor with a parameter of a variably modified type";
        else if (!why && decl.isImplicit())
            why = "implicit function with a parameter of a variably "
                  "modified type";
        else if (!why && !block)
            why = "function body that is not a block, with a parameter of a "
                  "variably modified type";
        if (!block)
            return unsupportedStmt(body, print, cprint, *why);
        guard::ctor _{print, "Sseq"};
        guard::list __{print};
        if (why) {
            unsupportedStmt(body, print, cprint, *why);
        } else {
            guard::ctor _{print, "Sdecl"};
            guard::list __{print};
            cprint.printVlaBounds(print, vla.bounds);
            print.cons();
        }
        print.cons();
        for (auto i : block->body())
            printListItem(i, print, cprint, ctxt);
    }

    void VisitWhileStmt(const WhileStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        print.ctor("Swhile");
        print.option(stmt->getConditionVariable(), [&](const VarDecl *v) {
            cprint.printLocalDecl(print, v);
        });
        print.space();
        cprint.printExpr(print, stmt->getCond());
        print.space();
        cprint.printStmt(print, stmt->getBody());
        print.end_ctor();
    }

    void VisitForStmt(const ForStmt *stmt, CoqPrinter &print,
                      ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sfor");
        print.option(stmt->getInit(), [&](const Stmt *v) {
            cprint.printStmt(print, v);
        });
        print.space();
        print.option(stmt->getConditionVariable(), [&](const VarDecl *v) {
            cprint.printLocalDecl(print, v);
        });
        print.space();
        print.option(stmt->getCond(), [&](const Expr *v) {
            cprint.printExpr(print, v);
        });
        print.space();
        print.option(stmt->getInc(), [&](const Expr *v) {
            // See [ClangPrinter::realignedAccess].
            auto saved = cprint.discardedExpr;
            cprint.discardedExpr = v->IgnoreParens();
            cprint.printExpr(print, v);
            cprint.discardedExpr = saved;
        });
        print.space();
        cprint.printStmt(print, stmt->getBody());
        print.end_ctor();
    }

    void VisitCXXForRangeStmt(const CXXForRangeStmt *stmt, CoqPrinter &print,
                              ClangPrinter &cprint, ASTContext &) {
        if (not(stmt->getRangeStmt() && stmt->getBeginStmt() &&
                stmt->getEndStmt())) {
            guard::ctor _{print, "Sunsupported"};
            print.str("dependent for-each loop");
            return;
        }
        print.ctor("Sforeach");
        cprint.printStmt(print, stmt->getRangeStmt());
        print.space();
        cprint.printStmt(print, stmt->getBeginStmt());
        print.space();
        cprint.printStmt(print, stmt->getEndStmt());
        print.space();
        print.option(stmt->getInit(), [&](const Stmt *v) {
            cprint.printStmt(print, v);
        });
        print.space();
        print.option(stmt->getCond(), [&](const Expr *v) {
            cprint.printExpr(print, v);
        });
        print.space();
        print.option(stmt->getInc(), [&](const Expr *v) {
            // See [ClangPrinter::realignedAccess].
            auto saved = cprint.discardedExpr;
            cprint.discardedExpr = v->IgnoreParens();
            cprint.printExpr(print, v);
            cprint.discardedExpr = saved;
        });
        print.space();
        cprint.printStmt(print, stmt->getLoopVarStmt());
        print.space();
        cprint.printStmt(print, stmt->getBody());
        print.end_ctor();
    }

    void VisitDoStmt(const DoStmt *stmt, CoqPrinter &print,
                     ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdo");
        cprint.printStmt(print, stmt->getBody());
        print.space();
        cprint.printExpr(print, stmt->getCond());
        print.end_ctor();
    }

    // Named loops (C2y N3355, clang 22 `-fnamed-loops`): `break L;` and
    // `continue L;` target the loop labeled `L`, not the innermost one, and
    // [Sbreak]/[Scontinue] cannot say so. See SkyLabsAI/BRiCk#540.
    static bool hasLoopLabel(const Stmt *stmt) {
#if CLANG_VERSION_MAJOR >= 22
        if (auto lc = dyn_cast<LoopControlStmt>(stmt))
            return lc->hasLabelTarget();
#endif
        return false;
    }

    void VisitBreakStmt(const BreakStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        if (hasLoopLabel(stmt))
            return unsupportedStmt(
                stmt, print, cprint,
                "named break (break label;), see SkyLabsAI/BRiCk#540");
        print.output() << "Sbreak";
    }

    void VisitContinueStmt(const ContinueStmt *stmt, CoqPrinter &print,
                           ClangPrinter &cprint, ASTContext &) {
        if (hasLoopLabel(stmt))
            return unsupportedStmt(
                stmt, print, cprint,
                "named continue (continue label;), see SkyLabsAI/BRiCk#540");
        print.output() << "Scontinue";
    }

    void VisitIfStmt(const IfStmt *stmt, CoqPrinter &print,
                     ClangPrinter &cprint, ASTContext &) {
        if (stmt->isConsteval()) {
            print.ctor("Sif_consteval");
        } else {
            print.ctor("Sif");
            print.option(stmt->getInit(), [&](const Stmt *v) {
                cprint.printStmt(print, v);
            });
            print.space();
            print.option(stmt->getConditionVariable(), [&](const VarDecl *v) {
                cprint.printLocalDecl(print, v);
            });
            print.space();
            cprint.printExpr(print, stmt->getCond());
            print.space();
        }
        cprint.printStmt(print, stmt->getThen());
        print.space();
        if (stmt->getElse()) {
            cprint.printStmt(print, stmt->getElse());
        } else {
            print.output() << "Sskip";
        }
        print.end_ctor();
    }

    static bool constexprEvalInt(const Expr &expr, ASTContext &ctxt,
                                 llvm::APSInt &value) {
        if (expr.containsErrors() || expr.isValueDependent() ||
            expr.isTypeDependent())
            return false;
        Expr::EvalResult result;
        if (!expr.EvaluateAsInt(result, ctxt))
            return false;
        value = result.Val.getInt();
        return true;
    }

    // Print [stmt] as items of an [Sseq] list, each followed by a cons:
    // [Scase]/[Sdefault] are markers within that list, not statements.
    void printListItem(const Stmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &ctxt) {
        if (auto cs = dyn_cast_or_null<CaseStmt>(stmt)) {
            llvm::APSInt lo, hi;
            auto rhs = cs->getRHS();
            if (!constexprEvalInt(*cs->getLHS(), ctxt, lo) ||
                (rhs && !constexprEvalInt(*rhs, ctxt, hi))) {
                // not evaluatable
                guard::ctor _{print, "Sunsupported"};
                print.str("unsupported (dependent) case label");
            } else if (rhs) {
                // evaluatable range
                guard::ctor _{print, "Scase"};
                guard::ctor __(print, "Range");
                print.output() << lo << fmt::nbsp << hi;
            } else {
                // evaluatable simple case
                guard::ctor _{print, "Scase"};
                guard::ctor __(print, "Exact");
                print.output() << lo;
            }
            print.cons();
            printListItem(cs->getSubStmt(), print, cprint, ctxt);
        } else if (auto ds = dyn_cast_or_null<DefaultStmt>(stmt)) {
            print.output() << "Sdefault";
            print.cons();
            if (ds->getSubStmt())
                printListItem(ds->getSubStmt(), print, cprint, ctxt);
        } else {
            cprint.printStmt(print, stmt);
            print.cons();
        }
    }

    // A label outside a statement list, e.g. <<if (c) case 1: s;>> (Duff's
    // device, state machines). Wrap it in a block so that the term is a
    // [Stmt]; [supported] rejects such a [switch] (case nested in a
    // statement).
    void VisitSwitchCase(const SwitchCase *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &ctxt) {
        guard::ctor _{print, "Sseq"};
        guard::list __{print};
        printListItem(stmt, print, cprint, ctxt);
    }

    void VisitSwitchStmt(const SwitchStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &ctxt) {
        print.ctor("Sswitch");
        if (auto v = stmt->getInit()) {
            print.some();
            cprint.printStmt(print, v);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        if (auto v = stmt->getConditionVariable()) {
            print.some();
            cprint.printLocalDecl(print, v);
            print.end_ctor();
        } else {
            print.none();
        }
        print.output() << fmt::nbsp;
        cprint.printExpr(print, stmt->getCond());
        print.output() << fmt::nbsp;
        /*
         * The body of a `switch` need not be a compound statement, but
         * `Scase`/`Sdefault` are markers *within* the list of an `Sseq`, and
         * `wp_switch` only looks for them there. Print the block that the
         * substatement already denotes: it "implicitly defines a block scope",
         * and when it is "a single statement and not a compound-statement, it
         * is as if it was rewritten to be a compound-statement containing the
         * original substatement" ([stmt.select]/2, [stmt.select.general]/2 in
         * later revisions). This is the shape gtest's
         * `GTEST_AMBIGUOUS_ELSE_BLOCKER_` (`switch (0) case 0: default:`)
         * expands to, and it yields exactly the AST of the braced spelling.
         *
         * The guard matters: wrapping a body that is already a compound
         * statement would bury its labels one `Sseq` deeper, where
         * `get_cases` cannot see them.
         */
        if (isa<CompoundStmt>(stmt->getBody())) {
            cprint.printStmt(print, stmt->getBody());
        } else {
            guard::ctor _{print, "Sseq"};
            guard::list __{print};
            printListItem(stmt->getBody(), print, cprint, ctxt);
        }
        print.end_ctor();
    }

    void VisitExpr(const Expr *expr, CoqPrinter &print, ClangPrinter &cprint,
                   ASTContext &) {
        print.ctor("Sexpr");
        // See [ClangPrinter::realignedAccess].
        auto saved = cprint.discardedExpr;
        cprint.discardedExpr = expr->IgnoreParens();
        cprint.printExpr(print, expr);
        cprint.discardedExpr = saved;
        print.end_ctor();
    }

    /*
     * The automatic variable whose copy or move into the returned object
     * `return x;` may elide (named return value optimization,
     * [class.copy.elision]/1.1), or `nullptr`.
     *
     * This is the standard's eligibility, which clang's AST does not record:
     * `ReturnStmt::getNRVOCandidate` and `VarDecl::isNRVOVariable` only mark
     * the variables clang *decides* to elide (one per scope, so a function
     * returning either of two locals has neither), and since clang 22 the
     * `CXXConstructExpr` is no longer `elidable`. The semantics must allow
     * elision wherever a conforming implementation may perform it, so
     * `Sreturn_nrvo` is printed for every eligible return; BRiCk then
     * verifies both executions.
     */
    static const VarDecl *nrvo_candidate(const ReturnStmt *stmt,
                                         ASTContext &ctxt) {
        auto rv = stmt->getRetValue();
        if (!rv)
            return nullptr;
        auto e = rv->IgnoreParens();
        if (auto ewc = dyn_cast<ExprWithCleanups>(e))
            e = ewc->getSubExpr()->IgnoreParens();
        auto ce = dyn_cast<CXXConstructExpr>(e);
        if (!ce || ce->getNumArgs() < 1 ||
            !ce->getConstructor()->isCopyOrMoveConstructor())
            return nullptr;
        auto dre = dyn_cast<DeclRefExpr>(ce->getArg(0)->IgnoreParenImpCasts());
        // A variable of an enclosing function (a lambda capture) is not an
        // automatic variable of this function.
        if (!dre || dre->refersToEnclosingVariableOrCapture())
            return nullptr;
        auto vd = dyn_cast<VarDecl>(dre->getDecl());
        if (!vd || !vd->hasLocalStorage() || isa<ParmVarDecl>(vd) ||
            vd->isExceptionVariable() || vd->getType().isVolatileQualified())
            return nullptr;
        // "with the same type (ignoring cv-qualification) as the function
        // return type": the constructed object is the returned object.
        if (!ctxt.hasSameUnqualifiedType(vd->getType(), ce->getType()))
            return nullptr;
        return vd;
    }

    void VisitReturnStmt(const ReturnStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &ctxt) {
        if (auto rv = stmt->getRetValue()) {
            if (auto vd = nrvo_candidate(stmt, ctxt)) {
                // Clang's own candidate, when it has one, must agree.
                if (auto cand = stmt->getNRVOCandidate(); cand && cand != vd) {
                    using namespace logging;
                    unsupported()
                        << "NRVO candidate disagreement at "
                        << cprint.sourceRange(stmt->getSourceRange()) << "\n";
                }
                print.ctor("Sreturn_nrvo");
                print.str(vd->getName()) << fmt::nbsp;
                cprint.printExpr(print, rv);
                print.end_ctor();
                return;
            }
            print.ctor("Sreturn_val");
            cprint.printExpr(print, rv);
            print.end_ctor();
        } else {
            print.output() << "Sreturn_void";
        }
    }

    void VisitCompoundStmt(const CompoundStmt *stmt, CoqPrinter &print,
                           ClangPrinter &cprint, ASTContext &ctxt) {
        print.ctor("Sseq");
        print.begin_list();
        for (auto i : stmt->body())
            printListItem(i, print, cprint, ctxt);
        print.end_list();
        print.end_ctor();
    }

    void VisitNullStmt(const NullStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sskip";
    }

    void VisitGCCAsmStmt(const GCCAsmStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        // `asm goto` may jump to one of its labels, which [Sasm] cannot
        // express.
        if (stmt->isAsmGoto())
            return unsupportedStmt(stmt, print, cprint, "asm goto");
        // todo(gmm): more to do here to support assembly
        print.ctor("Sasm");
#if CLANG_VERSION_MAJOR > 20
        print.str(stmt->getAsmString()) << fmt::nbsp;
#else
        print.str(stmt->getAsmString()->getString()) << fmt::nbsp;
#endif

        print.output() << (stmt->isVolatile() ? "true" : "false") << fmt::nbsp;

        // inputs
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumInputs(); ++i) {
            print.begin_tuple();
            print.str(stmt->getInputConstraint(i));
            print.next_tuple();
            cprint.printExpr(print, stmt->getInputExpr(i));
            print.end_tuple();
            print.cons();
        }
        print.end_list();

        // outputs
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumOutputs(); ++i) {
            print.begin_tuple();
            print.str(stmt->getOutputConstraint(i));
            print.next_tuple();
            cprint.printExpr(print, stmt->getOutputExpr(i));
            print.end_tuple();
            print.cons();
        }
        print.end_list();

        // clobbers
        print.begin_list();
        for (unsigned i = 0; i < stmt->getNumClobbers(); ++i) {
            print.str(stmt->getClobber(i));
            print.cons();
        }
        print.end_list();

        print.end_ctor();
    }

    // [Sattr] keeps only the names of a statement's attributes, and the
    // logic skips them ([wp_attr]). That is faithful for hints and
    // diagnostics, which do not change what a program does. This returns
    // why attribute [a] is not one of those, if so.
    //
    // Fail closed: an attribute that is not listed here is unsupported.
    // Among those are the promises that the compiler optimizes on:
    // - `[[assume(e)]]`, also spelled `__attribute__((assume(e)))`: the
    //   behaviour is undefined unless [e] holds, and [e] is not evaluated.
    // - `#pragma clang loop vectorize(assume_safety)`: the loop has no
    //   loop-carried memory dependency.
    // - `[[clang::musttail]]`: the lifetime of the caller's locals ends
    //   before the call, so passing their address is undefined.
    static std::optional<std::string> unsupportedStmtAttr(const Attr *a) {
        switch (a->getKind()) {
        case attr::Likely:
        case attr::Unlikely:
        case attr::FallThrough:
        case attr::CodeAlign:
        case attr::Suppress:
            return std::nullopt;
        case attr::LoopHint:
            if (cast<LoopHintAttr>(a)->getState() == LoopHintAttr::AssumeSafety)
                return "loop hint: assume_safety";
            return std::nullopt;
        default:
            // `noinline`, `always_inline`, `nomerge`, `annotate`.
            if (ClangPrinter::isNoOpAttr(a->getKind()))
                return std::nullopt;
            return std::string("statement attribute: ") + a->getSpelling();
        }
    }

    void VisitAttributedStmt(const clang::AttributedStmt *stmt,
                             CoqPrinter &print, ClangPrinter &cprint,
                             ASTContext &) {
        for (auto a : stmt->getAttrs())
            if (auto why = unsupportedStmtAttr(a))
                return unsupportedStmt(stmt, print, cprint, *why);

        print.ctor("Sattr");
        print.begin_list();
        for (auto i : stmt->getAttrs()) {
            print.str(i->getSpelling());
            print.cons();
        }
        print.end_list();

        cprint.printStmt(print, stmt->getSubStmt());

        print.end_ctor();
    }

    void VisitLabelStmt(const LabelStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        if (isGnuLocalLabel(stmt->getDecl())) {
            unsupportedGnuLocalLabel(stmt, print, cprint);
            return;
        }
        print.ctor("Slabeled");
        print.str(stmt->getDecl()->getNameAsString()) << fmt::nbsp;
        cprint.printStmt(print, stmt->getSubStmt());
        print.end_ctor();
    }

    void VisitGotoStmt(const GotoStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        if (isGnuLocalLabel(stmt->getLabel())) {
            unsupportedGnuLocalLabel(stmt, print, cprint);
            return;
        }
        print.ctor("Sgoto");
        print.str(stmt->getLabel()->getNameAsString());
        print.end_ctor();
    }

    void VisitCXXTryStmt(const CXXTryStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sunsupported");
        print.str("try");
        print.end_ctor();
    }
};

PrintStmt PrintStmt::printer;

fmt::Formatter &ClangPrinter::printStmt(CoqPrinter &print,
                                        const clang::Stmt *stmt) {
    if (trace(Trace::Stmt))
        trace("printStmt", loc::of(stmt));
    __attribute__((unused)) auto depth = print.output().get_depth();
    PrintStmt::printer.Visit(stmt, print, *this, *this->context_);
    always_assert(depth == print.output().get_depth());
    return print.output();
}

// Clang destroys the temporaries of an array bound at the end of the
// enclosing scope, since the bound is not a full-expression, while the
// logic destroys them after the bound. Bounds that may create temporaries
// are therefore not printed.
static bool boundMayCreateTemporary(const Expr *bound) {
    struct Finder : RecursiveASTVisitor<Finder> {
        bool found{false};
        bool VisitStmt(Stmt *s) {
            found = found ||
                    isa<CXXBindTemporaryExpr, MaterializeTemporaryExpr,
                        ExprWithCleanups, CXXDefaultArgExpr,
                        CXXDefaultInitExpr, LambdaExpr, StmtExpr,
                        CompoundLiteralExpr>(s);
            return !found;
        }
    } finder;
    finder.TraverseStmt(const_cast<Expr *>(bound));
    return finder.found;
}

// This follows `CodeGenFunction::EmitVariablyModifiedType`, which walks
// from the outermost type inward and evaluates the bound of each
// variable-length array once. The type of another typedef ends the walk:
// its bounds were evaluated at its own declaration. Clang also walks
// through other types (e.g. `typeof`, pointers to members, function
// types, `_Atomic`); those are unsupported here.
static void walkVlaBounds(QualType type, ClangPrinter::VlaBounds &vla) {
    while (!type.isNull() && type->isVariablyModifiedType()) {
        auto ty = type.getTypePtr();
        switch (ty->getTypeClass()) {
        case Type::Pointer:
            type = cast<PointerType>(ty)->getPointeeType();
            break;
        case Type::LValueReference:
        case Type::RValueReference:
            type = cast<ReferenceType>(ty)->getPointeeType();
            break;
        case Type::ConstantArray:
        case Type::IncompleteArray:
            type = cast<ArrayType>(ty)->getElementType();
            break;
        case Type::VariableArray: {
            auto vat = cast<VariableArrayType>(ty);
            auto bound = vat->getSizeExpr();
            if (!bound) {
                vla.unsupported =
                    "variably modified type: array of unspecified bound";
                return;
            }
            if (boundMayCreateTemporary(bound)) {
                vla.unsupported =
                    "variably modified type: array bound with a temporary";
                return;
            }
            vla.bounds.push_back(bound);
            type = vat->getElementType();
            break;
        }
        case Type::Paren:
            type = cast<ParenType>(ty)->getInnerType();
            break;
#if CLANG_VERSION_MAJOR < 22
        case Type::Elaborated:
            type = cast<ElaboratedType>(ty)->getNamedType();
            break;
#endif
        case Type::Typedef:
            return;
        default:
            vla.unsupported =
                std::string("variably modified type: unsupported ") +
                ty->getTypeClassName() + " type";
            return;
        }
    }
}

// The bounds of one type belong to one declarator, and C does not sequence
// their evaluations (C11 6.7.6p3 makes the full declarator the sequence
// point): `typedef int A[n++][n];` is undefined. Clang evaluates them from
// the outside in, but the logic must not rely on that order, so several
// bounds are printed only if none has a side effect.
void ClangPrinter::vlaBounds(QualType type, VlaBounds &vla,
                             const ASTContext &ctxt) {
    auto first = vla.bounds.size();
    walkVlaBounds(type, vla);
    if (vla.unsupported || vla.bounds.size() - first < 2)
        return;
    for (auto i = first; i < vla.bounds.size(); i++)
        if (vla.bounds[i]->HasSideEffects(ctxt))
            vla.unsupported = "variably modified type: unsequenced array "
                              "bounds with a side effect";
}

// A variable-length array itself (`int a[n];`) is printed as before, without
// its bounds: the logic cannot initialize an object of type
// [Tvariable_array].
ClangPrinter::VlaBounds ClangPrinter::varVlaBounds(const VarDecl &decl) {
    VlaBounds vla;
    if (!decl.getType().isNull() && !decl.getType()->isVariableArrayType())
        vlaBounds(decl.getType(), vla, decl.getASTContext());
    return vla;
}

// This follows `CodeGenFunction::StartFunction`, which emits the types of
// the parameters as written, in order.
ClangPrinter::VlaBounds ClangPrinter::paramVlaBounds(const FunctionDecl &decl) {
    VlaBounds vla;
    for (auto param : decl.parameters()) {
        vlaBounds(param->getOriginalType(), vla, decl.getASTContext());
        if (vla.unsupported)
            break;
    }
    return vla;
}

fmt::Formatter &
ClangPrinter::printVlaBounds(CoqPrinter &print,
                             const std::vector<const Expr *> &bounds) {
    guard::ctor _{print, "Dvla_bounds"};
    guard::list __{print};
    for (auto bound : bounds) {
        printExpr(print, bound);
        print.cons();
    }
    return print.output();
}

fmt::Formatter &ClangPrinter::printFunctionBody(CoqPrinter &print,
                                                const FunctionDecl &decl,
                                                const Stmt *body) {
    auto vla = paramVlaBounds(decl);
    auto printBody = [&]() -> fmt::Formatter & {
        if (vla.empty())
            return printStmt(print, body);
        __attribute__((unused)) auto depth = print.output().get_depth();
        PrintStmt::printer.printBodyWithParamBounds(decl, body, vla, print, *this,
                                                    *this->context_);
        always_assert(depth == print.output().get_depth());
        return print.output();
    };
    auto block = dyn_cast<CompoundStmt>(body);
    if (!decl.isMain() ||
        (block && !block->body_empty() && isa<ReturnStmt>(block->body_back())))
        return printBody();

    // [basic.start.main]: flowing off main is equivalent to returning zero.
    // Keep the body in its own scope, so its locals are destroyed on exit.
    guard::ctor seq{print, "Sseq"};
    guard::list stmts{print};
    printBody();
    print.cons();
    {
        guard::ctor ret{print, "Sreturn_val"};
        guard::ctor zero{print, "Eint"};
        print.output() << "0%Z" << fmt::nbsp;
        printQualType(print, decl.getReturnType(), loc::of(decl));
    }
    print.cons();
    return print.output();
}
