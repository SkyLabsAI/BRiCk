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

    void Visit(const Stmt *stmt, CoqPrinter &print, ClangPrinter &cprint,
               ASTContext &ctxt) {
        if (stmt == nullptr) [[unlikely]] {
            guard::ctor _{print, "Sunsupported"};
            print.str("empty statement");
            return;
        }
        ConstStmtVisitor<PrintStmt, void, CoqPrinter &, ClangPrinter &,
                         ASTContext &>::Visit(stmt, print, cprint, ctxt);
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
    // `typedef int A[(x = 1)];` assigns to `x`.
    static ClangPrinter::VlaBounds declVlaBounds(const Decl *d) {
        ClangPrinter::VlaBounds vla;
        if (auto td = dyn_cast<TypedefNameDecl>(d))
            ClangPrinter::vlaBounds(td->getUnderlyingType(), vla,
                                    d->getASTContext());
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
            auto vla = declVlaBounds(d);
            if (!vla.bounds.empty()) {
                cprint.printVlaBounds(print, vla.bounds);
                print.cons();
            }
            bool printed = cprint.printLocalDecl(print, d);
            always_assert(printed == printedLocalDecl(d) &&
                          "printedLocalDecl out of sync with printLocalDecl");
            if (printed)
                print.cons();
        }
        print.end_list();
        print.end_ctor();
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

    void VisitAttributedStmt(const clang::AttributedStmt *stmt,
                             CoqPrinter &print, ClangPrinter &cprint,
                             ASTContext &) {

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
