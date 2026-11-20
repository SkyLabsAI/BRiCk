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

    void VisitDeclStmt(const DeclStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sdecl");
        print.begin_list();
        for (auto d : stmt->decls()) {
            if (cprint.printLocalDecl(print, d))
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
            cprint.printExpr(print, v);
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
            cprint.printExpr(print, v);
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

    void VisitBreakStmt(const BreakStmt *stmt, CoqPrinter &print,
                        ClangPrinter &cprint, ASTContext &) {
        print.output() << "Sbreak";
    }

    void VisitContinueStmt(const ContinueStmt *stmt, CoqPrinter &print,
                           ClangPrinter &cprint, ASTContext &) {
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
        cprint.printExpr(print, expr);
        print.end_ctor();
    }

    void VisitReturnStmt(const ReturnStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        if (auto rv = stmt->getRetValue()) {
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
        print.ctor("Slabeled");
        print.str(stmt->getDecl()->getNameAsString()) << fmt::nbsp;
        cprint.printStmt(print, stmt->getSubStmt());
        print.end_ctor();
    }

    void VisitGotoStmt(const GotoStmt *stmt, CoqPrinter &print,
                       ClangPrinter &cprint, ASTContext &) {
        print.ctor("Sgoto");
        print.str(stmt->getLabel()->getNameAsString());
        print.end_ctor();
    }

    void VisitCXXTryStmt(const CXXTryStmt *stmt, CoqPrinter &print,
                         ClangPrinter &cprint, ASTContext &) {
        // Under BRiCk's non-throwing semantics (where throw expressions have
        // no WP rule), a verified try-block never throws, so the catch
        // handlers are unreachable and lowering to the try-block is sound.
        cprint.printStmt(print, stmt->getTryBlock());
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
