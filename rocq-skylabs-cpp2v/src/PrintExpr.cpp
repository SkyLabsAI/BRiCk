/*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "AtomicOp.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "OpaqueNames.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Builtins.h"
#include <clang/AST/DependenceFlags.h>
#include <clang/AST/Expr.h>
#include <clang/Basic/Version.inc>

using namespace clang;
using namespace fmt;

enum Done : unsigned {
    NONE = 0,
    T = 1,
    O = 2,
    DT = 4,
};

fmt::Formatter &ClangPrinter::printOverloadableOperator(
    CoqPrinter &print, clang::OverloadedOperatorKind oo, loc::loc loc) {
    if (trace(Trace::Expr))
        trace("printOverloadableOperator", loc);
    auto with_array = [&](StringRef name, bool array) -> auto & {
        guard::ctor _(print, name, false);
        return print.boolean(array);
    };
    switch (oo) {
    case OO_New:
        return with_array("OONew", false);
    case OO_Array_New:
        return with_array("OONew", true);
    case OO_Delete:
        return with_array("OODelete", false);
    case OO_Array_Delete:
        return with_array("OODelete", true);
    default:
        break;
    }
    switch (oo) {
#define OVERLOADED_OPERATOR(Name, Spelling, Token, Unary, Binary, MemberOnly)  \
    case OO_##Name:                                                            \
        return print.output() << "OO" << #Name;
#include "clang/Basic/OperatorKinds.def"
#undef OVERLOADED_OPERATOR
#undef OVERLOADED_OPERATOR_MULTI
    default:
        error_prefix(logging::fatal(), loc)
            << "unknown overloadable operator " << oo << "\n";
        logging::die();
    }
}

void printOptionalExpr(CoqPrinter &print, std::optional<const Expr *> expr,
                       ClangPrinter &cprint, OpaqueNames &li) {
    if (expr.has_value() && expr.value()) {
        print.some();
        cprint.printExpr(print, expr.value(), li);
        print.end_ctor();
    } else {
        print.none();
    }
}

bool is_dependent(const Expr *expr) {
    return static_cast<bool>(expr->getDependence() &
                             ExprDependence::TypeValueInstantiation);
}

bool is_static_member(ValueDecl *decl) {
    if (auto field = dyn_cast<FieldDecl>(decl)) {
        return not field->isCXXInstanceMember();
    } else if (auto meth = dyn_cast<CXXMethodDecl>(decl)) {
        return meth->isStatic();
    } else if (dyn_cast<FunctionDecl>(decl)) {
        return true;
    } else if (dyn_cast<VarDecl>(decl)) {
        return true; // vd->isStaticLocal();
    } else {
        decl->dump();
        llvm::errs().flush();
        always_assert(false && "unsupported [is_static_member]");
        return false;
    }
}

// todo(gmm): this is duplicated!
bool is_builtin(const Decl *d) {
    if (const FunctionDecl *fd = dyn_cast_or_null<const FunctionDecl>(d)) {
        if (Builtin::ID::NotBuiltin != fd->getBuiltinID()) {
            return true;
        }
    }
    return false;
}

fmt::Formatter &ClangPrinter::printValueDeclExpr(CoqPrinter &print,
                                                 const ValueDecl *decl,
                                                 OpaqueNames &on) {
    if (trace(Trace::Expr))
        trace("printValueDeclExpr", loc::of(decl));
    auto check_static_local = [](const ValueDecl *decl) {
        auto t = dyn_cast<VarDecl>(decl);
        return t && t->isStaticLocal();
    };
    auto t = on.find_anon(decl);
    if (t != -1) {
        print.ctor("Evar", false) << "(localname.anon " << t << ")";
    } else if (decl->getDeclContext()->isFunctionOrMethod() and
               not(isa<FunctionDecl>(decl) or check_static_local(decl))) {
        print.ctor("Evar", false);
        if (auto pd = dyn_cast<ParmVarDecl>(decl)) {
            printParamName(print, pd);
        } else {
            printUnqualifiedName(print, *decl);
        }
    } else {
        print.ctor("Eglobal", false);
        withDecl(decl).printName(print, *decl);
    }
    print.output() << fmt::nbsp;
    if (auto bd = dyn_cast<BindingDecl>(decl)) {
        auto hv = bd->getHoldingVar();
        printQualType(print, hv ? hv->getType() : decl->getType(),
                      loc::of(decl));
    } else {
        printQualType(print, decl->getType(), loc::of(decl));
    }
    return print.end_ctor();
}

fmt::Formatter &ClangPrinter::printValueDeclExpr(CoqPrinter &print,
                                                 const ValueDecl *decl) {
    OpaqueNames names;
    return printValueDeclExpr(print, decl, names);
}

void printDependentMember(ClangPrinter &cprint, CoqPrinter &print,
                          const CXXDependentScopeMemberExpr *expr) {
    cprint.printUnresolvedName(print, expr->getQualifier(), expr->getMember(),
                               expr->template_arguments(), loc::of(expr));
}

/**
 * This class prints a dependent name (of Coq type [Mname]).
 */
struct PrintDependentName : public ConstStmtVisitor<PrintDependentName, void> {

    PrintDependentName(CoqPrinter &print_, ClangPrinter &cprint_)
        : print(print_), cprint(cprint_) {}

    void Visit(const Expr *expr) {
        if (cprint.trace(Trace::Name)) {
            llvm::errs() << "printDependentName(" << expr->getStmtClassName()
                         << ")\n";
            expr->dump();
        }
        ConstStmtVisitor<PrintDependentName, void>::Visit(expr);
    }

    void
    VisitCXXDependentScopeMemberExpr(const CXXDependentScopeMemberExpr *expr) {
        guard::ctor _{print, "Ndependent"};
        guard::ctor __{print, "Tresult_member"};
        cprint.printQualType(print, expr->getBaseType(), loc::of(expr))
            << fmt::nbsp;
        printDependentMember(cprint, print, expr);
    }

    void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr *expr) {
        cprint.printUnresolvedName(print, expr->getQualifier(),
                                   expr->getDeclName(),
                                   expr->template_arguments(), loc::of(expr));
    }

    void VisitUnresolvedLookupExpr(const UnresolvedLookupExpr *expr) {
        cprint.printUnresolvedName(print, expr->getQualifier(), expr->getName(),
                                   expr->template_arguments(), loc::of(expr));
    }

    void VisitUnresolvedMemberExpr(const UnresolvedMemberExpr *expr) {
        auto name = expr->getName();
        llvm::errs() << "printDeclarationName(" << expr->getName().getNameKind()
                     << ")";
        name.dump();

        print.output() << "(Nunsupported \"VisitUnresolvedMemberExpr\")";
    }
    void VisitDeclRefExpr(const DeclRefExpr *expr) {
        cprint.printName(print, *expr->getDecl());
    }

    void VisitExpr(const Expr *expr) {
        llvm::errs() << "PrintDependentName(" << expr->getStmtClassName()
                     << ")\n";
        expr->dump();
        // TODO: DependentScopeMemberExpr
        print.ctor("Nunsupported");
        print.str(expr->getStmtClassName());
        print.end_ctor();
    }

private:
    CoqPrinter &print;
    ClangPrinter &cprint;
};

/**
 * This class prints an expression (of Coq type [Expr] or [MExpr])
 */
class PrintExpr : public ConstStmtVisitor<PrintExpr, void> {
private:
    CoqPrinter &print;
    ClangPrinter &cprint;
    const ASTContext &ctxt;
    OpaqueNames &names;

    fmt::Formatter &printDeclType(const Expr *expr) {
        auto ty = expr->getType();
        if (ty.isNull())
            return print.output() << "Tauto";
        if (expr->isLValue()) {
            guard::ctor _(print, "Tref", false);
            cprint.printQualType(print, ty, loc::of(expr));
        } else if (expr->isXValue()) {
            guard::ctor _(print, "Trv_ref", false);
            cprint.printQualType(print, ty, loc::of(expr));
        } else {
            cprint.printQualType(print, ty, loc::of(expr));
        }
        return print.output();
    }

    fmt::Formatter &done(const Expr *expr, Done want = Done::T) {
        if (want == Done::DT) {
            printDeclType(expr);
        } else {
            if (want & Done::T) {
                if (expr->getType().isNull())
                    return print.output() << "Tauto";
                print.output() << fmt::nbsp;
                cprint.printQualType(print, expr->getType(), loc::of(expr));
            }
            if (want & Done::O) {
                print.output() << fmt::nbsp;
                cprint.printQualTypeOption(print, expr->getType(),
                                           loc::of(expr));
            }
        }
        return print.end_ctor();
    }

public:
    PrintExpr(CoqPrinter &print, ClangPrinter &cprint, OpaqueNames &names)
        : print(print), cprint(cprint), ctxt(cprint.getContext()),
          names(names) {}

    void VisitStmt(const Stmt *stmt) {
        logging::fatal() << "Error: while printing an expr, got a statement '"
                         << stmt->getStmtClassName() << " at "
                         << cprint.sourceRange(stmt->getSourceRange()) << "'\n";
        logging::die();
    }

    void unsupported_expr(const Expr *expr,
                          std::optional<StringRef> msg = std::nullopt,
                          bool well_known = false) {
        auto loc = loc::of(expr);
        if (!well_known || ClangPrinter::warn_well_known) {
            cprint.error_prefix(logging::unsupported(), loc)
                << "warning: unsupported expression";
            if (msg)
                logging::unsupported() << ": " << *msg;
            logging::unsupported() << "\n";
        }
        print.ctor("Eunsupported", false);
        std::string coqmsg;
        llvm::raw_string_ostream os{coqmsg};
        os << loc::describe(loc, cprint.getContext());
        print.str(coqmsg) << fmt::nbsp;
        done(expr, Done::DT);
    }

    void Visit(const Expr *expr) {
        if (expr == nullptr) [[unlikely]] {
            guard::ctor _{print, "Eunsupported"};
            print.str("empty expression (nullptr)") << " Tauto";
        } else if (expr->containsErrors()) {
            auto loc = loc::of(expr);
            print.ctor("Eunsupported", false);
            std::string coqmsg;
            llvm::raw_string_ostream os{coqmsg};
            os << loc::describe(loc, cprint.getContext());
            print.str(coqmsg) << fmt::nbsp;
            done(expr, Done::DT);
        } else {
            ConstStmtVisitor<PrintExpr, void>::Visit(expr);
        }
    }

    void VisitExpr(const Expr *expr) { unsupported_expr(expr); }

#define IGNORE(E)                                                              \
    void Visit##E(const E *expr) {                                             \
        unsupported_expr(expr, std::nullopt, /*well_known*/ true);             \
    }

    // Unsupported
    IGNORE(CXXThrowExpr)
    IGNORE(CXXTypeidExpr)

    void VisitStmtExpr(const StmtExpr *expr) {
        guard::ctor _{print, "Estmt"};

        cprint.printStmt(print, expr->getSubStmt()) << fmt::nbsp;
        cprint.printQualType(print, expr->getType(), loc::of(expr));
    }

    void
    VisitCXXRewrittenBinaryOperator(const CXXRewrittenBinaryOperator *expr) {
        cprint.printExpr(print, expr->getSemanticForm(), names);
    }

    // These are template TODOs
    IGNORE(CXXUnresolvedConstructExpr)
    IGNORE(SizeOfPackExpr) // used in BHV

    void VisitGNUNullExpr(const GNUNullExpr *expr) {
        print.ctor("Egnu_null", false);
        done(expr);
    }

    void VisitDependentScopeDeclRefExpr(const DependentScopeDeclRefExpr *expr) {
        if (!print.templates())
            return unsupported_expr(expr);

        guard::ctor _(print, "Eunresolved_global", false);
        cprint.printUnresolvedName(print, expr->getQualifier(),
                                   expr->getDeclName(),
                                   expr->template_arguments(), loc::of(expr));
    }

    void VisitUnresolvedLookupExpr(const UnresolvedLookupExpr *expr) {
        if (!print.templates())
            return unsupported_expr(expr);

        guard::ctor _(print, "Eunresolved_global", false);
        cprint.printUnresolvedName(print, expr->getQualifier(), expr->getName(),
                                   expr->template_arguments(), loc::of(expr));
    }

    void VisitRecoveryExpr(const RecoveryExpr *expr) {
        using namespace logging;
        unsupported() << "Error detected when typechecking C++ code at "
                      << cprint.sourceRange(expr->getSourceRange()) << "\n"
                      << "Try fixing earlier errors\n";
        print.ctor("Eunsupported", false);
        print.str(expr->getStmtClassName());
        done(expr, Done::DT);
    }

    void printBinaryOperator(const BinaryOperator *expr) {
        switch (expr->getOpcode()) {
#define CASE(k, s)                                                             \
    case BinaryOperatorKind::BO_##k:                                           \
        print.output() << s;                                                   \
        break;
            CASE(Add, "Badd")
            CASE(And, "Band")
            CASE(Cmp, "Bcmp")
            CASE(Div, "Bdiv")
            CASE(EQ, "Beq")
            CASE(GE, "Bge")
            CASE(GT, "Bgt")
            CASE(LE, "Ble")
            CASE(LT, "Blt")
            CASE(Mul, "Bmul")
            CASE(NE, "Bneq")
            CASE(Or, "Bor")
            CASE(Rem, "Bmod")
            CASE(Shl, "Bshl")
            CASE(Shr, "Bshr")
            CASE(Sub, "Bsub")
            CASE(Xor, "Bxor")
            CASE(PtrMemD, "Bdotp")
            CASE(PtrMemI, "Bdotip")
#undef CASE
        default:
            logging::unsupported()
                << "Unsupported binary operator '" << expr->getOpcodeStr()
                << "' (at " << cprint.sourceRange(expr->getSourceRange())
                << ")\n";
            print.output() << "(Bunsupported \"" << expr->getOpcodeStr()
                           << "\")";
            break;
        }
    }

    void VisitBinaryOperator(const BinaryOperator *expr) {
#define ACASE(k, v)                                                            \
    case BinaryOperatorKind::BO_##k##Assign:                                   \
        print.ctor("Eassign_op") << #v << fmt::nbsp;                           \
        break;
        [[maybe_unused]] auto dependent =
            print.templates() && expr->getType()->isDependentType();
        switch (expr->getOpcode()) {
        case BinaryOperatorKind::BO_Comma:
            print.ctor("Ecomma");
            cprint.printExpr(print, expr->getLHS());
            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getRHS());
            // TODO: Can be overloaded
            always_assert(
                (dependent || expr->getRHS()->getType() == expr->getType()) &&
                "types must match");
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_LAnd:
            print.ctor("Eseqand");
            cprint.printExpr(print, expr->getLHS());
            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getRHS());
            // TODO: Can be overloaded
            always_assert(
                (dependent || expr->getType().getTypePtr()->isBooleanType()) &&
                "&& is a bool");
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_LOr:
            print.ctor("Eseqor");
            cprint.printExpr(print, expr->getLHS());
            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getRHS());
            // TODO: Can be overloaded
            always_assert(
                (dependent || expr->getType().getTypePtr()->isBooleanType()) &&
                "|| is a bool");
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_Assign:
            print.ctor("Eassign");
            break;
            ACASE(Add, Badd)
            ACASE(And, Band)
            ACASE(Div, Bdiv)
            ACASE(Mul, Bmul)
            ACASE(Or, Bor)
            ACASE(Rem, Bmod)
            ACASE(Shl, Bshl)
            ACASE(Shr, Bshr)
            ACASE(Sub, Bsub)
            ACASE(Xor, Bxor)
        default:
            print.ctor("Ebinop");
            printBinaryOperator(expr);
            print.output() << fmt::nbsp;
            break;
        }
#undef ACASE
        cprint.printExpr(print, expr->getLHS(), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getRHS(), names);
        done(expr, print.templates() ? Done::O : Done::T);
    }

    void printUnaryOperator(const UnaryOperator *expr) {
        switch (expr->getOpcode()) {
#define CASE(k, s)                                                             \
    case UnaryOperatorKind::UO_##k:                                            \
        print.output() << s;                                                   \
        break;
            CASE(Plus, "Uplus")
            CASE(Minus, "Uminus")
            CASE(Not, "Ubnot")
            CASE(LNot, "Unot")
            CASE(PostDec, "<PostDec>")
            CASE(PostInc, "<PostInc>")
            CASE(PreDec, "<PreDec>")
            CASE(PreInc, "<PreInc>")
#undef CASE
        default:
            logging::unsupported()
                << "Unsupported unary operator '"
                << UnaryOperator::getOpcodeStr(expr->getOpcode()) << "' (at "
                << cprint.sourceRange(expr->getSourceRange()) << ")\n";
            print.output() << "(Uunsupported \""
                           << UnaryOperator::getOpcodeStr(expr->getOpcode())
                           << "\")";
            break;
        }
    }

    void VisitUnaryOperator(const UnaryOperator *expr) {
        switch (expr->getOpcode()) {
        case UnaryOperatorKind::UO_Extension: {
            guard::ctor _{print, "Eextension"};
            cprint.printExpr(print, expr->getSubExpr(), names);
            return;
        }
        case UnaryOperatorKind::UO_AddrOf: {
            auto e = expr->getSubExpr();
            if (auto dre = dyn_cast<DeclRefExpr>(e)) {
                auto decl = dre->getDecl();
                if (not is_static_member(decl)) {
                    guard::ctor _(print, "Eglobal_member");
                    cprint.printName(print, decl, loc::of(expr));
                    print.output() << fmt::nbsp;
                    cprint.printQualType(print, decl->getType(), loc::of(expr));
                    return;
                }
            }
            print.ctor("Eaddrof");
            cprint.printExpr(print, e, names);
            print.end_ctor(); // elide type
            return;
        }
        case UnaryOperatorKind::UO_Deref:
            print.ctor("Ederef");
            break;
        case UnaryOperatorKind::UO_PostInc:
            print.ctor("Epostinc");
            break;
        case UnaryOperatorKind::UO_PreInc:
            print.ctor("Epreinc");
            break;
        case UnaryOperatorKind::UO_PostDec:
            print.ctor("Epostdec");
            break;
        case UnaryOperatorKind::UO_PreDec:
            print.ctor("Epredec");
            break;
        default:
            print.ctor("Eunop");
            printUnaryOperator(expr);
            print.output() << fmt::nbsp;
        }
        cprint.printExpr(print, expr->getSubExpr(), names);
        done(expr, print.templates() ? Done::O : Done::T);
    }

    static const FieldDecl *getCaptureField(const CXXRecordDecl *lambda,
                                            const ValueDecl *var) {
        llvm::DenseMap<const ValueDecl *, FieldDecl *> var_captures;
        FieldDecl *this_capture;
        lambda->getCaptureFields(var_captures, this_capture);
        for (auto &i : var_captures) {
            if (i.first == var) {
                return i.second;
            }
        }
        return nullptr;
    }

    static const FieldDecl *getCaptureThis(const CXXRecordDecl *lambda) {
        llvm::DenseMap<const ValueDecl *, FieldDecl *> var_captures;
        FieldDecl *this_capture;
        lambda->getCaptureFields(var_captures, this_capture);
        return this_capture;
    }

    void VisitDeclRefExpr(const DeclRefExpr *expr) {
        auto var_decl = expr->getDecl();
        if (!var_decl) {
            cprint.error_prefix(logging::fatal(), loc::of(expr))
                << "DeclRefExpr missing Decl\n";
            print.die();
        }

        if (ClangPrinter::debug && cprint.trace(Trace::Expr)) {
            auto &os = cprint.trace("VisitDeclRefExpr", loc::of(expr));
            auto loc = loc::of(var_decl);
            if (loc::can_describe(loc))
                os << "Declaration: " << loc::describe(loc, cprint.getContext())
                   << "\n";
        }
        if (expr->refersToEnclosingVariableOrCapture()) {
            auto maybe_lambda = cprint.getLambdaClass();
            always_assert(maybe_lambda.has_value() &&
                          "lambda class must be non-null during capture");
            auto &[lambda, cv] = maybe_lambda.value();
            if (auto capture = getCaptureField(lambda, expr->getDecl())) {

                // TODO this needs to become [Emember true Ethis (??) false _]
                print.ctor("Ecapture_var");
                // The qualifiers on the <<operator()>> method.
                cprint.printQualifier(print, cv.hasConst(), cv.hasVolatile())
                    << fmt::nbsp;
                // The name of the lambda class
                cprint.printName(print, lambda, loc::of(lambda)) << fmt::nbsp;
                // The name of the captured variable.
                // >> The actual [FieldDecl] might be (is?) anonymous, so we
                // pull the data from the
                //    variable that is being captured
                auto nm = var_decl->getName();
                always_assert(0 < nm.size());
                // TODO NAMES: this should never be anonymous, but it
                // technically could be
                print.str(nm) << fmt::nbsp;
                // The type of the field
                cprint.printQualType(print, capture->getType(),
                                     loc::of(var_decl));
                print.end_ctor();
            } else {
                print.ctor("Eunevaluated_var");
                cprint.printUnqualifiedName(print, *var_decl);
                done(expr);
            }
        } else if (auto ecd = dyn_cast<EnumConstantDecl>(var_decl)) {
            // References to `enum` constants are special because
            // they can be referenced both at the enumeration type
            // and (within the `enum` declaration) they can be
            // referenced at the underlying type. Here, we
            // unify these two so that the type of a reference to
            // an `enum` constant is *always* the `enum` type.
            // To match the type of the expression, we insert
            // an implicit integral cast.

            auto ed = dyn_cast<EnumDecl>(ecd->getDeclContext());
            if (expr->getType()->isEnumeralType()) {
                print.ctor("Eenum_const", false);
                cprint.printName(print, ed, loc::of(ecd));
                print.output() << fmt::nbsp;
                cprint.printUnqualifiedName(print, *ecd);
                print.end_ctor();
            } else {
                // TODO: is it possible to determine the `DeclContext` that
                // this expression occurs in? If so, then we could assert that
                // this is in the scope of the enumeration.
                print.ctor("Eenum_const_at", false);
                cprint.printName(print, ed, loc::of(ecd));
                print.output() << fmt::nbsp;
                cprint.printUnqualifiedName(print, *ecd);
                print.output() << fmt::nbsp;
                done(expr);
            }
        } else if (auto param = dyn_cast<NonTypeTemplateParmDecl>(var_decl)) {
            if (print.templates()) {
                // TODO: Add some tests
                guard::ctor _(print, "Eparam", false);
                cprint.printUnqualifiedName(print, *param);
            } else {
                cprint.printNonTypeTemplateParam(
                    print, param->getDepth(), param->getIndex(), loc::of(expr));
#if 0
				llvm::errs() << "\n";
				expr->dump();
				var_decl->dump();
				llvm::errs() << "\n";

				llvm::errs().flush();

				always_assert(false);
				unsupported_expr(expr, std::nullopt,
								 /*well_known*/ true);
#endif
            }
        } else {
            // expr->dump();
            // var_decl->dump();
            // auto found_decl = expr->getFoundDecl();
            // found_decl->dump();
            cprint.printValueDeclExpr(print, var_decl, names);
        }
    }

    void VisitCallExpr(const CallExpr *expr) {
        auto callee = expr->getCallee();
        if (is_dependent(expr)) {
            /*
            Either the function or an argument is dependent.
            */
            guard::ctor ctor(print, "Eunresolved_call");
            PrintDependentName{print, cprint}.Visit(callee);
            print.output() << fmt::nbsp;
            print.list(expr->arguments(),
                       [&](auto i) { cprint.printExpr(print, i, names); });
        } else if (auto pd = dyn_cast<CXXPseudoDestructorExpr>(callee)) {
            // in the clang AST, pseudo destructors are represented as calls
            // but in the BRiCk AST, they are their own construct.
            always_assert(expr->arguments().empty());
            print.ctor("Epseudo_destructor")
                << fmt::BOOL(pd->isArrow()) << fmt::nbsp;
            cprint.printQualType(print, pd->getDestroyedType(), loc::of(pd));
            print.output() << fmt::nbsp;
            cprint.printExpr(print, pd->getBase(), names);
            print.end_ctor();
        } else {
            print.ctor("Ecall");
            cprint.printExpr(print, expr->getCallee(), names);
            print.output() << fmt::line;
            print.list(expr->arguments(),
                       [&](auto i) { cprint.printExpr(print, i, names); });
            done(expr, Done::NONE);
        }
    }

    void VisitCXXOperatorCallExpr(const CXXOperatorCallExpr *expr) {
        // TODO operator calls sometimes have stricter order of evaluation
        // than regular function calls. Because our semantics overapproximates
        // the possible behaviors, it is sound for us to directly desugar them.
        auto callee = expr->getCalleeDecl();
        // some operator calls are actually method calls.
        // because we (and C++) distinguish between member calls
        // and function calls, we need to desugar this to a method
        // if the called function is a method.
        if (callee == nullptr) {
            print.ctor("Eunsupported");
            print.str("unsupported operator call (nullptr)");
            done(expr, Done::DT);
        } else if (auto method = dyn_cast<CXXMethodDecl>(callee)) {
            always_assert(!method->isStatic() &&
                          "operator overloads can not be static");
            guard::ctor _{print, "Eoperator_member_call"};
            cprint.printOverloadableOperator(print, expr->getOperator(),
                                             loc::of(expr))
                << fmt::nbsp;

            cprint.printName(print, *method);
            print.output() << fmt::nbsp
                           << (method->isVirtual() ? "Virtual" : "Direct")
                           << fmt::nbsp;
            cprint.printQualType(print, method->getType(), loc::of(method));
            print.output() << fmt::nbsp;

            cprint.printExpr(print, expr->getArg(0), names);

            print.output() << fmt::nbsp;
            // note skip the first parameter because it is the object.
            print.list_range(
                expr->arg_begin() + 1, expr->arg_end(),
                [&](auto i) { cprint.printExpr(print, i, names); });

        } else if (auto function = dyn_cast<FunctionDecl>(callee)) {
            guard::ctor _{print, "Eoperator_call"};
            cprint.printOverloadableOperator(print, expr->getOperator(),
                                             loc::of(expr))
                << fmt::nbsp;

            cprint.printName(print, *function);
            print.output() << fmt::nbsp;
            cprint.printQualType(print, function->getType(), loc::of(function));
            print.output() << fmt::nbsp;
            print.list(expr->arguments(),
                       [&](auto i) { cprint.printExpr(print, i, names); });
        } else {
            print.ctor("Eunsupported");
            print.str("unsupported operator call");
            done(expr, Done::DT);
        }
    }

    void printCast(const CastExpr *ce) {
        auto with_type = [&](const char *c) {
            guard::ctor _(print, c, false);
            printDeclType(ce);
        };
        auto without_type = [&](const char *c) { print.output() << c; };

        switch (ce->getCastKind()) {
#define CASE_NO_TYPE(a, b)                                                     \
    case CastKind::CK_##a:                                                     \
        without_type(#b);                                                      \
        break;
#define CASE_WITH_TYPE(a, b)                                                   \
    case CastKind::CK_##a:                                                     \
        with_type(#b);                                                         \
        break;
            CASE_WITH_TYPE(BitCast, Cbitcast)
            CASE_WITH_TYPE(LValueBitCast, Clvaluebitcast)
            CASE_NO_TYPE(LValueToRValue, Cl2r)
            CASE_WITH_TYPE(LValueToRValueBitCast, Cl2r_bitcast)
            CASE_WITH_TYPE(NoOp, Cnoop)
            CASE_NO_TYPE(ArrayToPointerDecay, Carray2ptr)
            CASE_NO_TYPE(FunctionToPointerDecay, Cfun2ptr)
            CASE_WITH_TYPE(IntegralToPointer, Cint2ptr)
            CASE_WITH_TYPE(PointerToIntegral, Cptr2int)

            CASE_NO_TYPE(PointerToBoolean, Cptr2bool)
            CASE_WITH_TYPE(IntegralCast, Cintegral)
            CASE_NO_TYPE(IntegralToBoolean, Cint2bool)

            CASE_WITH_TYPE(NullToPointer, Cnull2ptr)
            CASE_WITH_TYPE(NullToMemberPointer, Cnull2memberptr)

            CASE_WITH_TYPE(BuiltinFnToFnPtr, Cbuiltin2fun)

            CASE_WITH_TYPE(ConstructorConversion, Cctor)
            CASE_NO_TYPE(UserDefinedConversion, Cuser)

            CASE_NO_TYPE(ToVoid, C2void)

            CASE_WITH_TYPE(Dynamic, Cdynamic)

            // floating point casts
            CASE_WITH_TYPE(FloatingToIntegral, Cfloat2int)
            CASE_WITH_TYPE(IntegralToFloating, Cint2float)
            CASE_WITH_TYPE(FloatingCast, Cfloat)

            CASE_WITH_TYPE(Dependent, Cdependent)
#undef CASE_NO_TYPE
#undef CASE_WITH_TYPE

        case CastKind::CK_DerivedToBase:
        case CastKind::CK_UncheckedDerivedToBase: {
            print.ctor("Cderived2base");
            // note that [path] does *not* include the type of the argument
            print.list_range(ce->path().begin(), ce->path().end() - 1,
                             [&](auto i) {
                                 auto t = i->getType().getTypePtrOrNull();
                                 always_assert(t &&
                                               "Cderived2base without type");
                                 cprint.printType(print, *t, loc::of(ce));
                             })
                << fmt::nbsp;
            done(ce, Done::DT);
            break;
        }
        case CastKind::CK_BaseToDerived:
            print.ctor("Cbase2derived");
            // note that [path] does *not* include the type of the argument
            print.list_range(ce->path().begin(), ce->path().end() - 1,
                             [&](auto i) {
                                 auto t = i->getType().getTypePtrOrNull();
                                 always_assert(t &&
                                               "Cbase2derived without type");
                                 cprint.printType(print, *t, loc::of(ce));
                             })
                << fmt::nbsp;
            done(ce, Done::DT);
            break;
        default:
            logging::unsupported()
                << "unsupported cast kind \"" << ce->getCastKindName() << "\""
                << " (at " << cprint.sourceRange(ce->getSourceRange()) << ")\n";
            print.ctor("Cunsupported", false);
            print.str(ce->getCastKindName()) << fmt::nbsp;
            done(ce, Done::DT);
        }
    }

    void VisitExplicitCastExpr(const ExplicitCastExpr *expr) {
        if (isa<CStyleCastExpr>(expr)) {
            print.ctor("Ecstyle_cast");
        } else if (auto nc = dyn_cast<CXXNamedCastExpr>(expr)) {
            print.ctor(llvm::Twine("E") + nc->getCastName());
        } else if (isa<CXXFunctionalCastExpr>(expr)) {
            print.ctor("Efunctional_cast");
        } else if (isa<BuiltinBitCastExpr>(expr)) {
            print.ctor("Ebuiltin_bit_cast");
        } else {
            return unsupported_expr(expr, std::nullopt, false);
        }

        printCast(expr);
        print.output() << fmt::nbsp;
        cprint.printQualType(print, expr->getTypeAsWritten(), loc::of(expr));
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getSubExpr(), names);
        print.end_ctor();
    }

    void VisitImplicitCastExpr(const ImplicitCastExpr *expr) {
        // todo(gmm): this is a complete hack because there is no way that i
        // know of to get the type of a builtin. what this does is get the type
        // of the expression that contains the builtin.
        if (expr->getCastKind() == CastKind::CK_BuiltinFnToFnPtr) {
            auto ref = dyn_cast<DeclRefExpr>(expr->getSubExpr());
            always_assert(ref && "builtin function to function pointer must be "
                                 "applied to a literal variable");
            always_assert(is_builtin(ref->getDecl()));
            print.ctor("Ebuiltin", false);
            // assume that this is a builtin
            cprint.printName(print, ref->getDecl(), loc::of(ref)) << fmt::nbsp;
            auto type = expr->getType();
            if (type->isPointerType()) {
                // NOTE: in most instances, the type of this expression
                // is a pointer to a function type, but in some cases,
                // clang does not emit the top-level pointer.
                cprint.printQualType(print, type.getTypePtr()->getPointeeType(),
                                     loc::of(expr));
            } else {
                cprint.printQualType(print, type, loc::of(expr));
            }
            print.end_ctor();
            return;
        }

        guard::ctor _(print, "Ecast");
        printCast(expr);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getSubExpr(), names);
    }

    void VisitCastExpr(const CastExpr *expr) {
        always_assert(false && "Cast expression should be unreachable");
    }

    void VisitIntegerLiteral(const IntegerLiteral *lit) {
        print.ctor("Eint", false);
        SmallString<32> s;
        if (lit->getType()->isSignedIntegerOrEnumerationType()) {
            lit->getValue().toStringSigned(s);
        } else {
            lit->getValue().toStringUnsigned(s);
        }
        print.output() << s << "%Z";
        done(lit);
    }

    void VisitCharacterLiteral(const CharacterLiteral *lit) {
        print.ctor("Echar", false) << lit->getValue() << "%N";
        done(lit);
    }

    static void print_string_type(const Expr *expr, CoqPrinter &print,
                                  ClangPrinter &cprint) {
        if (auto at = dyn_cast<ArrayType>(expr->getType().getTypePtr())) {
            print.output() << fmt::nbsp;
            cprint.printType(print, at->getElementType().getTypePtr(),
                             loc::of(expr));
        } else {
            always_assert(false && "string literal does not have array type");
        }
    }

    void VisitSourceLocExpr(const SourceLocExpr *expr) {
        guard::ctor _{print, "Esource_loc"};
        print.str(expr->getBuiltinStr()) << fmt::nbsp;
        auto val = expr->EvaluateInContext(cprint.getContext(), nullptr);
        if (expr->isIntType()) {
            print.ctor("Eint");
            print.output() << fmt::Z(val.getInt(), false) << fmt::nbsp;
            done(expr);
        } else {
            // this is actually an LValue
            auto base = val.getLValueBase();
            always_assert(base.is<const Expr *>());
            cprint.printExpr(print, base.get<const Expr *>(), names);
        }
    }

    void VisitStringLiteral(const StringLiteral *lit) {
        print.ctor("Estring", false);
        // We get the string literal in bytes, but we need to encode it
        // as unsigned characters (not necessarily `char`) using the
        // internal character representation of BRiCk.
        auto bytes = lit->getBytes();
        const unsigned width = lit->getCharByteWidth();
        print.begin_list();
#if 18 <= CLANG_VERSION_MAJOR
        namespace endianNS = llvm;
#else
        namespace endianNS = llvm::support;
#endif
        for (unsigned i = 0, len = lit->getByteLength(); i < len;) {
            unsigned long long byte = 0;
            // TODO confirm that this is correct
            if (endianNS::endianness::native == endianNS::endianness::big) {
                for (unsigned j = 0; j < width; ++j) {
                    byte = (byte << 8) | static_cast<unsigned char>(bytes[i++]);
                }
            } else {
                for (unsigned j = 0; j < width; ++j) {
                    byte = (byte << 8) |
                           static_cast<unsigned char>(bytes[i + width - j - 1]);
                }
                i += width;
            }
            print.output() << byte << "%N";
            print.cons();
        }
        print.end_list();
        // NOTE: the trailing `\0` is added by the semantics
        print_string_type(lit, print, cprint);
        print.end_ctor();
    }

    void VisitPredefinedExpr(const PredefinedExpr *expr) {
        // [PredefinedExpr] constructs a [string] which is always ascii
        print.ctor("Estring");
        print.ctor("BS.string_to_bytes");
        print.str(expr->getFunctionName()->getString());
        print.end_ctor();
        print_string_type(expr, print, cprint);
        print.end_ctor();
    }

    void VisitCXXBoolLiteralExpr(const CXXBoolLiteralExpr *lit) {
        if (lit->getValue()) {
            print.output() << "(Ebool true)";
        } else {
            print.output() << "(Ebool false)";
        }
    }

    void VisitFloatingLiteral(const FloatingLiteral *lit) {
        print.ctor("Eunsupported") << fmt::nbsp << "\"float: ";
        lit->getValue().print(print.output().nobreak());
        print.output() << "\"";
        done(lit, Done::DT);
    }

    void VisitMemberExpr(const MemberExpr *expr) {
        auto member = expr->getMemberDecl();
        auto base = expr->getBase();

        print.ctor("Emember");
        print.boolean(expr->isArrow()) << fmt::nbsp;

        cprint.printExpr(print, base, names) << fmt::nbsp;
        if (auto fd = dyn_cast<FieldDecl>(member)) {
            // print.str(expr->getMemberDecl()->getNameAsString());
            guard::ctor _{print, "Field", false};
            cprint.printFieldName(print, *fd, loc::of(expr)) << fmt::nbsp;
            print.boolean(fd->isMutable()) << fmt::nbsp;
            // The type of the expression is determined by the type of the
            // object, the type of the member, and the mutability of the member.
            // The only piece of information that we are missing is the
            // mutability of the member. We can compute the type of the full
            // expression by 1/ if the field type is reference, or rv_reference,
            // that is type 2/ otherwise, taking the qualifiers of the object,
            // remove [const]
            //    if the field is [mutable], and then use the type of the field.

            cprint.printQualType(print, member->getType(), loc::of(member));
        } else if (auto ed = dyn_cast<EnumConstantDecl>(member)) {
            guard::ctor _{print, "Enum", false};
            cprint.printName(print, *ed);

        } else if (auto vd = dyn_cast<VarDecl>(member)) {
            always_assert(vd->isStaticDataMember() &&
                          "variable referenced through member must be "
                          "a static data member");
            guard::ctor _{print, "Static", false};
            cprint.printName(print, *vd) << fmt::nbsp;
            cprint.printQualType(print, member->getType(), loc::of(member));
        } else if (auto md = dyn_cast<CXXMethodDecl>(member)) {
            guard::ctor _{print, "Static", false};
            cprint.printName(print, *md) << fmt::nbsp;
            cprint.printQualType(print, member->getType(), loc::of(member));
        } else {
            logging::fatal() << "Unknown member in MemberExpr\n";
            logging::die();
        }
        print.end_ctor();
    }

    void
    VisitCXXDependentScopeMemberExpr(const CXXDependentScopeMemberExpr *expr) {
        guard::ctor _{print, "Eunresolved_member"};
        print.boolean(expr->isArrow()) << fmt::nbsp;
        cprint.printExpr(print, expr->getBase(), names) << fmt::nbsp;
        printDependentMember(cprint, print, expr);
    }

    void VisitArraySubscriptExpr(const ArraySubscriptExpr *expr) {
        // Array-to-pointer casts obscure value category inference because
        // the resulting pointer is a prvalue regardless of the value category
        // of the array. To make the typing rules composable, we drop this
        // cast and generalize the semantics of subscript to directly support
        // array types.
        auto under_cast = [](const Expr *expr) {
            if (auto ce = dyn_cast<ImplicitCastExpr>(expr)) {
                if (ce->getCastKind() == CastKind::CK_ArrayToPointerDecay)
                    return ce->getSubExpr();
            }
            return expr;
        };

        print.ctor("Esubscript");
        cprint.printExpr(print, under_cast(expr->getLHS()), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, under_cast(expr->getRHS()), names);
        done(expr, print.templates() ? Done::O : Done::T);
    }

    void VisitCXXConstructExpr(const CXXConstructExpr *expr) {
        print.ctor("Econstructor");
        // print.output() << expr->isElidable() << fmt::nbsp;
        cprint.printName(print, expr->getConstructor(), loc::of(expr));
        print.output() << fmt::nbsp;
        print.list(expr->arguments(),
                   [&](auto i) { cprint.printExpr(print, i, names); });
        // print.output() << fmt::nbsp << expr->isElidable();
        done(expr);
    }

    void VisitCXXInheritedCtorInitExpr(const CXXInheritedCtorInitExpr *expr) {
        print.ctor("Econstructor");
        // print.output() << expr->isElidable() << fmt::nbsp;
        auto ctor = expr->getConstructor();
        cprint.printName(print, ctor, loc::of(expr));
        print.output() << fmt::nbsp;
        // NOTE clang does not include the arguments to the constructor here
        // they are forwarded from the function itself; however, with the
        // data that we have, we can't get to the actual function.
        // A good solution would be to store this information in the
        // [OpaqueNames] object, but for now, we can get away with printing the
        // variable references directly.
        auto idx = 0;
        print.list(ctor->parameters(), [&](auto i) {
            print.ctor("Evar", false);
            print.output() << "(localname.anon " << idx << ")";
            print.output() << fmt::nbsp;
            cprint.printQualType(print, i->getType(), loc::of(i));
            print.end_ctor();
            ++idx;
        });
        // print.output() << fmt::nbsp << expr->isElidable();
        done(expr);
    }

    void VisitCXXMemberCallExpr(const CXXMemberCallExpr *expr) {
        print.ctor("Emember_call");
        auto callee = expr->getCallee()->IgnoreParens();
        auto method = expr->getMethodDecl();
        if (auto me = dyn_cast<MemberExpr>(callee)) {
            print.output() << fmt::BOOL(me->isArrow()) << fmt::nbsp;

            print.ctor("inl") << fmt::lparen;
            cprint.printName(print, method, loc::of(expr));
            print.output() << "," << fmt::nbsp;
            if (method->isVirtual() &&
                me->performsVirtualDispatch(ctxt.getLangOpts())) {
                print.output() << "Virtual";
            } else {
                print.output() << "Direct";
            }
            print.output() << "," << fmt::nbsp;

            if (const CXXMethodDecl *const md =
                    dyn_cast<CXXMethodDecl>(me->getMemberDecl())) {
                cprint.printQualType(print, md->getType(), loc::of(md));
            } else {
                always_assert(false &&
                              "MemberDecl in MemberCall must be a MethodDecl");
            }
            print.output() << fmt::rparen;
            print.end_ctor();

            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getImplicitObjectArgument(), names);
        } else if (auto bo = dyn_cast<BinaryOperator>(callee)) {
            always_assert(bo->getOpcode() == BinaryOperatorKind::BO_PtrMemD ||
                          bo->getOpcode() == BinaryOperatorKind::BO_PtrMemI);
            print.output() << fmt::BOOL(bo->getOpcode() ==
                                        BinaryOperatorKind::BO_PtrMemI)
                           << fmt::nbsp;

            print.ctor("inr");
            cprint.printExpr(print, bo->getRHS(), names);
            print.end_ctor() << fmt::nbsp;

            cprint.printExpr(print, expr->getImplicitObjectArgument(), names);
        } else {
            always_assert(false && "no method and not a binary operator");
        }
        print.output() << fmt::nbsp;
        print.list(expr->arguments(),
                   [&](auto i) { cprint.printExpr(print, i, names); });
#if 0
        print.output() << fmt::nbsp << fmt::lparen;
        for (auto i : expr->arguments()) {
          cprint.printExpr(print, i, names);
          print.cons();
        }
        print.end_list();
#endif
        done(expr, Done::NONE);
    }

    void VisitCXXDefaultArgExpr(const CXXDefaultArgExpr *expr) {
        print.ctor("Eimplicit");
        cprint.printExpr(print, expr->getExpr(), names);
        print.end_ctor();
    }

    void VisitConditionalOperator(const ConditionalOperator *expr) {
        print.ctor("Eif");
        cprint.printExpr(print, expr->getCond(), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getTrueExpr(), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getFalseExpr(), names);
        done(expr, Done::DT);
    }

    void VisitBinaryConditionalOperator(const BinaryConditionalOperator *expr) {
        print.ctor("Eif2");
        auto index = names.fresh(expr->getOpaqueValue());
        print.output() << index << fmt::nbsp;
        cprint.printExpr(print, expr->getCommon(), names);
        names.inc_index_count();
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getCond(), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getTrueExpr(), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getFalseExpr(), names);
        names.dec_index_count();
        done(expr, Done::DT);
    }

    void VisitConstantExpr(const ConstantExpr *expr) {
        this->Visit(expr->getSubExpr());
    }

    void VisitParenExpr(const ParenExpr *e) { this->Visit(e->getSubExpr()); }

    void VisitParenListExpr(const ParenListExpr *expr) {
        if (!print.templates()) {
            // This node type is purely syntactic.
            // When the type is known, the expression is represented
            // as [CXXConstructorExpr] or not represented at all, e.g.
            // in <<T x(1);>>.
            return unsupported_expr(expr);
        }
        print.ctor("Eunresolved_parenlist");

        cprint.printQualTypeOption(print, expr->getType(), loc::of(expr));
        print.output() << fmt::nbsp;

        // `print.list` unavailable because there's no constant
        // version of `ParenListExpr::exprs`.
        // TODO: Define and use iterator over integer ranges.

        auto n = expr->getNumExprs();
        if (n == 0)
            print.output() << "nil";
        else {
            print.begin_list();
            for (unsigned i = 0; i < n; i++) {
                cprint.printExpr(print, expr->getExpr(i), names);
                print.cons();
            }
            print.end_list();
        }
        print.end_ctor();
    }

    void VisitInitListExpr(const InitListExpr *expr) {
        if (expr->isTransparent()) {
            // "transparent" intializer lists are no-ops in the semantics
            // and are retained in the clang AST only for printing purposes.
            always_assert(expr->inits().size() == 1);
            cprint.printExpr(print, expr->getInit(0), names);
        } else if (auto fld = expr->getInitializedFieldInUnion()) {
            print.ctor("Einitlist_union");
            assert(expr->inits().size() <= 1 &&
                   "init length must be 1 for union initializer");
            assert(expr->getArrayFiller() == nullptr &&
                   "array filler not allowed for union initializer");

            cprint.printFieldName(print, *fld, loc::of(expr)) << fmt::nbsp;
            if (0 < expr->inits().size()) {
                guard::some _{print};
                cprint.printExpr(print, expr->getInit(0), names);
            } else {
                print.none();
            }
            done(expr);
        } else {
            print.ctor("Einitlist");

            print.list(expr->inits(), [&](auto i) {
                cprint.printExpr(print, i, names);
            }) << fmt::nbsp;

            if (expr->getArrayFiller()) {
                print.some();
                cprint.printExpr(print, expr->getArrayFiller(), names);
                print.end_ctor();
            } else {
                print.none();
            }

            done(expr);
        }
    }

    void VisitCXXThisExpr(const CXXThisExpr *expr) {
        if (auto maybe_lambda = cprint.getLambdaClass()) {
            auto &[lambda, cv] = maybe_lambda.value();
            auto capture = getCaptureThis(lambda);
            always_assert(capture && "captured variable is not captured");

            print.ctor("Ecapture_this", false);
            // The qualifiers on the <<operator()>> method
            cprint.printQualifier(print, cv.hasConst(), cv.hasVolatile())
                << fmt::nbsp;
            // The name of the lambda class
            cprint.printName(print, lambda, loc::of(expr)) << fmt::nbsp;
            // The type of the referenced field
            cprint.printQualType(print, capture->getType(), loc::of(expr));
            print.end_ctor();
        } else {
            print.ctor("Ethis", false);
            done(expr);
        }
    }

    void VisitCXXNullPtrLiteralExpr(const CXXNullPtrLiteralExpr *expr) {
        // <<nullptr>> has a special type
        print.output() << "Enull" << fmt::nbsp;
    }

    void VisitUnaryExprOrTypeTraitExpr(const UnaryExprOrTypeTraitExpr *expr) {
        auto do_arg = [&]() {
            if (expr->isArgumentType()) {
                print.ctor("inl", false);
                cprint.printQualType(print, expr->getArgumentType(),
                                     loc::of(expr));
                print.output() << fmt::rparen;
            } else if (expr->getArgumentExpr()) {
                print.ctor("inr", false);
                cprint.printExpr(print, expr->getArgumentExpr(), names);
                print.output() << fmt::rparen;
            } else {
                always_assert(false);
                // fatal("argument to sizeof/alignof is not a type or an
                // expression.");
            }
        };

        switch (expr->getKind()) {
        case UnaryExprOrTypeTrait::UETT_AlignOf: {
            print.ctor("Ealignof", false);
            do_arg();
            done(expr);
            break;
        }
        case UnaryExprOrTypeTrait::UETT_PreferredAlignOf: {
            print.ctor("Ealignof_preferred", false);
            do_arg();
            done(expr);
            break;
        }
        case UnaryExprOrTypeTrait::UETT_SizeOf: {
            print.ctor("Esizeof", false);
            do_arg();
            done(expr);
            break;
        }
        default: {
            using namespace logging;
            cprint.error_prefix(logging::unsupported(), loc::of(expr))
                << "warning: unsupported expression "
                   "`UnaryExprOrTypeTraitExpr`\n";
            print.ctor("Eunsupported");
            print.output() << "\"UnaryExprOrTypeTraitExpr(" << expr->getKind()
                           << ")\"" << fmt::nbsp;
            done(expr);
        }
        }
    }

    void VisitOffsetOfExpr(const OffsetOfExpr *expr) {
        auto unsupported = [&](const std::string what) {
            unsupported_expr(expr, what);
        };
        if (expr->getNumComponents() != 1)
            return unsupported(
                "offsetof with no components, or multiple components");

        auto comm = expr->getComponent(0);
        switch (comm.getKind()) {
        case OffsetOfNode::Kind::Field: {
            print.ctor("Eoffsetof");
            auto field = comm.getField();
            auto parent = field ? field->getParent() : nullptr;
            auto ty = parent ? parent->getTypeForDecl() : nullptr;
            always_assert(ty && "offsetof without type");

            cprint.printType(print, *ty, loc::of(expr)) << fmt::nbsp;
            print.str(comm.getField()->getName()) << fmt::nbsp;
            done(expr);
            return;
        }
        default:
            return unsupported(
                "offsetof only supported on fields and base classes");
        }
    }

    void VisitSubstNonTypeTemplateParmExpr(
        const SubstNonTypeTemplateParmExpr *expr) {
        this->Visit(expr->getReplacement());
    }

    void VisitCXXNewExpr(const CXXNewExpr *expr) {
        auto new_fn = expr->getOperatorNew();
        if (not new_fn) {
            unsupported_expr(expr, "dependent call to new");
            return;
        }

        print.ctor("Enew");

        print.begin_tuple();
        cprint.printName(print, *new_fn);
        print.next_tuple();
        cprint.printQualType(print, new_fn->getType(), loc::of(new_fn));
        print.end_tuple() << fmt::nbsp;

        print.list(expr->placement_arguments(), [&](auto arg) {
            cprint.printExpr(print, arg, names);
        }) << fmt::nbsp;

        if (new_fn->isReservedGlobalPlacementOperator()) {
            always_assert(expr->getNumPlacementArgs() == 1 &&
                          "placement new gets a single argument");
            always_assert(!expr->passAlignment() &&
                          "alignment is not passed to placement new");
            print.output() << "new_form.NonAllocating" << fmt::nbsp;
        } else {
            print.ctor("new_form.Allocating")
                << fmt::BOOL(expr->passAlignment()) << fmt::nbsp;
            print.end_ctor() << fmt::nbsp;
        }

        cprint.printQualType(print, expr->getAllocatedType(), loc::of(expr));

        print.output() << fmt::nbsp;

        // NOTE: the clang documentation says that this can return
        // None even if it is an array new, but I have not found a
        // way to trigger that.
        always_assert(expr->isArray() == (bool)expr->getArraySize());
        printOptionalExpr(print, expr->getArraySize(), cprint, names);

        print.output() << fmt::nbsp;

        printOptionalExpr(print, expr->getInitializer(), cprint, names);

        print.end_ctor();
    }

    void VisitCXXDeleteExpr(const CXXDeleteExpr *expr) {
        if (expr->getOperatorDelete()) {
            print.ctor("Edelete");
            print.output() << fmt::BOOL(expr->isArrayForm()) << fmt::nbsp;

            if (auto op = expr->getOperatorDelete()) {
                cprint.printName(print, *op);
            } else {
                logging::fatal() << "missing [delete] operator\n";
                logging::die();
            }
            print.output() << fmt::nbsp;

            cprint.printExpr(print, expr->getArgument(), names);

            print.output() << fmt::nbsp;

            cprint.printQualType(print, expr->getDestroyedType(),
                                 loc::of(expr));

            // no need to print the type information on [delete]
            print.end_ctor();
        } else {
            guard::ctor _{print, "Eunresolved_delete"};
            print.output() << fmt::BOOL(expr->isArrayForm()) << fmt::nbsp;
            cprint.printExpr(print, expr->getArgument(), names);
        }
    }

    void VisitExprWithCleanups(const ExprWithCleanups *expr) {
        // NOTE candidate for removal
        // our semantics cleans everything, so we don't need to
        // mark this explicitly.
        print.ctor("Eandclean");
        if (ClangPrinter::debug && cprint.trace(Trace::Expr)) {
            auto &os = llvm::errs();
            os << "and_clean objects: " << expr->getNumObjects() << "\n";
            for (auto i : expr->getObjects()) {
                os << i.getOpaqueValue() << "\n";
            }
        }
        cprint.printExpr(print, expr->getSubExpr(), names);
        print.end_ctor();
    }

    void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *expr) {
        if (expr->getExtendingDecl()) {
            // BRiCk does not currently support scope-extruded temporaries
            return unsupported_expr(expr, "scope-extruded temporary");
        }

        guard::ctor _{print, "Ematerialize_temp"};
        cprint.printExpr(print, expr->getSubExpr(), names) << fmt::nbsp;
        cprint.printValCat(print, expr);
    }

    void VisitCXXBindTemporaryExpr(const CXXBindTemporaryExpr *expr) {
        // According to [clang
        // docs](https://clang.llvm.org/doxygen/classclang_1_1CXXBindTemporaryExpr.html),
        // a CXXBindTemporary node "represents binding an expression to a
        // temporary. This ensures the destructor is called for the temporary.
        // It should only be needed for non-POD, non-trivially destructable
        // class types." We can omit these nodes because in our semantics,
        // objects are *always* deleted with destructors, even if the destructor
        // is trivial. Thus, our semantics essentially implicitly has a
        // [BindTemporary] node around all automatic storage duration
        // aggregates.

        cprint.printExpr(print, expr->getSubExpr(), names);
    }

    void VisitOpaqueValueExpr(const OpaqueValueExpr *expr) {
        print.ctor("Eopaque_ref") << names.find(expr);
        done(expr, Done::DT);
    }

    void VisitAtomicExpr(const clang::AtomicExpr *expr) {
        print.ctor("Eatomic");

        print.str(AtomicOpBackport::getOpAsString(expr)) << fmt::nbsp;

        print.begin_list();
        for (unsigned i = 0; i < expr->getNumSubExprs(); ++i) {
            cprint.printExpr(print, expr->getSubExprs()[i], names);
            print.cons();
        }
        print.end_list();

        done(expr);
    }

    void VisitCXXDefaultInitExpr(const CXXDefaultInitExpr *expr) {
        print.ctor("Edefault_init_expr");
        cprint.printExpr(print, expr->getExpr(), names);
        print.end_ctor();
    }

    void VisitVAArgExpr(const VAArgExpr *expr) {
        print.ctor("Eva_arg");
        cprint.printExpr(print, expr->getSubExpr(), names);
        done(expr);
    }

    void VisitLambdaExpr(const LambdaExpr *expr) {
        print.ctor("Elambda");
        cprint.printName(print, *expr->getLambdaClass()) << fmt::nbsp;

        print.list(expr->capture_inits(), [&](auto capture) {
            cprint.printExpr(print, capture, this->names);
        });
        print.end_ctor();
    }

    void VisitImplicitValueInitExpr(const ImplicitValueInitExpr *expr) {
        print.ctor("Eimplicit_init");
        done(expr);
    }

    void VisitCXXPseudoDestructorExpr(const CXXPseudoDestructorExpr *expr) {
        print.ctor("Epseudo_destructor");
        cprint.printQualType(print, expr->getDestroyedType(), loc::of(expr));
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getBase(), names);
        print.end_ctor();
    }

    void VisitCXXNoexceptExpr(const CXXNoexceptExpr *expr) {
        print.ctor("Enoexcept");
        cprint.printExpr(print, expr->getOperand(), names) << fmt::nbsp;
        print.boolean(expr->getValue());
        print.end_ctor();
    }

    void VisitTypeTraitExpr(const TypeTraitExpr *expr) {
        // note: i should record the fact that this is a type trait expression
        if (expr->isInstantiationDependent()) {
            print.ctor("Eunsupported");
            print.str("dependent type trait expr");
            done(expr);
        } else {
            print.ctor("Ebool");
            print.boolean(expr->getValue());
            print.end_ctor();
        }
    }

    void VisitConceptSpecializationExpr(const ConceptSpecializationExpr *expr) {
        if (expr->getDependence() && print.templates()) {
            print.ctor("Eunsupported");
            print.str("potentially dependent concept specialization");
            done(expr);
            return;
        }
        print.ctor("Econcept_specialization");
#if CLANG_VERSION_MAJOR <= 17
        auto cr = static_cast<const ConceptReference *>(expr);
#else
        auto cr = expr->getConceptReference();
#endif

        cprint.printUnresolvedName(
            print, cr->getNestedNameSpecifierLoc().getNestedNameSpecifier(),
            cr->getConceptNameInfo().getName(), expr->getTemplateArguments(),
            loc::of(expr))
            << fmt::nbsp;

        if (expr->getDependence()) {
            guard::ctor _{print, "Some", false};
            print.boolean(expr->isSatisfied());
        } else
            print.none();

        print.end_ctor();
    }

    void VisitCXXScalarValueInitExpr(const CXXScalarValueInitExpr *expr) {
        print.ctor("Eimplicit_init");
        cprint.printQualType(print, expr->getType(), loc::of(expr));
        print.end_ctor();
    }

    void VisitArrayInitLoopExpr(const ArrayInitLoopExpr *expr) {
        print.ctor("Earrayloop_init");

        auto index = names.fresh(expr->getCommonExpr());
        print.output() << index << fmt::nbsp;

        // this is the source array which we are initializing
        auto src = expr->getCommonExpr()->getSourceExpr();
        cprint.printExpr(print, src, names);

        // this is the expression that is evaluated
        names.inc_index_count();
        print.output() << names.index_count() << fmt::nbsp
                       << expr->getArraySize() << fmt::nbsp;
        cprint.printExpr(print, expr->getSubExpr(), names);
        names.dec_index_count();
        names.free(
            expr->getCommonExpr()); // index goes out of scope at this point

        done(expr);
    }

    void VisitArrayInitIndexExpr(const ArrayInitIndexExpr *expr) {
        print.ctor("Earrayloop_index") << names.index_count() << fmt::nbsp;
        done(expr);
    }
};

fmt::Formatter &ClangPrinter::printExpr(CoqPrinter &print,
                                        const clang::Expr *expr,
                                        OpaqueNames &li) {
    if (trace(Trace::Expr))
        trace("printExpr", loc::of(expr));

    auto depth = print.output().get_depth();
    PrintExpr{print, *this, li}.Visit(expr);
    if (depth != print.output().get_depth()) {
        using namespace logging;
        fatal() << "Error: BUG indentation bug in during: "
                << expr->getStmtClassName() << " start = " << depth
                << ", end = " << print.output().get_depth() << "\n";
        always_assert(false);
    }
    return print.output();
}

fmt::Formatter &ClangPrinter::printExpr(CoqPrinter &print,
                                        const clang::Expr *expr) {
    OpaqueNames names;
    return printExpr(print, expr, names);
}
