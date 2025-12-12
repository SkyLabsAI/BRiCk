#include "PrePrint.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "TypeVisitorWithArgs.h"
#include "clang/AST/StmtVisitor.h"
#include <Assert.hpp>

using namespace clang;

namespace {
struct PrePrint : TypeVisitor<PrePrint, bool>,
                  ConstStmtVisitor<PrePrint, void>,
                  ConstDeclVisitorArgs<PrePrint, void> {
    bool Visit(QualType qt) {
        if (qt.isNull())
            return false;
        Visit(qt.getTypePtr());
        return false;
    }

    // BEGIN TypeVisitor
    bool Visit(const Type *type) {
        if (not type)
            return false;
        if (not cache_.lookup(type))
            if (TypeVisitor<PrePrint, bool>::Visit(type)) {
                auto name = cache_.fresh(type);
                type_printer_(Cache::TYPE_PREFIX, name, type);
                cache_.store(type, name);
            }
        return false;
    }

    bool VisitType(const Type *type) {
#if 0
		llvm::errs() << type->getTypeClassName() << "\n";
#endif
        return false;
    }
    bool VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType *type) {
        Visit(type->getReplacementType());
        return false;
    }
    bool VisitElaboratedType(const ElaboratedType *type) {
        Visit(type->getNamedType());
        return false;
    }
    bool VisitTagType(const TagType *type) {
        VisitName(type->getDecl());
        return true;
    }
    bool VisitReferenceType(const ReferenceType *type) {
        Visit(type->getPointeeType());
        return true;
    }
    bool VisitPointerType(const PointerType *type) {
        Visit(type->getPointeeType());
        return true;
    }
    bool VisitArrayType(const ArrayType *type) {
        Visit(type->getElementType());
        return true;
    }
    bool VisitVariableArrayType(const VariableArrayType *type) {
        Visit(type->getSizeExpr());
        return false;
    }
    bool VisitDecayedType(const DecayedType *type) {
        Visit(type->getOriginalType());
        Visit(type->getAdjustedType());
        return false;
    }
    bool VisitFunctionType(const FunctionType *type) {
        Visit(type->getReturnType());
        return true;
    }
    bool VisitFunctionProtoType(const FunctionProtoType *type) {
        for (auto i : type->getParamTypes()) {
            Visit(i);
        }
        return VisitFunctionType(type);
    }
    // END TypeVisitor

    // BEGIN ExprVisitor
    void Visit(const Stmt *stmt) {
        if (not stmt)
            return;
        // I'm not going to cache statements
        if (auto e = dyn_cast<Expr>(stmt))
            Visit(e->getType());
        ConstStmtVisitor<PrePrint, void>::Visit(stmt);
    }

    void VisitDeclRefExpr(const DeclRefExpr *expr) {
        // Do not print references to local variables
        auto d = expr->getDecl();
        if (auto vd = dyn_cast<VarDecl>(d)) {
            if (!vd->getDeclContext()->isFunctionOrMethod() ||
                vd->isStaticLocal() || vd->isStaticDataMember())
                VisitName(d);
        } else {
            VisitName(d);
        }
    }
    void VisitBinaryOperator(const BinaryOperator *expr) {
        Visit(expr->getLHS());
        Visit(expr->getRHS());
    }
    void VisitUnaryOperator(const UnaryOperator *expr) {
        Visit(expr->getSubExpr());
    }
    void VisitCallExpr(const CallExpr *expr) {
        Visit(expr->getCallee());
        for (auto i : expr->arguments()) {
            Visit(i);
        }
    }
    void VisitCXXMemberCallExpr(const CXXMemberCallExpr *expr) {
        VisitName(expr->getMethodDecl());
        return VisitCallExpr(expr);
    }
    void VisitCXXConstructExpr(const CXXConstructExpr *expr) {
        VisitName(expr->getConstructor());
        for (auto i : expr->arguments())
            Visit(i);
    }
    void VisitCastExpr(const CastExpr *expr) {
        Visit(expr->getSubExpr());
        Visit(expr->getType());
    }
    void VisitCompoundStmt(const CompoundStmt *stmt) {
        for (auto i : stmt->body())
            Visit(i);
    }
    void VisitReturnStmt(const ReturnStmt *stmt) { Visit(stmt->getRetValue()); }
    void VisitFromDecl(const VarDecl *d) {
        if (d)
            Visit(d->getInit());
    }
    void VisitWhileStmt(const WhileStmt *stmt) {
        VisitFromDecl(stmt->getConditionVariable());
        Visit(stmt->getCond());
        Visit(stmt->getBody());
    }
    void VisitDoStmt(const DoStmt *stmt) {
        Visit(stmt->getBody());
        Visit(stmt->getCond());
    }
    void VisitForStmt(const ForStmt *stmt) {
        VisitFromDecl(stmt->getConditionVariable());
        Visit(stmt->getCond());
        Visit(stmt->getInc());
        Visit(stmt->getBody());
    }
    void VisitIfStmt(const IfStmt *stmt) {
        VisitFromDecl(stmt->getConditionVariable());
        Visit(stmt->getCond());
        Visit(stmt->getThen());
        Visit(stmt->getElse());
    }
    void VisitStmtExpr(const StmtExpr *stmt) {
        if (false) // the main logic does not support these statements anyways
            Visit(stmt->getSubStmt());
    }
    // END ExprVisitor

    // BEGIN DeclVisitor
    void Visit(const clang::Decl *decl) {
        if (not decl)
            return;
        ConstDeclVisitorArgs<PrePrint, void>::Visit(decl);
    }

    void VisitVarDecl(const VarDecl *decl) { Visit(decl->getType()); }
    void VisitFunctionDecl(const FunctionDecl *decl) {
        for (auto i : decl->parameters()) {
            Visit(i->getType());
        }
        Visit(decl->getReturnType());

        // visit the name after the argument types because the name will
        // reference the argument types
        VisitName(decl);

        if (decl->getBody())
            Visit(decl->getBody());
    }
    void VisitCXXConstructorDecl(const CXXConstructorDecl *decl) {
        for (auto i : decl->inits())
            Visit(i->getInit());
        VisitFunctionDecl(decl);
    }
    void VisitRecordDecl(const RecordDecl *decl) {
        VisitName(decl);
        for (auto i : decl->fields()) {
            Visit(i->getType());
        }
    }
    // END DeclVisitor

    // BEGIN NameVisitor
    void VisitName(const NamedDecl *decl) {
        if (not decl)
            return;
        if (decl == nullptr)
            return;
        if (not cache_.lookup(decl)) {
            auto name = cache_.fresh(decl);
            name_printer_(Cache::NAME_PREFIX, name, decl);
            cache_.store(decl, name);
        }
    }

#if 0
	void VisitPath(const DeclContext* ctx) {
		if (ctx->isTranslationUnit())
			return;
		if (ctx->getParent()) {
			VisitPath(ctx->getParent());
		}
		if (auto d = dyn_cast<Decl>(ctx))
			VisitName(d);
	}
#endif

    // END NameVisitor

private:
    Cache &cache_;
    const PRINTER<clang::Type> &type_printer_;
    const PRINTER<clang::NamedDecl> &name_printer_;

public:
    PrePrint(Cache &c, const PRINTER<clang::Type> &tprint,
             const PRINTER<clang::NamedDecl> &nprint)
        : cache_(c), type_printer_(tprint), name_printer_(nprint) {}
};
} // namespace

void prePrintDecl(const clang::Decl *decl, Cache &cache,
                  const PRINTER<clang::Type> &type_fn,
                  const PRINTER<clang::NamedDecl> &name_fn) {
    PrePrint{cache, type_fn, name_fn}.Visit(decl);
}
