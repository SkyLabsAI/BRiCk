// Direct tests for defensive printer paths that valid C++ cannot select.
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/Expr.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/raw_ostream.h>

int main() {
    auto ast = clang::tooling::buildASTFromCodeWithArgs(R"(
        template<class T> struct WrongKind {};
        template<class T> void specialized() {}
        template void specialized<int>();
    )", {"-std=c++17"});
    if (!ast)
        return 1;
    auto &context = ast->getASTContext();
    clang::CompilerInstance compiler;
    compiler.createDiagnostics();
    ClangPrinter printer(&compiler, &context, Trace::NONE, false);
    Cache cache;
    fmt::Formatter output(llvm::outs());
    CoqPrinter print(output, true, cache);
    output << "Require skylabs.lang.cpp.mparser.\n"
              "Import skylabs.lang.cpp.mparser.\n"
              "#[local] Open Scope pstring_scope.\n";

    clang::OpaqueValueExpr prvalue({}, context.IntTy, clang::VK_PRValue);
    clang::OpaqueValueExpr lvalue({}, context.IntTy, clang::VK_LValue);
    clang::OpaqueValueExpr xvalue({}, context.IntTy, clang::VK_XValue);
    auto emit = [&](const char *name, ClangPrinter &p,
                    const clang::Expr *expr) {
        output << "Definition " << name << " : MExpr := ";
        p.printTemplateValueParamRef(print, 0, 0, expr, loc::of(expr));
        output << ".\n";
    };
    emit("unresolved_prvalue", printer, &prvalue);
    emit("unresolved_lvalue", printer, &lvalue);
    emit("unresolved_xvalue", printer, &xvalue);
    for (auto *decl : context.getTranslationUnitDecl()->decls()) {
        if (auto *templ = clang::dyn_cast<clang::ClassTemplateDecl>(decl)) {
            auto scoped = printer.withDecl(templ->getTemplatedDecl());
            emit("wrong_kind", scoped, &prvalue);
        }
        if (auto *templ = clang::dyn_cast<clang::FunctionTemplateDecl>(decl)) {
            for (auto *specialization : templ->specializations()) {
                auto scoped = printer.withDecl(specialization);
                // A type argument is deliberately queried as a value argument.
                emit("unsupported_argument", scoped, &prvalue);
            }
        }
    }
    output.flush();
}
