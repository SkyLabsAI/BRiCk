/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "Location.hpp"
#include "Logging.hpp"
#include "Trace.hpp"
#include <clang/Basic/Diagnostic.h>
#include <clang/Basic/Version.inc>
#include <llvm/ADT/ArrayRef.h>

namespace clang {
class Decl;
class Stmt;
class Expr;
class NamedDecl;
class QualType;
class FunctionDecl;
enum OverloadedOperatorKind : int;
class TranslationUnitDecl;
class ParmVarDecl;
class Type;
class BuiltinType;
class DecltypeType;
class ASTContext;
class MangleContext;
class ValueDecl;
class SourceRange;
class CompilerInstance;
class Sema;
class TypeDecl;
class FieldDecl;
class RecordDecl;
class DeclContext;
class TemplateDecl;
class TemplateTypeParmDecl;
class TemplateParameterList;
class TemplateArgument;
class TemplateArgumentLoc;
class TemplateArgumentList;
class NestedNameSpecifier;
class DeclarationName;
class IdentifierInfo;
class Qualifiers;
} // namespace clang

namespace fmt {
class Formatter;
}

// TODO: The following are misplaced
/*
A reference to a `T` that is less error-prone than `T&`.

Example: To safely call a function `const DeclContext& f()`, one must
wite `auto& ctx = f();` rather than `auto ctx = f();`. The latter
results in a declaration context `ctx` which _does not_ satisfy clang's
invariants and readily leads to segmentation violations and other bad
symptoms. Returning `ref<const DeclContext>` avoids this foot gun.
*/
template <typename T> class ref final {
private:
    T &ref_;
    ref() = delete;

public:
    explicit ref(T &r) : ref_{r} {}

    operator T &() const { return ref_; }

    using type = typename std::remove_reference<T>::type;
    type *operator->() const { return &ref_; }
};
template <typename T> explicit ref(T &) -> ref<T>;

/*
C++23 permits attributes in a closure to decorate its operator().
To avoid a compiler warning, we instead use gcc's attribute syntax.
Attribution: https://stackoverflow.com/a/70991613
*/
#define NORETURN __attribute__((__noreturn__))
#define NODISCARD __attribute__((__warn_unused_result__))

class CoqPrinter;
struct OpaqueNames;

bool is_dependent(const clang::Expr *);

class ClangPrinter {
private:
    const clang::CompilerInstance *compiler_;
    clang::ASTContext *context_;
    clang::MangleContext *mangleContext_;
    const Trace::Mask trace_;
    const clang::Decl *decl_{nullptr};
    const bool comment_{false};
    const bool typedefs_;

    ClangPrinter(const ClangPrinter &from, const clang::Decl *decl)
        : compiler_(from.compiler_), context_(from.context_),
          mangleContext_(from.mangleContext_), trace_(from.trace_), decl_{decl},
          comment_{from.comment_}, typedefs_{from.typedefs_} {}

public:
    // Silence some warnings until we can improve our diagnostics
    static inline constexpr bool warn_well_known = false;

    // Make `--trace` output more verbose
    static inline constexpr bool debug = false;

    ClangPrinter(clang::CompilerInstance *compiler, clang::ASTContext *context,
                 Trace::Mask trace, bool comment, bool typdefs = false);

    /*
      This declaration provides context for resolving template
      argument names and for diagnostics (e.g., an approximate
      source location for type-related warnings).
      */
    ClangPrinter withDecl(const clang::Decl *decl) const;

#if CLANG_VERSION_MAJOR >= 22
    using NestedNameSpecifierArg = clang::NestedNameSpecifier;
#else
    using NestedNameSpecifierArg = const clang::NestedNameSpecifier *;
#endif

private:
    const clang::Decl *getDecl() const;

    fmt::Formatter &printNestedName(CoqPrinter &, NestedNameSpecifierArg,
                                    loc::loc);

public:
    clang::ASTContext &getContext() { return *context_; }

    const clang::CompilerInstance &getCompiler() { return *compiler_; }

    clang::MangleContext &getMangleContext() { return *mangleContext_; }

    bool printTypedefs() const { return typedefs_; }

    std::optional<std::pair<const clang::CXXRecordDecl *, clang::Qualifiers>>
    getLambdaClass() const;

    // Helpers for diagnostics
    llvm::raw_ostream &debug_dump(loc::loc);
    llvm::raw_ostream &error_prefix(llvm::raw_ostream &, loc::loc);

    std::string sourceLocation(const clang::SourceLocation) const;
    std::string sourceRange(const clang::SourceRange sr) const;

    // Helpers for `--trace`
    bool trace(Trace::Mask m) const { return trace_ & m; }
    llvm::raw_ostream &trace(llvm::StringRef whence, loc::loc);

    // Operators

    fmt::Formatter &printOverloadableOperator(CoqPrinter &,
                                              clang::OverloadedOperatorKind,
                                              loc::loc);

    // Names

    fmt::Formatter &printNameComment(CoqPrinter &, const clang::Decl &);

    // TODO: eliminate [printNameAsKey]
    fmt::Formatter &printNameAsKey(CoqPrinter &, const clang::Decl &); // : bs
    fmt::Formatter &printNameAsKey(CoqPrinter &, const clang::Decl *, loc::loc);

    fmt::Formatter &printName(CoqPrinter &, const clang::Decl &,
                              bool full = true); // name
    fmt::Formatter &printName(CoqPrinter &, const clang::Decl *, loc::loc,
                              bool full = true);
    fmt::Formatter &printUnresolvedName(
        CoqPrinter &, NestedNameSpecifierArg /* optional */,
        const clang::DeclarationName &,
        llvm::ArrayRef<clang::TemplateArgumentLoc> /* optional */, loc::loc);
    fmt::Formatter &
    printUnresolvedName(CoqPrinter &, NestedNameSpecifierArg /* optional */,
                        const clang::DeclarationName &,
                        llvm::ArrayRef<clang::TemplateArgument> /* optional */,
                        loc::loc);

    fmt::Formatter &printUnresolvedName(CoqPrinter &,
                                        NestedNameSpecifierArg /* optional */,
                                        const clang::DeclarationName &,
                                        loc::loc);

    // TODO: Can we drop these?
    fmt::Formatter &printUnsupportedName(CoqPrinter &, llvm::StringRef); // name

    fmt::Formatter &printDtorName(CoqPrinter &,
                                  const clang::CXXRecordDecl &); // name

    fmt::Formatter &printUnqualifiedName(CoqPrinter &,
                                         const clang::NamedDecl &); // : ident
    fmt::Formatter &printUnqualifiedName(CoqPrinter &, const clang::NamedDecl *,
                                         loc::loc);

    fmt::Formatter &printFieldName(CoqPrinter &, const clang::FieldDecl &,
                                   loc::loc);

    // Print one Rocq [temp_param].
    fmt::Formatter &printTemplateParam(CoqPrinter &, const clang::NamedDecl *,
                                       loc::loc);

    // Print a Rocq [list (temp_param * option temp_arg)].
    fmt::Formatter &printTemplateParams(CoqPrinter &,
                                        llvm::ArrayRef<clang::NamedDecl *>,
                                        loc::loc);

    // Print all template parameters in scope for a declaration as a Rocq
    // [list (temp_param * option temp_arg)]. For example, with
    // ```
    // template<typename T> struct s {
    //   template<typename U> void f(T, U);
    // };
    // ```
    // emits roughly `<T>` for `s` and `<T,U>` for `s::f`.
    fmt::Formatter &printTemplateParamsForDecl(CoqPrinter &,
                                               const clang::Decl &);

    // Print one Rocq [temp_arg].
    fmt::Formatter &printTemplateArg(CoqPrinter &,
                                     const clang::TemplateArgument &, loc::loc);
    fmt::Formatter &printTemplateArg(CoqPrinter &, const clang::NamedDecl *,
                                     loc::loc);

    // Print a Rocq [list temp_arg].
    fmt::Formatter &printTemplateArgList(CoqPrinter &,
                                         const clang::TemplateArgumentList &,
                                         loc::loc);
    fmt::Formatter &printTemplateArgs(CoqPrinter &,
                                      llvm::ArrayRef<clang::TemplateArgument>);
    fmt::Formatter &
    printTemplateArgs(CoqPrinter &, llvm::ArrayRef<clang::TemplateArgumentLoc>);

    // Print all template arguments in scope for a declaration as a Rocq
    // [list temp_arg].
    fmt::Formatter &printTemplateArgsForDecl(CoqPrinter &, const clang::Decl &);

    // Print template parameter references in the Rocq sort required by their
    // use site.
    fmt::Formatter &
    printTemplateTypeParamRef(CoqPrinter &, const clang::TemplateTypeParmDecl *,
                              loc::loc);
    fmt::Formatter &printTemplateTypeParamRef(CoqPrinter &, unsigned depth,
                                              unsigned index, loc::loc);
    fmt::Formatter &printTemplateValueParamRef(CoqPrinter &, unsigned depth,
                                               unsigned index, loc::loc);

    // Types

    fmt::Formatter &printQualType(CoqPrinter &print, const clang::QualType &qt,
                                  loc::loc loc);
    fmt::Formatter &printQualTypeOption(CoqPrinter &print,
                                        const clang::QualType &qt,
                                        loc::loc loc);
    // TODO: Deprecate
    fmt::Formatter &printType(CoqPrinter &print, const clang::Type &type,
                              loc::loc loc);
    fmt::Formatter &printType(CoqPrinter &print, const clang::Type *t,
                              loc::loc loc);

    fmt::Formatter &printQualifier(CoqPrinter &, bool is_const,
                                   bool is_volatile) const;
    fmt::Formatter &printQualifier(CoqPrinter &,
                                   const clang::QualType &qt) const;

    fmt::Formatter &printValCat(CoqPrinter &, const clang::Expr *d);

    fmt::Formatter &printCallingConv(CoqPrinter &, clang::CallingConv,
                                     loc::loc);

    fmt::Formatter &printVariadic(CoqPrinter &, bool) const;

    fmt::Formatter &printExceptionSpec(CoqPrinter &,
                                       const clang::FunctionDecl &);

    unsigned getTypeSize(const clang::BuiltinType *type) const;

    // Expressions

    fmt::Formatter &printExpr(CoqPrinter &, const clang::Expr *d,
                              OpaqueNames &li);
    fmt::Formatter &printExpr(CoqPrinter &, const clang::Expr *d);

    fmt::Formatter &printValueDeclExpr(CoqPrinter &, const clang::ValueDecl *,
                                       OpaqueNames &);
    fmt::Formatter &printValueDeclExpr(CoqPrinter &, const clang::ValueDecl *);

    // TODO: Discuss. Rename to printFunctionParamName.
    fmt::Formatter &printParamName(CoqPrinter &, const clang::ParmVarDecl *d);

    // Statements

    fmt::Formatter &printStmt(CoqPrinter &, const clang::Stmt *s);

    // true if printed
    bool printLocalDecl(CoqPrinter &, const clang::Decl *d);

    // Notation

    fmt::Formatter &printField(CoqPrinter &, const clang::ValueDecl *);
};
