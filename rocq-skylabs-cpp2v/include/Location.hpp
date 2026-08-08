/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include <clang/Basic/SourceLocation.h>
#include <optional>

namespace llvm {
class raw_ostream;
class StringRef;
} // namespace llvm

namespace clang {
class ASTContext;
class Decl;
class DeclContext;
class FunctionDecl;
class NamedDecl;
class QualType;
class Stmt;
class Type;
class TypeLoc;
class TypeSourceInfo;
class TemplateArgumentLoc;
class CXXRecordDecl;
class CXXBaseSpecifier;
} // namespace clang

// Low-level utilities shared by the structured name printer and
// locations. (In general, these cannot safely use locations.)
namespace structured {

// TODO: Drop this in favor of printing `?null`
void locfree_warn(const clang::Decl &, const clang::ASTContext &,
                  llvm::StringRef);

const clang::FunctionDecl *recoverFunction(const clang::Decl &decl);

/// A variant of NamedDecl::getNameForDiagnostic that adds template
/// parameters, function parameters, and function qualifiers.
llvm::raw_ostream &printNameForDiagnostics(llvm::raw_ostream &,
                                           const clang::NamedDecl &,
                                           const clang::ASTContext &);
} // namespace structured

namespace loc {

/*
Roughly, a sum of a few types that can be dumped
and have an optional location.
*/
class Loc final {
private:
    // Used to impose invariants
    template <typename T> struct box {
        const T *unbox;
        const T *operator->() const { return unbox; }
        const T &operator*() const { return *unbox; }
    };

    enum class Kind {
        Decl,
        Stmt,
        TypeLoc,
        QualType,
        Type,
        Tsi,
        Tal,
        Location,
    } kind;

    union {
        const clang::Decl *decl;
        const clang::Stmt *stmt;
        const box<clang::TypeLoc> typeloc;    // type is non-null
        const box<clang::TypeSourceInfo> tsi; // type is non-null
        const box<clang::QualType> qualtype;  // type is non-null
        const clang::Type *type;
        const clang::TemplateArgumentLoc *tal;
        const clang::SourceLocation::UIntTy location;
    } u;

    Loc(const box<clang::TypeLoc> &t) : kind{Kind::TypeLoc}, u{.typeloc = t} {}
    Loc(const box<clang::TypeSourceInfo> &t) : kind{Kind::Tsi}, u{.tsi = t} {}
    Loc(const box<clang::QualType> &t)
        : kind{Kind::QualType}, u{.qualtype = t} {}

public:
    Loc() = delete;
    Loc(const clang::Decl &d) : kind{Kind::Decl}, u{.decl = &d} {}
    Loc(const clang::Stmt &s) : kind{Kind::Stmt}, u{.stmt = &s} {}
    Loc(const clang::Type &t) : kind{Kind::Type}, u{.type = &t} {}
    Loc(const clang::TemplateArgumentLoc &a) : kind{Kind::Tal}, u{.tal = &a} {}
    Loc(const clang::SourceLocation l)
        : kind{Kind::Location}, u{.location = l.getRawEncoding()} {}

    static std::optional<Loc> mk(const clang::TypeLoc &);
    static std::optional<Loc> mk(const clang::TypeSourceInfo &);
    static std::optional<Loc> mk(const clang::QualType &);

    // Location (may be invalid)

    clang::SourceLocation getLoc() const;

    // Short description

    llvm::raw_ostream &describe(llvm::raw_ostream &,
                                const clang::ASTContext &) const;

    // Clang's AST dump

    llvm::raw_ostream &dump(llvm::raw_ostream &,
                            const clang::ASTContext &) const;
};

using loc = std::optional<Loc>;

// Introduction

inline constexpr loc none = std::nullopt;

// Use constructors when they can't go wrong
template <typename T> loc of(T &ref) { return {Loc{ref}}; }

// Use factory methods to check side-conditions
template <> inline loc of<>(const clang::TypeLoc &ref) { return Loc::mk(ref); }
template <> inline loc of<>(clang::TypeLoc &ref) { return Loc::mk(ref); }
template <> inline loc of<>(const clang::TypeSourceInfo &ref) {
    return Loc::mk(ref);
}
template <> inline loc of<>(clang::TypeSourceInfo &ref) { return Loc::mk(ref); }
template <> inline loc of<>(const clang::QualType &ref) { return Loc::mk(ref); }
template <> inline loc of<>(clang::QualType &ref) { return Loc::mk(ref); }

// Avoid an ambiguous constructor
template <> loc of<>(const clang::DeclContext &);
template <> loc of<>(clang::DeclContext &);

// Handle pointers
template <typename T> loc of(T *ptr) { return ptr ? of(*ptr) : none; }

/// `loc` if that's defined and has a location; otherwise `fallback`
loc refine(loc fallback, loc loc);

/// `loc::of(t)` if that's defined and has a location; otherwise,
/// `fallback`
template <typename T> loc refine(loc fallback, T *t) {
    return refine(fallback, of(t));
}

/// `loc::of(t)` if that's defined and has a location; otherwise,
/// `fallback`
template <typename T> loc refine(loc fallback, T &t) {
    return refine(fallback, of(t));
}

// Formatting

// Describe loc (e.g., "Var x"), if present.
inline bool can_describe(loc loc) { return loc.has_value(); }
struct Describe {
    loc location;
    const clang::ASTContext &context;
};
inline Describe describe(loc loc, const clang::ASTContext &context) {
    return {loc, context};
}
llvm::raw_ostream &operator<<(llvm::raw_ostream &, Describe);

// Dump loc (presumed under decl) or decl, if either is present.
struct Dump {
    loc location;
    const clang::ASTContext &context;
    const clang::Decl *decl;
};
inline Dump dump(loc loc, const clang::ASTContext &context,
                 const clang::Decl *decl = nullptr) {
    return {loc, context, decl};
}
llvm::raw_ostream &operator<<(llvm::raw_ostream &, Dump);

// Print diagnostic prefix "ADDR (DESCRIBE): " for loc, falling back to
// "RANGE: " for decl, falling back to "".
struct Prefix {
    loc location;
    const clang::ASTContext &context;
    const clang::Decl *decl;
};
inline Prefix prefix(loc loc, const clang::ASTContext &context,
                     const clang::Decl *decl = nullptr) {
    return {loc, context, decl};
}
llvm::raw_ostream &operator<<(llvm::raw_ostream &, Prefix);

// Print trace suffix "DESCRIBE at/in ADDR" for loc, falling back to "".
inline bool can_trace(loc loc, const clang::Decl *decl = nullptr) {
    return loc.has_value();
}
struct Trace {
    loc location;
    const clang::ASTContext &context;
    const clang::Decl *decl;
};
inline Trace trace(loc loc, const clang::ASTContext &context,
                   const clang::Decl *decl = nullptr) {
    return {loc, context, decl};
}
llvm::raw_ostream &operator<<(llvm::raw_ostream &, Trace);

} // namespace loc
