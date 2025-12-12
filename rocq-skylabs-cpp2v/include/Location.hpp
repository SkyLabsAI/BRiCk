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
using namespace llvm;
using namespace clang;

// TODO: Drop this in favor of printing `?null`
void locfree_warn(const Decl &, const ASTContext &, StringRef);

const FunctionDecl *recoverFunction(const Decl &decl);

/// A variant of NamedDecl::getNameForDiagnostic that adds template
/// parameters, function parameters, and function qualifiers.
raw_ostream &printNameForDiagnostics(raw_ostream &, const NamedDecl &,
                                     const ASTContext &);
} // namespace structured

namespace loc {

using namespace llvm;
using namespace clang;

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
        const Decl *decl;
        const Stmt *stmt;
        const box<TypeLoc> typeloc;    // type is non-null
        const box<TypeSourceInfo> tsi; // type is non-null
        const box<QualType> qualtype;  // type is non-null
        const clang::Type *type;
        const TemplateArgumentLoc *tal;
        const SourceLocation::UIntTy location;
    } u;

    Loc(const box<TypeLoc> &t) : kind{Kind::TypeLoc}, u{.typeloc = t} {}
    Loc(const box<TypeSourceInfo> &t) : kind{Kind::Tsi}, u{.tsi = t} {}
    Loc(const box<QualType> &t) : kind{Kind::QualType}, u{.qualtype = t} {}

public:
    Loc() = delete;
    Loc(const Decl &d) : kind{Kind::Decl}, u{.decl = &d} {}
    Loc(const Stmt &s) : kind{Kind::Stmt}, u{.stmt = &s} {}
    Loc(const clang::Type &t) : kind{Kind::Type}, u{.type = &t} {}
    Loc(const TemplateArgumentLoc &a) : kind{Kind::Tal}, u{.tal = &a} {}
    Loc(const SourceLocation l)
        : kind{Kind::Location}, u{.location = l.getRawEncoding()} {}

    static std::optional<Loc> mk(const TypeLoc &);
    static std::optional<Loc> mk(const TypeSourceInfo &);
    static std::optional<Loc> mk(const QualType &);

    // Location (may be invalid)

    SourceLocation getLoc() const;

    // Short description

    raw_ostream &describe(raw_ostream &, const ASTContext &) const;

    // Clang's AST dump

    raw_ostream &dump(raw_ostream &, const ASTContext &) const;
};

using loc = std::optional<Loc>;

// Introduction

inline constexpr loc none = std::nullopt;

// Use constructors when they can't go wrong
template <typename T> loc of(T &ref) { return {Loc{ref}}; }

// Use factory methods to check side-conditions
template <> inline loc of<>(const TypeLoc &ref) { return Loc::mk(ref); }
template <> inline loc of<>(TypeLoc &ref) { return Loc::mk(ref); }
template <> inline loc of<>(const TypeSourceInfo &ref) { return Loc::mk(ref); }
template <> inline loc of<>(TypeSourceInfo &ref) { return Loc::mk(ref); }
template <> inline loc of<>(const QualType &ref) { return Loc::mk(ref); }
template <> inline loc of<>(QualType &ref) { return Loc::mk(ref); }

// Avoid an ambiguous constructor
template <> loc of<>(const DeclContext &);
template <> loc of<>(DeclContext &);

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
    const ASTContext &context;
};
inline Describe describe(loc loc, const ASTContext &context) {
    return {loc, context};
}
raw_ostream &operator<<(raw_ostream &, Describe);

// Dump loc (presumed under decl) or decl, if either is present.
struct Dump {
    loc location;
    const ASTContext &context;
    const Decl *decl;
};
inline Dump dump(loc loc, const ASTContext &context,
                 const Decl *decl = nullptr) {
    return {loc, context, decl};
}
raw_ostream &operator<<(raw_ostream &, Dump);

// Print location in loc, falling back to address range of decl, falling
// back to nothing.
bool can_addr(loc loc, const Decl *decl = nullptr);
struct Addr {
    loc location;
    const ASTContext &context;
    const Decl *decl;
};
inline Addr addr(loc loc, const ASTContext &context,
                 const Decl *decl = nullptr) {
    return {loc, context, decl};
}
raw_ostream &operator<<(raw_ostream &, Addr);

// Print diagnostic prefix "ADDR (DESCRIBE): " for loc, falling back to
// "RANGE: " for decl, falling back to "".
struct Prefix {
    loc location;
    const ASTContext &context;
    const Decl *decl;
};
inline Prefix prefix(loc loc, const ASTContext &context,
                     const Decl *decl = nullptr) {
    return {loc, context, decl};
}
raw_ostream &operator<<(raw_ostream &, Prefix);

// Print trace suffix "DESCRIBE at/in ADDR" for loc, falling back to "".
inline bool can_trace(loc loc, const Decl *decl = nullptr) {
    return loc.has_value();
}
struct Trace {
    loc location;
    const ASTContext &context;
    const Decl *decl;
};
inline Trace trace(loc loc, const ASTContext &context,
                   const Decl *decl = nullptr) {
    return {loc, context, decl};
}
raw_ostream &operator<<(raw_ostream &, Trace);

} // namespace loc
