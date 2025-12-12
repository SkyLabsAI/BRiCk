/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Location.hpp"
#include "Assert.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/Basic/Version.h>

using namespace clang;

namespace structured {

void locfree_warn(const Decl &decl, const ASTContext &context, StringRef msg) {
    auto &os = logging::unsupported();
    auto src = decl.getBeginLoc();
    if (src.isValid()) {
        src.print(os, context.getSourceManager());
        os << ' ';
    }
    os << '(' << decl.getDeclKindName();
    if (isa<NamedDecl>(decl)) {
        os << ' ';
        cast<NamedDecl>(decl).getNameForDiagnostic(
            os, context.getPrintingPolicy(), true);
    }
    os << "): warning: " << msg << '\n';
    decl.dump(logging::debug());
}

} // namespace structured

namespace loc {

template <> loc of<>(const DeclContext &c) { return of(cast<Decl>(c)); }

template <> loc of<>(DeclContext &c) { return of(cast<Decl>(c)); }

loc refine(loc fallback, loc loc) {
    return loc && loc->getLoc().isValid() ? loc : fallback;
}

loc Loc::mk(const TypeLoc &t) {
    if (t.getType().getTypePtrOrNull()) {
        Loc::box<TypeLoc> box{&t};
        Loc loc{box};
        return {loc};
    } else
        return none;
}

loc Loc::mk(const TypeSourceInfo &t) {
    if (t.getType().getTypePtrOrNull()) {
        Loc::box<TypeSourceInfo> box{&t};
        Loc loc{box};
        return {loc};
    } else
        return none;
}

loc Loc::mk(const QualType &t) {
    if (t.getTypePtrOrNull()) {
        Loc::box<QualType> box{&t};
        Loc loc{box};
        return {loc};
    } else
        return none;
}

static constexpr SourceLocation invalid_loc;

static SourceLocation pointOfInstantiation(const Decl &decl) {
    if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(&decl))
        return ts->getPointOfInstantiation();
    if (auto fd = structured::recoverFunction(decl)) {
        // NOTE: A FunctionDecl's POI can point uselessly into the
        // template. The POIs FunctionDecl::getPointOfInstantiation and
        // FunctionDecl::getTemplateSpecializationInfo;
        // FunctionTemplateSpecialization::getPointOfInstantiation seem
        // to always agree (unsurprisingly), even when they're "off".
        return fd->getPointOfInstantiation();
    }
    if (auto ts = dyn_cast<VarTemplateSpecializationDecl>(&decl))
        return ts->getPointOfInstantiation();
    return invalid_loc;
}

static SourceLocation getDeclLoc(const Decl &decl) {
    // Prefer point of instantiation
    auto loc = pointOfInstantiation(decl);
    return loc.isValid() ? loc : decl.getBeginLoc();
}

SourceLocation Loc::getLoc() const {
    switch (kind) {
    case Kind::Decl:
        return getDeclLoc(*u.decl);
    case Kind::Stmt:
        return u.stmt->getBeginLoc();
    case Kind::TypeLoc:
        return u.typeloc->getBeginLoc();
    case Kind::Tsi:
        return u.tsi->getTypeLoc().getBeginLoc();
    case Kind::QualType:
    case Kind::Type:
        return invalid_loc;
    case Kind::Tal:
        return u.tal->getSourceRange().getBegin();
    case Kind::Location:
        return SourceLocation::getFromRawEncoding(u.location);
    default:
        always_assert(false && "Unknown location type");
    }
}

raw_ostream &Loc::describe(raw_ostream &os, const ASTContext &context) const {
    auto &policy = context.getPrintingPolicy();
    auto qualtype = [&](QualType qt) -> auto & {
        os << qt.getTypePtr()->getTypeClassName() << ' ';
        qt.print(os, policy);
        return os;
    };
    switch (kind) {
    case Kind::Decl: {
        auto decl = u.decl;
        os << decl->getDeclKindName();
        if (auto nd = dyn_cast<NamedDecl>(decl)) {
            os << ' ';
            structured::printNameForDiagnostics(os, *nd, context);
        }
        return os;
    }
    case Kind::Stmt:
        return os << u.stmt->getStmtClassName();
    case Kind::TypeLoc:
        return qualtype(u.typeloc->getType());
    case Kind::Tsi:
        return qualtype(u.tsi->getType());
    case Kind::QualType:
        return qualtype(*u.qualtype);
    case Kind::Type:
        return qualtype(context.getQualifiedType(u.type, Qualifiers()));
    case Kind::Tal:
        u.tal->getArgument().print(policy, os, true);
        return os;
    case Kind::Location:
        SourceLocation::getFromRawEncoding(u.location)
            .print(os, context.getSourceManager());
        return os;
    default:
        always_assert(false);
    }
}

raw_ostream &Loc::dump(raw_ostream &os, const ASTContext &context) const {
    auto qualtype = [&](QualType qt) -> auto & {
        qt.dump(os, context);
        return os;
    };
    switch (kind) {
    case Kind::Decl:
        u.decl->dump(os);
        return os;
    case Kind::Stmt:
        u.stmt->dump(os, context);
        return os;
    case Kind::TypeLoc:
        return qualtype(u.typeloc->getType());
    case Kind::Tsi:
        return qualtype(u.tsi->getType());
    case Kind::QualType:
        return qualtype(*u.qualtype);
    case Kind::Type:
        u.type->dump(os, context);
        return os;
    case Kind::Tal:
#if 19 <= CLANG_VERSION_MAJOR
        u.tal->getArgument().dump(os, context);
#else
        u.tal->getArgument().dump(os);
#endif
        return os;
    case Kind::Location:
        SourceLocation::getFromRawEncoding(u.location)
            .print(os, context.getSourceManager());
        return os;
    default:
        always_assert(false);
    }
}

raw_ostream &operator<<(raw_ostream &os, Describe d) {
    auto &[loc, context] = d;
    return loc ? loc->describe(os, context) : os;
}

raw_ostream &operator<<(raw_ostream &os, Dump d) {
    auto [loc, context, decl] = d;
    if (loc)
        loc->dump(os, context);
    if (loc && decl)
        os << "\tinside\n";
    if (decl)
        decl->dump(os);
    if (loc || decl)
        os << "\n"; // visually separate unrelated dumps
    return os;
}

bool can_addr(loc loc, const Decl *decl) {
    return (loc.has_value() && loc->getLoc().isValid()) || decl;
}

raw_ostream &operator<<(raw_ostream &os, Addr s) {
    auto &[loc, context, decl] = s;
    auto &SM = context.getSourceManager();
    if (loc) {
        auto src = loc->getLoc();
        if (src.isValid()) {
            src.print(os, SM);
            return os;
        }
    }
    if (decl)
        decl->getSourceRange().print(os, SM);
    return os;
}

raw_ostream &operator<<(raw_ostream &os, Prefix p) {
    auto &[loc, context, decl] = p;
    auto &SM = context.getSourceManager();
    if (loc) {
        auto src = loc->getLoc();
        if (src.isValid()) {
            src.print(os, SM);
            os << " ";
        } else if (decl) {
            decl->getSourceRange().print(os, SM);
            os << " ";
        }
        os << "(";
        return loc->describe(os, context) << "): ";
    } else if (decl) {
        decl->getSourceRange().print(os, SM);
        return os << ": ";
    } else
        return os;
}

raw_ostream &operator<<(raw_ostream &os, Trace t) {
    auto &[loc, context, decl] = t;
    if (loc) {
        auto &SM = context.getSourceManager();
        loc->describe(os, context);
        auto src = loc->getLoc();
        if (src.isValid()) {
            os << " at ";
            src.print(os, SM);
        } else if (decl) {
            os << " in ";
            decl->getSourceRange().print(os, SM);
        }
    }
    return os;
}
} // namespace loc
