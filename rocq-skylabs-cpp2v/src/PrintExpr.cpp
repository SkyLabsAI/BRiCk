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
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DependenceFlags.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/Version.inc"
#include "llvm/ADT/APFloat.h"
#include "llvm/Support/Base64.h"
#include "llvm/Support/ConvertUTF.h"
#include <clang/AST/OperationKinds.h>
#include <optional>

using namespace clang;
using namespace fmt;

// Printing of string literals as [literal_string.t] values.
//
// Long literals must not be printed as one term per character: Rocq needs
// stack and time proportional to the nesting depth of such terms. We print
// either a single primitive string, <<literal_string.Build_t "..." bpc>>,
// or <<literal_string.decode bpc (seg :: ... :: nil)>>, a short list of
// segments that Rocq decodes and concatenates (see [literal_string.segment] in
// rocq-skylabs-brick). Primitive array syntax would allow longer lists, but
// Rocq cannot parse it while list notations are imported.
//
// The printed term always equals <<literal_string.of_list_N chars>>; in
// particular, [bpc] is computed exactly as [literal_string.bpc_of_list_N].
namespace string_literal {
// [Pstring.max_length_int] in the Rocq kernel.
constexpr uint64_t max_bytes = 16777211;
// Bytes per base64 segment; its encoding (1 MiB) stays below [max_bytes].
constexpr size_t base64_chunk_bytes = 3 << 18;
// Runs of at least [merge_run] consecutive segments, each shorter than
// [short_segment] characters, are encoded as a single base64 segment.
constexpr size_t short_segment = 8;
constexpr size_t merge_run = 8;
// The most segments printed; the list nests this deep. Literals that would
// need more are printed as base64 only.
constexpr size_t max_segments = 256;
// The printable ASCII range that shifted segments are mapped to.
constexpr uint32_t shift_lo = 0x20, shift_hi = 0x7e;

/// The fewest bytes that can hold every character, and at least 1.
/// Mirrors [literal_string.bpc_of_list_N].
static unsigned bytes_per_char(llvm::ArrayRef<uint32_t> chars) {
    uint32_t max = 1;
    for (auto c : chars)
        max = std::max(max, c);
    unsigned bits = 0;
    for (; max != 0; max >>= 1)
        ++bits;
    return (bits + 7) / 8;
}

enum class Kind { Verbatim, Shifted, Base64 };

struct Segment {
    Kind kind;
    size_t begin, end; // character range [begin, end)
    uint32_t lo = 0, hi = 0; // character range of a shifted segment
};

/// Characters printed as is in any literal: printable ASCII, tab and newline.
static bool plain(uint32_t c) {
    return (0x20 <= c && c <= 0x7e) || c == '\t' || c == '\n';
}

/// Number of characters, starting at [i], that form one valid UTF-8 sequence
/// of a printable, non-ASCII code point, or 0. Only for [bpc = 1].
static size_t utf8_sequence(llvm::ArrayRef<uint32_t> chars, size_t i) {
    if (chars[i] < 0x80)
        return 0;
    auto n = llvm::getNumBytesForUTF8(static_cast<llvm::UTF8>(chars[i]));
    if (n < 2 || n > 4 || i + n > chars.size())
        return 0;
    llvm::UTF8 seq[4];
    for (unsigned j = 0; j < n; ++j)
        seq[j] = static_cast<llvm::UTF8>(chars[i + j]);
    if (!llvm::isLegalUTF8Sequence(seq, seq + n))
        return 0;
    // Exclude C1 control characters (U+0080 to U+009F).
    if (seq[0] == 0xc2 && seq[1] < 0xa0)
        return 0;
    return n;
}

static std::vector<Segment> segments(llvm::ArrayRef<uint32_t> chars,
                                     unsigned bpc) {
    std::vector<Segment> segs;
    auto add = [&](Kind kind, size_t begin, size_t end) {
        if (!segs.empty() && segs.back().kind == kind &&
            segs.back().end == begin && kind != Kind::Shifted) {
            segs.back().end = end;
        } else {
            segs.push_back(Segment{kind, begin, end});
        }
    };
    for (size_t i = 0; i < chars.size();) {
        const uint32_t c = chars[i];
        if (plain(c)) {
            add(Kind::Verbatim, i, i + 1);
            ++i;
        } else if (size_t n = bpc == 1 ? utf8_sequence(chars, i) : 0) {
            add(Kind::Verbatim, i, i + n);
            i += n;
        } else if (c < 0x100) {
            // Extend the shifted run while it fits the printable range.
            if (!segs.empty() && segs.back().kind == Kind::Shifted &&
                segs.back().end == i) {
                auto &last = segs.back();
                const uint32_t lo = std::min(last.lo, c);
                const uint32_t hi = std::max(last.hi, c);
                if (hi - lo <= shift_hi - shift_lo) {
                    last.lo = lo;
                    last.hi = hi;
                    last.end = i + 1;
                    ++i;
                    continue;
                }
            }
            segs.push_back(Segment{Kind::Shifted, i, i + 1, c, c});
            ++i;
        } else {
            add(Kind::Base64, i, i + 1);
            ++i;
        }
    }

    // Replace long runs of short segments (e.g. binary data) by base64.
    std::vector<Segment> merged;
    for (size_t i = 0; i < segs.size();) {
        size_t j = i;
        while (j < segs.size() && segs[j].end - segs[j].begin < short_segment)
            ++j;
        if (j - i >= merge_run) {
            Segment seg{Kind::Base64, segs[i].begin, segs[j - 1].end};
            if (!merged.empty() && merged.back().kind == Kind::Base64)
                merged.back().end = seg.end;
            else
                merged.push_back(seg);
            i = j;
        } else {
            auto push = [&](const Segment &seg) {
                if (seg.kind == Kind::Base64 && !merged.empty() &&
                    merged.back().kind == Kind::Base64 &&
                    merged.back().end == seg.begin)
                    merged.back().end = seg.end;
                else
                    merged.push_back(seg);
            };
            for (; i < j; ++i)
                push(segs[i]);
            if (i < segs.size())
                push(segs[i++]);
        }
    }

    // Bound the number of segments regardless of the input. (Base64 chunks
    // of at most [max_bytes] bytes number at most 22.)
    if (merged.size() > max_segments)
        merged = {Segment{Kind::Base64, 0, chars.size()}};

    // Keep each base64 string below Rocq's string length limit.
    std::vector<Segment> result;
    const size_t chunk = std::max<size_t>(1, base64_chunk_bytes / bpc);
    for (auto &seg : merged) {
        if (seg.kind != Kind::Base64) {
            result.push_back(seg);
            continue;
        }
        for (size_t b = seg.begin; b < seg.end; b += chunk)
            result.push_back(
                Segment{Kind::Base64, b, std::min(seg.end, b + chunk)});
    }
    return result;
}

static void print_segment(CoqPrinter &print, llvm::ArrayRef<uint32_t> chars,
                          unsigned bpc, const Segment &seg) {
    std::string bytes;
    switch (seg.kind) {
    case Kind::Verbatim:
        for (size_t i = seg.begin; i < seg.end; ++i)
            bytes.push_back(static_cast<char>(chars[i]));
        print.output() << "(literal_string.Verbatim" << fmt::nbsp;
        break;
    case Kind::Shifted: {
        const uint32_t k = (shift_lo - seg.lo) & 0xff;
        for (size_t i = seg.begin; i < seg.end; ++i)
            bytes.push_back(static_cast<char>((chars[i] + k) & 0xff));
        print.output() << "(literal_string.Shifted " << k << "%N"
                       << fmt::nbsp;
        break;
    }
    case Kind::Base64: {
        std::string raw;
        for (size_t i = seg.begin; i < seg.end; ++i)
            for (unsigned j = bpc; j-- > 0;)
                raw.push_back(static_cast<char>((chars[i] >> (8 * j)) & 0xff));
        bytes = llvm::encodeBase64(raw);
        print.output() << "(literal_string.Base64" << fmt::nbsp;
        break;
    }
    }
    print.str(bytes) << ")";
}

/// Print [chars] as a [literal_string.t] with [bpc] bytes per character.
static void print(CoqPrinter &print, llvm::ArrayRef<uint32_t> chars,
                  unsigned bpc) {
    auto segs = segments(chars, bpc);
    if (bpc == 1 &&
        (segs.empty() || (segs.size() == 1 && segs[0].kind == Kind::Verbatim))) {
        std::string bytes(chars.begin(), chars.end());
        print.output() << "(literal_string.Build_t" << fmt::nbsp;
        print.str(bytes) << " 1%N)";
        return;
    }
    print.output() << "(literal_string.decode " << bpc << "%N" << fmt::nbsp;
    print.begin_list();
    for (auto &seg : segs) {
        print_segment(print, chars, bpc, seg);
        print.cons();
    }
    print.end_list() << ")";
}
} // namespace string_literal

enum Done : unsigned {
    NONE = 0,
    T = 1,
    O = 2,
    DT = 4,
};

static const char *apFloatSemanticsName(llvm::APFloatBase::Semantics sem) {
    switch (sem) {
    case llvm::APFloatBase::S_IEEEhalf:
        return "IEEEhalf";
    case llvm::APFloatBase::S_BFloat:
        return "BFloat";
    case llvm::APFloatBase::S_IEEEsingle:
        return "IEEEsingle";
    case llvm::APFloatBase::S_IEEEdouble:
        return "IEEEdouble";
    case llvm::APFloatBase::S_IEEEquad:
        return "IEEEquad";
    case llvm::APFloatBase::S_PPCDoubleDouble:
        return "PPCDoubleDouble";
    case llvm::APFloatBase::S_x87DoubleExtended:
        return "x87DoubleExtended";
    default:
        return "unknown";
    }
}

static const char *builtinTypeKindName(const BuiltinType *bt) {
    if (!bt)
        return "non-builtin";
    switch (bt->getKind()) {
    case BuiltinType::Float16:
        return "Float16";
    case BuiltinType::Float:
        return "Float";
    case BuiltinType::Double:
        return "Double";
    case BuiltinType::LongDouble:
        return "LongDouble";
    case BuiltinType::Float128:
        return "Float128";
    default:
        return "other-builtin";
    }
}

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
    print.option(expr,
                 [&](const Expr *expr) { cprint.printExpr(print, expr, li); });
}

bool is_dependent(const Expr *expr) {
    return static_cast<bool>(expr->getDependence() &
                             ExprDependence::TypeValueInstantiation);
}

/**
 * Determine if the value is a member of a class
 */
bool is_class_member(ValueDecl *decl) {
    if (auto field = dyn_cast<FieldDecl>(decl)) {
        return field->isCXXInstanceMember();
    } else if (auto meth = dyn_cast<CXXMethodDecl>(decl)) {
        return not meth->isStatic();
    }
    return false;
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
    } else if (isa<TemplateParamObjectDecl>(decl)) {
        // ponytail: the object is not emitted. Its symbol (e.g.
        // <<_ZTAXtl1PLi3EEE>>) keeps <<f<P{3}>>> and <<f<P{4}>>> apart.
        std::string symbol;
        llvm::raw_string_ostream os{symbol};
        getMangleContext().mangleName(GlobalDecl(decl), os);
        print.ctor("Eunsupported", false);
        print.str(symbol);
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

// Whether the class conversion [ce] takes a step to a virtual base.
//
// Clang's path for such a conversion starts at the last virtual step and
// skips the classes before it, so the path does not say where the virtual
// base is. A path whose steps all go to non-virtual bases is complete, and
// each step has a static offset, also out of a class with virtual bases
// (whose non-virtual bases are in [vs_struct] of its [Dvstruct]).
// A base-to-derived conversion never takes a virtual step: the base may not be
// a virtual base, nor a base of one (https://eel.is/c++draft/expr.static.cast).
static bool castTakesVirtualStep(const CastExpr &ce) {
    switch (ce.getCastKind()) {
    case CastKind::CK_DerivedToBase:
    case CastKind::CK_UncheckedDerivedToBase:
    case CastKind::CK_BaseToDerived:
        return llvm::any_of(ce.path(), [](const CXXBaseSpecifier *b) {
            return b->isVirtual();
        });
    default:
        return false;
    }
}

fmt::Formatter &ClangPrinter::printDeclType(CoqPrinter &print,
                                          const Expr *expr) {
    auto ty = expr->getType();
    if (ty.isNull())
        return print.output() << "Tauto";
    if (expr->isLValue()) {
        guard::ctor _(print, "Tref", false);
        printQualType(print, ty, loc::of(expr));
    } else if (expr->isXValue()) {
        guard::ctor _(print, "Trv_ref", false);
        printQualType(print, ty, loc::of(expr));
    } else {
        printValueQualType(print, ty, loc::of(expr));
    }
    return print.output();
}

fmt::Formatter &ClangPrinter::printExprAt(CoqPrinter &print, const Expr *e,
                                          const QualType &dest,
                                          OpaqueNames &names) {
    auto &ctxt = getContext();
    bool convert = false;
    if (e && !dest.isNull() && !e->isTypeDependent() &&
        !dest->isDependentType() && !e->getType().isNull()) {
        if (auto rt = dest->getAs<ReferenceType>()) {
            auto obj = rt->getPointeeType();
            convert = e->isGLValue() &&
                      ctxt.hasSameUnqualifiedType(e->getType(), obj) &&
                      realignedDiffer(ctxt, e->getType(), obj, false);
        } else {
            convert = e->isPRValue() &&
                      ctxt.hasSameUnqualifiedType(e->getType(), dest) &&
                      realignedDiffer(ctxt, e->getType(), dest, true);
        }
    }
    if (!convert)
        return printExpr(print, e, names);
    guard::ctor _(print, "Ecast");
    print.ctor("Cnoop", false);
    if (auto rt = dest->getAs<ReferenceType>()) {
        guard::ctor _r(print, e->isXValue() ? "Trv_ref" : "Tref", false);
        printQualType(print, rt->getPointeeType(), loc::of(e));
    } else
        printValueQualType(print, dest, loc::of(e));
    print.end_ctor() << fmt::nbsp;
    return printExpr(print, e, names);
}

fmt::Formatter &ClangPrinter::printExprAt(CoqPrinter &print, const Expr *e,
                                          const QualType &dest) {
    OpaqueNames names;
    return printExprAt(print, e, dest, names);
}

/**
 * This class prints an expression (of Coq type [Expr] or [MExpr])
 */
class PrintExpr : public ConstStmtVisitor<PrintExpr, void> {
private:
    CoqPrinter &print;
    ClangPrinter &cprint;
    const ASTContext &ctxt;
    OpaqueNames &names;

    fmt::Formatter &done(const Expr *expr, Done want = Done::T) {
        if (want == Done::DT) {
            cprint.printDeclType(print, expr);
        } else {
            if (want & Done::T) {
                if (expr->getType().isNull())
                    return print.output() << "Tauto";
                print.output() << fmt::nbsp;
                if (cprint.realignedInit == expr)
                    cprint.printRealignedQualType(print, expr->getType(),
                                                  cprint.realignedInitAlign,
                                                  loc::of(expr));
                else if (expr->isPRValue())
                    cprint.printValueQualType(print, expr->getType(),
                                              loc::of(expr));
                else
                    cprint.printQualType(print, expr->getType(),
                                         loc::of(expr));
            }
            if (want & Done::O) {
                print.output() << fmt::nbsp;
                cprint.printQualTypeOption(print, expr->getType(),
                                           loc::of(expr));
            }
        }
        return print.end_ctor();
    }

    // An initializer under the wrappers that print as their subexpression.
    static const Expr *initCore(const Expr *e) {
        for (;;) {
            if (auto d = dyn_cast<CXXDefaultInitExpr>(e))
                e = d->getExpr();
            else if (auto c = dyn_cast<ConstantExpr>(e))
                e = c->getSubExpr();
            else
                return e;
        }
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

    /// Whether `decl` is a weak symbol (`weak`, `weakref` or `weak_import`)
    /// that this translation unit does not define. The linker resolves an
    /// undefined weak symbol to address 0 when no other object defines it,
    /// while BRiCk's `global_ptr_nonnull` makes every global's address
    /// non-null. A weak symbol defined here has a non-null address.
    static bool isUndefinedWeak(const ValueDecl *decl) {
        if (!decl)
            return false;
        auto weak = [](const Decl *d) {
            return d->hasAttr<WeakAttr>() || d->hasAttr<WeakRefAttr>() ||
                   d->isWeakImported();
        };
        if (auto vd = dyn_cast<VarDecl>(decl)) {
            if (!vd->hasGlobalStorage() || vd->isStaticLocal())
                return false;
            return llvm::any_of(vd->redecls(), weak) &&
                   (vd->hasAttr<WeakRefAttr>() ||
                    vd->hasDefinition() == VarDecl::DeclarationOnly);
        }
        if (auto fd = dyn_cast<FunctionDecl>(decl))
            return llvm::any_of(fd->redecls(), weak) &&
                   (fd->hasAttr<WeakRefAttr>() || !fd->isDefined());
        return false;
    }

    /// Whether `expr` names an undefined weak symbol: a variable, function or
    /// static member, a method, or a constructor.
    static bool refersToUndefinedWeak(const Expr &expr) {
        if (auto dre = dyn_cast<DeclRefExpr>(&expr))
            return isUndefinedWeak(dre->getDecl());
        if (auto me = dyn_cast<MemberExpr>(&expr))
            return isUndefinedWeak(me->getMemberDecl());
        if (auto ce = dyn_cast<CXXConstructExpr>(&expr))
            return isUndefinedWeak(ce->getConstructor());
        if (auto mc = dyn_cast<CXXMemberCallExpr>(&expr))
            return isUndefinedWeak(mc->getMethodDecl());
        return false;
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

    // Clang evaluates the array bounds of a variably modified type named by
    // an explicit cast, e.g. `(int (*)[n++])p`
    // (`CodeGenModule::EmitExplicitCastExprType`), and a cast has no place
    // for them.
    bool variablyModifiedCast(const Expr *expr) {
        ClangPrinter::VlaBounds vla;
        if (auto cast = dyn_cast<ExplicitCastExpr>(expr))
            ClangPrinter::vlaBounds(cast->getType(), vla, ctxt);
        return !vla.empty();
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
        } else if (refersToUndefinedWeak(*expr)) {
            unsupported_expr(expr, "reference to an undefined weak symbol");
        } else if (auto why = overAlignedAccess(expr)) {
            unsupported_expr(expr, *why);
        } else if (variablyModifiedCast(expr)) {
            unsupported_expr(expr, "cast to a variably modified type");
        } else if (expr->isPRValue() && !expr->getType().isNull() &&
                   !expr->getType()->isScalarType() &&
                   underAligned(expr->getType())) {
            // Clang initializes a class or array prvalue of an under-aligned
            // type in a slot allocated at that type's alignment when the
            // context does not provide one (e.g. <<U();>> or <<make();>>,
            // with no [MaterializeTemporaryExpr]), while BRiCk initializes
            // an object of the erased type, naturally aligned.
            unsupported_expr(expr, "under-aligned prvalue");
        } else {
            ConstStmtVisitor<PrintExpr, void>::Visit(expr);
        }
    }

    // The alignment, in bits, that BRiCk assumes for objects of type [ty],
    // the type cpp2v prints (see [modelTypeAlign]); a byte for types without
    // a layout, such as incomplete types.
    uint64_t modelAlign(QualType ty) {
        auto elem = ctxt.getBaseElementType(ty);
        if (elem->isIncompleteType() || elem->isDependentType() ||
            elem->isPlaceholderType() || elem->isUndeducedType() ||
            elem->isSizelessType() || elem->isFunctionType())
            return ctxt.getCharWidth();
        return modelTypeAlign(ctxt, ty);
    }

    // The alignment, in bits, that Clang's code generation assumes for an
    // object of type [ty] accessed through a pointer or reference
    // ([CodeGenModule::getNaturalTypeAlignment]): that of the outermost
    // typedef carrying an alignment attribute, even for an incomplete or
    // array type, and otherwise that of the base element type.
    uint64_t clangNaturalAlign(QualType ty) {
        if (auto tt = ty->getAs<TypedefType>())
            if (auto align = tt->getDecl()->getMaxAlignment())
                return align;
        auto elem = ctxt.getBaseElementType(ty);
        if (elem->isIncompleteType() || elem->isDependentType() ||
            elem->isPlaceholderType() || elem->isUndeducedType() ||
            elem->isSizelessType() || elem->isFunctionType())
            return ctxt.getCharWidth();
        return ctxt.getTypeAlign(elem);
    }

    // Whether Clang assumes objects of type [ty] are more aligned than BRiCk
    // does, as for <<typedef int X32 __attribute__((aligned(32)))>>, which
    // cpp2v prints as [Tint].
    bool overAligned(QualType ty) {
        if (ty.isNull() || ty->isDependentType())
            return false;
        return clangNaturalAlign(ty) > modelAlign(ty);
    }

    // Whether Clang may allocate an object of type [ty] less aligned than
    // BRiCk assumes: Clang allocates temporaries at the alignment of their
    // type, typedef sugar included ([CodeGenFunction::CreateMemTemp]), which
    // an alignment attribute on a typedef can lower, as for
    // <<typedef S U __attribute__((aligned(1)))>>.
    bool underAligned(QualType ty) {
        if (ty.isNull() || ty->isDependentType())
            return false;
        auto elem = ctxt.getBaseElementType(ty);
        if (elem->isIncompleteType() || elem->isDependentType() ||
            elem->isPlaceholderType() || elem->isUndeducedType() ||
            elem->isSizelessType() || elem->isFunctionType())
            return false;
        return ctxt.getTypeAlign(ty) < modelAlign(ty);
    }

    // Clang takes the alignment of an access from the static type of the
    // pointer or reference it goes through, typedef sugar included: through
    // an <<X32*>> it loads and stores with alignment 32, and the optimizer
    // relies on that. Since <<X32*>> and <<int*>> are the same type, a
    // program can reach such an access from any <<int*>> without a cast.
    // BRiCk only requires the alignment of [Tint], so it would accept
    // programs that Clang miscompiles. [overAlignedAccess] finds such
    // accesses, which are printed as unsupported.
    //
    // A local variable used in its own function, or a variable defined in
    // this translation unit (strongly, not as an alias) at least as aligned
    // as the declaration used, has the alignment Clang assumes, since Clang
    // allocates it. (A by-value parameter or a named return value lives at
    // the ABI's alignment instead; Clang only trusts that, not the declared
    // one, in its own function.) So does a field, at
    // the alignment of its record (which BRiCk takes from Clang's layout), and
    // a temporary. An assignment, a parenthesized or conditional glvalue, a
    // base-class subobject and a structured binding have the alignment of
    // the glvalue they designate.
    std::optional<StringRef> unsafeVar(const VarDecl *vd, bool captured) {
        if (vd->getType()->isReferenceType())
            return overAligned(vd->getType()->getPointeeType())
                       ? std::optional<StringRef>(
                             "access through a reference to an over-aligned "
                             "type")
                       : std::nullopt;
        // C++ requires every definition of a variable declared with an
        // <<alignas>> to specify the same alignment ([dcl.align]/6), so only
        // the alignment from GNU attributes and typedefs needs a definition
        // here.
        auto untrusted = clangNaturalAlign(vd->getType());
        // ([AlignedAttr::getAlignment] only reads the context.)
        auto &mctxt = const_cast<ASTContext &>(ctxt);
        for (auto *attr : vd->specific_attrs<AlignedAttr>())
            if (!attr->isAlignas() && !attr->isAlignmentDependent())
                untrusted =
                    std::max<uint64_t>(untrusted, attr->getAlignment(mctxt));
        // cpp2v prints the variable at an aligned typedef's alignment (see
        // [typedefAlign]), so BRiCk would assume the object is that aligned:
        // only a definition here, which Clang allocates, guarantees it.
        if (untrusted <= modelAlign(vd->getType().getCanonicalType()))
            return std::nullopt;
        auto need = ctxt.toBits(ctxt.getDeclAlign(vd));
        if (vd->hasLocalStorage())
            return captured ? std::optional<StringRef>(
                                  "use of a captured variable of an "
                                  "over-aligned type")
                            : std::nullopt;
        // An alias or a weak definition is a definition for Clang, but the
        // storage may be that of another definition.
        auto def = vd->getDefinition();
        if (def && !def->hasAttr<AliasAttr>() && !def->isWeak() &&
            !def->hasAttr<SelectAnyAttr>() &&
            ctxt.toBits(ctxt.getDeclAlign(def)) >= need)
            return std::nullopt;
        return "access to a variable declared more aligned than its "
               "definition";
    }

    std::optional<StringRef> unsafeGlvalue(const Expr *expr) {
        if (expr->isTypeDependent() || expr->isValueDependent())
            return std::nullopt;
        expr = expr->IgnoreParens();
        if (isa<MaterializeTemporaryExpr, CompoundLiteralExpr>(expr))
            return std::nullopt;
        if (auto co = dyn_cast<AbstractConditionalOperator>(expr)) {
            if (auto why = unsafeGlvalue(co->getTrueExpr()))
                return why;
            return unsafeGlvalue(co->getFalseExpr());
        }
        if (auto bo = dyn_cast<BinaryOperator>(expr)) {
            if (bo->isAssignmentOp())
                return unsafeGlvalue(bo->getLHS());
            if (bo->isCommaOp())
                return unsafeGlvalue(bo->getRHS());
        }
        if (auto uo = dyn_cast<UnaryOperator>(expr);
            uo && uo->isIncrementDecrementOp())
            return unsafeGlvalue(uo->getSubExpr());
        if (auto ce = dyn_cast<CastExpr>(expr)) {
            switch (ce->getCastKind()) {
            case CK_NoOp:
            case CK_DerivedToBase:
            case CK_UncheckedDerivedToBase:
                return unsafeGlvalue(ce->getSubExpr());
            default:
                break;
            }
        }
        if (auto dre = dyn_cast<DeclRefExpr>(expr)) {
            if (auto vd = dyn_cast<VarDecl>(dre->getDecl()))
                return unsafeVar(vd, dre->refersToEnclosingVariableOrCapture());
            if (auto bd = dyn_cast<BindingDecl>(dre->getDecl()))
                if (auto binding = bd->getBinding())
                    return unsafeGlvalue(binding);
        } else if (auto me = dyn_cast<MemberExpr>(expr)) {
            auto member = me->getMemberDecl();
            if (auto vd = dyn_cast<VarDecl>(member))
                return unsafeVar(vd, false);
            if (auto fd = dyn_cast<FieldDecl>(member)) {
                if (fd->getType()->isReferenceType())
                    return overAligned(fd->getType()->getPointeeType())
                               ? std::optional<StringRef>(
                                     "access through a reference to an "
                                     "over-aligned type")
                               : std::nullopt;
                if (!me->isArrow())
                    return unsafeGlvalue(me->getBase());
                if (unsafePointer(me->getBase()))
                    return "member access through a pointer to an "
                           "over-aligned type";
                return std::nullopt;
            }
        }
        if (overAligned(expr->getType()))
            return "access through an over-aligned type";
        return std::nullopt;
    }

    // Whether Clang derives an alignment larger than BRiCk's for the object
    // a pointer [e] points to ([CodeGenFunction::EmitPointerWithAlignment]):
    // from the object of <<&e>>, or from the static pointee type, looking
    // through implicit conversions such as derived-to-base ones. (An
    // explicit cast resets the alignment to that of its type.)
    bool unsafePointer(const Expr *e) {
        while (e) {
            e = e->IgnoreParens();
            if (auto uo = dyn_cast<UnaryOperator>(e);
                uo && uo->getOpcode() == UO_AddrOf)
                return unsafeGlvalue(uo->getSubExpr()).has_value();
            if (auto pt = e->getType()->getAs<PointerType>();
                pt && overAligned(pt->getPointeeType()))
                return true;
            auto ice = dyn_cast<ImplicitCastExpr>(e);
            if (!ice)
                return false;
            switch (ice->getCastKind()) {
            case CK_NoOp:
            case CK_BitCast:
            case CK_DerivedToBase:
            case CK_UncheckedDerivedToBase:
                e = ice->getSubExpr();
                break;
            default:
                return false;
            }
        }
        return false;
    }

    std::optional<StringRef> overAlignedAccess(const Expr *expr) {
        if (expr->isTypeDependent() || expr->isValueDependent())
            return std::nullopt;
        if (expr->isGLValue())
            if (auto why = unsafeGlvalue(expr))
                return why;
        auto overAlignedArg = [&](auto args) {
            return std::any_of(args.begin(), args.end(),
                               [&](const Expr *a) { return unsafePointer(a); });
        };
        // A member call through a pointer: Clang takes the alignment of the
        // object (e.g. for a virtual call's vtable load, or the copy of a
        // trivial assignment) from the pointer.
        if (auto me = dyn_cast<MemberExpr>(expr);
            me && me->isArrow() && unsafePointer(me->getBase()))
            return "member access through a pointer to an over-aligned type";
        if (auto mce = dyn_cast<CXXMemberCallExpr>(expr))
            if (auto me =
                    dyn_cast<MemberExpr>(mce->getCallee()->IgnoreParens());
                me && me->isArrow() && unsafePointer(me->getBase()))
                return "member call through a pointer to an over-aligned type";
        if (auto dc = dyn_cast<CXXDynamicCastExpr>(expr);
            dc && unsafePointer(dc->getSubExpr()))
            return "dynamic_cast of a pointer to an over-aligned type";
        if (auto ce = dyn_cast<CallExpr>(expr);
            ce && ce->getBuiltinCallee() && overAlignedArg(ce->arguments()))
            return "builtin call on a pointer to an over-aligned type";
        if (auto ae = dyn_cast<AtomicExpr>(expr);
            ae && overAlignedArg(
                      llvm::ArrayRef(ae->getSubExprs(), ae->getNumSubExprs())))
            return "atomic operation on a pointer to an over-aligned type";
        // A conversion to a virtual base loads the base's offset through the
        // pointer.
        if (auto ce = dyn_cast<CastExpr>(expr);
            ce &&
            (ce->getCastKind() == CK_DerivedToBase ||
             ce->getCastKind() == CK_UncheckedDerivedToBase) &&
            ce->getType()->isPointerType() &&
            std::any_of(
                ce->path_begin(), ce->path_end(),
                [](const CXXBaseSpecifier *b) { return b->isVirtual(); }) &&
            unsafePointer(ce->getSubExpr()))
            return "conversion of a pointer to an over-aligned type to a "
                   "virtual base";
        // A delete expression loads the vtable of a polymorphic object, or
        // the array cookie, at the alignment of the destroyed type.
        if (auto de = dyn_cast<CXXDeleteExpr>(expr);
            de && (overAligned(de->getDestroyedType()) ||
                   unsafePointer(de->getArgument())))
            return "delete of an over-aligned type";
        // Clang initializes the object of a new expression, including a
        // placement new, at the alignment of the allocated type.
        if (auto ne = dyn_cast<CXXNewExpr>(expr);
            ne && overAligned(ne->getAllocatedType()))
            return "new of an over-aligned type";
        return std::nullopt;
    }

    void VisitExpr(const Expr *expr) { unsupported_expr(expr); }

#define IGNORE(E)                                                              \
    void Visit##E(const E *expr) {                                             \
        unsupported_expr(expr, std::nullopt, /*well_known*/ true);             \
    }

    // Unsupported
    IGNORE(CXXThrowExpr)

    // <<typeid(op)>> ([expr.typeid]) prints as [Etypeid op t] with [t] the
    // type of the result (<<const std::type_info>>).
    // - A potentially-evaluated operand (a glvalue of polymorphic class type,
    //   [expr.typeid]/4) prints as [inr e]. So does an expression operand
    //   whose type is dependent, since its polymorphism is not yet known.
    // - Any other operand prints as [inl ty]: for a type operand, the type;
    //   for an unevaluated expression operand, its static type. Either way
    //   [ty] is canonical, with references and top-level (and array element)
    //   cv-qualifiers removed ([expr.typeid]/5-7), so that two [typeid]s of
    //   the same type carry syntactically equal types.
    void VisitCXXTypeidExpr(const CXXTypeidExpr *expr) {
        auto print_type = [&](QualType ty) {
            ty = ty.getNonReferenceType().getCanonicalType();
            ty = ctxt.getUnqualifiedArrayType(ty).getCanonicalType();
            print.ctor("inl", false);
            cprint.printQualType(print, ty, loc::of(expr));
            print.output() << fmt::rparen;
        };

        print.ctor("Etypeid", false);
        if (expr->isTypeOperand()) {
            print_type(expr->getTypeOperand(ctxt));
        } else {
            auto op = expr->getExprOperand();
            if (expr->isPotentiallyEvaluated() || op->isTypeDependent()) {
                print.ctor("inr", false);
                cprint.printExpr(print, op, names);
                print.output() << fmt::rparen;
            } else {
                print_type(op->getType());
            }
        }
        done(expr);
    }

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

    void VisitSizeOfPackExpr(const SizeOfPackExpr *expr) {
        print.ctor("Esizeof_pack", false);
        if (expr->isValueDependent()) {
            print.none();
        } else {
            print.some();
            llvm::APInt length(64, expr->getPackLength());
            print.output() << fmt::N(length);
            print.end_ctor();
        }
        print.output() << fmt::nbsp;
        auto pack = expr->getPack();
        if (auto id = pack ? pack->getIdentifier() : nullptr) {
            print.str(id->getName());
        } else if (pack) {
            print.str(pack->getNameAsString());
        } else {
            print.str("<unknown pack>");
        }
        done(expr);
    }

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

    // The [Trealigned] type of [expr], an access to an under-aligned object.
    // In templates, the [mparser]'s operators take an optional type, as in
    // [done]: a type-dependent [expr] gets none, so the [mparser] keeps it
    // unresolved like other dependent operators; otherwise its type is the
    // same as outside templates.
    void printRealignedResult(const Expr *expr, QualType type, uint64_t align) {
        if (print.templates() && expr->isTypeDependent()) {
            print.none();
            return;
        }
        if (print.templates())
            print.some();
        cprint.printRealignedQualType(print, type, align, loc::of(expr));
        if (print.templates())
            print.end_ctor();
    }

    // An assignment or compound assignment to an under-aligned field, which
    // accesses it at the field's [Trealigned] type (BRiCk computes a compound
    // assignment at the underlying type); only when its result is discarded
    // or read (see [ClangPrinter::realignedAccess]).
    bool printRealignedAssign(const BinaryOperator *expr) {
        if (!realignedAssign(expr))
            return false;
        auto obj = realignedObject(expr->getLHS());
        if (cprint.discardedExpr != expr && cprint.realignedAccess != expr) {
            printCheckedRealigned(expr);
            return true;
        }
        auto lhs = expr->getLHS()->IgnoreParens();
        if (expr->isCompoundAssignmentOp()) {
            print.ctor("Eassign_op");
            switch (expr->getOpcode()) {
#define ACASE(k, v)                                                            \
    case BinaryOperatorKind::BO_##k##Assign:                                   \
        print.output() << #v << fmt::nbsp;                                     \
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
#undef ACASE
            default:
                always_assert(false && "unknown compound assignment");
            }
        } else
            print.ctor("Eassign");
        cprint.realignedAccess = lhs;
        cprint.printExpr(print, expr->getLHS(), names);
        cprint.realignedAccess = nullptr;
        print.output() << fmt::nbsp;
        cprint.printExpr(print, expr->getRHS(), names);
        print.output() << fmt::nbsp;
        printRealignedResult(expr, obj->type, obj->align);
        print.end_ctor();
        return true;
    }

    // An increment or decrement of an under-aligned field, which accesses it
    // at the field's [Trealigned] type (BRiCk computes at the underlying
    // type). A prefix one is a glvalue, like an assignment; a postfix one is
    // a prvalue of the field's underlying type.
    bool printRealignedIncDec(const UnaryOperator *expr) {
        if (!expr->isIncrementDecrementOp())
            return false;
        auto obj = realignedObject(expr->getSubExpr());
        if (!obj)
            return false;
        if (expr->isPrefix() && cprint.discardedExpr != expr &&
            cprint.realignedAccess != expr) {
            printCheckedRealigned(expr);
            return true;
        }
        switch (expr->getOpcode()) {
        case UnaryOperatorKind::UO_PostInc:
            print.ctor("Epostinc");
            break;
        case UnaryOperatorKind::UO_PreInc:
            print.ctor("Epreinc");
            break;
        case UnaryOperatorKind::UO_PostDec:
            print.ctor("Epostdec");
            break;
        default:
            print.ctor("Epredec");
            break;
        }
        auto sub = expr->getSubExpr()->IgnoreParens();
        cprint.realignedAccess = sub;
        cprint.printExpr(print, expr->getSubExpr(), names);
        cprint.realignedAccess = nullptr;
        print.output() << fmt::nbsp;
        if (expr->isPrefix())
            printRealignedResult(expr, obj->type, obj->align);
        else if (print.templates())
            cprint.printQualTypeOption(print, expr->getType(), loc::of(expr));
        else
            cprint.printQualType(print, expr->getType(), loc::of(expr));
        print.end_ctor();
        return true;
    }

    void VisitBinaryOperator(const BinaryOperator *expr) {
        if (printRealignedAssign(expr))
            return;
        // A comma whose result is a bit-field glvalue, and an assignment or
        // compound assignment to one, have their own nodes (see [Ebf_comma]
        // in syntax/core.v). Clang tracks bit-field glvalues as the object
        // kind of the node. Assignments test their left operand: in C++ the
        // result is a bit-field exactly when the operand is, but in C the
        // result is a prvalue while the operand is still a bit-field.
        const bool bitfield = expr->refersToBitField();
        // A type-dependent assignment (in a template) keeps the ordinary
        // node: it is unresolved, and its operand need not be a bit-field
        // once instantiated.
        const bool lhs_bitfield = expr->isAssignmentOp() &&
                                  !expr->isTypeDependent() &&
                                  expr->getLHS()->refersToBitField();
#define ACASE(k, v)                                                            \
    case BinaryOperatorKind::BO_##k##Assign:                                   \
        print.ctor(lhs_bitfield ? "Ebf_assign_op" : "Eassign_op")                  \
            << #v << fmt::nbsp;                                                \
        break;
        [[maybe_unused]] auto dependent =
            print.templates() && expr->getType()->isDependentType();
        switch (expr->getOpcode()) {
        case BinaryOperatorKind::BO_Comma:
            print.ctor(bitfield ? "Ebf_comma" : "Ecomma");
            printDiscarded(expr->getLHS());
            print.output() << fmt::nbsp;
            // The right operand of a discarded comma is discarded too.
            if (cprint.discardedExpr == expr)
                printDiscarded(expr->getRHS());
            else
                cprint.printExpr(print, expr->getRHS());
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_LAnd:
            print.ctor("Eseqand");
            cprint.printExpr(print, expr->getLHS());
            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getRHS());
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_LOr:
            print.ctor("Eseqor");
            cprint.printExpr(print, expr->getLHS());
            print.output() << fmt::nbsp;
            cprint.printExpr(print, expr->getRHS());
            print.end_ctor(); // no type information
            return;
        case BinaryOperatorKind::BO_Assign:
            print.ctor(lhs_bitfield ? "Ebf_assign" : "Eassign");
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
        // An assignment stores its right operand in its left one.
        if (expr->getOpcode() == BinaryOperatorKind::BO_Assign)
            cprint.printExprAt(print, expr->getRHS(), expr->getLHS()->getType(),
                               names);
        else
            cprint.printExpr(print, expr->getRHS(), names);
        // In templates, the bit-field nodes are not wrapped by the
        // [mparser], so they carry their type like outside templates.
        done(expr, print.templates() && !lhs_bitfield ? Done::O : Done::T);
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
        if (printRealignedIncDec(expr))
            return;
        // A pre-increment or pre-decrement whose result is a bit-field
        // glvalue, and a post-increment or post-decrement of a bit-field
        // glvalue, have their own nodes (see [Ebf_preinc] in syntax/core.v).
        bool bitfield = false;
        // As for assignments: a type-dependent operator keeps its ordinary
        // node.
        const bool operand_bitfield = !expr->isTypeDependent() &&
                                      expr->getSubExpr()->refersToBitField();
        switch (expr->getOpcode()) {
        case UnaryOperatorKind::UO_Extension: {
            guard::ctor _{print, "Eextension"};
            cprint.printExpr(print, expr->getSubExpr(), names);
            return;
        }
        case UnaryOperatorKind::UO_AddrOf: {
            auto e = expr->getSubExpr();
            if (realignedGLValue(e)) {
                // The address of an under-aligned object points to its
                // [Trealigned] type. A pointer cast converting it checks the
                // target type's alignment; otherwise a checked no-op cast to
                // the expression's type does ([wp_operand_cast_noop]).
                const bool converted = cprint.realignedAddr == expr;
                cprint.realignedAddr = nullptr;
                if (!converted) {
                    print.ctor("Ecast");
                    print.ctor("Cnoop", false);
                    cprint.printQualType(print, expr->getType(),
                                         loc::of(expr));
                    print.end_ctor() << fmt::nbsp;
                }
                {
                    guard::ctor _{print, "Eaddrof"};
                    auto saved = cprint.realignedAccess;
                    cprint.realignedAccess = e->IgnoreParens();
                    cprint.printExpr(print, e, names);
                    cprint.realignedAccess = saved;
                }
                if (!converted)
                    print.end_ctor();
                return;
            }
            if (auto dre = dyn_cast<DeclRefExpr>(e)) {
                auto decl = dre->getDecl();
                if (is_class_member(decl)) {
                    if (isUndefinedWeak(decl))
                        return unsupported_expr(
                            expr, "pointer to an undefined weak member");
                    guard::ctor _(print, "Eglobal_member");
                    cprint.printName(print, decl, loc::of(expr));
                    print.output() << fmt::nbsp;
                    cprint.printQualType(print, decl->getType(), loc::of(expr));
                    return;
                }
            }
            guard::ctor _{print, "Eaddrof"};
            cprint.printExpr(print, e, names);
            return;
        }
        case UnaryOperatorKind::UO_Deref:
            print.ctor("Ederef");
            break;
        case UnaryOperatorKind::UO_PostInc:
            bitfield = operand_bitfield;
            print.ctor(bitfield ? "Ebf_postinc" : "Epostinc");
            break;
        case UnaryOperatorKind::UO_PreInc:
            bitfield = operand_bitfield;
            print.ctor(bitfield ? "Ebf_preinc" : "Epreinc");
            break;
        case UnaryOperatorKind::UO_PostDec:
            bitfield = operand_bitfield;
            print.ctor(bitfield ? "Ebf_postdec" : "Epostdec");
            break;
        case UnaryOperatorKind::UO_PreDec:
            bitfield = operand_bitfield;
            print.ctor(bitfield ? "Ebf_predec" : "Epredec");
            break;
        default:
            print.ctor("Eunop");
            printUnaryOperator(expr);
            print.output() << fmt::nbsp;
        }
        cprint.printExpr(print, expr->getSubExpr(), names);
        // See [VisitBinaryOperator] for the type in templates.
        done(expr, print.templates() && !bitfield ? Done::O : Done::T);
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
            // E.g. a lambda's default argument, printed at the call site.
            if (!maybe_lambda)
                return unsupported_expr(expr, "capture outside its lambda");
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
                always_assert(0 < var_decl->getName().size());
                // TODO NAMES: this should never be anonymous, but it
                // technically could be
                cprint.printCaptureVarName(print, *lambda, *var_decl)
                    << fmt::nbsp;
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
                cprint.printTemplateValueParamRef(
                    print, param->getDepth(), param->getIndex(), expr,
                    loc::of(expr));
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
        } else if (auto vd = dyn_cast<VarDecl>(var_decl);
                   vd && vd->getTLSKind() != VarDecl::TLS_None) {
            // BRiCk has no thread-local storage: printing the variable as an
            // ordinary global would model one object shared by all threads.
            cprint.error_prefix(logging::unsupported(), loc::of(expr))
                << "warning: unsupported thread_local variable\n";
            print.ctor("Eunsupported", false);
            print.str("thread_local variable") << fmt::nbsp;
            done(expr, Done::DT);
        } else {
            // expr->dump();
            // var_decl->dump();
            // auto found_decl = expr->getFoundDecl();
            // found_decl->dump();
            cprint.printValueDeclExpr(print, var_decl, names);
        }
    }

    // The arguments of these builtins are not evaluated, but [Ecall] would
    // evaluate them: those clang marks unevaluated (`__builtin_constant_p`),
    // MS `__noop` (code generation drops its arguments), and
    // `__builtin_assume` and MS `__assume`, whose argument is only assumed:
    // the behaviour is undefined unless it holds.
    bool unevaluatedArgsBuiltin(const FunctionDecl &fd) {
        auto id = fd.getBuiltinID();
        if (id == Builtin::ID::NotBuiltin)
            return false;
        return cprint.getContext().BuiltinInfo.isUnevaluated(id) ||
               id == Builtin::BI__noop || id == Builtin::BI__assume ||
               id == Builtin::BI__builtin_assume;
    }

    // The prototype of a function, a pointer to one, or a member pointer to
    // one, if any.
    static const FunctionProtoType *protoOf(QualType t) {
        if (t.isNull())
            return nullptr;
        if (auto pt = t->getAs<PointerType>())
            t = pt->getPointeeType();
        else if (auto mp = t->getAs<MemberPointerType>())
            t = mp->getPointeeType();
        return t->getAs<FunctionProtoType>();
    }

    // Prints the arguments of a call, each at the type of its parameter (see
    // [ClangPrinter::printExprAt]). The argument at index [-first] is that of
    // the first parameter: a member operator's object argument has none.
    template <typename Args>
    void printArgs(Args args, const FunctionProtoType *proto, int first = 0) {
        int i = first;
        print.list(args, [&](auto a) {
            QualType dest;
            if (proto && i >= 0 && unsigned(i) < proto->getNumParams())
                dest = proto->getParamType(i);
            ++i;
            cprint.printExprAt(print, a, dest, names);
        });
    }

    void VisitCallExpr(const CallExpr *expr) {
        auto callee = expr->getCallee();
        if (auto pd = dyn_cast<CXXPseudoDestructorExpr>(callee)) {
            // in the clang AST, pseudo destructors are represented as calls
            // but in the BRiCk AST, they are their own construct.
            always_assert(expr->arguments().empty());
            print.ctor("Epseudo_destructor")
                << fmt::BOOL(pd->isArrow()) << fmt::nbsp;
            cprint.printQualType(print, pd->getDestroyedType(), loc::of(pd));
            print.output() << fmt::nbsp;
            cprint.printExpr(print, pd->getBase(), names);
            print.end_ctor();
        } else if (is_dependent(expr)) {
            /*
            Either the function or an argument is dependent.
            */
            guard::ctor ctor(print, "Eunresolved_call");
            cprint.printExpr(print, callee, names);
            print.output() << fmt::nbsp;
            print.list(expr->arguments(),
                       [&](auto i) { cprint.printExpr(print, i, names); });
        } else if (auto fd = expr->getDirectCallee();
                   fd && unevaluatedArgsBuiltin(*fd)) {
            auto msg = "builtin whose arguments are not evaluated: " +
                       fd->getNameAsString();
            cprint.error_prefix(logging::unsupported(), loc::of(expr))
                << "warning: unsupported " << msg << "\n";
            print.ctor("Eunsupported", false);
            print.str(msg) << fmt::nbsp;
            done(expr, Done::DT);
        } else {
            print.ctor("Ecall");
            cprint.printExpr(print, expr->getCallee(), names);
            print.output() << fmt::line;
            printArgs(expr->arguments(),
                      protoOf(fd ? fd->getType() : callee->getType()));
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
            guard::ctor _{print, "Eoperator_member_call"};
            cprint.printOverloadableOperator(print, expr->getOperator(),
                                             loc::of(expr))
                << fmt::nbsp;

            cprint.printName(print, *method);
            print.output() << fmt::nbsp
                           << (method->isStatic()    ? "Static_dispatch"
                               : method->isVirtual() ? "Virtual"
                                                     : "Direct")
                           << fmt::nbsp;
            cprint.printQualType(print, method->getType(), loc::of(method));
            print.output() << fmt::nbsp;
            printArgs(expr->arguments(), protoOf(method->getType()),
                      method->isStatic() ? 0 : -1);
        } else if (auto function = dyn_cast<FunctionDecl>(callee)) {
            guard::ctor _{print, "Eoperator_call"};
            cprint.printOverloadableOperator(print, expr->getOperator(),
                                             loc::of(expr))
                << fmt::nbsp;

            cprint.printName(print, *function);
            print.output() << fmt::nbsp;
            cprint.printQualType(print, function->getType(), loc::of(function));
            print.output() << fmt::nbsp;
            printArgs(expr->arguments(), protoOf(function->getType()));
        } else {
            print.ctor("Eunsupported");
            print.str("unsupported operator call");
            done(expr, Done::DT);
        }
    }

    void printCast(const CastExpr *ce) {
        auto with_type = [&](const char *c) {
            guard::ctor _(print, c, false);
            cprint.printDeclType(print, ce);
        };
        auto without_type = [&](const char *c) { print.output() << c; };

        if (castTakesVirtualStep(*ce)) {
            logging::unsupported()
                << "unsupported cast to a virtual base"
                << " (at " << cprint.sourceRange(ce->getSourceRange()) << ")\n";
            print.ctor("Cunsupported", false);
            print.str(ce->getCastKindName()) << fmt::nbsp;
            done(ce, Done::DT);
            return;
        }

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
        // The lvalue-to-rvalue conversion of a bit-field glvalue has its own
        // cast (see [Cl2r_bitfield] in syntax/core.v).
        case CastKind::CK_LValueToRValue:
            without_type(ce->getSubExpr()->refersToBitField() ? "Cl2r_bitfield"
                                                              : "Cl2r");
            break;
            CASE_WITH_TYPE(LValueToRValueBitCast, Cl2r_bitcast)
            CASE_WITH_TYPE(NoOp, Cnoop)
            CASE_NO_TYPE(ArrayToPointerDecay, Carray2ptr)
            CASE_NO_TYPE(FunctionToPointerDecay, Cfun2ptr)
            CASE_WITH_TYPE(IntegralToPointer, Cint2ptr)
            CASE_WITH_TYPE(PointerToIntegral, Cptr2int)

            CASE_NO_TYPE(PointerToBoolean, Cptr2bool)
            CASE_WITH_TYPE(IntegralCast, Cintegral)
            CASE_NO_TYPE(IntegralToBoolean, Cint2bool)
            CASE_NO_TYPE(FloatingToBoolean, Cfloat2bool)

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
        if (expr->isPRValue())
            cprint.printValueQualType(print, expr->getTypeAsWritten(),
                                      loc::of(expr));
        else
            cprint.printQualType(print, expr->getTypeAsWritten(),
                                 loc::of(expr));
        print.output() << fmt::nbsp;
        if (expr->getCastKind() == CastKind::CK_ToVoid)
            printDiscarded(expr->getSubExpr());
        else {
            noteRealignedAddr(expr);
            cprint.printExpr(print, expr->getSubExpr(), names);
        }
        print.end_ctor();
    }

    void VisitImplicitCastExpr(const ImplicitCastExpr *expr) {
        // todo(gmm): this is a complete hack because there is no way that i
        // know of to get the type of a builtin. what this does is get the type
        // of the expression that contains the builtin.
        if (expr->getCastKind() == CastKind::CK_BuiltinFnToFnPtr) {
            auto ref =
                dyn_cast<DeclRefExpr>(expr->getSubExpr()->IgnoreParens());
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

        if (expr->getCastKind() == CastKind::CK_LValueToRValue &&
            (realignedObject(expr->getSubExpr()) ||
             realignedUpdate(expr->getSubExpr()) ||
             realignedTypedefHead(ctxt, expr->getSubExpr()->getType()))) {
            // Read the realigned object (a packed field, the result of an
            // update of one, or an object of a realigned typedef type), then
            // retype the value at the expression's type, as a value:
            // [wp_operand_cast_noop] makes the prover show that the value
            // has that type.
            guard::ctor noop(print, "Ecast");
            print.ctor("Cnoop", false);
            cprint.printValueQualType(print, expr->getType(), loc::of(expr));
            print.end_ctor() << fmt::nbsp;
            guard::ctor l2r(print, "Ecast");
            print.output() << "Cl2r" << fmt::nbsp;
            cprint.realignedAccess = expr->getSubExpr()->IgnoreParens();
            cprint.printExpr(print, expr->getSubExpr(), names);
            cprint.realignedAccess = nullptr;
            return;
        }

        guard::ctor _(print, "Ecast");
        printCast(expr);
        print.output() << fmt::nbsp;
        if (expr->getCastKind() == CastKind::CK_ToVoid)
            printDiscarded(expr->getSubExpr());
        else {
            noteRealignedAddr(expr);
            cprint.printExpr(print, expr->getSubExpr(), names);
        }
    }

    // A pointer conversion of the address of an under-aligned object (see
    // [ClangPrinter::realignedAddr]).
    void noteRealignedAddr(const CastExpr *expr) {
        if (expr->getCastKind() != CastKind::CK_BitCast &&
            expr->getCastKind() != CastKind::CK_NoOp)
            return;
        if (!expr->getType()->isPointerType())
            return;
        auto uo = dyn_cast<UnaryOperator>(expr->getSubExpr()->IgnoreParens());
        if (uo && uo->getOpcode() == UnaryOperatorKind::UO_AddrOf &&
            realignedGLValue(uo->getSubExpr()))
            cprint.realignedAddr = uo;
    }

    void VisitCastExpr(const CastExpr *expr) {
        always_assert(false && "Cast expression should be unreachable");
    }

    void VisitIntegerLiteral(const IntegerLiteral *lit) {
        print.ctor("Eint", false);
        llvm::APSInt value(
            lit->getValue(),
            !lit->getType()->isSignedIntegerOrEnumerationType());
        print.output() << fmt::Z(value);
        done(lit);
    }

    void VisitCharacterLiteral(const CharacterLiteral *lit) {
        const auto type = lit->getType();
        const auto value = llvm::APInt(32, lit->getValue())
                               .zextOrTrunc(cprint.getContext().getTypeSize(type));
        if (type->isAnyCharacterType()) {
            // Clang sign-extends ordinary signed-char literals in its unsigned
            // storage. Vchar represents the code unit, so discard those high
            // bits rather than printing an out-of-range character value.
            print.ctor("Echar", false) << value.getZExtValue() << "%N";
        } else {
            // Ordinary multicharacter literals have type int, not char.
            const llvm::APSInt int_value(value, false);
            print.ctor("Eint", false) << fmt::Z(int_value);
        }
        done(lit);
    }

    static void print_string_type(const Expr *expr, CoqPrinter &print,
                                  ClangPrinter &cprint) {
        // The type may be sugared, e.g. <<typedef char B[4]; B b = "abc";>>.
        if (auto at = expr->getType()->getAsArrayTypeUnsafe()) {
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
        auto val = expr->EvaluateInContext(
            cprint.getContext(), cprint.sourceLocExprScope().getDefaultExpr());
        if (expr->isIntType()) {
            print.ctor("Eint");
            print.output() << fmt::Z(val.getInt(), false) << fmt::nbsp;
            done(expr);
        } else {
            // this is actually an LValue
            auto base = val.getLValueBase();
            // E.g. <<__builtin_source_location()>> points to a global object
            // clang makes up.
            if (!base.is<const Expr *>())
                return unsupported_expr(expr, "source location object");
            cprint.printExpr(print, base.get<const Expr *>(), names);
        }
    }

    /// Prints <<Estring s t>> for the string literal [lit] whose type is
    /// that of [expr] (they differ for predefined expressions).
    void print_string_literal(const StringLiteral *lit, const Expr *expr) {
        std::vector<uint32_t> chars;
        chars.reserve(lit->getLength());
        for (unsigned i = 0, len = lit->getLength(); i < len; ++i)
            chars.push_back(lit->getCodeUnit(i));
        const unsigned bpc = string_literal::bytes_per_char(chars);
        if (uint64_t(chars.size()) * bpc > string_literal::max_bytes)
            return unsupported_expr(
                expr, "string literal exceeds Rocq's maximum string length");
        guard::ctor _{print, "Estring", false};
        // NOTE: the trailing `\0` is added by the semantics
        string_literal::print(print, chars, bpc);
        print_string_type(expr, print, cprint);
    }

    void VisitStringLiteral(const StringLiteral *lit) {
        print_string_literal(lit, lit);
    }

    void VisitPredefinedExpr(const PredefinedExpr *expr) {
        if (auto name = expr->getFunctionName()) {
            always_assert(!expr->getType()->isDependentType() &&
                          "dependent type of predefined expr");
            print_string_literal(name, expr);
        } else {
            guard::ctor _{print, "Eunresolved_string_literal"};
            print.output() << "Tchar";
        }
    }

    void VisitCXXBoolLiteralExpr(const CXXBoolLiteralExpr *lit) {
        if (lit->getValue()) {
            print.output() << "(Ebool true)";
        } else {
            print.output() << "(Ebool false)";
        }
    }

    void unsupportedFloatingLiteral(const FloatingLiteral *lit,
                                    llvm::StringRef reason) {
        const auto value = lit->getValue();
        std::string msg;
        llvm::raw_string_ostream os{msg};
        os << reason << ": ";
        value.print(os);

        print.ctor("Eunsupported", false);
        print.str(msg) << fmt::nbsp;
        done(lit, Done::DT);
    }

    void VisitFloatingLiteral(const FloatingLiteral *lit) {
        const BuiltinType *bt = lit->getType()->getAs<BuiltinType>();
        const char *ft = nullptr;
        if (bt) {
            switch (bt->getKind()) {
            case BuiltinType::Float16:
                if (lit->getRawSemantics() == llvm::APFloatBase::S_IEEEhalf)
                    ft = "float_type.Ffloat16";
                break;
            case BuiltinType::Float:
                if (lit->getRawSemantics() == llvm::APFloatBase::S_IEEEsingle)
                    ft = "float_type.Ffloat";
                break;
            case BuiltinType::Double:
                if (lit->getRawSemantics() == llvm::APFloatBase::S_IEEEdouble)
                    ft = "float_type.Fdouble";
                break;
            case BuiltinType::Float128:
                if (lit->getRawSemantics() == llvm::APFloatBase::S_IEEEquad)
                    ft = "float_type.Ffloat128";
                break;
            case BuiltinType::LongDouble:
                /* BRiCk marks [Flongdouble] unsupported; reject literals here
                   to match the type printer and checker. */
                break;
            default:
                break;
            }
        }

        if (!ft) {
            std::string reason;
            llvm::raw_string_ostream os{reason};
            os << "unsupported floating-point semantics "
               << apFloatSemanticsName(lit->getRawSemantics()) << " for "
               << builtinTypeKindName(bt);
            return unsupportedFloatingLiteral(lit, os.str());
        }

        SmallString<64> bits;
        lit->getValue().bitcastToAPInt().toStringUnsigned(bits);

        print.ctor("Efloat_of_bits", false);
        print.output() << ft << fmt::nbsp << bits << "%Z" << fmt::nbsp;
        done(lit, Done::NONE);
    }

    // Whether [e] is a glvalue for an under-aligned object, accessed at its
    // [Trealigned] type where its context allows it.
    bool realignedGLValue(const Expr *e) {
        return realignedObject(e) || realignedArray(e) || realignedUpdate(e);
    }

    // Prints the glvalue [e] for an under-aligned object, used at its
    // naturally aligned type: a no-op cast to that type, whose rule
    // ([wp_lval_cast_noop]) asks the prover to show that the object is
    // naturally aligned, as Clang assumes (e.g. for a reference bound to it).
    void printCheckedRealigned(const Expr *e) {
        guard::ctor _(print, "Ecast");
        print.ctor("Cnoop", false);
        print.ctor(e->isXValue() ? "Trv_ref" : "Tref", false);
        cprint.printQualType(print, e->getType(), loc::of(e));
        print.end_ctor();
        print.end_ctor() << fmt::nbsp;
        auto saved = cprint.realignedAccess;
        cprint.realignedAccess = e->IgnoreParens();
        cprint.printExpr(print, e, names);
        cprint.realignedAccess = saved;
    }

    // Prints [e], whose value its context discards (see
    // [ClangPrinter::realignedAccess]).
    void printDiscarded(const Expr *e) {
        auto saved = cprint.discardedExpr;
        cprint.discardedExpr = e->IgnoreParens();
        cprint.printExpr(print, e, names);
        cprint.discardedExpr = saved;
    }

    // Whether [e] is an assignment or compound assignment to an
    // under-aligned field.
    bool realignedAssign(const Expr *e) {
        auto bo = dyn_cast<BinaryOperator>(e->IgnoreParens());
        return bo && bo->isAssignmentOp() && realignedObject(bo->getLHS());
    }

    // Whether [e] is a glvalue for an under-aligned field computed by an
    // assignment, a compound assignment, or a prefix increment or decrement.
    bool realignedUpdate(const Expr *e) {
        if (realignedAssign(e))
            return true;
        auto uo = dyn_cast<UnaryOperator>(e->IgnoreParens());
        return uo && uo->isPrefix() && uo->isIncrementDecrementOp() &&
               realignedObject(uo->getSubExpr());
    }

    // An under-aligned object that a glvalue [e] designates: a scalar field
    // of a packed record, or an element of an under-aligned array field.
    // [type] is the object's type, which cpp2v prints wrapped in
    // [Trealigned align].
    struct Realigned {
        uint64_t align;
        QualType type;
    };
    std::optional<Realigned> realignedObject(const Expr *e) {
        e = e->IgnoreParens();
        if (auto me = dyn_cast<MemberExpr>(e)) {
            if (me->getType()->isArrayType())
                return std::nullopt;
            if (auto align = realignedMember(me))
                return Realigned{*align, me->getMemberDecl()->getType()};
            return std::nullopt;
        }
        if (auto ase = dyn_cast<ArraySubscriptExpr>(e)) {
            if (ase->getType()->isArrayType())
                return std::nullopt;
            if (auto align = realignedArray(subscriptArray(ase)))
                return Realigned{*align, ase->getType()};
        }
        return std::nullopt;
    }

    // The array operand of a subscript, without its array-to-pointer decay
    // (see [VisitArraySubscriptExpr]).
    static const Expr *subscriptArray(const ArraySubscriptExpr *ase) {
        auto base = ase->getBase()->IgnoreParens();
        if (auto ce = dyn_cast<ImplicitCastExpr>(base))
            if (ce->getCastKind() == CastKind::CK_ArrayToPointerDecay)
                return ce->getSubExpr()->IgnoreParens();
        return nullptr;
    }

    // The alignment of the elements of an under-aligned array glvalue [e]:
    // an array field of a packed record, an array element of one, or an
    // opaque value bound to one (an array copy loop's source).
    std::optional<uint64_t> realignedArray(const Expr *e) {
        if (!e)
            return std::nullopt;
        e = e->IgnoreParens();
        if (!e->getType()->isArrayType() || !e->isGLValue())
            return std::nullopt;
        if (auto ove = dyn_cast<OpaqueValueExpr>(e))
            return realignedArray(ove->getSourceExpr());
        if (auto me = dyn_cast<MemberExpr>(e))
            return realignedMember(me);
        if (auto ase = dyn_cast<ArraySubscriptExpr>(e))
            return realignedArray(subscriptArray(ase));
        return std::nullopt;
    }

    // The alignment of the under-aligned field that [e] accesses, if any.
    std::optional<uint64_t> realignedMember(const Expr *e) {
        auto me = dyn_cast<MemberExpr>(e->IgnoreParens());
        if (!me)
            return std::nullopt;
        auto fd = dyn_cast<FieldDecl>(me->getMemberDecl());
        if (!fd)
            return std::nullopt;
        return realignedFieldAlign(cprint.getContext(), *fd);
    }

    void VisitMemberExpr(const MemberExpr *expr) {
        auto member = expr->getMemberDecl();
        auto base = expr->getBase();

        // A bit-field has no address, so its accesses are [Ebitfield], never
        // [Emember], whatever the record (see [Ebitfield] in syntax/core.v).
        if (auto fd = dyn_cast<FieldDecl>(member); fd && fd->isBitField()) {
            guard::ctor _{print, "Ebitfield"};
            print.boolean(expr->isArrow()) << fmt::nbsp;
            cprint.printExpr(print, base, names) << fmt::nbsp;
            print.str(fd->getName()) << fmt::nbsp;
            cprint.printQualType(print, member->getType(), loc::of(member));
            return;
        }

        std::optional<uint64_t> realigned;
        if (auto fd = dyn_cast<FieldDecl>(member))
            realigned = realignedFieldAlign(cprint.getContext(), *fd);
        if (realigned && cprint.realignedAccess != expr) {
            // See [ClangPrinter::realignedAccess].
            printCheckedRealigned(expr);
            return;
        }

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

            if (realigned)
                cprint.printRealignedQualType(print, member->getType(),
                                              *realigned, loc::of(member));
            else
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
        guard::ctor _{print, "core.Eunresolved_member"};
        if (expr->isArrow()) {
            guard::ctor arrow{print, "Eunresolved_unop", false};
            print.output() << "Rarrow" << fmt::nbsp;
            cprint.printExpr(print, expr->getBase(), names) << fmt::nbsp;
        } else {
            cprint.printExpr(print, expr->getBase(), names);
        }
        print.output() << fmt::nbsp;
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

        if (auto align = realignedArray(subscriptArray(expr))) {
            // An element (or row) of an under-aligned array: allowed where
            // an under-aligned field is (see [ClangPrinter::realignedAccess];
            // a row only as the array of another subscript, since a decayed
            // row would be a pointer that BRiCk assumes naturally aligned),
            // and typed with [Trealigned].
            if (cprint.realignedAccess != expr->IgnoreParens()) {
                printCheckedRealigned(expr);
                return;
            }
            auto array = subscriptArray(expr);
            print.ctor("Esubscript");
            cprint.realignedAccess = array;
            if (expr->getBase()->IgnoreParens() == expr->getLHS()->IgnoreParens()) {
                cprint.printExpr(print, array, names);
                cprint.realignedAccess = nullptr;
                print.output() << fmt::nbsp;
                cprint.printExpr(print, under_cast(expr->getRHS()), names);
            } else {
                cprint.realignedAccess = nullptr;
                cprint.printExpr(print, under_cast(expr->getLHS()), names);
                print.output() << fmt::nbsp;
                cprint.realignedAccess = array;
                cprint.printExpr(print, array, names);
                cprint.realignedAccess = nullptr;
            }
            print.output() << fmt::nbsp;
            printRealignedResult(expr, expr->getType(), *align);
            print.end_ctor();
            return;
        }

        print.ctor("Esubscript");
        cprint.printExpr(print, under_cast(expr->getLHS()), names);
        print.output() << fmt::nbsp;
        cprint.printExpr(print, under_cast(expr->getRHS()), names);
        done(expr, print.templates() ? Done::O : Done::T);
    }

    void VisitCXXConstructExpr(const CXXConstructExpr *expr) {
        print.ctor("Econstructor");
        cprint.printName(print, expr->getConstructor(), loc::of(expr));
        print.output() << fmt::nbsp;
        printArgs(expr->arguments(), protoOf(expr->getConstructor()->getType()));
        done(expr);
    }

    void VisitCXXInheritedCtorInitExpr(const CXXInheritedCtorInitExpr *expr) {
        // See the documentation in the AST for why this needs to be a different
        // constructor
        print.ctor("Einherited_constructor");
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
            print.output() << "localname.anon " << idx;
            ++idx;
        });
        done(expr);
    }

    void VisitCXXMemberCallExpr(const CXXMemberCallExpr *expr) {
        auto callee = expr->getCallee()->IgnoreParens();
        auto method = expr->getMethodDecl();
        // An explicit destructor call destroys a complete object, virtual
        // bases included. BRiCk's destructor of a class with virtual bases
        // only destroys the non-virtual part (see [wp_dtor]), and a member
        // call would invoke exactly that.
        if (auto dtor = dyn_cast_or_null<CXXDestructorDecl>(method)) {
            auto cls = dtor->getParent();
            if (cls && cls->isCompleteDefinition() &&
                !cls->isDependentContext() && cls->getNumVBases() > 0)
                return unsupported_expr(
                    expr, "explicit destructor call for a class with "
                          "virtual bases");
        }
        print.ctor("Emember_call");
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
        auto proto = method ? protoOf(method->getType()) : nullptr;
        if (auto bo = dyn_cast<BinaryOperator>(callee); !proto && bo)
            proto = protoOf(bo->getRHS()->getType());
        printArgs(expr->arguments(), proto);
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
        // Match Clang CodeGen: nested defaults retain the outer use site.
        CurrentSourceLocExprScope::SourceLocExprScopeGuard scope(
            expr, cprint.sourceLocExprScope());
        print.ctor("Eimplicit");
        cprint.printExpr(print, expr->getExpr(), names);
        print.end_ctor();
    }

    void VisitConditionalOperator(const ConditionalOperator *expr) {
        // A conditional whose result is a bit-field glvalue has its own node
        // (see [Ebf_if] in syntax/core.v). Such a conditional is a bit-field
        // as soon as one arm is ([expr.cond]/5), so each arm that is not one
        // is an ordinary glvalue, which we mark with [Ebf_glvalue].
        const bool bitfield = expr->refersToBitField();
        // Each arm is converted to the conditional's type, as a glvalue
        // (a reference) or a value (see [ClangPrinter::printExprAt]).
        QualType dest = expr->getType();
        if (!dest.isNull() && !dest->isDependentType()) {
            if (expr->isLValue())
                dest = ctxt.getLValueReferenceType(dest);
            else if (expr->isXValue())
                dest = ctxt.getRValueReferenceType(dest);
        }
        auto arm = [&](const Expr *e) {
            print.output() << fmt::nbsp;
            if (bitfield && !e->refersToBitField()) {
                guard::ctor _{print, "Ebf_glvalue"};
                cprint.printExpr(print, e, names);
            } else if (bitfield) {
                cprint.printExpr(print, e, names);
            } else {
                cprint.printExprAt(print, e, dest, names);
            }
        };
        print.ctor(bitfield ? "Ebf_if" : "Eif");
        cprint.printExpr(print, expr->getCond(), names);
        arm(expr->getTrueExpr());
        arm(expr->getFalseExpr());
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
        } else if (expr->getType()->isVoidType()) {
            print.ctor("Eunresolved_initlist");
            print.none();
            print.output() << fmt::nbsp;
            print.list(expr->inits(),
                       [&](auto i) { cprint.printExpr(print, i, names); });
            print.end_ctor();
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

            // The context for the initializers of under-aligned array
            // fields, or of the rows of an under-aligned array.
            const Expr *self = cprint.realignedInit;
            const uint64_t selfAlign = cprint.realignedInitAlign;
            const bool realignedRows =
                self == expr && expr->getType()->isArrayType() &&
                ctxt.getAsArrayType(expr->getType())
                    ->getElementType()
                    ->isArrayType();
            std::vector<std::optional<uint64_t>> fieldAligns;
            // The types the initializers initialize (see
            // [ClangPrinter::printExprAt]): of the bases and fields, then of
            // the elements.
            std::vector<QualType> fieldTypes;
            QualType elemType;
            if (auto at = ctxt.getAsArrayType(expr->getType()))
                elemType = at->getElementType();
            if (auto rd = expr->getType()->getAsRecordDecl()) {
                if (auto crd = dyn_cast<CXXRecordDecl>(rd)) {
                    fieldAligns.resize(crd->getNumBases());
                    for (auto &b : crd->bases())
                        fieldTypes.push_back(b.getType());
                }
                for (auto f : rd->fields())
                    if (!f->isUnnamedBitField()) {
                        fieldAligns.push_back(
                            f->getType()->isArrayType()
                                ? realignedFieldAlign(ctxt, *f)
                                : std::nullopt);
                        fieldTypes.push_back(f->getType());
                    }
            }
            unsigned index = 0;
            auto printInit = [&](const Expr *i) {
                std::optional<uint64_t> align;
                if (realignedRows)
                    align = selfAlign;
                else if (index < fieldAligns.size())
                    align = fieldAligns[index];
                QualType dest =
                    index < fieldTypes.size() ? fieldTypes[index] : elemType;
                ++index;
                cprint.realignedInit = align ? initCore(i) : nullptr;
                cprint.realignedInitAlign = align ? *align : 0;
                if (align)
                    cprint.printExpr(print, i, names);
                else
                    cprint.printExprAt(print, i, dest, names);
            };
            print.list(expr->inits(), printInit) << fmt::nbsp;

            if (expr->getArrayFiller()) {
                print.some();
                index = fieldAligns.size(); // fillers are array elements
                printInit(expr->getArrayFiller());
                print.end_ctor();
            } else {
                print.none();
            }

            cprint.realignedInit = self;
            cprint.realignedInitAlign = selfAlign;
            done(expr);
            cprint.realignedInit = nullptr;
        }
    }

    /// The implicit construction of a <<std::initializer_list<E>>> from the
    /// backing array of <http://eel.is/c++draft/dcl.init.list#5>.
    ///
    /// The sub-expression is printed verbatim: it is a [MaterializeTemporaryExpr]
    /// wrapping an [InitListExpr] of type <<const E[N]>>, so the backing array's
    /// storage is handled by the existing temporary machinery. Note that this
    /// means the lifetime-extended case, e.g.
    /// <<std::initializer_list<int> il = {1,2,3};>>, reports the
    /// "scope-extruded temporary" limitation from
    /// [VisitMaterializeTemporaryExpr].
    void VisitCXXStdInitializerListExpr(const CXXStdInitializerListExpr *expr) {
        print.ctor("Einitlist_std");
        cprint.printExpr(print, expr->getSubExpr(), names) << fmt::nbsp;
        done(expr);
    }

    void VisitCXXThisExpr(const CXXThisExpr *expr) {
        if (auto maybe_lambda = cprint.getLambdaClass()) {
            auto &[lambda, cv] = maybe_lambda.value();
            auto capture = getCaptureThis(lambda);
            // E.g. <<sizeof(this)>> needs no capture.
            if (!capture)
                return unsupported_expr(expr, "uncaptured this in lambda");

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

    // Clang's value of [alignof(T)] or [alignof(e)] when it differs from the
    // alignment BRiCk's [align_of] gives [T] without its alignment
    // attributes: those on enums, non-scalar typedefs (and declarations, for
    // GNU [alignof(e)]) do not survive the type translation. Such an
    // [alignof] is printed as Clang's constant instead, as is one of a
    // scalar typedef, whose [Trealigned] type would give the same value.
    std::optional<llvm::APSInt>
    attributedAlignOf(const UnaryExprOrTypeTraitExpr &expr) {
        if (expr.getKind() != UnaryExprOrTypeTrait::UETT_AlignOf ||
            expr.isValueDependent() || expr.isTypeDependent())
            return std::nullopt;
        auto &ctxt = cprint.getContext();
        auto ty = expr.isArgumentType() ? expr.getArgumentType()
                                        : expr.getArgumentExpr()->getType();
        // [alignof(T&)] is the alignment of [T], and [alignof(T[])] or
        // [alignof(T[n])] that of [T].
        if (auto ref = ty->getAs<ReferenceType>())
            ty = ref->getPointeeType();
        ty = ty.getCanonicalType();
        if (auto array = ctxt.getAsArrayType(ty))
            ty = ctxt.getBaseElementType(array).getCanonicalType();
        if (ty->isDependentType() || ty->isIncompleteType() ||
            ty->isFunctionType())
            return std::nullopt;
        auto value = expr.EvaluateKnownConstInt(ctxt);
        const auto model =
            ctxt.toCharUnitsFromBits(modelTypeAlign(ctxt, ty)).getQuantity();
        if (value == model)
            return std::nullopt;
        return value;
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
            if (auto value = attributedAlignOf(*expr)) {
                print.ctor("Eint", false) << fmt::Z(*value);
                done(expr);
                break;
            }
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
#if CLANG_VERSION_MAJOR >= 22
            QualType parentTy = parent ? parent->getASTContext().getTagType(
                                             ElaboratedTypeKeyword::None,
                                             std::nullopt, parent, false)
                                       : QualType{};
            const Type *ty =
                parentTy.isNull() ? nullptr : parentTy.getTypePtr();
#else
            const Type *ty = parent ? parent->getTypeForDecl() : nullptr;
#endif
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

    // An aligned allocation or deallocation function receives Clang's
    // alignment of the allocated type, while BRiCk passes [align_of] of the
    // type cpp2v prints, which only has the alignment attributes of scalar
    // typedefs (see [modelTypeAlign]). Such a call is unsupported rather than
    // modelled with the wrong argument.
    bool attributedAlignedAllocation(QualType ty, bool aligned) {
        if (!aligned || ty.isNull() || ty->isDependentType() ||
            ty->isIncompleteType())
            return false;
        auto &ctxt = cprint.getContext();
        auto elem = ty;
        if (auto array = ctxt.getAsArrayType(elem))
            elem = ctxt.getBaseElementType(array);
        return ctxt.getTypeAlign(elem) != modelTypeAlign(ctxt, elem);
    }

    void VisitCXXNewExpr(const CXXNewExpr *expr) {
        auto new_fn = expr->getOperatorNew();
        if (not new_fn) {
            unsupported_expr(expr, "dependent call to new");
            return;
        }
        if (attributedAlignedAllocation(expr->getAllocatedType(),
                                        expr->passAlignment())) {
            unsupported_expr(expr, "aligned new of a type with an alignment "
                                   "attribute");
            return;
        }
        // Without an alignment argument, the storage is only aligned to
        // <<__STDCPP_DEFAULT_NEW_ALIGNMENT__>>, and Clang omits the argument
        // for an under-aligned typedef of an over-aligned class, while BRiCk
        // constructs the object at the erased type, naturally aligned.
        if (!expr->passAlignment() && underAligned(expr->getAllocatedType()) &&
            modelAlign(expr->getAllocatedType()) >
                cprint.getContext().getTargetInfo().getNewAlign()) {
            unsupported_expr(expr, "new of an under-aligned type");
            return;
        }

        print.ctor("Enew");

        print.begin_tuple();
        cprint.printName(print, *new_fn);
        print.next_tuple();
        cprint.printQualType(print, new_fn->getType(), loc::of(new_fn));
        print.end_tuple() << fmt::nbsp;

        // The placement arguments follow the size and, if passed, the
        // alignment.
        printArgs(expr->placement_arguments(), protoOf(new_fn->getType()),
                  expr->passAlignment() ? 2 : 1);
        print.output() << fmt::nbsp;

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

        if (auto init = expr->getInitializer()) {
            guard::some _{print};
            cprint.printExprAt(print, init, expr->getAllocatedType(), names);
        } else
            print.none();

        print.end_ctor();
    }

    void VisitCXXDeleteExpr(const CXXDeleteExpr *expr) {
        if (auto op = expr->getOperatorDelete()) {
            bool aligned = false;
            for (auto param : op->parameters())
                aligned |= param->getType()->isAlignValT();
            if (attributedAlignedAllocation(expr->getDestroyedType(),
                                            aligned)) {
                unsupported_expr(expr, "aligned delete of a type with an "
                                       "alignment attribute");
                return;
            }
            // As for [VisitCXXNewExpr]: Clang picks a deallocation function
            // without an alignment argument for such a type, unlike the one
            // that allocated an object of the erased type.
            auto ty = expr->getDestroyedType();
            if (!aligned && underAligned(ty) &&
                modelAlign(ty) >
                    cprint.getContext().getTargetInfo().getNewAlign()) {
                unsupported_expr(expr, "delete of an under-aligned type");
                return;
            }
        }
        if (expr->getOperatorDelete()) {
            print.ctor("Edelete");
            print.output() << fmt::BOOL(expr->isArrayForm()) << fmt::nbsp
                           << fmt::BOOL(expr->isGlobalDelete()) << fmt::nbsp;

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
            always_assert(print.templates() &&
                          "unresolved delete in non-templated code");
            guard::ctor _{print, "Eunresolved_delete"};
            print.output() << fmt::BOOL(expr->isArrayForm()) << fmt::nbsp
                           << fmt::BOOL(expr->isGlobalDelete()) << fmt::nbsp;
            cprint.printExpr(print, expr->getArgument(), names);
        }
    }

    void VisitExprWithCleanups(const ExprWithCleanups *expr) {
        // This node cannot be dropped: the semantics relies on it to
        // destroy temporaries in initializers of static locals and
        // structured bindings, and in default member initializers used
        // by aggregate initialization. See the comment on
        // [wp_lval_clean] in <<logic/expr.v>>.
        // A full-expression whose result is a bit-field glvalue has its own
        // node (see [Ebf_andclean] in syntax/core.v).
        print.ctor(expr->getSubExpr()->refersToBitField() ? "Ebf_andclean"
                                                          : "Eandclean");
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
        // Clang allocates the temporary at the alignment of its type (e.g.
        // only 1 for <<f(U{7})>>, or <<f(I1(5))>> with an under-aligned
        // typedef I1 of int), while BRiCk materializes it at the type of
        // the value, which has no alignment (see
        // [ClangPrinter::printValueQualType]), naturally aligned.
        if (underAligned(expr->getType()) ||
            (!expr->getType()->isDependentType() &&
             !expr->getType()->isIncompleteType() &&
             ctxt.getTypeAlign(expr->getType()) <
                 modelAlign(expr->getType().getCanonicalType())))
            return unsupported_expr(expr, "under-aligned temporary");

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
        if (auto align = realignedArray(expr)) {
            // Bound to an under-aligned array (see [VisitArrayInitLoopExpr]).
            // As [printQualType] does, the qualifiers of the elements are
            // printed around the array type.
            Qualifiers quals;
            auto unqual = ctxt.getUnqualifiedArrayType(
                expr->getType().getCanonicalType(), quals);
            const bool c = quals.hasConst(), v = quals.hasVolatile();
            print.ctor(expr->isLValue() ? "Tref" : "Trv_ref", false);
            if (c || v)
                print.ctor(c ? (v ? "Qconst_volatile" : "Qconst") : "Qvolatile",
                           false);
            cprint.printRealignedQualType(print, unqual, *align,
                                          loc::of(expr));
            if (c || v)
                print.end_ctor();
            print.end_ctor();
            print.end_ctor();
            return;
        }
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
        // Match Clang CodeGen: nested defaults retain the outer use site.
        CurrentSourceLocExprScope::SourceLocExprScopeGuard scope(
            expr, cprint.sourceLocExprScope());
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

        auto LambdaClass = expr->getLambdaClass();

        cprint.printName(print, *LambdaClass) << fmt::nbsp;

        if (print.templates()) {
            // get the mapping for captures so that we can compute their
            // types
            llvm::DenseMap<const ValueDecl *, FieldDecl *> CaptureFields;
            FieldDecl *ThisCapture = nullptr;
            LambdaClass->getCaptureFields(CaptureFields, ThisCapture);

            auto icap = expr->capture_begin();
            auto iinit = expr->capture_init_begin();
            print.begin_list();
            for (; icap != expr->capture_end() &&
                   iinit != expr->capture_init_end();
                 ++icap, ++iinit) {
                auto &capture = *icap;
                if (capture.capturesVariable()) {
                    auto var = capture.getCapturedVar();
                    auto field = CaptureFields[var];
                    always_assert(field && "uncaptured field");
                    guard::ctor _{print, "expr.Einitializing_type"};
                    cprint.printQualType(print, field->getType(), loc::of(expr))
                        << fmt::nbsp;
                    cprint.printExpr(print, *iinit, this->names);
                } else if (capture.capturesThis()) {
                    always_assert(ThisCapture && "this capture is null");
                    guard::ctor _{print, "expr.Einitializing_type"};
                    cprint.printQualType(print, ThisCapture->getType(),
                                         loc::of(expr))
                        << fmt::nbsp;
                    cprint.printExpr(print, *iinit, this->names);
                } else if (capture.capturesVLAType()) {
                    guard::ctor _{print, "Eunsupported"};
                    print.str("variable length array capture") << fmt::nbsp;
                    guard::ctor type{print, "Tunsupported"};
                    print.str("variable length array capture type");
                } else {
                    always_assert(false && "unreachable lambda capture type");
                }
                print.cons();
            }
            print.end_list();
        } else {
            print.list(expr->capture_inits(), [&](auto init) {
                cprint.printExpr(print, init, this->names);
            });
        }

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
#if CLANG_VERSION_MAJOR >= 21
            print.boolean(expr->getBoolValue());
#else
            print.boolean(expr->getValue());
#endif
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

        if (!expr->getDependence()) {
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
        // An under-aligned source array is only read element by element, at
        // its [Trealigned] element type (see [realignedArray]).
        if (realignedArray(src))
            cprint.realignedAccess = src->IgnoreParens();
        cprint.printExpr(print, src, names);
        cprint.realignedAccess = nullptr;

        // this is the expression that is evaluated
        names.inc_index_count();
        print.output() << names.index_count() << fmt::nbsp
                       << expr->getArraySize() << fmt::nbsp;
        // The rows of an under-aligned array are initialized by an inner
        // loop with the same element alignment.
        const Expr *self = cprint.realignedInit;
        const uint64_t selfAlign = cprint.realignedInitAlign;
        cprint.realignedInit =
            self == expr && isa<ArrayInitLoopExpr>(initCore(expr->getSubExpr()))
                ? initCore(expr->getSubExpr())
                : nullptr;
        cprint.printExpr(print, expr->getSubExpr(), names);
        cprint.realignedInit = self;
        cprint.realignedInitAlign = selfAlign;
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

fmt::Formatter &ClangPrinter::printFieldInit(CoqPrinter &print,
                                             const clang::Expr *e,
                                             const clang::QualType &ty,
                                             std::optional<uint64_t> align) {
    auto saved = realignedInit;
    auto savedAlign = realignedInitAlign;
    if (align && ty->isArrayType()) {
        auto core = e;
        for (;;) {
            if (auto d = dyn_cast<CXXDefaultInitExpr>(core))
                core = d->getExpr();
            else if (auto c = dyn_cast<ConstantExpr>(core))
                core = c->getSubExpr();
            else if (auto c = dyn_cast<ExprWithCleanups>(core))
                core = c->getSubExpr();
            else
                break;
        }
        realignedInit = core;
        realignedInitAlign = *align;
    }
    printExprAt(print, e, ty);
    realignedInit = saved;
    realignedInitAlign = savedAlign;
    return print.output();
}

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
