/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "Template.hpp"
#include "config.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/Builtins.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include <clang/AST/Type.h>
#include <clang/Basic/Version.inc>

using namespace clang;

const char *templateArgumentKindName(TemplateArgument::ArgKind);

[[noreturn]] static void fatal(ClangPrinter &cprint, loc::loc loc,
                               StringRef msg) {
    cprint.error_prefix(logging::fatal(), loc) << "error: " << msg << "\n";
    cprint.debug_dump(loc);
    logging::die();
}

static raw_ostream &unsupported(ClangPrinter &cprint, loc::loc loc,
                                const Twine &msg) {
    auto &os = cprint.error_prefix(logging::unsupported(), loc)
               << "warning: unsupported " << msg << "\n";
    cprint.debug_dump(loc);
    return os;
}

static CallingConv getCallingConv(const Type *type, ClangPrinter &cprint,
                                  loc::loc loc) {
    if (auto ft = dyn_cast_or_null<FunctionType>(type)) {
        return ft->getCallConv();
    } else if (auto at = dyn_cast_or_null<AttributedType>(type)) {
        return getCallingConv(at->getModifiedType().getTypePtr(), cprint, loc);
    } else if (auto toe = dyn_cast_or_null<TypeOfExprType>(type)) {
        return getCallingConv(toe->desugar().getTypePtr(), cprint, loc);
    } else
        fatal(cprint, loc,
              "getCallingConv: FunctionDecl type is not a FunctionType");
}

fmt::Formatter &ClangPrinter::printCallingConv(CoqPrinter &print,
                                               const FunctionDecl &decl) {
    if (ClangPrinter::debug && trace(Trace::Decl))
        trace("printCallingConv", loc::of(decl));
    auto loc = loc::of(decl);
    auto cc = getCallingConv(decl.getType().getTypePtr(), *this, loc);
    return printCallingConv(print, cc, loc);
}

// Template specializations
namespace {

/**
Decide if `decl` is an implicit C++ special member function.

These can show up in specialized structures but do not arise in
templated structures (where it is generally impossible to decide if a
given structure should have a given implicit).
*/
static bool isImplicitSpecialMethod(const Decl &decl) {
    if (!decl.isImplicit())
        return false;
    // Order matters: constructors and destructors are methods.
    if (auto d = dyn_cast<CXXConstructorDecl>(&decl))
        return d->isDefaultConstructor() || d->isCopyConstructor() ||
               d->isMoveConstructor();
    if (isa<CXXDestructorDecl>(&decl))
        return true;
    if (auto d = dyn_cast<CXXMethodDecl>(&decl))
        return d->isCopyAssignmentOperator() || d->isMoveAssignmentOperator();
    return false;
}

/// Decide if `decl` arose from template specialization
static bool isSpecialized(const Decl &decl) {
    if (isImplicitSpecialMethod(decl))
        return false;
    if (isa<EnumConstantDecl>(&decl))
        return false; // avoid too many warnings

    // We conservatively avoid recoverPattern. Instead, we check the
    // declaration and its context for specializations.

    if (recoverSpecialization(decl))
        return true;
    for (auto ctx = decl.getDeclContext(); ctx; ctx = ctx->getParent()) {
        if (recoverSpecialization(*cast<Decl>(ctx)))
            return true;
    }
    return false;
}

/// Decide if `decl` is a template, or lives in a template scope
static bool isTemplate(const Decl &decl) {
    if (recoverTemplate(decl))
        return true;
    for (auto ctx = decl.getDeclContext(); ctx; ctx = ctx->getParent()) {
        if (recoverTemplate(*cast<Decl>(ctx)))
            return true;
    }
    return false;
}
} // namespace

const NamedDecl *recoverPattern(const Decl &decl) {
    // Declarations synthesized by template specialization include
    // pointers back to the "patterns" they specialize.
    if (auto d = dyn_cast<CXXRecordDecl>(&decl)) {
        if (auto pat = d->getInstantiatedFromMemberClass())
            return pat;
        return d->getTemplateInstantiationPattern();
    } else if (auto d = dyn_cast<FunctionDecl>(&decl)) {
        if (auto pat = d->getInstantiatedFromMemberFunction())
            return pat;
        if (auto pat = d->getInstantiatedFromDecl())
            return pat;
        return d->getTemplateInstantiationPattern();
    } else if (auto d = dyn_cast<EnumDecl>(&decl)) {
        if (auto pat = d->getInstantiatedFromMemberEnum())
            return pat;
        return d->getTemplateInstantiationPattern();
    } else if (auto d = dyn_cast<VarDecl>(&decl)) {
        if (auto pat = d->getInstantiatedFromStaticDataMember())
            return pat;
        return d->getTemplateInstantiationPattern();
    } else
        return nullptr;
}

[[nodiscard]] static bool
printSpecialization(CoqPrinter &print, const Decl &decl, ClangPrinter &cprint) {
    if (!print.templates() || !isSpecialized(decl))
        return false;

    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printSpecialization", loc::of(decl));

    if (auto pat = recoverPattern(decl)) {
        guard::ctor _(print, "Dinstantiation");
        cprint.printNameComment(print, decl) << fmt::nbsp;
        cprint.printNameAsKey(print, decl) << fmt::nbsp;
        cprint.printNameComment(print, *pat) << fmt::nbsp;
        cprint.printNameAsKey(print, *pat) << fmt::nbsp;
        cprint.printTemplateArguments(print, decl);
        return true;
    } else {
        unsupported(cprint, loc::of(decl), "template specialization");
        return false;
    }
}

/// Print an untemplated declaration
template <typename T>
using Printer = fmt::Formatter &(*)(CoqPrinter &, const T &, ClangPrinter &,
                                    const ASTContext &);

template <typename T> struct DeclPrinter {
    /* Return [nullptr] if valid, an error message otherwise. */
    using Valid = const char *(*)(const T &, const ASTContext &);
    static const char *alwaysValid(const T &, const ASTContext &) {
        return nullptr;
    }

    const StringRef ctor;
    const Valid invalid;
    const Printer<T> print_body;

    DeclPrinter() = delete;
    DeclPrinter(StringRef c, Printer<T> p, Valid v = alwaysValid)
        : ctor{c}, invalid(v), print_body{p} {
        always_assert(p != nullptr);
    }

    /// Project a decl D from an inhabitant of T
    template <typename D> using ToDecl = const D &(*)(const T &);

    template <typename D> static inline const D &toDeclDecl(const D &decl) {
        return decl;
    }

    /// Set context using ClangPrinter::withDeclContext and emit
    ///
    /// - `(ctor name body)` if `decl` is neither a template nor a
    /// specialization,
    ///
    /// - `(Dinstantiation ..)` if `decl` is a specialization.

    template <typename D = T, ToDecl<D> unbox = toDeclDecl>
    [[nodiscard]] bool print(const T &box, CoqPrinter &print,
                             ClangPrinter &cprint,
                             const ASTContext &ctxt) const {
        const D &decl = unbox(box);
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("DeclPrinter::print", loc::of(decl));
        auto printDecl = [&](ClangPrinter &cprint) {
            if (print.templates()) {
                // We print untemplated code and template specializations
                // elsewhere.
                if (!decl.isTemplated() || isSpecialized(decl))
                    return false;

                guard::ctor _(print, ctor);
                cprint.printNameComment(print, decl) << fmt::nbsp;
                cprint.printTemplateParameters(print, decl) << fmt::nbsp;
                cprint.printNameAsKey(print, decl) << fmt::nbsp;
                print_body(print, box, cprint, ctxt);
                return true;
            } else {
                guard::ctor _(print, ctor);
                cprint.printNameComment(print, decl) << fmt::nbsp;
                cprint.printNameAsKey(print, decl) << fmt::nbsp;
                print_body(print, box, cprint, ctxt);
                return true;
            }
        };
        auto printDeclWith = [&]() {
            auto cp = cprint.withDecl(&decl);
            if (auto msg = invalid(box, ctxt)) {
                guard::ctor _(print, "Dunsupported");
                cp.printName(print, decl) << fmt::nbsp;
                print.str(msg);
                return true;
            } else {
                return printDecl(cp);
            }
        };
        return printDeclWith() || printSpecialization(print, decl, cprint);
    }
};
template <typename D>
DeclPrinter(StringRef, Printer<D>, bool) -> DeclPrinter<D>;

// Incomplete types
namespace {
static fmt::Formatter &printType(CoqPrinter &print, const TypeDecl &decl,
                                 ClangPrinter &cprint, const ASTContext &ctxt) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printType", loc::of(decl));
    return print.output();
}
} // namespace
static const DeclPrinter Dtype("Dtype", printType,
                               DeclPrinter<TypeDecl>::alwaysValid);

// Type aliases
namespace {
static fmt::Formatter &printTypedef(CoqPrinter &print,
                                    const TypedefNameDecl &decl,
                                    ClangPrinter &cprint,
                                    const ASTContext &ctxt) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printTypedef", loc::of(decl));
    return cprint.printQualType(print, decl.getUnderlyingType(), loc::of(decl));
}
} // namespace
static const DeclPrinter Dtypedef("Dtypedef", printTypedef,
                                  DeclPrinter<TypedefNameDecl>::alwaysValid);

// Structures and unions
namespace {

static fmt::Formatter &printClassName(CoqPrinter &print, const RecordDecl &decl,
                                      ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printClassName", loc::of(decl));

    if (print.templates()) {
        /*
        NOTE: Locally, we know `decl` is a template, making it
        reasonable to synthesize _all_ template arguments from
        parameters. Nevertheless, we leave it to the type printer (and
        VisitInjectedClassNameType) to handle argument synthesis
        because such types get printed from other contexts.
        */
        guard::ctor _{print, "Ndependent'", false};
        return cprint.printType(print, decl.getTypeForDecl(), loc::of(decl));
    } else
        return cprint.printName(print, decl);
}

static fmt::Formatter &printClassName(CoqPrinter &print, const RecordDecl *decl,
                                      ClangPrinter &cprint, loc::loc loc) {
    if (decl)
        return printClassName(print, *decl, cprint);
    else
        fatal(cprint, loc, "null class name");
}

static fmt::Formatter &printClassName(CoqPrinter &print, const Type &type,
                                      ClangPrinter &cprint, loc::loc loc) {
    if (auto decl = type.getAsCXXRecordDecl()) {
        return printClassName(print, *decl, cprint);
    } else {
        guard::ctor _{print, "Nunsupported"};
        return print.output()
               << "\"printClassName: " << type.getTypeClassName() << "\"";
    }
}

static fmt::Formatter &printClassName(CoqPrinter &print, const Type *type,
                                      ClangPrinter &cprint, loc::loc loc) {
    if (type) {
        return printClassName(print, *type, cprint, loc);
    } else {
        fatal(cprint, loc, "null class name type");
    }
}
static fmt::Formatter &printClassName(CoqPrinter &print, QualType type,
                                      ClangPrinter &cprint, loc::loc loc) {
    return printClassName(print, type.getTypePtrOrNull(), cprint, loc);
}

static fmt::Formatter &printLayoutInfo(CoqPrinter &print,
                                       CharUnits::QuantityType li) {
    guard::ctor _(print, "Build_LayoutInfo");
    return print.output() << li;
}

static const CXXRecordDecl *getTypeAsRecord(const ValueDecl &decl) {
    if (auto type = decl.getType().getTypePtrOrNull())
        return type->getAsCXXRecordDecl();
    else
        return nullptr;
}

static fmt::Formatter &printAnonymousFieldName(CoqPrinter &print,
                                               const FieldDecl &field,
                                               ClangPrinter &cprint) {
    if (auto rd = dyn_cast<CXXRecordDecl>(field.getParent())) {
        if (rd->isLambda()) {
            guard::ctor _(print, "field_name.CaptureVar");
            llvm::DenseMap<const ValueDecl *, FieldDecl *> captures;
            FieldDecl *this_capture;
            rd->getCaptureFields(captures, this_capture);
            if (this_capture == &field) {
                return print.str("this");
            } else {
                for (auto &i : captures) {
                    if (i.second == &field) {
                        return print.str(i.first->getName());
                    }
                }
            }
        }
    }
    if (auto rec = getTypeAsRecord(field)) {
        return cprint.printName(print, rec, loc::of(field), false);
    } else {
        unsupported(cprint, loc::of(field),
                    "anonymous field not of record type");
        guard::ctor _(print, "field_name.Id", false);
        return print.str("<anonymous field not of record type>");
    }
}
} // namespace

fmt::Formatter &ClangPrinter::printFieldName(CoqPrinter &print,
                                             const FieldDecl &field, loc::loc) {
    if (auto id = field.getIdentifier()) {
        guard::ctor _(print, "field_name.Id", false);
        return print.str(id->getName());
    }
    return printAnonymousFieldName(print, field, *this);
}

namespace {
static fmt::Formatter &printFieldInitializer(CoqPrinter &print,
                                             const FieldDecl &field,
                                             ClangPrinter &cprint) {
    if (auto expr = field.getInClassInitializer()) {
        guard::some _(print);
        return cprint.printExpr(print, expr);
    } else
        return print.none();
}

static fmt::Formatter &printFields(const CXXRecordDecl &decl,
                                   const ASTRecordLayout *layout,
                                   CoqPrinter &print, ClangPrinter &cprint) {
    auto i = 0;
    return print.list(decl.fields(), [&](auto field) {
        if (!field)
            fatal(cprint, loc::of(decl), "null field");
        if (field->isBitField())
            fatal(cprint, loc::of(field), "bit fields are not supported");

        guard::ctor _(print, "mkMember", i != 0);
        cprint.printFieldName(print, *field, loc::of(field)) << fmt::nbsp;
        cprint.printQualType(print, field->getType(), loc::of(field))
            << fmt::nbsp;
        print.boolean(field->isMutable()) << fmt::nbsp;
        printFieldInitializer(print, *field, cprint) << fmt::nbsp;
        auto li = layout ? layout->getFieldOffset(i++) : 0;
        printLayoutInfo(print, li);
    });
    return print.output();
}

static fmt::Formatter &printStructBases(const CXXRecordDecl &decl,
                                        const ASTRecordLayout *layout,
                                        CoqPrinter &print,
                                        ClangPrinter &cprint) {
    return print.list(decl.bases(), [&](CXXBaseSpecifier base) {
        auto fatal = [&](StringRef msg) NORETURN {
            auto loc = loc::refine(loc::of(decl), base.getTypeSourceInfo());
            ::fatal(cprint, loc, msg);
        };

        if (base.isVirtual())
            fatal("virtual base classes are not supported");

        auto type = base.getType().getTypePtrOrNull();
        if (!type)
            fatal("null base class");

        auto dependent = [&]() -> auto & {
            guard::ctor _(print, "mkBase");
            {
                guard::ctor _2(print, "Ndependent'");
                cprint.printType(print, type, loc::of(decl)) << fmt::nbsp;
            }
            return printLayoutInfo(print, 0);
        };
        if (print.templates())
            return dependent();
        else {
            auto record = type->getAsCXXRecordDecl();
            always_assert(record && "base class not a RecordType");
            guard::ctor _(print, "mkBase");
            cprint.printName(print, record, loc::of(type)) << fmt::nbsp;
            auto li =
                layout ? layout->getBaseClassOffset(record).getQuantity() : 0;
            return printLayoutInfo(print, li);
        }
    });
}

bool is_pure_virtual(const clang::FunctionDecl &d) {
#if 18 <= CLANG_VERSION_MAJOR
    return d.isPureVirtual();
#else
    return d.isPure();
#endif
}

static fmt::Formatter &printStructVirtuals(CoqPrinter &print,
                                           const CXXRecordDecl &decl,
                                           ClangPrinter &cprint) {
    return print.list_filter(decl.methods(), [&](auto m) {
        if (!m)
            fatal(cprint, loc::of(decl), "null method");
        if (not m->isVirtual())
            return false;
        guard::ctor _(print, is_pure_virtual(*m) ? "pure_virt" : "impl_virt",
                      false);
        cprint.printName(print, m, loc::of(decl));
        return true;
    });
}

static fmt::Formatter &printStructOverrides(CoqPrinter &print,
                                            const CXXRecordDecl &decl,
                                            ClangPrinter &cprint) {
    guard::list _(print);
    for (auto m : decl.methods()) {
        if (!m)
            fatal(cprint, loc::of(decl), "null method");
        if (m->isVirtual() and not is_pure_virtual(*m)) {
            for (auto o : m->overridden_methods()) {
                print.output() << "(";
                cprint.printName(print, o, loc::of(m)) << fmt::tuple_sep;
                cprint.printName(print, *m) << ")" << fmt::cons;
            }
        }
    }
    return print.output();
}

static fmt::Formatter &printDeleteName(CoqPrinter &print,
                                       const CXXRecordDecl &decl,
                                       ClangPrinter &cprint) {
    auto dtor = decl.getDestructor();
    auto del = dtor ? dtor->getOperatorDelete() : nullptr;
    if (del) {
        guard::some _(print);
        return cprint.printName(print, *del);
    } else
        return print.none();
}

static fmt::Formatter &printTriviallyDestructible(CoqPrinter &print,
                                                  const CXXRecordDecl &decl,
                                                  ClangPrinter &cprint) {
    return print.output() << fmt::BOOL(decl.hasTrivialDestructor());
}

static fmt::Formatter &printLayoutType(CoqPrinter &print,
                                       const CXXRecordDecl &decl,
                                       ClangPrinter &cprint) {
    if (decl.isPOD()) {
        print.output() << "POD";
    } else if (decl.isStandardLayout()) {
        print.output() << "Standard";
    } else {
        print.output() << "Unspecified";
    }
    return print.output();
}

static fmt::Formatter &printSizeAlign(const CXXRecordDecl &decl,
                                      const ASTRecordLayout *layout,
                                      CoqPrinter &print, ClangPrinter &cprint) {
    auto size = layout ? layout->getSize().getQuantity() : 0;
    auto align = layout ? layout->getAlignment().getQuantity() : 0;
    return print.output() << size << fmt::nbsp << align;
}

static fmt::Formatter &printStruct(CoqPrinter &print, const CXXRecordDecl &decl,
                                   ClangPrinter &cprint,
                                   const ASTContext &ctxt) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printStruct", loc::of(decl));
#if 18 <= CLANG_VERSION_MAJOR
    always_assert(decl.getTagKind() == TagTypeKind::Class ||
                  decl.getTagKind() == TagTypeKind::Struct);
#else
    always_assert(decl.getTagKind() == TagTypeKind::TTK_Class ||
                  decl.getTagKind() == TagTypeKind::TTK_Struct);
#endif

    if (!decl.isCompleteDefinition())
        return print.none();

    const auto layout =
        decl.isDependentContext() ? nullptr : &ctxt.getASTRecordLayout(&decl);

    guard::some some(print);
    guard::ctor _(print, "Build_Struct");

    printStructBases(decl, layout, print, cprint) << fmt::line;
    printFields(decl, layout, print, cprint) << fmt::nbsp;
    printStructVirtuals(print, decl, cprint) << fmt::nbsp;
    printStructOverrides(print, decl, cprint) << fmt::nbsp;
    cprint.printDtorName(print, decl) << fmt::nbsp;
    printTriviallyDestructible(print, decl, cprint) << fmt::nbsp;
    printDeleteName(print, decl, cprint) << fmt::line;
    printLayoutType(print, decl, cprint) << fmt::nbsp;
    return printSizeAlign(decl, layout, print, cprint);
}

static fmt::Formatter &printUnion(CoqPrinter &print, const CXXRecordDecl &decl,
                                  ClangPrinter &cprint,
                                  const ASTContext &ctxt) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printUnion", loc::of(decl));
#if 18 <= CLANG_VERSION_MAJOR
    always_assert(decl.getTagKind() == TagTypeKind::Union);
#else
    always_assert(decl.getTagKind() == TagTypeKind::TTK_Union);
#endif

    if (!decl.isCompleteDefinition())
        return print.none();

    const auto layout =
        decl.isDependentContext() ? nullptr : &ctxt.getASTRecordLayout(&decl);

    guard::some some(print);
    guard::ctor _(print, "Build_Union");

    printFields(decl, layout, print, cprint) << fmt::nbsp;
    cprint.printDtorName(print, decl) << fmt::nbsp;
    printTriviallyDestructible(print, decl, cprint) << fmt::nbsp;
    printDeleteName(print, decl, cprint) << fmt::line;
    return printSizeAlign(decl, layout, print, cprint);
}

static const char *supportedRecord(const CXXRecordDecl &decl,
                                   const ASTContext &ctxt) {
    for (auto base : decl.bases()) {
        if (base.isVirtual())
            return "virtual base classes are not supported";
    }
    for (auto f : decl.fields()) {
        if (f->isBitField())
            return "bitfields are not supported";
        if (f->isInvalidDecl())
            return "invalid field";
    }
    return nullptr;
}
} // namespace

static const DeclPrinter Dstruct("Dstruct", printStruct, supportedRecord);
static const DeclPrinter Dunion("Dunion", printUnion, supportedRecord);

// Functions
namespace {
static fmt::Formatter &printFunctionParams(CoqPrinter &print,
                                           const FunctionDecl &decl,
                                           ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printFunctionParams", loc::of(decl));
    auto loc = loc::of(decl);
    return print.list(decl.parameters(), [&](auto *param) {
        guard::tuple _(print);
        cprint.printParamName(print, param) << fmt::tuple_sep;
        cprint.printQualType(print, param->getType(), loc);
    });
}

static fmt::Formatter &printFunction(CoqPrinter &print,
                                     const FunctionDecl &decl,
                                     ClangPrinter &cprint, const ASTContext &) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printFunction", loc::of(decl));
    guard::ctor _(print, "Build_Func");
    cprint.printQualType(print, decl.getReturnType(), loc::of(decl))
        << fmt::line;
    printFunctionParams(print, decl, cprint) << fmt::nbsp;
    cprint.printCallingConv(print, decl) << fmt::nbsp;
    cprint.printVariadic(print, decl.isVariadic()) << fmt::nbsp;
    cprint.printExceptionSpec(print, decl) << fmt::line;
    if (auto body = decl.getBody()) {
        guard::some some(print, false);
        guard::ctor _(print, "Impl", false);
        return cprint.printStmt(print, body);
    } else if (decl.getBuiltinID() != Builtin::ID::NotBuiltin) {
        guard::some some(print, false);
        guard::ctor _(print, "Builtin", false);
        return print.str(
            cprint.getContext().BuiltinInfo.getName(decl.getBuiltinID()));
    } else {
        return print.none();
    }
}

static fmt::Formatter &printMethod(CoqPrinter &print, const CXXMethodDecl &decl,
                                   ClangPrinter &cprint, const ASTContext &) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printMethod", loc::of(decl));

    print.output() << fmt::BOOL(decl.isStatic()) << fmt::nbsp;

    guard::ctor _(print, "Build_Method");
    cprint.printQualType(print, decl.getReturnType(), loc::of(decl))
        << fmt::nbsp;
    printClassName(print, decl.getParent(), cprint, loc::of(decl)) << fmt::nbsp;
    cprint.printQualifier(print, decl.isConst(), decl.isVolatile())
        << fmt::nbsp;
    printFunctionParams(print, decl, cprint) << fmt::nbsp;
    cprint.printCallingConv(print, decl) << fmt::nbsp;
    cprint.printVariadic(print, decl.isVariadic()) << fmt::nbsp;
    cprint.printExceptionSpec(print, decl) << fmt::nbsp;
    if (auto body = decl.getBody()) {
        guard::some some(print);
        guard::ctor _(print, "UserDefined");
        return cprint.printStmt(print, body);
    } else if (decl.isDefaulted()) {
        return print.output() << "(Some Defaulted)";
    } else {
        return print.none();
    }
}

// NOTE: We make implicit initialization explicit, and we resepect
// initialization order.
static ref<IdentifierInfo>
printIndirectFieldChain(const CXXConstructorDecl &ctor,
                        const IndirectFieldDecl &decl, CoqPrinter &print,
                        ClangPrinter &cprint) {
    auto fatal = [&](StringRef msg)
                     NORETURN { ::fatal(cprint, loc::of(decl), msg); };
    guard::list _(print);
    for (auto nd : decl.chain()) {
        if (auto id = nd->getIdentifier())
            return ref{*id};
        else if (auto fd = dyn_cast<FieldDecl>(nd)) {
            guard::tuple _(print);
            cprint.printFieldName(print, *fd, loc::of(decl)) << fmt::tuple_sep;
            printClassName(print, fd->getType(), cprint, loc::of(decl));
        } else
            fatal("non-field in indirect field chain");
        print.cons();
    }
    fatal("no named field in indirect field chain");
}

static fmt::Formatter &printInitPath(const CXXConstructorDecl &decl,
                                     const CXXCtorInitializer &init,
                                     CoqPrinter &print, ClangPrinter &cprint) {
    auto fatal = [&](StringRef msg)
                     NORETURN { ::fatal(cprint, loc::of(decl), msg); };
    if (init.isMemberInitializer()) {
        auto fd = init.getMember();
        always_assert(fd && "member initializer without member");
        guard::ctor _(print, "InitField", false);
        return cprint.printFieldName(print, *fd, loc::of(decl));
    } else if (init.isBaseInitializer()) {
        // TODO: [getBaseClass] might return
        guard::ctor _(print, "@InitBase", false);
        return printClassName(print, init.getBaseClass(), cprint,
                              loc::of(decl));
    } else if (init.isIndirectMemberInitializer()) {
        auto fd = init.getIndirectMember();
        if (!fd)
            fatal("indirect field initializer without field");
        guard::ctor _1(print, "@InitIndirect", false);
        auto id = printIndirectFieldChain(decl, *fd, print, cprint);
        print.output() << fmt::nbsp;
        guard::ctor _2(print, "field_name.Id", false);
        return print.str(id->getName());
    } else if (init.isDelegatingInitializer())
        return print.output() << "InitThis";
    else
        fatal("initializer path of unknown type");
}

static fmt::Formatter &printInitType(const CXXConstructorDecl &decl,
                                     const CXXCtorInitializer &init,
                                     CoqPrinter &print, ClangPrinter &cprint) {
    // TODO: Print Tunsupported and keep going
    auto fatal = [&](StringRef msg)
                     NORETURN { ::fatal(cprint, loc::of(decl), msg); };
    auto use_type = [&](const Type &type) -> auto & {
        return cprint.printType(print, type, loc::of(decl));
    };
    auto use_qualtype = [&](const QualType qt) -> auto & {
        return cprint.printQualType(print, qt, loc::of(decl));
    };
    if (auto fd = init.getMember())
        return use_qualtype(fd->getType());
    else if (auto fd = init.getIndirectMember())
        return use_qualtype(fd->getType());
    else if (auto type = init.getBaseClass())
        return use_type(*type);
    else if (init.isDelegatingInitializer()) {
        // getThisType() returns a pointer type.
        if (const auto *OPT =
                decl.getThisType().getTypePtr()->getAs<clang::PointerType>())
            return use_qualtype(OPT->getPointeeType());
        else
            fatal("[getThisType] on delegating initializer unexpectedly "
                  "returned a non-pointer type!");
    } else
        fatal("initializer not memeber, base class, or indirect");
}

static fmt::Formatter &printInitializer(const CXXConstructorDecl &ctor,
                                        const CXXCtorInitializer &init,
                                        CoqPrinter &print,
                                        ClangPrinter &cprint) {
    auto e = init.getInit();
    if (!e)
        fatal(cprint, loc::of(ctor), "initializer without expression");
    guard::ctor _(print, "Build_Initializer");
    printInitPath(ctor, init, print, cprint) << fmt::nbsp;
    return cprint.printExpr(print, e);
}

static fmt::Formatter &printInitializerList(CoqPrinter &print,
                                            const CXXConstructorDecl &decl,
                                            ClangPrinter &cprint) {
    // The order here is corrrect with respect to initalization order.
    return print.list(decl.inits(), [&](auto init) {
        if (init)
            printInitializer(decl, *init, print, cprint);
        else
            fatal(cprint, loc::of(decl), "null initializer");
    });
}

static fmt::Formatter &printConstructor(CoqPrinter &print,
                                        const CXXConstructorDecl &decl,
                                        ClangPrinter &cprint,
                                        const ASTContext &) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printConstructor", loc::of(decl));
    guard::ctor _(print, "Build_Ctor");
    printClassName(print, decl.getParent(), cprint, loc::of(decl)) << fmt::nbsp;
    printFunctionParams(print, decl, cprint) << fmt::nbsp;
    cprint.printCallingConv(print, decl) << fmt::nbsp;
    cprint.printVariadic(print, decl.isVariadic()) << fmt::nbsp;
    cprint.printExceptionSpec(print, decl) << fmt::nbsp;
    if (auto body = decl.getBody()) {
        guard::some s(print);
        guard::ctor ud(print, "UserDefined");
        guard::tuple _(print);
        printInitializerList(print, decl, cprint) << fmt::tuple_sep;
        return cprint.printStmt(print, body);
    } else {
        return print.none();
    }
}

static fmt::Formatter &printDestructor(CoqPrinter &print,
                                       const CXXDestructorDecl &decl,
                                       ClangPrinter &cprint,
                                       const ASTContext &) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printDestructor", loc::of(decl));

    guard::ctor _(print, "Build_Dtor");
    printClassName(print, decl.getParent(), cprint, loc::of(decl)) << fmt::nbsp;
    cprint.printCallingConv(print, decl) << fmt::nbsp;
    cprint.printExceptionSpec(print, decl) << fmt::nbsp;
    if (auto body = decl.getBody()) {
        guard::some some(print);
        guard::ctor _(print, "UserDefined");
        return cprint.printStmt(print, body);
    } else if (decl.isDefaulted()) {
        return print.output() << "(Some Defaulted)";
    } else {
        return print.none();
    }
}
} // namespace

static const DeclPrinter Dfunction("Dfunction", printFunction);
static const DeclPrinter Dmethod("Dmethod", printMethod);
static const DeclPrinter Dconstructor("Dconstructor", printConstructor);
static const DeclPrinter Ddestructor("Ddestructor", printDestructor);

// Variables
namespace {
static fmt::Formatter &printVar(CoqPrinter &print, const VarDecl &decl,
                                ClangPrinter &cprint, const ASTContext &) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printVar", loc::of(decl));

    // TODO handling of [constexpr] needs to be improved.
    cprint.printQualType(print, decl.getType(), loc::of(decl)) << fmt::nbsp;
    if (decl.hasExternalStorage()) {
        always_assert(!decl.getInit() &&
                      "external variable with an initializer");
        return print.output() << "global_init.Extern";
    } else if (dyn_cast<FunctionDecl>(decl.getDeclContext())) {
        return print.output() << "global_init.Delayed";
    } else if (auto e = decl.getInit()) {
        guard::ctor _(print, "global_init.Init");
        return cprint.printExpr(print, e);
    } else if (decl.getTemplateSpecializationKind() ==
               TemplateSpecializationKind::TSK_ImplicitInstantiation) {
        return print.output() << "global_init.ImplicitInit";
    } else
        return print.output() << "global_init.NoInit";
}
} // namespace
static const DeclPrinter Dvariable("Dvariable", printVar,
                                   DeclPrinter<VarDecl>::alwaysValid);

// Enumerations
namespace {

static fmt::Formatter &printEnum(CoqPrinter &print, const EnumDecl &decl,
                                 ClangPrinter &cprint, const ASTContext &) {
    auto loc = loc::of(decl);
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printEnum", loc);

    cprint.printQualType(print, decl.getIntegerType(), loc::of(decl))
        << fmt::nbsp;
    // TODO: Tidy up enumeration constants. We might emit their values
    // here as well, rather than as separate declarations.
    auto printConst = [&](EnumConstantDecl *c) {
        cprint.printUnqualifiedName(print, c, loc);
    };
    return print.list(decl.enumerators(), printConst);
}

/// Types that BRiCk represents using [Tchar_]
static bool isBRiCkCharacterType(const BuiltinType &type) {
    switch (type.getKind()) {
    case BuiltinType::Kind::Char_S:
    case BuiltinType::Kind::Char_U:
    case BuiltinType::Kind::WChar_S:
    case BuiltinType::Kind::WChar_U:
    case BuiltinType::Kind::Char16:
    case BuiltinType::Kind::Char8:
    case BuiltinType::Kind::Char32:
        return true;
    default:
        return false;
    }
}

static uint64_t toBRiCkCharacter(size_t bitsize, int64_t val) {
    return static_cast<uint64_t>(val) & ((1ull << bitsize) - 1);
}

struct EnumConst {
    struct UVal {
        // TODO: bool
        const enum Kind { Kint, Kchar } kind;
        const size_t bitsize;
        const llvm::APSInt val;
        UVal() = delete;
        UVal(llvm::APSInt v) : kind{Kint}, bitsize{0}, val{v} {}
        UVal(size_t sz, llvm::APSInt v) : kind{Kchar}, bitsize{sz}, val{v} {}

        fmt::Formatter &print(CoqPrinter &print) const {
            switch (kind) {
            case Kint: {
                return print.output() << "(inr " << val << ")";
            }
            case Kchar: {
                auto c = toBRiCkCharacter(bitsize, val.getExtValue());
                return print.output() << "(inl " << c << "%N)";
            }
            default:
                always_assert(false);
            }
        }
    };

    const EnumConstantDecl &ec;
    const EnumDecl &ed;
    const QualType ut;
    const UVal uv;

    EnumConst() = delete;
    EnumConst(const EnumConstantDecl &c, const EnumDecl &e, const QualType u,
              const UVal v)
        : ec{c}, ed{e}, ut{u}, uv{v} {}
};

static const EnumConstantDecl &enumConstToDecl(const EnumConst &c) {
    return c.ec;
}

static std::optional<EnumConst> crackEnumConst(const EnumConstantDecl &decl,
                                               CoqPrinter &print,
                                               ClangPrinter &cprint,
                                               const ASTContext &ctxt) {
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("crackEnumConst", loc::of(decl));
    auto fail = [&](const Twine &msg) NODISCARD {
        unsupported(cprint, loc::of(decl),
                    Twine("enumeration constant: ").concat(msg));
        return std::nullopt;
    };
    auto ed = dyn_cast_or_null<EnumDecl>(decl.getDeclContext());
    if (!ed)
        return fail("no enum");
    auto ut = ed->getIntegerType();
    if (ut.isNull())
        return fail("underlying type not integral");
    auto bt = ut.getTypePtr()->getAs<BuiltinType>();
    if (!bt) {
        /*
        TODO: With work here and in Coq, we might support constants in
        enumerations with dependent underlying types.
        */
        return fail("underlying integral type not a builtin");
    }
    if (isTemplate(*ed)) {
        /*
        TODO: With work here, we could print concrete enumeration
        constants in dependent scopes.
        */
        return fail("dependent scope");
    }

    auto ret = [&](auto uv) -> std::optional<EnumConst> {
        EnumConst c(decl, *ed, ut, uv);
        return {c};
    };
    auto v = decl.getInitVal();
    if (isBRiCkCharacterType(*bt))
        return ret(EnumConst::UVal(ctxt.getTypeSize(bt), v));
    else
        return ret(EnumConst::UVal(v));
}

static fmt::Formatter &printEnumConst(CoqPrinter &print, const EnumConst &c,
                                      ClangPrinter &cprint,
                                      const ASTContext &) {
    auto &[decl, ed, ut, uv] = c;
    if (ClangPrinter::debug && cprint.trace(Trace::Decl))
        cprint.trace("printEnumConst", loc::of(decl));

    cprint.printName(print, ed) << fmt::nbsp;
    cprint.printQualType(print, ut, loc::of(decl)) << fmt::nbsp;
    uv.print(print) << fmt::nbsp;
    if (auto e = decl.getInitExpr()) {
        guard::some _(print);
        cprint.printExpr(print, e);
    } else
        print.none();
    return print.output();
}
} // namespace

static const DeclPrinter Denum("Denum", printEnum,
                               DeclPrinter<EnumDecl>::alwaysValid);
static const DeclPrinter Denum_constant("Denum_constant", printEnumConst,
                                        DeclPrinter<EnumConst>::alwaysValid);

// Static asserts
namespace {
static const StringLiteral *staticAssertMessage(const StaticAssertDecl &decl) {
#if CLANG_VERSION_MAJOR <= 16
    return decl.getMessage();
#else
    return dyn_cast_or_null<StringLiteral>(decl.getMessage());
#endif
}
} // namespace

class PrintDecl
    : public ConstDeclVisitorArgs<PrintDecl, bool, CoqPrinter &, ClangPrinter &,
                                  const ASTContext &> {
private:
    PrintDecl() = default;

public:
    static PrintDecl printer;

    bool VisitDecl(const Decl *decl, CoqPrinter &print, ClangPrinter &cprint,
                   const ASTContext &) {
        unsupported(cprint, loc::of(decl), "declaration");
        return false;
    }

#define IGNORE(D)                                                              \
    bool Visit##D(const D *, CoqPrinter &, ClangPrinter &,                     \
                  const ASTContext &) {                                        \
        return false;                                                          \
    }

    IGNORE(EmptyDecl)
    IGNORE(FriendDecl)
    IGNORE(IndirectFieldDecl)
    IGNORE(LinkageSpecDecl)
    IGNORE(UsingDecl)
    IGNORE(UsingDirectiveDecl)
    IGNORE(UsingShadowDecl)

#undef IGNORE

    // Variables

    bool VisitVarDecl(const VarDecl *decl, CoqPrinter &print,
                      ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitVarDecl", loc::of(decl));

        return Dvariable.print(*decl, print, cprint, ctxt);
    }

    // Functions

    bool VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print,
                           ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitFunctionDecl", loc::of(decl));
        return Dfunction.print(*decl, print, cprint, ctxt);
    }

    bool VisitCXXMethodDecl(const CXXMethodDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitCXXMethodDecl", loc::of(decl));
        return Dmethod.print(*decl, print, cprint, ctxt);
    }

    bool VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitCXXConstructorDecl", loc::of(decl));
        return Dconstructor.print(*decl, print, cprint, ctxt);
    }

    bool VisitCXXDestructorDecl(const CXXDestructorDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitCXXDestructorDecl", loc::of(decl));
        return Ddestructor.print(*decl, print, cprint, ctxt);
    }

    // Type aliases

    bool VisitTypedefNameDecl(const TypedefNameDecl *decl, CoqPrinter &print,
                              ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitTypedefNameDecl", loc::of(decl));

        if (cprint.printTypedefs()) {
            // TODO: Adjust `type_table_le` and the template logic.
            return Dtypedef.print(*decl, print, cprint, ctxt);
        } else {
            return false;
        }
    }

    // Types

    template <typename D>
    bool printType(const DeclPrinter<D> &printer, const D &decl,
                   CoqPrinter &print, ClangPrinter &cprint,
                   const ASTContext &ctxt) {
        if (decl.isCompleteDefinition())
            return printer.print(decl, print, cprint, ctxt);
        else
            return Dtype.print(decl, print, cprint, ctxt);
    }

    bool VisitUnionDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                        ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitUnionDecl", loc::of(decl));
        return printType(Dunion, *decl, print, cprint, ctxt);
    }

    bool VisitStructDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                         ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitStructDecl", loc::of(decl));
        return printType(Dstruct, *decl, print, cprint, ctxt);
    }

    bool VisitCXXRecordDecl(const CXXRecordDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitCXXRecordDecl", loc::of(decl));
        if (decl->isStruct() or decl->isClass()) {
            return VisitStructDecl(decl, print, cprint, ctxt);
        } else if (decl->isUnion()) {
            return VisitUnionDecl(decl, print, cprint, ctxt);
        } else {
            std::string msg;
            llvm::raw_string_ostream os{msg};
            os << "CXXRecord with tag kind " << decl->getKindName();
            unsupported(cprint, loc::of(decl), msg);
            return false;
        }
    }

    // Declarations that are only indirectly templated

    bool VisitEnumDecl(const EnumDecl *decl, CoqPrinter &print,
                       ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitEnumDecl", loc::of(decl));

        // The isCompleteDefinition in printType seems inadequate for
        // enumerations.
        if (decl->getIntegerType().isNull()) {
            if (!decl->getIdentifier()) {
                unsupported(cprint, loc::of(decl),
                            "anonymous forward declaration");
                return false;
            } else
                return Dtype.print(*decl, print, cprint, ctxt);
        } else
            return Denum.print(*decl, print, cprint, ctxt);
    }

    bool VisitEnumConstantDecl(const EnumConstantDecl *decl, CoqPrinter &print,
                               ClangPrinter &cprint, const ASTContext &ctxt) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitEnumConstantDecl", loc::of(decl));
        if (auto c = crackEnumConst(*decl, print, cprint, ctxt))
            return Denum_constant.print<EnumConstantDecl, enumConstToDecl>(
                *c, print, cprint, ctxt);
        else
            return false;
    }

    bool VisitStaticAssertDecl(const StaticAssertDecl *decl, CoqPrinter &print,
                               ClangPrinter &cprint, const ASTContext &) {
        if (ClangPrinter::debug && cprint.trace(Trace::Decl))
            cprint.trace("VisitStaticAssertDecl", loc::of(decl));
        /*
        TODO: There _might_ be a case for supporting templated static
        asserts (e.g., when they have complicated proofs based mostly on
        templated code)).
        */
        if (auto e = decl->getAssertExpr()) {
            guard::ctor _(print, "Dstatic_assert");
            /*
            TODO: We insist on a StringLiteral message (the historical
            type). Consider dropping that requirement and using
            Stmt::printPretty.
            */
            if (auto msg = staticAssertMessage(*decl)) {
                guard::some _(print);
                print.str(msg->getString());
            } else {
                print.none();
            }
            print.output() << fmt::nbsp;
            cprint.printExpr(print, e);
            return true;
        } else {
            unsupported(cprint, loc::of(decl),
                        "static assert without expression");
            return false;
        }
    }
};

PrintDecl PrintDecl::printer;

bool ClangPrinter::printDecl(CoqPrinter &print, const clang::Decl *decl) {
    if (trace(Trace::Decl))
        trace("printDecl", loc::of(decl));
    return PrintDecl::printer.Visit(decl, print, *this, *context_);
}
