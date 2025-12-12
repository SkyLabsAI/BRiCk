/*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Logging.hpp"
#include "TypeVisitorWithArgs.h"
#include "config.hpp"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/Type.h"
#include <Formatter.hpp>

using namespace clang;
using namespace fmt;

[[noreturn]] static void fatal(CoqPrinter &print, ClangPrinter &cprint,
                               loc::loc loc, StringRef msg) {
    cprint.error_prefix(logging::fatal(), loc) << "error: " << msg << "\n";
    cprint.debug_dump(loc);
    print.die();
}

static void unsupported(CoqPrinter &print, ClangPrinter &cprint, loc::loc loc,
                        const Twine &msg, bool well_known = false) {
    if (!well_known || ClangPrinter::warn_well_known) {
        cprint.error_prefix(logging::unsupported(), loc)
            << "warning: unsupported " << msg << "\n";
        cprint.debug_dump(loc);
    }
    guard::ctor _(print, "Tunsupported", false);
    {
        std::string coqmsg;
        llvm::raw_string_ostream os{coqmsg};
        os << loc::describe(loc, cprint.getContext());
        print.str(coqmsg);
    }
}

static void unsupported_type(CoqPrinter &print, ClangPrinter &cprint,
                             const Type *type, bool well_known = false) {
    unsupported(print, cprint, loc::of(type), "type", well_known);
}

class PrintType
    : public TypeVisitor<PrintType, void, CoqPrinter &, ClangPrinter &> {
private:
    PrintType() = default;

public:
    static PrintType printer;

    void Visit(const Type *type, CoqPrinter &print, ClangPrinter &cprint) {
        if (not print.reference(type))
            TypeVisitor<PrintType, void, CoqPrinter &, ClangPrinter &>::Visit(
                type, print, cprint);
    }

    void VisitType(const Type *type, CoqPrinter &print, ClangPrinter &cprint) {
        unsupported_type(print, cprint, type);
    }

#define IGNORE(T)                                                              \
    void Visit##T(const T *type, CoqPrinter &print, ClangPrinter &cprint) {    \
        unsupported_type(print, cprint, type, /*well_known*/ true);            \
    }

    // Several of these are template TODOs

    IGNORE(BlockPointerType)
    IGNORE(PackExpansionType)

    void VisitAttributedType(const AttributedType *type, CoqPrinter &print,
                             ClangPrinter &cprint) {
        cprint.printQualType(print, type->getModifiedType(), loc::of(type));
    }

    static const char *getTransformName(UnaryTransformType::UTTKind k) {
        switch (k) {
#define TRANSFORM_TYPE_TRAIT_DEF(Enum, Str)                                    \
    case UnaryTransformType::UTTKind::Enum:                                    \
        return #Str;
#include "clang/Basic/TransformTypeTraits.def"
#undef TRANSFORM_TYPE_TRAIT_DEF
        default:
            return "unknown";
        }
    }

    void VisitDependentSizedArrayType(const DependentSizedArrayType *type,
                                      CoqPrinter &print, ClangPrinter &cprint) {
        guard::ctor _{print, "Tvariable_array"};
        cprint.printQualType(print, type->getElementType(), loc::of(type))
            << fmt::nbsp;
        cprint.printExpr(print, type->getSizeExpr());
    }

    void VisitDependentNameType(const DependentNameType *type,
                                CoqPrinter &print, ClangPrinter &cprint) {
        if (type->isSugared()) {
            cprint.printQualType(print, type->desugar(), loc::of(type));
        } else {
            guard::ctor _{print, "Tnamed"};
            cprint.printUnresolvedName(print, type->getQualifier(),
                                       DeclarationName{type->getIdentifier()},
                                       ArrayRef<TemplateArgument>{},
                                       loc::of(type));
            // type->dump();
            //  unsupported_type(print, cprint, type, true);
        }
    }
    void VisitUnaryTransformType(const UnaryTransformType *type,
                                 CoqPrinter &print, ClangPrinter &cprint) {
        if (type->isDependentType()) {
            // TODO: templates
            unsupported_type(print, cprint, type,
                             /*well_known*/ true);
            return;
        }

        switch (auto kind = type->getUTTKind()) {
        case UnaryTransformType::UTTKind::EnumUnderlyingType:

            // An `__underlying_type (type)` expression
            // where `type` is a scoped enumeration type.
            //
            // See:
            //
            // https://en.cppreference.com/w/cpp/utility/to_underlying
            // https://gcc.gnu.org/onlinedocs/gcc-11.1.0/gcc/Type-Traits.html

            print.ctor("@Tunderlying", false);
            break;

        default:
            print.ctor("@Tunary_xform", false);

            print.str(getTransformName(kind));
            print.output() << "%bs" << fmt::nbsp;
            break;
        }

        // The argument
        cprint.printQualType(print, type->getBaseType(), loc::of(type));
        print.output() << fmt::nbsp;

        // The result (can be null if dependent)
        cprint.printQualType(print, type->getUnderlyingType(), loc::of(type));
        print.end_ctor();
    }

    void VisitAutoType(const AutoType *type, CoqPrinter &print,
                       ClangPrinter &cprint) {
        if (type->isDeduced() && !type->isDependentType()) {
            cprint.printQualType(print, type->getDeducedType(), loc::of(type));
        } else {
            if (print.templates())
                print.output() << "Tauto";
            else
                unsupported_type(print, cprint, type, /*well_known*/ true);
        }
    }

    void VisitDeducedType(const DeducedType *type, CoqPrinter &print,
                          ClangPrinter &cprint) {
        if (type->isDeduced()) {
            auto ty = type->getDeducedType();
            if (ty.isNull()) {
                print.output() << "Tauto";
            } else {
                cprint.printQualType(print, ty, loc::of(type));
            }
        } else {
            unsupported_type(print, cprint, type);
        }
    }

    void VisitTemplateTypeParmType(const TemplateTypeParmType *type,
                                   CoqPrinter &print, ClangPrinter &cprint) {
        cprint.printTypeTemplateParam(print, type->getDepth(), type->getIndex(),
                                      loc::of(type));
    }

    void VisitEnumType(const EnumType *type, CoqPrinter &print,
                       ClangPrinter &cprint) {
        auto ed = type->getDecl()->getCanonicalDecl();
        print.ctor("Tenum", false);
        cprint.printName(print, ed, loc::of(type));
        print.end_ctor();
    }

    void VisitRecordType(const RecordType *type, CoqPrinter &print,
                         ClangPrinter &cprint) {
        print.ctor("Tnamed", false);
        cprint.printName(print, type->getDecl(), loc::of(type));
        print.end_ctor();
    }

    void VisitParenType(const ParenType *type, CoqPrinter &print,
                        ClangPrinter &cprint) {
        cprint.printQualType(print, type->getInnerType(), loc::of(type));
    }

    void VisitBuiltinType(const BuiltinType *type, CoqPrinter &print,
                          ClangPrinter &cprint) {
        switch (type->getKind()) {
#define CASE(x, str)                                                           \
    case BuiltinType::Kind::x:                                                 \
        print.output() << str;                                                 \
        break;
            CASE(Bool, "Tbool")
            CASE(Void, "Tvoid")
            CASE(NullPtr, "Tnullptr")
            CASE(SChar, "Tschar")
            CASE(UChar, "Tuchar")
            // Both [Char_S] and [Char_U] are representations of the C++ 'char'
            // type, but are used depending on the platform's choice of whether
            // 'char' is signed or not.
            CASE(Char_S, "Tchar")
            CASE(Char_U, "Tchar")
            CASE(WChar_S, "Twchar")
            CASE(WChar_U, "Twchar")
            CASE(Char16, "Tchar16")
            CASE(Char32, "Tchar32")
            CASE(Char8, "Tchar8")
            CASE(Short, "Tshort")
            CASE(UShort, "Tushort")
            CASE(Int, "Tint")
            CASE(UInt, "Tuint")
            CASE(Long, "Tlong")
            CASE(ULong, "Tulong")
            CASE(LongLong, "Tlonglong")
            CASE(ULongLong, "Tulonglong")
            CASE(Int128, "Tint128_t")
            CASE(UInt128, "Tuint128_t")
            CASE(Float, "Tfloat")
            CASE(Double, "Tdouble")
            CASE(LongDouble, "Tlongdouble")
            CASE(Float16, "Tfloat16")
            CASE(Float128, "Tfloat128")
#undef CASE
        case BuiltinType::Kind::Dependent:
            if (print.templates()) {
                print.output() << "Tauto";
            } else if (false) {
                // We prefer to keep going with Tunsupported
                using namespace logging;
                fatal()
                    << "Clang failed to resolve type, due to earlier errors or "
                       "unresolved templates\n"
                    << "Try fixing earlier errors, or ask for help. Aborting\n";
                die();
            } else
                unsupported_type(print, cprint, type, /*well_known*/ true);
            break;

        default:
            if (type->isSizelessBuiltinType()) {
                // TODO: This seems a bit random. Do we need
                // another type constructor?
                print.output() << fmt::lparen << "Tarch None \""
                               << type->getNameAsCString(
                                      cprint.getContext().getPrintingPolicy())
                               << "\"" << fmt::rparen;
                break;
            } else {
                unsupported(print, cprint, loc::of(type),
                            type->getNameAsCString(
                                cprint.getContext().getPrintingPolicy()));
            }
        }
    }

    void VisitLValueReferenceType(const LValueReferenceType *type,
                                  CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Tref", false);
        cprint.printQualType(print, type->getPointeeType(), loc::of(type));
        print.end_ctor();
    }

    void VisitRValueReferenceType(const RValueReferenceType *type,
                                  CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Trv_ref", false);
        cprint.printQualType(print, type->getPointeeType(), loc::of(type));
        print.end_ctor();
    }

    void VisitPointerType(const PointerType *type, CoqPrinter &print,
                          ClangPrinter &cprint) {
        print.ctor("Tptr", false);
        cprint.printQualType(print, type->getPointeeType(), loc::of(type));
        print.end_ctor();
    }

    void VisitTypedefType(const TypedefType *type, CoqPrinter &print,
                          ClangPrinter &cprint) {
        if (PRINT_ALIAS) {
            print.ctor("@Talias", false);
            cprint.printName(print, type->getDecl(), loc::of(type));
            cprint.printQualType(
                print, type->getDecl()->getCanonicalDecl()->getUnderlyingType(),
                loc::of(type));
            print.end_ctor();
        } else {
            cprint.printQualType(
                print, type->getDecl()->getCanonicalDecl()->getUnderlyingType(),
                loc::of(type));
        }
    }

    void VisitFunctionProtoType(const FunctionProtoType *type,
                                CoqPrinter &print, ClangPrinter &cprint) {
        guard::ctor _1(print, "Tfunction");
        print.output() << (print.templates() ? "Mtype" : "type") << fmt::nbsp;
        cprint.printCallingConv(print, type->getCallConv(), loc::of(type))
            << fmt::nbsp;
        cprint.printVariadic(print, type->isVariadic()) << fmt::nbsp;
        cprint.printQualType(print, type->getReturnType(), loc::of(type))
            << fmt::nbsp;
        print.list(type->param_types(), [&](QualType i) {
            // Note that we do not need to print top-level qualifiers on
            // argument types
            cprint.printType(print, i.getTypePtr(), loc::of(type));
        });
    }

    void VisitElaboratedType(const ElaboratedType *type, CoqPrinter &print,
                             ClangPrinter &cprint) {
        if (type->getNamedType().isNull()) {
            guard::ctor _{print, "Tunsupported"};
            print.str("elaborated type w/ null");
        } else {
            cprint.printQualType(print, type->getNamedType(), loc::of(type));
        }
    }

    void VisitConstantArrayType(const ConstantArrayType *type,
                                CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Tarray", false);
        cprint.printQualType(print, type->getElementType(), loc::of(type));
        print.output() << fmt::nbsp << type->getSize().getLimitedValue();
        print.end_ctor();
    }

    void VisitSubstTemplateTypeParmType(const SubstTemplateTypeParmType *type,
                                        CoqPrinter &print,
                                        ClangPrinter &cprint) {
        cprint.printQualType(print, type->getReplacementType(), loc::of(type));
    }

    void VisitIncompleteArrayType(const IncompleteArrayType *type,
                                  CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Tincomplete_array", false);
        cprint.printQualType(print, type->getElementType(), loc::of(type));
        print.end_ctor();
    }

    void VisitVariableArrayType(const VariableArrayType *type,
                                CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Tvariable_array", false);
        cprint.printQualType(print, type->getElementType(), loc::of(type));
        print.output() << fmt::nbsp;
        cprint.printExpr(print, type->getSizeExpr());
        print.end_ctor();
    }

    void VisitDecayedType(const DecayedType *type, CoqPrinter &print,
                          ClangPrinter &cprint) {
        print.ctor("Tdecay_type", false);
        cprint.printQualType(print, type->getOriginalType(), loc::of(type));
        print.output() << fmt::nbsp;
        cprint.printQualType(print, type->getAdjustedType(), loc::of(type));
        print.end_ctor();
    }

    fmt::Formatter &printRiskyTypeComment(CoqPrinter &print, const Type *type,
                                          ClangPrinter &cprint) {
        if (ClangPrinter::debug && cprint.trace(Trace::Type)) {
            auto loc = loc::of(type);
            cprint.trace("printRiskyTypeComment", loc);
            std::string cmt;
            llvm::raw_string_ostream os{cmt};
            auto &context = cprint.getContext();
            os << "risky type";
            if (loc::can_describe(loc))
                os << ": " << loc::describe(loc, context);
            cprint.error_prefix(logging::unsupported(), loc)
                << "warning: " << cmt << "\n";
            return print.cmt(cmt);
        } else
            return print.output();
    }

    void VisitTemplateSpecializationType(const TemplateSpecializationType *type,
                                         CoqPrinter &print,
                                         ClangPrinter &cprint) {
        auto unsupported = [&]() {
            unsupported_type(print, cprint, type, /*well_known*/ true);
        };
        if (type->isTypeAlias()) {
            cprint.printQualType(print, type->getAliasedType(), loc::of(type));
        } else if (type->isSugared()) {
            cprint.printQualType(print, type->desugar(), loc::of(type));
        } else {

            /*
            TODO: See the comment in VisitInjectedClassNameType. We
            probably have to print the entire specialized scope, and not
            just this type.
            */
            auto temp = type->getTemplateName().getAsTemplateDecl();
            auto args = type->template_arguments();
            if (temp) {
                printRiskyTypeComment(print, type, cprint) << fmt::nbsp;
                guard::ctor _1(print, "Tnamed", false);
                guard::ctor _2(print, "Ninst (* TemplateSpecializationType *)",
                               false);
                cprint.printName(print, *temp) << fmt::nbsp;
                cprint.printTemplateArgumentList(print, args);
            } else
                unsupported();
        }
    }

    void VisitDecltypeType(const DecltypeType *type, CoqPrinter &print,
                           ClangPrinter &cprint) {
        if (type->isSugared()) {
            // The guard ensure the type visitor terminates.
            cprint.printQualType(print, type->desugar(), loc::of(type));
        } else if (print.templates()) {
            auto which = isa<DeclRefExpr>(type->getUnderlyingExpr())
                             ? "Texprtype"
                             : "Tdecltype";
            guard::ctor _(print, which, false);
            cprint.printExpr(print, type->getUnderlyingExpr());
        } else
            unsupported_type(print, cprint, type, /*well_known*/ true);
    }

    void VisitTypeOfExprType(const TypeOfExprType *type, CoqPrinter &print,
                             ClangPrinter &cprint) {
        if (type->isSugared()) {
            // The guard ensure the type visitor terminates.
            cprint.printQualType(print, type->desugar(), loc::of(type));
        } else if (print.templates()) {
            /*
            TODO: Test whether we need printQualTypeOption here.
            */
            cprint.printQualType(print, type->getUnderlyingExpr()->getType(),
                                 loc::of(type));
        } else {
            unsupported_type(print, cprint, type);
        }
    }

    void VisitInjectedClassNameType(const InjectedClassNameType *type,
                                    CoqPrinter &print, ClangPrinter &cprint) {
        // PrintingPolicy p;
        // unsupported_type(print, cprint, type);

        // std::cerr << "VisitInjectedClassNameType: "
        // 		  // << type->getTemplateName()
        // 		  << " - " << type->getTemplateName(p).<< "\n";
        always_assert(print.templates());

        if (auto decl = type->getDecl()) {
            /*
            TODO: We probably have to make this smarter.

            Cobble up some examples and decide if there is a problem
            with always synthesizing arguments.

            Example idea: Print the type of a template in a
            (partially) specialized scope.

            Algorithm idea: We probably have have to walk up the
            declaration context chain, collecting a list of
            `TemplateArgument + TemplateParameter` entries, and
            synthesizing only those arguments that are "missing".
            */
            printRiskyTypeComment(print, type, cprint) << fmt::nbsp;
            guard::ctor _1(print, "Tnamed", false);
            // guard::ctor _2(print, "Ninst{InjectedClassNameType}", false);
            cprint.printName(print, *decl) << fmt::nbsp;
            // cprint.printTemplateParameters(print, *decl, true);
        } else {
            unsupported(print, cprint, loc::of(type),
                        "injected class name without declaration");
        }
    }

    void VisitMemberPointerType(const MemberPointerType *type,
                                CoqPrinter &print, ClangPrinter &cprint) {
        print.ctor("Tmember_pointer", false);
        cprint.printType(print, type->getClass(), loc::of(type));
        print.output() << fmt::nbsp;
        cprint.printQualType(print, type->getPointeeType(), loc::of(type));
        print.end_ctor();
    }

    void VisitMacroQualifiedType(const MacroQualifiedType *type,
                                 CoqPrinter &print, ClangPrinter &cprint) {
        cprint.printQualType(print, type->getModifiedType(), loc::of(type));
    }

    void VisitUsingType(const UsingType *type, CoqPrinter &print,
                        ClangPrinter &cprint) {
        always_assert(type->isSugared());
        cprint.printQualType(print, type->getUnderlyingType(), loc::of(type));
    }
};

PrintType PrintType::printer;

fmt::Formatter &ClangPrinter::printType(CoqPrinter &print, const Type &type,
                                        loc::loc loc) {
    if (trace(Trace::Type))
        trace("printType", loc::refine(loc, type));
    __attribute__((unused)) auto depth = print.output().get_depth();
    PrintType::printer.Visit(&type, print, *this);
    always_assert(depth == print.output().get_depth());
    return print.output();
}

fmt::Formatter &ClangPrinter::printType(CoqPrinter &print,
                                        const clang::Type *type, loc::loc loc) {
    if (type)
        return printType(print, *type, loc);
    else
        fatal(print, *this, loc, "unexpected null type in printType");
}

fmt::Formatter &ClangPrinter::printQualType(CoqPrinter &print,
                                            const QualType &qt, loc::loc loc) {
    if (trace(Trace::Type))
        trace("printQualType", loc::of(qt));
    if (auto p = qt.getTypePtrOrNull()) {
        if (qt.isLocalConstQualified()) {
            if (qt.isVolatileQualified()) {
                print.ctor("Qconst_volatile", false);
            } else {
                print.ctor("Qconst", false);
            }
            printType(print, *p, loc);
            print.end_ctor();
        } else {
            if (qt.isLocalVolatileQualified()) {
                print.ctor("Qvolatile", false);
                printType(print, *p, loc);
                print.end_ctor();
            } else {
                printType(print, *p, loc);
            }
        }
        return print.output();
    } else
        fatal(print, *this, loc, "unexpected null type in printQualType");
}

fmt::Formatter &ClangPrinter::printQualTypeOption(CoqPrinter &print,
                                                  const QualType &qt,
                                                  loc::loc loc) {
    auto t = qt.getTypePtrOrNull();
    if (t == nullptr || t->isDependentType()) {
        return print.none();
    } else {
        print.some();
        printQualType(print, qt, loc);
        return print.end_ctor();
    }
}

fmt::Formatter &ClangPrinter::printQualifier(CoqPrinter &print,
                                             const QualType &qt) const {
    return printQualifier(print, qt.isConstQualified(),
                          qt.isVolatileQualified());
}

fmt::Formatter &ClangPrinter::printQualifier(CoqPrinter &print, bool is_const,
                                             bool is_volatile) const {
    if (is_const) {
        if (is_volatile) {
            return print.output() << "QCV";
        } else {
            return print.output() << "QC";
        }
    } else {
        if (is_volatile) {
            return print.output() << "QV";
        } else {
            return print.output() << "QM";
        }
    }
}
