/*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "DefaultTemplateAlias.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Location.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Type.h>
#include <clang/Basic/Version.inc>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <functional>
#include <optional>
#include <vector>

using namespace clang;

namespace {

static std::string getTemplateParamName(const NamedDecl &decl) {
    if (auto id = decl.getIdentifier())
        return id->getName().str();

    auto position_name = [](auto &param, StringRef prefix) {
        return (prefix + Twine(param.getDepth()) + "_" +
                Twine(param.getIndex()))
            .str();
    };

    if (auto param = dyn_cast<TemplateTypeParmDecl>(&decl))
        return position_name(*param, "__type_");
    if (auto param = dyn_cast<NonTypeTemplateParmDecl>(&decl))
        return position_name(*param, "__value_");
    if (auto param = dyn_cast<TemplateTemplateParmDecl>(&decl))
        return position_name(*param, "__template_");

    return "__template_param";
}

static fmt::Formatter &printTemplateParamArg(CoqPrinter &print,
                                             const NamedDecl *param,
                                             ClangPrinter &cprint) {
    return cprint.printTemplateArg(print, param, loc::of(param));
}

static fmt::Formatter &printTemplateParam(CoqPrinter &print,
                                          const NamedDecl *param,
                                          ClangPrinter &cprint) {
    return cprint.printTemplateParam(print, param, loc::of(param));
}

static fmt::Formatter &printId(CoqPrinter &print, StringRef name) {
    guard::ctor _{print, "Nid", false};
    return print.str(name);
}

static fmt::Formatter &printTemplateBaseName(CoqPrinter &print,
                                             const NamedDecl &decl,
                                             ClangPrinter &cprint) {
    auto ctx = decl.getDeclContext();
    while (ctx && !ctx->isTranslationUnit() && !isa<NamedDecl>(ctx))
        ctx = ctx->getParent();

    if (!ctx || ctx->isTranslationUnit()) {
        guard::ctor _{print, "Nglobal", false};
        return printId(print, decl.getName());
    }

    guard::ctor _{print, "Nscoped", false};
    cprint.printName(print, *cast<NamedDecl>(Decl::castFromDeclContext(ctx)))
        << fmt::nbsp;
    return printId(print, decl.getName());
}

static fmt::Formatter &printTemplateNameWithArgs(
    CoqPrinter &print, const NamedDecl &decl, ClangPrinter &cprint,
    llvm::function_ref<void()> print_args) {
    guard::ctor _{print, "Ninst", false};
    printTemplateBaseName(print, decl, cprint) << fmt::nbsp;
    print_args();
    return print.output();
}

static fmt::Formatter &
printDefaultAliasKey(CoqPrinter &print, const NamedDecl &decl,
                     ArrayRef<const NamedDecl *> params, unsigned keep,
                     ClangPrinter &cprint) {
    return printTemplateNameWithArgs(print, decl, cprint, [&]() {
        print.list(params.take_front(keep), [&](const NamedDecl *param) {
            printTemplateParamArg(print, param, cprint);
        });
    });
}

static const Expr *ignoreValueDefaultCasts(const Expr *expr) {
    return expr ? expr->IgnoreParenImpCasts() : nullptr;
}

static const NonTypeTemplateParmDecl *
getReferencedValueParam(const Expr *expr) {
    expr = ignoreValueDefaultCasts(expr);
    if (auto *subst = dyn_cast_or_null<SubstNonTypeTemplateParmExpr>(expr))
        expr = ignoreValueDefaultCasts(subst->getReplacement());
    if (auto *ref = dyn_cast_or_null<DeclRefExpr>(expr))
        return dyn_cast<NonTypeTemplateParmDecl>(ref->getDecl());
    return nullptr;
}

static const TemplateTypeParmDecl *
asTemplateTypeParmDecl(const TemplateTypeParmDecl *decl) {
    return decl;
}

static const TemplateTypeParmDecl *
asTemplateTypeParmDecl(const TemplateTypeParmType *type) {
    return type ? type->getDecl() : nullptr;
}

static const TemplateTypeParmDecl *
getReferencedTypeParam(QualType qt) {
    auto *type = qt.getTypePtrOrNull();
    if (!type)
        return nullptr;

    if (auto *type_param = dyn_cast<TemplateTypeParmType>(type))
        return type_param->getDecl();

    if (auto *subst = dyn_cast<SubstTemplateTypeParmType>(type)) {
        if (auto *replacement =
                getReferencedTypeParam(subst->getReplacementType()))
            return replacement;
        return asTemplateTypeParmDecl(subst->getReplacedParameter());
    }

    if (auto *paren = dyn_cast<ParenType>(type))
        return getReferencedTypeParam(paren->getInnerType());

    if (auto *attr = dyn_cast<AttributedType>(type))
        return getReferencedTypeParam(attr->getModifiedType());

    if (auto *adjusted = dyn_cast<AdjustedType>(type))
        return getReferencedTypeParam(adjusted->getOriginalType());

    if (auto *type_param = type->getAs<TemplateTypeParmType>())
        return type_param->getDecl();

    return nullptr;
}

static const TemplateTypeParmDecl *
getDirectReferencedTypeParam(QualType qt) {
    if (qt.hasLocalQualifiers())
        return nullptr;

    auto *type = qt.getTypePtrOrNull();
    if (!type)
        return nullptr;

    if (auto *type_param = dyn_cast<TemplateTypeParmType>(type))
        return type_param->getDecl();

    if (auto *subst = dyn_cast<SubstTemplateTypeParmType>(type)) {
        if (auto *replacement =
                getDirectReferencedTypeParam(subst->getReplacementType()))
            return replacement;
        return asTemplateTypeParmDecl(subst->getReplacedParameter());
    }

    if (auto *paren = dyn_cast<ParenType>(type))
        return getDirectReferencedTypeParam(paren->getInnerType());

    if (auto *attr = dyn_cast<AttributedType>(type))
        return getDirectReferencedTypeParam(attr->getModifiedType());

    return nullptr;
}

static bool isSupportedValueDefaultExpr(const Expr *expr) {
    expr = ignoreValueDefaultCasts(expr);
    if (!expr)
        return false;
    if (isa<IntegerLiteral>(expr) || isa<CharacterLiteral>(expr) ||
        isa<CXXBoolLiteralExpr>(expr))
        return true;
    return getReferencedValueParam(expr) != nullptr;
}

static QualType getTemplateTypeDefault(const TemplateTypeParmDecl *param) {
#if CLANG_VERSION_MAJOR >= 19
    return param->getDefaultArgument().getArgument().getAsType();
#else
    return param->getDefaultArgument();
#endif
}

static const Expr *getTemplateValueDefault(const NonTypeTemplateParmDecl *param) {
#if CLANG_VERSION_MAJOR >= 19
    auto &def = param->getDefaultArgument();
    switch (def.getArgument().getKind()) {
    case TemplateArgument::Expression:
        return def.getSourceExpression();
    case TemplateArgument::Integral:
        return def.getSourceIntegralExpression();
    case TemplateArgument::Declaration:
        return def.getSourceDeclExpression();
    case TemplateArgument::NullPtr:
        return def.getSourceNullPtrExpression();
    default:
        return nullptr;
    }
#else
    return param->getDefaultArgument();
#endif
}

static bool sameTemplateTypeParam(const TemplateTypeParmDecl *lhs,
                                  const NamedDecl *rhs) {
    auto *rhs_type = dyn_cast<TemplateTypeParmDecl>(rhs);
    return lhs == rhs_type ||
           (rhs_type && lhs->getDepth() == rhs_type->getDepth() &&
            lhs->getIndex() == rhs_type->getIndex());
}

static bool sameTemplateValueParam(const NonTypeTemplateParmDecl *lhs,
                                   const NamedDecl *rhs) {
    auto *rhs_value = dyn_cast<NonTypeTemplateParmDecl>(rhs);
    return lhs == rhs_value ||
           (rhs_value && lhs->getDepth() == rhs_value->getDepth() &&
            lhs->getIndex() == rhs_value->getIndex());
}

enum class ArgumentKind { Type, Value };

struct Argument {
    ArgumentKind kind;
    std::optional<unsigned> param_ref;
    QualType default_type;
    const Expr *default_expr = nullptr;
};

struct ExprSubstitution {
    std::optional<unsigned> param_ref;
    const Expr *expr = nullptr;
};

static std::optional<unsigned>
findTypeParam(const TemplateTypeParmDecl *needle,
              ArrayRef<const NamedDecl *> params, unsigned limit) {
    for (unsigned j = 0; j < limit; ++j)
        if (sameTemplateTypeParam(needle, params[j]))
            return j;
    return std::nullopt;
}

static std::optional<unsigned>
findValueParam(const NonTypeTemplateParmDecl *needle,
               ArrayRef<const NamedDecl *> params, unsigned limit) {
    for (unsigned j = 0; j < limit; ++j)
        if (sameTemplateValueParam(needle, params[j]))
            return j;
    return std::nullopt;
}

static QualType templateParamType(ASTContext &context, const NamedDecl *param) {
    auto *type_param = cast<TemplateTypeParmDecl>(param);
    return context.getTemplateTypeParmType(
        type_param->getDepth(), type_param->getIndex(),
        type_param->isParameterPack(),
        const_cast<TemplateTypeParmDecl *>(type_param));
}

static QualType substDefaultType(ASTContext &context, QualType qt,
                                 unsigned limit,
                                 ArrayRef<const NamedDecl *> params,
                                 ArrayRef<Argument> args) {
    auto *type = qt.getTypePtrOrNull();
    if (!type)
        return qt;

    auto subst_with_local_qualifiers = [&](QualType inner) {
        auto result = substDefaultType(context, inner, limit, params, args);
        return context.getQualifiedType(result, qt.getLocalQualifiers());
    };

    QualType unqualified = qt.getLocalQualifiers().empty()
                               ? qt
                               : qt.getLocalUnqualifiedType();

    if (unqualified != qt)
        return subst_with_local_qualifiers(unqualified);

    if (auto *subst = dyn_cast<SubstTemplateTypeParmType>(type))
        return substDefaultType(context, subst->getReplacementType(), limit,
                                params, args);

    if (auto *paren = dyn_cast<ParenType>(type))
        return substDefaultType(context, paren->getInnerType(), limit, params,
                                args);

    if (auto *attr = dyn_cast<AttributedType>(type))
        return substDefaultType(context, attr->getModifiedType(), limit, params,
                                args);

    if (auto *type_param = getReferencedTypeParam(qt)) {
        if (auto index = findTypeParam(type_param, params, limit)) {
            auto arg = args[*index];
            if (arg.param_ref)
                return templateParamType(context, params[*arg.param_ref]);
            return substDefaultType(context, arg.default_type, *index, params,
                                    args);
        }
    }

    if (auto *specialization = dyn_cast<TemplateSpecializationType>(type)) {
        if (specialization->isTypeAlias())
            return substDefaultType(context, specialization->getAliasedType(),
                                    limit, params, args);

        bool changed = false;
        SmallVector<TemplateArgument, 8> subst_args;
        for (auto arg : specialization->template_arguments()) {
            if (arg.getKind() == TemplateArgument::Type) {
                auto old_type = arg.getAsType();
                auto new_type =
                    substDefaultType(context, old_type, limit, params, args);
                changed |= new_type != old_type;
                subst_args.emplace_back(new_type);
            } else {
                subst_args.push_back(arg);
            }
        }
        if (!changed)
            return qt;
        return context.getTemplateSpecializationType(
            specialization->getKeyword(), specialization->getTemplateName(),
            subst_args, subst_args);
    }

    if (auto *array = dyn_cast<ConstantArrayType>(type)) {
        auto element = substDefaultType(context, array->getElementType(), limit,
                                        params, args);
        if (element == array->getElementType())
            return qt;
        return context.getConstantArrayType(
            element, array->getSize(), array->getSizeExpr(),
            array->getSizeModifier(), array->getIndexTypeCVRQualifiers());
    }

    if (auto *ptr = dyn_cast<PointerType>(type)) {
        auto pointee =
            substDefaultType(context, ptr->getPointeeType(), limit, params, args);
        if (pointee == ptr->getPointeeType())
            return qt;
        return context.getPointerType(pointee);
    }

    if (auto *ref = dyn_cast<LValueReferenceType>(type)) {
        auto pointee =
            substDefaultType(context, ref->getPointeeType(), limit, params, args);
        if (pointee == ref->getPointeeType())
            return qt;
        return context.getLValueReferenceType(pointee, ref->isSpelledAsLValue());
    }

    if (auto *ref = dyn_cast<RValueReferenceType>(type)) {
        auto pointee =
            substDefaultType(context, ref->getPointeeType(), limit, params, args);
        if (pointee == ref->getPointeeType())
            return qt;
        return context.getRValueReferenceType(pointee);
    }

    if (auto *func = dyn_cast<FunctionProtoType>(type)) {
        bool changed = false;
        auto return_type =
            substDefaultType(context, func->getReturnType(), limit, params, args);
        changed |= return_type != func->getReturnType();

        SmallVector<QualType, 8> param_types;
        for (auto param_type : func->param_types()) {
            auto subst_param =
                substDefaultType(context, param_type, limit, params, args);
            changed |= subst_param != param_type;
            param_types.push_back(subst_param);
        }
        if (!changed)
            return qt;
        return context.getFunctionType(return_type, param_types,
                                       func->getExtProtoInfo());
    }

    if (auto *member_ptr = dyn_cast<MemberPointerType>(type)) {
        auto pointee = substDefaultType(context, member_ptr->getPointeeType(),
                                        limit, params, args);
        if (pointee == member_ptr->getPointeeType())
            return qt;
#if CLANG_VERSION_MAJOR >= 21
        return context.getMemberPointerType(
            pointee, member_ptr->getQualifier(),
            member_ptr->getMostRecentCXXRecordDecl());
#else
        return context.getMemberPointerType(pointee, member_ptr->getClass());
#endif
    }

    return qt;
}

static ExprSubstitution substDefaultExpr(const Expr *expr, unsigned limit,
                                         ArrayRef<const NamedDecl *> params,
                                         ArrayRef<Argument> args) {
    if (auto *value_param = getReferencedValueParam(expr)) {
        if (auto index = findValueParam(value_param, params, limit)) {
            auto arg = args[*index];
            if (arg.param_ref)
                return {*arg.param_ref, nullptr};
            return substDefaultExpr(arg.default_expr, *index, params, args);
        }
    }
    return {std::nullopt, expr};
}

static bool collectTemplateParamsForDecl(const Decl &decl,
                                         std::vector<const NamedDecl *> &out) {
    if (auto *ctx = decl.getDeclContext()) {
        if (!ctx->isTranslationUnit()) {
            if (!collectTemplateParamsForDecl(*Decl::castFromDeclContext(ctx),
                                              out))
                return false;
        }
    }

    const TemplateParameterList *params = nullptr;
    if (auto *record = dyn_cast<CXXRecordDecl>(&decl)) {
        if (auto *templ = record->getDescribedClassTemplate())
            params = templ->getTemplateParameters();
    } else if (auto *alias = dyn_cast<TypeAliasDecl>(&decl)) {
        if (auto *templ = alias->getDescribedAliasTemplate())
            params = templ->getTemplateParameters();
    }

    if (!params)
        return true;

    for (auto *param : params->asArray()) {
        if (!isa<TemplateTypeParmDecl>(param) &&
            !isa<NonTypeTemplateParmDecl>(param))
            return false;
        if (param->isParameterPack())
            return false;
        out.push_back(param);
    }

    return true;
}

static bool hasDuplicateTemplateParamNames(
    ArrayRef<const NamedDecl *> first, ArrayRef<const NamedDecl *> second) {
    std::vector<std::string> names;
    names.reserve(first.size() + second.size());

    auto add_name = [&](const NamedDecl *param) {
        auto name = getTemplateParamName(*param);
        if (llvm::is_contained(names, name))
            return false;
        names.push_back(std::move(name));
        return true;
    };

    for (auto *param : first)
        if (!add_name(param))
            return true;
    for (auto *param : second)
        if (!add_name(param))
            return true;

    return false;
}

} // namespace

namespace default_template_alias {

bool isSupportedValueDefault(const NonTypeTemplateParmDecl *param) {
    return isSupportedValueDefaultExpr(getTemplateValueDefault(param));
}

void printDefaultTemplateAliases(const Decl *decl, CoqPrinter &print,
                                 ClangPrinter &cprint) {
    const NamedDecl *templated_decl = nullptr;
    const TemplateParameterList *template_params = nullptr;

    if (auto *record = dyn_cast_or_null<CXXRecordDecl>(decl)) {
        if (auto *templ = record->getDescribedClassTemplate()) {
            templated_decl = record;
            template_params = templ->getTemplateParameters();
        }
    } else if (auto *alias = dyn_cast_or_null<TypeAliasDecl>(decl)) {
        if (auto *templ = alias->getDescribedAliasTemplate()) {
            templated_decl = alias;
            template_params = templ->getTemplateParameters();
        }
    }

    if (!templated_decl || !template_params)
        return;

    auto params = template_params->asArray();
    if (params.empty())
        return;

    unsigned first_default = params.size();
    std::vector<const NamedDecl *> prefix_params;
    prefix_params.reserve(params.size());

    for (unsigned i = 0; i < params.size(); ++i) {
        if (params[i]->isParameterPack())
            return;

        if (auto *param = dyn_cast<TemplateTypeParmDecl>(params[i])) {
            if (param->hasDefaultArgument()) {
                first_default = std::min(first_default, i);
            } else if (first_default != params.size()) {
                return;
            }
        } else if (auto *param = dyn_cast<NonTypeTemplateParmDecl>(params[i])) {
            if (param->hasDefaultArgument()) {
                if (!isSupportedValueDefault(param))
                    return;
                first_default = std::min(first_default, i);
            } else if (first_default != params.size()) {
                return;
            }
        } else {
            return;
        }
        prefix_params.push_back(params[i]);
    }

    if (first_default == params.size())
        return;

    auto cp = cprint.withDecl(templated_decl);
    std::vector<const NamedDecl *> enclosing_params;
    if (auto *ctx = templated_decl->getDeclContext()) {
        if (!ctx->isTranslationUnit())
            if (!collectTemplateParamsForDecl(*Decl::castFromDeclContext(ctx),
                                              enclosing_params))
                return;
    }
    if (hasDuplicateTemplateParamNames(enclosing_params, prefix_params))
        return;

    for (unsigned keep = first_default; keep < params.size(); ++keep) {
        {
            guard::ctor _{print, "Dtemplated_typedef"};
            {
                guard::list _{print};
                for (auto *param : enclosing_params)
                    printTemplateParam(print, param, cp) << fmt::cons;
                for (auto *param :
                     ArrayRef<const NamedDecl *>(prefix_params).take_front(keep))
                    printTemplateParam(print, param, cp) << fmt::cons;
            }
            print.output() << fmt::nbsp;
            printDefaultAliasKey(print, *templated_decl, params, keep, cp)
                << fmt::nbsp;
            {
                guard::ctor _{print, "Tnamed", false};
                printTemplateNameWithArgs(print, *templated_decl, cp, [&]() {
                    printTargetArgs(print, params, keep, cp);
                });
            }
        }
        print.cons();
    }
}

fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                ArrayRef<const NamedDecl *> params,
                                unsigned keep, ClangPrinter &cprint) {
    /*
    This is a small, local substitution engine for defaults that are simple
    enough to represent directly in the generated alias table.

    TODO: Consider replacing this local substitution engine with Clang's Sema
    substitution machinery. Clang does expose the more general machinery in Sema:
    Sema::SubstType, Sema::SubstExpr, and Sema::SubstTemplateArgument over a
    MultiLevelTemplateArgumentList. That is the principled long-term direction,
    but it is not a drop-in replacement here. The generated alias targets often
    substitute template parameters with other dependent parameters, not with
    concrete arguments; constructing the correct dependent TemplateArguments is
    delicate, especially for non-type parameters. Sema substitution can also
    emit diagnostics, instantiate semantic state, and otherwise behave more like
    compiler action than pure AST rewriting. For now, this code deliberately
    handles only the simple defaults that cpp2v can print predictably.
    */
    std::vector<Argument> args;
    args.reserve(params.size());

    for (unsigned i = 0; i < params.size(); ++i) {
        if (i < keep) {
            args.push_back({isa<TemplateTypeParmDecl>(params[i])
                                ? ArgumentKind::Type
                                : ArgumentKind::Value,
                            i, QualType{}});
            continue;
        }

        if (auto *param = dyn_cast<TemplateTypeParmDecl>(params[i])) {
            auto default_type = getTemplateTypeDefault(param);
            std::optional<unsigned> ref;
            if (auto *type_param = getDirectReferencedTypeParam(default_type))
                if (auto index = findTypeParam(type_param, params, i))
                    ref = args[*index].param_ref;
            args.push_back({ArgumentKind::Type, ref, default_type});
        } else {
            auto *value_param = cast<NonTypeTemplateParmDecl>(params[i]);
            auto *default_expr = getTemplateValueDefault(value_param);
            std::optional<unsigned> ref;
            if (auto *referenced = getReferencedValueParam(default_expr))
                if (auto index = findValueParam(referenced, params, i))
                    ref = args[*index].param_ref;
            args.push_back({ArgumentKind::Value, ref, QualType{},
                            default_expr});
        }
    }

    auto &context = cprint.getContext();
    guard::list _{print};
    for (unsigned i = 0; i < params.size(); ++i) {
        auto arg = args[i];
        if (arg.param_ref) {
            printTemplateParamArg(print, params[*arg.param_ref], cprint);
        } else if (arg.kind == ArgumentKind::Type) {
            guard::ctor _{print, "Atype", false};
            cprint.printQualType(
                print, substDefaultType(context, arg.default_type, i, params,
                                        args),
                loc::of(arg.default_type.getTypePtrOrNull()));
        } else {
            guard::ctor _{print, "Avalue", false};
            auto subst = substDefaultExpr(arg.default_expr, i, params, args);
            if (subst.param_ref) {
                guard::ctor _{print, "Eparam", false};
                print.str(getTemplateParamName(*params[*subst.param_ref]));
            } else {
                cprint.printExpr(print, subst.expr);
            }
        }
        print.output() << fmt::cons;
    }
    return print.output();
}

} // namespace default_template_alias
