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
#include <clang/AST/Decl.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Type.h>
#include <clang/Basic/Version.inc>
#include <llvm/ADT/STLExtras.h>
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

static fmt::Formatter &printTemplateParamType(CoqPrinter &print,
                                              const NamedDecl *param) {
    guard::ctor _{print, "Tparam", false};
    return print.str(getTemplateParamName(*param));
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

static fmt::Formatter &printQualifiers(CoqPrinter &print, QualType qt,
                                       llvm::function_ref<void()> print_type) {
    if (qt.isLocalConstQualified()) {
        print.ctor(qt.isVolatileQualified() ? "Qconst_volatile" : "Qconst",
                   false);
        print_type();
        return print.end_ctor();
    }

    if (qt.isLocalVolatileQualified()) {
        print.ctor("Qvolatile", false);
        print_type();
        return print.end_ctor();
    }

    print_type();
    return print.output();
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
    enum class ArgumentKind { Type, Value };
    struct Argument {
        ArgumentKind kind;
        std::optional<unsigned> param_ref;
        QualType default_type;
        const Expr *default_expr = nullptr;
    };
    std::vector<Argument> args;
    args.reserve(params.size());

    auto find_param = [&](const TemplateTypeParmDecl *needle,
                          unsigned limit) -> std::optional<unsigned> {
        for (unsigned j = 0; j < limit; ++j) {
            if (sameTemplateTypeParam(needle, params[j]))
                return j;
        }
        return std::nullopt;
    };

    auto find_value_param = [&](const NonTypeTemplateParmDecl *needle,
                                unsigned limit) -> std::optional<unsigned> {
        for (unsigned j = 0; j < limit; ++j) {
            if (sameTemplateValueParam(needle, params[j]))
                return j;
        }
        return std::nullopt;
    };

    std::function<fmt::Formatter &(QualType, unsigned)> print_type =
        [&](QualType qt, unsigned limit) -> fmt::Formatter & {
        return printQualifiers(print, qt, [&]() {
            auto *type = qt.getTypePtrOrNull();
            if (!type) {
                cprint.printQualType(print, qt, loc::none);
                return;
            }

            if (auto *subst = dyn_cast<SubstTemplateTypeParmType>(type)) {
                print_type(subst->getReplacementType(), limit);
                return;
            }

            if (auto *paren = dyn_cast<ParenType>(type)) {
                print_type(paren->getInnerType(), limit);
                return;
            }

            if (auto *attr = dyn_cast<AttributedType>(type)) {
                print_type(attr->getModifiedType(), limit);
                return;
            }

            if (auto *type_param = getReferencedTypeParam(qt)) {
                if (auto index = find_param(type_param, limit)) {
                    auto arg = args[*index];
                    if (arg.param_ref) {
                        printTemplateParamType(print, params[*arg.param_ref]);
                    } else {
                        print_type(arg.default_type, *index);
                    }
                    return;
                }
            }

            if (auto *specialization =
                    dyn_cast<TemplateSpecializationType>(type)) {
                if (specialization->isTypeAlias()) {
                    print_type(specialization->getAliasedType(), limit);
                    return;
                }

                auto *templ =
                    specialization->getTemplateName().getAsTemplateDecl();
                if (templ) {
                    guard::ctor _{print, "Tnamed", false};
                    guard::ctor __{print, "Ninst", false};
                    cprint.printName(print, *templ) << fmt::nbsp;
                    guard::list ___{print};
                    for (auto arg : specialization->template_arguments()) {
                        if (arg.getKind() == TemplateArgument::Type) {
                            guard::ctor _{print, "Atype", false};
                            print_type(arg.getAsType(), limit);
                        } else {
                            cprint.printTemplateArg(print, arg, loc::of(type));
                        }
                        print.output() << fmt::cons;
                    }
                    return;
                }
            }

            if (auto *array = dyn_cast<ConstantArrayType>(type)) {
                guard::ctor _{print, "Tarray", false};
                print_type(array->getElementType(), limit);
                print.output() << fmt::nbsp
                               << array->getSize().getLimitedValue();
                return;
            }

            if (auto *ptr = dyn_cast<PointerType>(type)) {
                guard::ctor _{print, "Tptr", false};
                print_type(ptr->getPointeeType(), limit);
                return;
            }

            if (auto *ref = dyn_cast<LValueReferenceType>(type)) {
                guard::ctor _{print, "Tref", false};
                print_type(ref->getPointeeType(), limit);
                return;
            }

            if (auto *ref = dyn_cast<RValueReferenceType>(type)) {
                guard::ctor _{print, "Trv_ref", false};
                print_type(ref->getPointeeType(), limit);
                return;
            }

            if (auto *func = dyn_cast<FunctionProtoType>(type)) {
                guard::ctor _{print, "Tfunction"};
                print.output() << (print.templates() ? "Mtype" : "type")
                               << fmt::nbsp;
                cprint.printCallingConv(print, func->getCallConv(),
                                        loc::of(type))
                    << fmt::nbsp;
                cprint.printVariadic(print, func->isVariadic()) << fmt::nbsp;
                print_type(func->getReturnType(), limit) << fmt::nbsp;
                print.list(func->param_types(), [&](QualType param_type) {
                    print_type(param_type, limit);
                });
                return;
            }

            if (auto *member_ptr = dyn_cast<MemberPointerType>(type)) {
                guard::ctor _{print, "Tmember_pointer", false};
#if CLANG_VERSION_MAJOR >= 22
                {
                    NestedNameSpecifier NNS = member_ptr->getQualifier();
                    if (NNS &&
                        NNS.getKind() == NestedNameSpecifier::Kind::Type) {
                        cprint.printType(print, NNS.getAsType(), loc::of(type));
                    } else {
                        cprint.printUnsupportedName(
                            print, "unresolved class type in MemberPointerType");
                    }
                }
#elif CLANG_VERSION_MAJOR >= 21
                {
                    const NestedNameSpecifier *NNS = member_ptr->getQualifier();
                    if (const Type *class_type = NNS->getAsType()) {
                        cprint.printType(print, class_type, loc::of(type));
                    } else {
                        cprint.printUnsupportedName(
                            print, "unresolved class type in MemberPointerType");
                    }
                }
#else
                cprint.printType(print, member_ptr->getClass(), loc::of(type));
#endif
                print.output() << fmt::nbsp;
                print_type(member_ptr->getPointeeType(), limit);
                return;
            }

            cprint.printQualType(print, qt, loc::of(type));
        });
    };

    std::function<fmt::Formatter &(const Expr *, unsigned)> print_expr =
        [&](const Expr *expr, unsigned limit) -> fmt::Formatter & {
            if (auto *value_param = getReferencedValueParam(expr)) {
                if (auto index = find_value_param(value_param, limit)) {
                    auto arg = args[*index];
                    if (arg.param_ref) {
                        guard::ctor _{print, "Eparam", false};
                        return print.str(
                            getTemplateParamName(*params[*arg.param_ref]));
                    }
                    return print_expr(arg.default_expr, *index);
                }
            }
            return cprint.printExpr(print, expr);
        };

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
                if (auto index = find_param(type_param, i))
                    ref = args[*index].param_ref;
            args.push_back({ArgumentKind::Type, ref, default_type});
        } else {
            auto *value_param = cast<NonTypeTemplateParmDecl>(params[i]);
            auto *default_expr = getTemplateValueDefault(value_param);
            std::optional<unsigned> ref;
            if (auto *referenced = getReferencedValueParam(default_expr))
                if (auto index = find_value_param(referenced, i))
                    ref = args[*index].param_ref;
            args.push_back({ArgumentKind::Value, ref, QualType{},
                            default_expr});
        }
    }

    guard::list _{print};
    for (unsigned i = 0; i < params.size(); ++i) {
        auto arg = args[i];
        if (arg.param_ref) {
            printTemplateParamArg(print, params[*arg.param_ref], cprint);
        } else if (arg.kind == ArgumentKind::Type) {
            guard::ctor _{print, "Atype", false};
            print_type(arg.default_type, i);
        } else {
            guard::ctor _{print, "Avalue", false};
            print_expr(arg.default_expr, i);
        }
        print.output() << fmt::cons;
    }
    return print.output();
}

} // namespace default_template_alias
