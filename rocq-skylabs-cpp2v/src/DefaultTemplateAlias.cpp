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
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Sema/Sema.h>
#include <clang/Sema/Template.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <optional>
#include <vector>

using namespace clang;

namespace {

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

static fmt::Formatter &
printDefaultAliasKey(CoqPrinter &print, const NamedDecl &decl,
                     ArrayRef<const NamedDecl *> params, unsigned keep,
                     ClangPrinter &cprint) {
    return cprint.printTemplateNameWithArgs(print, decl, [&]() {
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

static Expr *getTemplateValueDefault(const NonTypeTemplateParmDecl *param) {
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
    Expr *default_expr = nullptr;
};

static std::optional<unsigned>
findValueParam(const NonTypeTemplateParmDecl *needle,
               ArrayRef<const NamedDecl *> params, unsigned limit) {
    for (unsigned j = 0; j < limit; ++j)
        if (sameTemplateValueParam(needle, params[j]))
            return j;
    return std::nullopt;
}

static QualType templateParamType(ASTContext &context, NamedDecl *param) {
    auto *type_param = cast<TemplateTypeParmDecl>(param);
    return context.getTemplateTypeParmType(
        type_param->getDepth(), type_param->getIndex(),
        type_param->isParameterPack(), type_param);
}

static DeclRefExpr *templateValueParamExpr(ASTContext &context,
                                           NamedDecl *param) {
    auto *value_param = cast<NonTypeTemplateParmDecl>(param);
    return DeclRefExpr::Create(
        context, NestedNameSpecifierLoc{}, SourceLocation{}, value_param, false,
        value_param->getLocation(), value_param->getType(), VK_PRValue);
}

static TemplateArgument templateArgumentFor(ASTContext &context,
                                            const Argument &arg,
                                            ArrayRef<NamedDecl *> params) {
    if (arg.param_ref) {
        auto *param = params[*arg.param_ref];
        if (isa<TemplateTypeParmDecl>(param))
            return TemplateArgument(templateParamType(context, param));
        return TemplateArgument(templateValueParamExpr(context, param), false);
    }

    if (arg.kind == ArgumentKind::Type)
        return TemplateArgument(arg.default_type);
    return TemplateArgument(arg.default_expr, false);
}

struct TemplateArgumentListBuilder {
    SmallVector<SmallVector<TemplateArgument, 4>, 4> levels;
    MultiLevelTemplateArgumentList template_args;
};

struct TemplateParamPosition {
    unsigned depth;
    unsigned index;
};

static TemplateParamPosition getTemplateParamPosition(const NamedDecl *param) {
    if (auto *type = dyn_cast<TemplateTypeParmDecl>(param))
        return {type->getDepth(), type->getIndex()};
    auto *value = cast<NonTypeTemplateParmDecl>(param);
    return {value->getDepth(), value->getIndex()};
}

static TemplateArgumentListBuilder
buildTemplateArgumentList(ASTContext &context, unsigned limit,
                          ArrayRef<NamedDecl *> params,
                          ArrayRef<Argument> args) {
    TemplateArgumentListBuilder builder;
    unsigned max_depth = 0;
    for (auto *param : params) {
        auto position = getTemplateParamPosition(param);
        max_depth = std::max(max_depth, position.depth);
    }

    builder.levels.resize(max_depth + 1);
    for (unsigned i = 0; i < params.size(); ++i) {
        auto position = getTemplateParamPosition(params[i]);
        if (builder.levels[position.depth].size() <= position.index)
            builder.levels[position.depth].resize(position.index + 1);
        builder.levels[position.depth][position.index] =
            i < limit ? templateArgumentFor(context, args[i], params)
                      : TemplateArgument{};
    }

    for (auto level = builder.levels.rbegin(); level != builder.levels.rend();
         ++level)
        builder.template_args.addOuterTemplateArguments(nullptr, *level, false);
    return builder;
}

static QualType substDefaultType(Sema &sema, QualType qt, unsigned limit,
                                 ArrayRef<NamedDecl *> params,
                                 ArrayRef<Argument> args, SourceLocation loc) {
    auto builder =
        buildTemplateArgumentList(sema.Context, limit, params, args);
    bool incomplete = false;
    auto result = sema.SubstType(qt, builder.template_args, loc,
                                DeclarationName{}, &incomplete);
    if (result.isNull() || incomplete)
        return qt;
    return result;
}

static Expr *substDefaultExpr(Sema &sema, Expr *expr, unsigned limit,
                              ArrayRef<NamedDecl *> params,
                              ArrayRef<Argument> args) {
    auto builder =
        buildTemplateArgumentList(sema.Context, limit, params, args);
    auto result = sema.SubstExpr(expr, builder.template_args);
    if (result.isInvalid())
        return expr;
    return result.get();
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
    ArrayRef<const NamedDecl *> first, ArrayRef<const NamedDecl *> second,
    const ClangPrinter &cprint) {
    std::vector<std::string> names;
    names.reserve(first.size() + second.size());

    auto add_name = [&](const NamedDecl *param) {
        auto name = cprint.getTemplateParamName(*param);
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

static bool isSupportedValueDefault(const NonTypeTemplateParmDecl *param) {
    return isSupportedValueDefaultExpr(getTemplateValueDefault(param));
}

static fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                       ArrayRef<const NamedDecl *> params,
                                       unsigned keep, ClangPrinter &cprint);

} // namespace

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
    std::vector<const NamedDecl *> validated_params;
    validated_params.reserve(params.size());

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
        validated_params.push_back(params[i]);
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
    if (hasDuplicateTemplateParamNames(enclosing_params, validated_params, cp))
        return;

    for (unsigned keep = first_default; keep < params.size(); ++keep) {
        {
            guard::ctor _{print, "Dtemplated_typedef"};
            {
                guard::list _{print};
                for (auto *param : enclosing_params)
                    printTemplateParam(print, param, cp) << fmt::cons;
                for (auto *param :
                     ArrayRef<const NamedDecl *>(validated_params)
                         .take_front(keep))
                    printTemplateParam(print, param, cp) << fmt::cons;
            }
            print.output() << fmt::nbsp;
            printDefaultAliasKey(print, *templated_decl, params, keep, cp)
                << fmt::nbsp;
            {
                guard::ctor _{print, "Tnamed", false};
                cp.printTemplateNameWithArgs(print, *templated_decl, [&]() {
                    printTargetArgs(print, params, keep, cp);
                });
            }
        }
        print.cons();
    }
}

namespace {

static fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                       ArrayRef<const NamedDecl *> params,
                                       unsigned keep, ClangPrinter &cprint) {
    /*
    This uses Sema substitution for defaults that are simple enough to represent
    directly in the generated alias table.

    TODO: The generated alias targets often substitute template parameters with
    other dependent parameters, not with concrete arguments. Keep the
    MultiLevelTemplateArgumentList construction isolated so that any remaining
    Clang-version differences or future support for packs/template-template
    parameters are handled at that boundary.
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
            args.push_back({ArgumentKind::Type, std::nullopt, default_type});
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

    /*
    Clang's Sema substitution APIs take non-const AST node pointers even when
    those pointers are used only as identity handles. `printTargetArgs` exposes a
    const-correct interface because it does not mutate declarations. The mutable
    view below is therefore safe as long as it is used only to construct Sema
    template arguments, not to modify the declarations.
    */
    SmallVector<NamedDecl *, 8> sema_params;
    sema_params.reserve(params.size());
    for (auto *param : params)
        sema_params.push_back(const_cast<NamedDecl *>(param));

    auto &sema = cprint.getCompiler().getSema();
    guard::list _{print};
    for (unsigned i = 0; i < params.size(); ++i) {
        auto arg = args[i];
        if (arg.param_ref) {
            printTemplateParamArg(print, params[*arg.param_ref], cprint);
        } else if (arg.kind == ArgumentKind::Type) {
            guard::ctor _{print, "Atype", false};
            cprint.printQualType(
                print,
                substDefaultType(sema, arg.default_type, i, sema_params, args,
                                 SourceLocation{}),
                loc::of(arg.default_type.getTypePtrOrNull()));
        } else {
            guard::ctor _{print, "Avalue", false};
            auto subst =
                substDefaultExpr(sema, arg.default_expr, i, sema_params, args);
            cprint.printExpr(print, subst);
        }
        print.output() << fmt::cons;
    }
    return print.output();
}

} // namespace
