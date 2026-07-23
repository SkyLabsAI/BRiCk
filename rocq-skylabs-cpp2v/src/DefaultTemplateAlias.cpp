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

static TemplateArgument templateArgumentForParam(ASTContext &context,
                                                 NamedDecl *param) {
    if (isa<TemplateTypeParmDecl>(param))
        return TemplateArgument(templateParamType(context, param));
    return TemplateArgument(templateValueParamExpr(context, param), false);
}

static TemplateArgumentLoc substDefaultTemplateArgument(
    Sema &sema, TemplateDecl *templ, Decl *param,
    ArrayRef<TemplateArgument> sugared_converted,
    ArrayRef<TemplateArgument> canonical_converted, SourceLocation loc) {
    bool has_default_arg = false;
#if CLANG_VERSION_MAJOR >= 22
    return sema.SubstDefaultTemplateArgumentIfAvailable(
        templ, SourceLocation{}, loc, SourceLocation{}, param,
        sugared_converted, canonical_converted, has_default_arg);
#else
    return sema.SubstDefaultTemplateArgumentIfAvailable(
        templ, loc, SourceLocation{}, param, sugared_converted,
        canonical_converted, has_default_arg);
#endif
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

static fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                       TemplateDecl *template_decl,
                                       ArrayRef<const NamedDecl *> params,
                                       unsigned keep, ClangPrinter &cprint);

} // namespace

void printDefaultTemplateAliases(const Decl *decl, CoqPrinter &print,
                                 ClangPrinter &cprint) {
    const NamedDecl *templated_decl = nullptr;
    TemplateDecl *template_decl = nullptr;
    const TemplateParameterList *template_params = nullptr;

    if (auto *record = dyn_cast_or_null<CXXRecordDecl>(decl)) {
        if (auto *templ = record->getDescribedClassTemplate()) {
            templated_decl = record;
            template_decl = templ;
            template_params = templ->getTemplateParameters();
        }
    } else if (auto *alias = dyn_cast_or_null<TypeAliasDecl>(decl)) {
        if (auto *templ = alias->getDescribedAliasTemplate()) {
            templated_decl = alias;
            template_decl = templ;
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
                    printTargetArgs(print, template_decl, params, keep, cp);
                });
            }
        }
        print.cons();
    }
}

namespace {

static fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                       TemplateDecl *template_decl,
                                       ArrayRef<const NamedDecl *> params,
                                       unsigned keep, ClangPrinter &cprint) {
    /*
    This uses Clang's default-template-argument substitution API so nested
    dependent defaults are interpreted in the context of the template whose
    alias table is being generated.

    TODO: The generated alias targets often substitute template parameters with
    other dependent parameters, not with concrete arguments. Keep the converted
    argument construction isolated so that any remaining Clang-version
    differences or future support for packs/template-template parameters are
    handled at that boundary.
    */
    auto &sema = cprint.getCompiler().getSema();
    SmallVector<TemplateArgument, 8> sugared_converted;
    SmallVector<TemplateArgument, 8> canonical_converted;

    guard::list _{print};
    for (unsigned i = 0; i < params.size(); ++i) {
        TemplateArgument converted;
        bool have_converted = true;
        if (i < keep) {
            auto *param = const_cast<NamedDecl *>(params[i]);
            converted = templateArgumentForParam(sema.Context, param);
            printTemplateParamArg(print, params[i], cprint);
        } else {
            auto *param = const_cast<NamedDecl *>(params[i]);
            auto subst = substDefaultTemplateArgument(
                sema, template_decl, param, sugared_converted,
                canonical_converted, param->getLocation());
            converted = subst.getArgument();
            if (converted.isNull()) {
                have_converted = false;
                guard::ctor _{print, "Aunsupported", false};
                print.str("default template argument substitution");
            } else {
                cprint.printTemplateArg(print, converted, loc::of(subst));
            }
        }
        if (have_converted) {
            sugared_converted.push_back(converted);
            canonical_converted.push_back(
                sema.Context.getCanonicalTemplateArgument(converted));
        }
        print.output() << fmt::cons;
    }
    return print.output();
}

} // namespace
