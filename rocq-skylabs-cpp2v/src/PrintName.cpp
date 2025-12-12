/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "Template.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Basic/Version.inc>
#include <clang/Frontend/CompilerInstance.h>
#include <optional>

using namespace clang;

const TemplateDecl *recoverTemplate(const Decl &decl) {
    if (auto td = dyn_cast<TemplateDecl>(&decl))
        return td;
    if (auto rd = dyn_cast<CXXRecordDecl>(&decl))
        return rd->getDescribedClassTemplate();
    if (auto fd = dyn_cast<FunctionDecl>(&decl))
        return fd->getDescribedFunctionTemplate();
    if (auto td = dyn_cast<TypeAliasDecl>(&decl))
        return td->getDescribedAliasTemplate();
    if (auto vd = dyn_cast<VarDecl>(&decl))
        return vd->getDescribedVarTemplate();
    return nullptr;
}

const char *templateArgumentKindName(TemplateArgument::ArgKind kind) {
#define CASE(k)                                                                \
    case TemplateArgument::ArgKind::k:                                         \
        return #k;
    switch (kind) {
        CASE(Null)
        CASE(Type)
        CASE(Declaration)
        CASE(NullPtr)
        CASE(Integral)
        CASE(Template)
        CASE(TemplateExpansion)
        CASE(Expression)
        CASE(Pack)
    default:
        return "<unknown>";
    }
#undef CASE
}

namespace structured {

using ParameterLists =
    SmallVector<std::pair<const TemplateParameterList *, loc::loc>>;

// Returns the total length of lists appended to dest
static unsigned collectParameterLists(const Decl &decl,
                                      const ASTContext &context,
                                      ParameterLists &dest) {
    auto n = 0;
    if (auto ctx = decl.getDeclContext()) {
        auto loc = loc::of(decl);
        auto &cdecl = cast<const Decl>(*ctx);
        n += collectParameterLists(cdecl, context, dest);
        if (auto td = recoverTemplate(decl)) {
            if (auto params = td->getTemplateParameters()) {
                n += params->size();
                dest.push_back(std::make_pair(params, loc));
            } else {
                // TODO: Drop this function
                // and instead emit a marker
                // like `?null`.
                locfree_warn(decl, context,
                             "collectParameterLists "
                             "ignoring template with null "
                             "parameter list");
            }
        }
    }
    return n;
}

static raw_ostream &printTemplateParameters(raw_ostream &os, const Decl &decl,
                                            const ASTContext &context) {
    ParameterLists lists;
    auto n = collectParameterLists(decl, context, lists);
    if (!lists.empty()) {
        auto &policy = context.getPrintingPolicy();
        os << '<';
        for (auto [params, loc] : lists) {
            for (auto param : params->asArray()) {
                param->printName(os, policy);
                if (--n)
                    os << ", ";
            }
        }
        os << '>';
    }
    return os;
}

static raw_ostream &printFunctionParameterTypes(raw_ostream &os,
                                                const FunctionDecl &decl,
                                                const PrintingPolicy &policy) {
    os << '(';
    auto ps = decl.parameters();
    for (size_t i = 0; i < ps.size(); i++) {
        if (auto vd = ps[i])
            vd->getType().print(os, policy);
        else
            os << "?null";
        if (i + 1 < ps.size())
            os << ", ";
    }
    os << ')';
    return os;
}

const FunctionDecl *recoverFunction(const Decl &decl) {
    if (auto fd = dyn_cast<FunctionDecl>(&decl))
        return fd;
    if (auto td = dyn_cast<FunctionTemplateDecl>(&decl))
        return td->getTemplatedDecl();
    return nullptr;
}

static raw_ostream &
printFunctionQualifiersForDiagnostics(raw_ostream &os,
                                      const FunctionDecl &decl) {
    if (auto md = dyn_cast<CXXMethodDecl>(&decl)) {
        if (md->isConst()) {
            os << " const";
        }
        if (md->isVolatile()) {
            os << " volatile";
        }
        switch (md->getRefQualifier()) {
        case RefQualifierKind::RQ_LValue:
            os << " &";
            break;
        case RefQualifierKind::RQ_RValue:
            os << " &&";
            break;
        default:
            break;
        }
    }
    return os;
}

raw_ostream &printNameForDiagnostics(raw_ostream &os, const NamedDecl &decl,
                                     const ASTContext &context) {
    printTemplateParameters(os, decl, context);
    auto &policy = context.getPrintingPolicy();
    decl.getNameForDiagnostic(os, policy, true);
    // TODO: Make template arguments explicit in all cases?
    if (auto fd = recoverFunction(decl)) {
        printFunctionParameterTypes(os, *fd, policy);
        printFunctionQualifiersForDiagnostics(os, *fd);
    }
    return os;
}
} // namespace structured

static raw_ostream &fatal(ClangPrinter &cprint, loc::loc loc) {
    cprint.debug_dump(loc);
    return cprint.error_prefix(logging::fatal(), loc) << "error: ";
}

static raw_ostream &warning(ClangPrinter &cprint, loc::loc loc,
                            bool dump = true) {
    if (dump)
        cprint.debug_dump(loc);
    return cprint.error_prefix(logging::unsupported(), loc) << "warning: ";
}

static raw_ostream &unsupported(ClangPrinter &cprint, loc::loc loc,
                                bool dump = true) {
    return warning(cprint, loc, dump) << "unsupported ";
}

static ref<const Decl> toDecl(const DeclContext &ctx, ClangPrinter &cprint,
                              loc::loc loc) {
    if (auto p = dyn_cast<Decl>(&ctx))
        return ref{*p};
    else {
        fatal(cprint, loc) << "declaration context of kind "
                           << ctx.getDeclKindName() << " not a declaration\n";
        logging::die();
    }
}

namespace structured {

/*
We classify declaration contexts into

- _global_ contexts (translation units, implicit in `Nglobal`)
- _scope_ contexts (these show up under `Nscoped`)
- _ignorable_ contexts (these are suppressed in `Nscoped`)

We assign anonymous indices to any declaration `D` inherting from `Decl`
but not `NamedDecl`, as well as to a few ostensibly named declarations
which lack a name (e.g., unnamed, unscoped enumerations).

To assign an anonymous index to a declaration, we count relative to its
first non-ignorable ancestor. Such an ancestor always exists because the
declarations we name arise in the context of a translation unit, which
isn't ignorable. (It would be a mistake to, for example, suppress
ignorable contexts in `Nscoped` but then to number an anonymous
declaration relative to its ignored-by-`Nscoped` parent.)

We permit more anonymous declarations than the Itanium ABI because we
are not free to ignore names with internal linkage (which matter for
verification). Fortunately, we don't need our anonymous indices to match
the numbers picked by the ABI (e.g., in its  nonterminals
<<discriminator>>, <<unnamed-type-name>>).

TODO: Clang does not use declaration contexts to separate names with
internal linkage inside function bodies. To assign disambiguating
anonymous indices, we have to traverse the function's body, and not just
the declaration context chain. See FunctionDecl::getBody and
Stmt::children.
*/

enum class ContextKind { Global, Scope, Ingorable };

static ContextKind classifyContext(const DeclContext &ctx,
                                   ClangPrinter &cprint) {
    if (false && cprint.trace(Trace::Name))
        cprint.trace("classifyContext", loc::of(ctx));

    switch (ctx.getDeclKind()) {
    case Decl::Kind::TranslationUnit:
        return ContextKind::Global;

    case Decl::Kind::Namespace:
    case Decl::Kind::Record:
    case Decl::Kind::CXXRecord:
    case Decl::Kind::ClassTemplateSpecialization:
    case Decl::Kind::ClassTemplatePartialSpecialization:
    case Decl::Kind::Function:
    case Decl::Kind::CXXMethod:
    case Decl::Kind::CXXConstructor:
    case Decl::Kind::CXXDestructor:
    case Decl::Kind::CXXConversion:
    case Decl::Kind::Block:
        return ContextKind::Scope;

    case Decl::Kind::Enum:
        /*
        technically, un-scoped enumerations are ignorable, but, for uniformity,
           we always use qualifiers on enumeration constants.
        return cast<EnumDecl>(ctx).isScoped() ? ContextKind::Scope :
                            ContextKind::Ingorable;
        */
        return ContextKind::Scope;

    case Decl::Kind::LinkageSpec:
    case Decl::Kind::ExternCContext:
    case Decl::Kind::Export:
    case Decl::Kind::RequiresExprBody:
    case Decl::Kind::CXXDeductionGuide:
        return ContextKind::Ingorable;

    default: {
        warning(cprint, loc::of(ctx)) << "ignoring declaration context\n";
        return ContextKind::Ingorable;
    }
    }
}

static bool isIgnorableContext(const DeclContext &ctx, ClangPrinter &cprint) {
    return classifyContext(ctx, cprint) == ContextKind::Ingorable;
}

static ref<const DeclContext> getNonIgnorableAncestor(const Decl &decl,
                                                      ClangPrinter &cprint) {
    auto fatal = [&](const std::string what, loc::loc loc) NORETURN {
        ::fatal(cprint, loc) << what << "\n";
        logging::die();
    };
    auto parent = [&](const DeclContext *ctx) {
        if (auto p = ctx->getParent()) {
            if (cprint.trace(Trace::Name))
                cprint.trace("getNonIgnorableAncestor skipping", loc::of(ctx));
            return p;
        } else
            fatal("declaration context outside any translation unit",
                  loc::of(ctx));
    };
    if (auto p = decl.getDeclContext()) {
        for (; isIgnorableContext(*p, cprint); p = parent(p))
            ;
        if (false && cprint.trace(Trace::Name)) {
            std::string what;
            llvm::raw_string_ostream os{what};
            os << "getNonIgnorableAncestor (= "
               << loc::describe(loc::of(p), cprint.getContext()) << ")";
            cprint.trace(what, loc::of(decl));
        }
        return ref{*p};
    } else
        fatal("declaration outside any translation unit\n", loc::of(decl));
}

// Decide if a declaration is named or anonymous.
static const NamedDecl *isNamed(const Decl &decl) {
    if (auto nd = dyn_cast<NamedDecl>(&decl))
        if (!nd->getIdentifier())
            return nullptr;
    if (auto nd = dyn_cast<NamespaceDecl>(&decl))
        return nd->isAnonymousNamespace() ? nullptr : nd;
    else if (auto crd = dyn_cast<CXXRecordDecl>(&decl)) {
        if (crd->isLambda() || crd->isAnonymousStructOrUnion())
            return nullptr;
        return crd;
    } else if (auto rd = dyn_cast<RecordDecl>(&decl))
        return rd->isAnonymousStructOrUnion() ? nullptr : rd;
    else if (auto ed = dyn_cast<EnumDecl>(&decl))
        // unnamed, scoped enums might be impossible
        return ed;
    else if (auto nd = dyn_cast<NamedDecl>(&decl))
        return nd;
    else
        return nullptr;
}

static bool isAnonymous(const Decl &decl) { return isNamed(decl) == nullptr; }

// Assign indices to anonymous declarations
static bool getAnonymousIndex(const DeclContext &ctx, const Decl &decl,
                              unsigned &acc, ClangPrinter &cprint) {
    for (auto d : ctx.decls()) {
        if (d == &decl)
            return true;
        if (!d) {
            fatal(cprint, loc::of(ctx))
                << "declaration context with null declaration\n";
            logging::die();
        }
        if (auto dctx = dyn_cast<DeclContext>(d)) {
            if (isIgnorableContext(*dctx, cprint) &&
                getAnonymousIndex(*dctx, decl, acc, cprint))
                return true;
        }
        if (isAnonymous(*d))
            ++acc;
    }
    return false;
}

static unsigned getAnonymousIndex(const DeclContext &ctx, const Decl &decl,
                                  ClangPrinter &cprint) {
    unsigned i{0};
    if (!getAnonymousIndex(ctx, decl, i, cprint)) {
        fatal(cprint, loc::of(decl))
            << "could not find anonymous declaration in context\n";
        logging::die();
    }
    if (false && cprint.trace(Trace::Name)) {
        std::string what;
        llvm::raw_string_ostream os{what};
        os << "getAnonymousIndex (= " << i << " )";
        cprint.trace(what, loc::of(decl));
    }
    return i;
}

static fmt::Formatter &printTemplateParameter(CoqPrinter &print,
                                              const NamedDecl *pdecl,
                                              ClangPrinter &cprint,
                                              loc::loc gloc,
                                              bool as_arg = false) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printTemplateParameter", loc::of(pdecl));
    always_assert(pdecl->isTemplateParameter() && "template parameter");

    auto unsupported = [&](StringRef msg) -> auto & {
        auto loc = loc::refine(gloc, pdecl);
        ::unsupported(cprint, loc) << msg << "\n";
        guard::ctor _(print, as_arg ? "Aunsupported" : "Punsupported", false);
        return print.str(msg);
    };

    if (!pdecl)
        return unsupported("null template parameter");
    auto &decl = *pdecl;

    if (decl.isParameterPack())
        return unsupported("template parameter pack");

    /*
    TODO: We could presumably infer a name for some unnamed template
    parameters.

    See `TemplateParmPosition`, `printTypeTemplateParam`.
    */
    auto id = decl.getIdentifier();
    if (!id)
        return unsupported("unnamed template parameter");
    auto name = id->getName();

    switch (decl.getKind()) {
    case Decl::Kind::TemplateTypeParm:
        if (as_arg) {
            guard::ctor _1(print, "Atype", false);
            guard::ctor _2(print, "Tparam", false);
            return print.str(name);
        } else {
            guard::ctor _(print, "Ptype", false);
            return print.str(name);
        }

    case Decl::Kind::NonTypeTemplateParm:
        if (as_arg) {
            guard::ctor _1(print, "Avalue", false);
            guard::ctor _2(print, "Eparam", false);
            return print.str(name);
        } else {
            auto &param = cast<NonTypeTemplateParmDecl>(decl);
            guard::ctor _(print, "Pvalue", false);
            print.str(name) << fmt::nbsp;
            return cprint.printQualType(print, param.getType(), loc::of(param));
        }

    case Decl::Kind::TemplateTemplateParm:
    default:
        return unsupported("template parameter kind");
    }
}

static fmt::Formatter &printTemplateParameters(CoqPrinter &print,
                                               const Decl &decl,
                                               ClangPrinter &cprint,
                                               bool as_arg) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printTemplateParameters", loc::of(decl));
    ParameterLists lists;
    if (collectParameterLists(decl, cprint.getContext(), lists)) {
        guard::list _(print);
        for (auto [params, loc] : lists)
            for (auto param : params->asArray())
                printTemplateParameter(print, param, cprint, loc, as_arg)
                    << fmt::cons;
        return print.output();
    } else
        return print.output() << "nil";
}

static fmt::Formatter &printTemplateArgument(CoqPrinter &print,
                                             const TemplateArgument &arg,
                                             ClangPrinter &cprint,
                                             loc::loc loc) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printTemplateArgument", loc);
    auto kind = arg.getKind();
    auto Avalue = [&](auto val) -> auto & {
        guard::ctor _(print, "Avalue", false);
        val();
        return print.output();
    };
    switch (kind) {
    case TemplateArgument::ArgKind::Type: {
        guard::ctor _(print, "Atype", false);
        return cprint.printQualType(print, arg.getAsType(), loc);
    }
    case TemplateArgument::ArgKind::Expression:
        return Avalue(
            [&]() { return cprint.printExpr(print, arg.getAsExpr()); });

    case TemplateArgument::ArgKind::Integral:
        return Avalue([&]() {
            guard::ctor _(print, "Eint", false);
            print.output() << arg.getAsIntegral() << fmt::nbsp;
            return cprint.printQualType(print, arg.getIntegralType(), loc);
        });

    case TemplateArgument::ArgKind::NullPtr:
        return Avalue([&]() { return print.output() << "Enull"; });

    case TemplateArgument::ArgKind::Declaration:
        /*
        TODO: Examples
        ```
        struct B { int next; };
        template<int(B::*next_ptr)> struct A{};
        void test() {
        A<&B::next> a;
        }
        ```
        */
        return Avalue([&]() {
            return cprint.printValueDeclExpr(print, arg.getAsDecl());
        });

    case TemplateArgument::ArgKind::Pack: {
        guard::ctor _(print, "Apack", false);
        return print.list(arg.getPackAsArray(), [&](auto value) {
            printTemplateArgument(print, value, cprint, loc);
        });
    }
    case TemplateArgument::ArgKind::Template: {
        auto templ = arg.getAsTemplate();
        if (auto dt = templ.getAsTemplateDecl()) {
            guard::ctor _(print, "Atemplate", false);
            return cprint.printName(print, *dt);
        } /* else if (auto qtn = templ.getAsQualifiedTemplateName()) {
          return cprint.printName(print, qtn->getQualifier(), qtn->get)
        } */
        [[fallthrough]];
    }
    default: {
        auto k = templateArgumentKindName(kind);
        if (cprint.warn_well_known) {
            unsupported(cprint, loc, false)
                << "template argument of kind " << k << "\n";
#if 19 <= CLANG_VERSION_MAJOR
            arg.dump();
#else
            arg.dump(logging::debug());
#endif
        }
        guard::ctor _(print, "Aunsupported", false);
        return print.str(k);
    }
    }
}

static fmt::Formatter &
printTemplateArgumentList(CoqPrinter &print, const TemplateArgumentList &args,
                          ClangPrinter &cprint, loc::loc loc) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printTemplateArgumentList", loc);
    return print.list(args.asArray(), [&](auto &arg) {
        printTemplateArgument(print, arg, cprint, loc);
    });
}

static const TemplateArgumentList *recoverTemplateArgs(const Decl &decl) {
    auto sd = recoverSpecialization(decl);
    return sd ? &(sd->args) : nullptr;
}

using ArgumentLists =
    SmallVector<std::pair<const TemplateArgumentList *, loc::loc>>;

// Returns the total length of lists appended to dest
static unsigned collectArgumentLists(const Decl &decl,
                                     const ASTContext &context,
                                     ArgumentLists &dest) {
    auto n = 0;
    if (auto ctx = decl.getDeclContext()) {
        auto loc = loc::of(decl);
        auto &cdecl = cast<const Decl>(*ctx);
        n += collectArgumentLists(cdecl, context, dest);
        if (auto args = recoverTemplateArgs(decl)) {
            n += args->size();
            dest.push_back(std::make_pair(args, loc));
        }
    }
    return n;
}

static fmt::Formatter &printTemplateArguments(CoqPrinter &print,
                                              const Decl &decl,
                                              ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printTemplateArguments", loc::of(decl));
    ArgumentLists lists;
    if (collectArgumentLists(decl, cprint.getContext(), lists)) {
        guard::list _(print);
        for (auto [args, loc] : lists)
            for (auto arg : args->asArray())
                printTemplateArgument(print, arg, cprint, loc) << fmt::cons;
        return print.output();
    } else
        return print.output() << "nil";
}

static fmt::Formatter &printFunctionQualifiers(CoqPrinter &print,
                                               const FunctionDecl &decl,
                                               ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printFunctionQualifiers", loc::of(decl));
    const char *const_volatile_cat[2][2][3] = {
        {{"N", "Nl", "Nr"}, {"Nv", "Nvl", "Nvr"}},
        {{"Nc", "Ncl", "Ncr"}, {"Ncv", "Ncvl", "Ncvr"}}};

    if (auto md = dyn_cast<CXXMethodDecl>(&decl)) {
        static_assert(RefQualifierKind::RQ_None == 0);
        static_assert(RefQualifierKind::RQ_LValue == 1);
        static_assert(RefQualifierKind::RQ_RValue == 2);
        return print.output()
               << "function_qualifiers."
               << const_volatile_cat[md->isConst()][md->isVolatile()]
                                    [md->getRefQualifier()];
    } else {
        return print.output() << "function_qualifiers.N";
    }

    return print.output();
}

static fmt::Formatter &printFunctionParamTypes(CoqPrinter &print,
                                               const FunctionDecl &decl,
                                               ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printFunctionParamTypes", loc::of(decl));
    auto loc = loc::of(decl);
    return print.list(decl.parameters(), [&](auto *param) {
        cprint.printQualType(print, param->getType(), loc);
    });
}

static fmt::Formatter &printFunctionName(CoqPrinter &print,
                                         const FunctionDecl &decl,
                                         ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printFunctionName", loc::of(decl));
    auto unsupported = [&]() -> auto & {
        std::string what;
        llvm::raw_string_ostream os{what};
        os << "function name: ";
        decl.getNameForDiagnostic(os, cprint.getContext().getPrintingPolicy(),
                                  false);
        ::unsupported(cprint, loc::of(decl)) << what << "\n";
        guard::ctor _(print, "Nunsupported_atomic", false);
        return print.str(what);
    };
    if (decl.isExternC()) {
        guard::ctor _(print, "Nid", false);
        return print.str(decl.getName());
    }
    auto name = decl.getDeclName();
    switch (name.getNameKind()) {

    case DeclarationName::NameKind::Identifier:
        if (auto id = name.getAsIdentifierInfo()) {
            guard::ctor _(print, "Nfunction", false);
            printFunctionQualifiers(print, decl, cprint) << fmt::nbsp;
            print.str(id->getName()) << fmt::nbsp;
            return printFunctionParamTypes(print, decl, cprint);
        } else
            return unsupported();

    case DeclarationName::NameKind::CXXConstructorName: {
        guard::ctor _(print, "Nctor", false);
        return printFunctionParamTypes(print, decl, cprint);
    }

    case DeclarationName::NameKind::CXXDestructorName:
        always_assert(decl.getNumParams() == 0);
        return print.output() << "Ndtor";

    case DeclarationName::NameKind::CXXOperatorName: {
        guard::ctor _(print, "Nop", false);
        printFunctionQualifiers(print, decl, cprint) << fmt::nbsp;
        cprint.printOverloadableOperator(print, name.getCXXOverloadedOperator(),
                                         loc::of(decl))
            << fmt::nbsp;
        return printFunctionParamTypes(print, decl, cprint);
    }

    case DeclarationName::NameKind::CXXConversionFunctionName: {
        always_assert(decl.getNumParams() == 0);
        guard::ctor _(print, "Nop_conv", false);
        printFunctionQualifiers(print, decl, cprint) << fmt::nbsp;
        return cprint.printQualType(print, name.getCXXNameType(),
                                    loc::of(decl));
    }

    case DeclarationName::NameKind::CXXLiteralOperatorName:
        if (auto id = name.getCXXLiteralIdentifier()) {
            guard::ctor _(print, "Nop_lit", false);
            print.str(id->getName()) << fmt::nbsp;
            return printFunctionParamTypes(print, decl, cprint);
        } else
            return unsupported();

    default:
        return unsupported();
    }
}

static fmt::Formatter &printAtomicName(const DeclContext &ctx, const Decl &decl,
                                       CoqPrinter &print,
                                       ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printAtomicName", loc::of(decl));

    auto unsupported = [&](StringRef what) -> auto & {
        ::unsupported(cprint, loc::of(decl)) << what << "\n";
        guard::ctor ctor(print, "Nunsupported_atomic", false);
        return print.str(what);
    };

    // finds the duplicate index for a name. For example, the clang AST
    // sometimes ends up with multiple variables with the same name, e.g. due to
    // template parameter pack expansion. This logic aims to find which index we
    // want.
    auto duplicate_index = [&](const NamedDecl &nd) -> unsigned {
        if (auto dc = decl.getParentFunctionOrMethod()) {
            auto body = dyn_cast<FunctionDecl>(dc)->getBody();
            /* Count declarations with the same name as [nd] in [body] but
             * _stop_ when visiting [nd]. */
            struct Finder : RecursiveASTVisitor<Finder> {
                unsigned count{0};
                int result{-1};
                const NamedDecl *const target;
                const std::string target_name;
                Finder(const NamedDecl *_target)
                    : target(_target), target_name(_target->getNameAsString()) {
                }
                bool shouldVisitLambdaBody() const { return false; }
                bool VisitDecl(Decl *d) {
                    if (d == target) {
                        result = count;
                        return false; // stop traversal
                    } else if (auto nd2 = dyn_cast<NamedDecl>(d)) {
                        if (target_name == nd2->getNameAsString())
                            ++count;
                    }
                    return true;
                }
            } finder{&nd};
            finder.TraverseStmt(body);
            if (finder.result < 0) {
                // TODO: figure out what is wrong in the above code that we
                // can see a reference to a name that is not in scope.
                logging::verbose() << "Failed to find target "
                                   << nd.getNameAsString() << " in ";
                body->dump(logging::verbose(), ctx.getParentASTContext());
            }
            return finder.result;
        }
        return 0;
    };

    auto ident = [&]() -> auto & {
        if (auto nd = isNamed(decl)) {
            auto n = duplicate_index(*nd);
            if (n == -1) {
                guard::ctor _{print, "Nunsupported"};
                return print.str("failed to find identifier");
            } else {
                guard::ctor _(print, "Nid", false);
                if (n) {
                    auto t = nd->getNameAsString();
                    t += "'" + std::to_string(n - 1);
                    return print.str(t);
                } else {
                    return print.str(nd->getName());
                }
            }
        }
        always_assert(false && "ident for un-named term");
        return unsupported("ident for un-named term");
    };

    auto ident_or_anon = [&](const std::optional<std::string> anon_error =
                                 std::nullopt) -> auto & {
        if (auto nd = isNamed(decl)) {
            return ident();
        } else if (!anon_error) {
            guard::ctor _(print, "Nanon", false);
            return print.output() << getAnonymousIndex(ctx, decl, cprint);
        } else
            return unsupported(anon_error.value());
    };
    auto by_first_decl = [&](const TagDecl *decl) {
        // this heuristic tries to construct a name using the first declaration
        // that has that type. For example,
        //
        //  struct { } x;
        //
        // the name of the struct is essentially [decltype(x)].
        for (auto by_decl = decl->getNextDeclInContext(); by_decl;
             by_decl = by_decl->getNextDeclInContext()) {
            if (auto vd = dyn_cast<ValueDecl>(by_decl)) {
                auto type = vd->getType().getTypePtr();
                if (type->getAsTagDecl() == decl && vd->getIdentifier()) {
                    guard::ctor _(print, "Nby_first_decl", false);
                    print.str(vd->getIdentifier()->getName());
                    return true;
                }
                break;
            }
            // This returns [false] if [by_decl] is not a lexical child of
            // [decl]
            for (auto i = by_decl->getLexicalDeclContext(); i;
                 i = i->getParent()) {
                if (i->isTranslationUnit())
                    return false;
            }
        }
        return false;
    };

    if (auto td = dyn_cast<TagDecl>(&decl)) {
        if (isNamed(*td)) {
            return ident();
        }
        if (auto type_def = td->getTypedefNameForAnonDecl()) {
            guard::ctor _(print, "Nid", false);
            return print.str(type_def->getName());
        }
        if (by_first_decl(td))
            return print.output();
    }
    if (auto rd = dyn_cast<RecordDecl>(&decl)) {
        if (rd->getParent()->isTranslationUnit()) {
            logging::unsupported()
                << "Anonymous global records without declarations are not "
                   "supported. These can not be referenced in C++!\n "
                << fmt::dump(*rd);
            return unsupported("record");
        }
        for (auto i : rd->fields()) {
            if (i->getIdentifier()) {
                guard::ctor _(print, "Nrecord_by_field", false);
                return print.str(i->getIdentifier()->getName());
            }
        }
    } else if (auto ed = dyn_cast<EnumDecl>(&decl)) {
        for (auto i : ed->enumerators()) {
            if (i->getIdentifier()) {
                guard::ctor _(print, "Nenum_by_enumerator", false);
                return print.str(i->getIdentifier()->getName());
            }
        }
        if (ed->getParent()->isTranslationUnit()) {
            logging::unsupported() << "Unsupported empty enumeration in global "
                                      "context. These can not be "
                                      "referenced in C++!\n"
                                   << fmt::dump(*ed);
            return unsupported("enum");
        }
    } else if (auto ns = dyn_cast<NamespaceDecl>(&decl)) {
        if (isNamed(*ns)) {
            return ident();
        }
        return print.output() << "Nanonymous";
        /*
        for (auto i : ns->decls()) {
          if (auto nd = dyn_cast<NamedDecl>(i)) {
            if (nd->getIdentifier()) {
              guard::ctor _(print, "Nnamespace_by_decl", false);
              return print.str(nd->getIdentifier()->getName());
            }
          }
        } */
    }

    switch (decl.getKind()) {
    case Decl::Kind::Namespace:
    case Decl::Kind::Record:
    case Decl::Kind::CXXRecord:
    case Decl::Kind::Enum:
    case Decl::Kind::TypeAlias:
    case Decl::Kind::Typedef:
    case Decl::Kind::ClassTemplate:
        return ident_or_anon();

    case Decl::Kind::Field:
        /*
        TODO: Other parts of cpp2v emit anonymous fields using
        <<field_name.t>>. Here, we use <<Nanon>>.
        */
        return ident_or_anon();

    case Decl::Kind::FunctionTemplate: {
        // TODO: this does not work
        auto &fd = *cast<FunctionTemplateDecl>(decl).getTemplatedDecl();
        return printFunctionName(print, fd, cprint);
        // guard::ctor _(print, "Nfunction", false);
        // printFunctionQualifiers(print, fd, cprint) << fmt::nbsp;
        // printFunctionName(print, fd, cprint) << fmt::nbsp;
        // return printFunctionParamTypes(print, fd, cprint);
    }
    case Decl::Kind::Function:
    case Decl::Kind::CXXMethod:
    case Decl::Kind::CXXConstructor:
    case Decl::Kind::CXXDestructor:
    case Decl::Kind::CXXConversion: {
        auto &fd = cast<FunctionDecl>(decl);
        return printFunctionName(print, fd, cprint);
    }

    case Decl::Kind::TypeAliasTemplate:
    case Decl::Kind::VarTemplate:
    case Decl::Kind::VarTemplateSpecialization:
    case Decl::Kind::VarTemplatePartialSpecialization:
        return ident_or_anon("anonymous template");

    case Decl::Kind::Var:
        return ident_or_anon("anonymous variable");

    case Decl::Kind::EnumConstant:
        /*
        Enum constant names should not arise in practice (see
        `Eenum_const`). They're supported here for `--test-name`.
        */
        return ident_or_anon("anonymous enum constant");
        // TODO: Ndecltype
        // TODO: Nclosure
    case Decl::Kind::Binding:
        return ident_or_anon("anonymous binding");
    default:
        std::string what;
        llvm::raw_string_ostream os{what};
        os << "atomic name of kind " << decl.getDeclKindName();
        return unsupported(what);
    }
}

static fmt::Formatter &printName(CoqPrinter &print, const Decl &decl,
                                 ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("structured::printName", loc::of(decl));
    if (auto nd = dyn_cast<NamedDecl>(&decl)) {
        if (print.reference(nd))
            return print.output();
    } else {
        llvm::errs() << "not a named decl\n";
        decl.dump();
        always_assert(false);
    }

    auto name = [&]() {
        auto ctx = getNonIgnorableAncestor(decl, cprint);
        if (ctx->isTranslationUnit()) {
            guard::ctor _(print, "Nglobal", false);
            printAtomicName(ctx, decl, print, cprint);
        } else {
            guard::ctor _(print, "Nscoped", false);
            cprint.printName(print, toDecl(ctx, cprint, loc::of(decl)))
                << fmt::nbsp;
            printAtomicName(ctx, decl, print, cprint);
        }
    };
    auto parameters = [&](auto dct) {
        print.list(dct->getTemplateParameters()->asArray(),
                   [&](const clang::NamedDecl *p) {
                       guard::ctor _(print, "Atype", false);
                       guard::ctor __(print, "Tparam", false);
                       print.str(p->getNameAsString());
                   });
    };

    if (auto cd = dyn_cast<CXXRecordDecl>(&decl)) {
        if (auto dct = cd->getDescribedClassTemplate()) {
            guard::ctor _(print, "Ninst", true);
            name();
            print.output() << fmt::nbsp;
            parameters(dct);
            return print.output();
        }
    } else if (auto fd = dyn_cast<FunctionDecl>(&decl)) {
        if (auto dct = fd->getDescribedFunctionTemplate()) {
            guard::ctor _(print, "Ninst", true);
            name();
            print.output() << fmt::nbsp;
            parameters(dct);
            return print.output();
        }
    }

    auto sd = recoverSpecialization(decl);
    if (sd) {
        print.ctor("Ninst", false);
    }

    name();

    if (sd) {
        print.output() << fmt::nbsp;
        printTemplateArgumentList(print, sd->args, cprint, loc::of(decl));
        print.end_ctor();
    }
    return print.output();
}

static fmt::Formatter &printDtorName(CoqPrinter &print,
                                     const CXXRecordDecl &decl,
                                     ClangPrinter &cprint) {
    if (ClangPrinter::debug && cprint.trace(Trace::Name))
        cprint.trace("printDtorName", loc::of(decl));

    guard::ctor _(print, "Nscoped", false);
    printName(print, decl, cprint) << fmt::nbsp;
    return print.output() << "Ndtor";
}

} // namespace structured

template <typename T>
T &deref(CoqPrinter &print, ClangPrinter &cprint, const std::string whence,
         T *p, loc::loc loc) {
    if (!p) {
        fatal(cprint, loc) << whence << ": null pointer\n";
        print.die();
    }
    return *p;
}

fmt::Formatter &ClangPrinter::printNameComment(CoqPrinter &print,
                                               const Decl &decl) {
    if (trace(Trace::Name))
        trace("printNameComment", loc::of(decl));
    if (comment_)
        if (auto nd = dyn_cast<NamedDecl>(&decl)) {
            std::string cmt;
            llvm::raw_string_ostream os{cmt};
            structured::printNameForDiagnostics(os, *nd, getContext());
            return print.cmt(cmt);
        }
    return print.output();
}

fmt::Formatter &ClangPrinter::printNameAsKey(CoqPrinter &print,
                                             const Decl &decl) {
    if (trace(Trace::Name))
        trace("printNameAsKey", loc::of(decl));
    return printName(print, decl);
}

fmt::Formatter &ClangPrinter::printNameAsKey(CoqPrinter &print, const Decl *p,
                                             loc::loc loc) {
    return printNameAsKey(print, deref(print, *this, "printNameAsKey", p, loc));
}

fmt::Formatter &ClangPrinter::printName(CoqPrinter &print, const Decl &decl,
                                        bool full) {
    if (trace(Trace::Name))
        trace("printName", loc::of(decl));
    if (full) {
        auto temp = withDecl(&decl);
        return structured::printName(print, decl, temp);
    } else
        return structured::printAtomicName(*(decl.getDeclContext()), decl,
                                           print, *this);
}

fmt::Formatter &ClangPrinter::printName(CoqPrinter &print, const Decl *p,
                                        loc::loc loc, bool full) {
    return printName(print, deref(print, *this, "printName", p, loc), full);
}

fmt::Formatter &ClangPrinter::printUnsupportedName(CoqPrinter &print,
                                                   StringRef msg) {
    guard::ctor _(print, "Nunsupported", false);
    return print.str(msg);
}

fmt::Formatter &ClangPrinter::printDtorName(CoqPrinter &print,
                                            const CXXRecordDecl &decl) {
    if (trace(Trace::Name))
        trace("printDtorName", loc::of(decl));
    return structured::printDtorName(print, decl, *this);
}

fmt::Formatter &ClangPrinter::printUnqualifiedName(CoqPrinter &print,
                                                   const NamedDecl &decl) {
    if (trace(Trace::Name))
        trace("printUnqualifiedName", loc::of(decl));
    if (auto id = decl.getIdentifier())
        return print.str(id->getName());
    else {
        unsupported(*this, loc::of(decl)) << "unnamed, unqualified name\n";
        return print.str("<unsupported unnamed, unqualified name>");
    }
}

fmt::Formatter &ClangPrinter::printUnqualifiedName(CoqPrinter &print,
                                                   const NamedDecl *p,
                                                   loc::loc loc) {
    return printUnqualifiedName(
        print, deref(print, *this, "printUnqualifiedName", p, loc));
}

fmt::Formatter &ClangPrinter::printTemplateParameters(CoqPrinter &print,
                                                      const Decl &decl,
                                                      bool as_arg) {
    if (trace(Trace::Name))
        trace("printTemplateParameters", loc::of(decl));
    return structured::printTemplateParameters(print, decl, *this, as_arg);
}

fmt::Formatter &ClangPrinter::printTemplateArguments(CoqPrinter &print,
                                                     const Decl &decl) {
    if (trace(Trace::Name))
        trace("printTemplateArguments", loc::of(decl));
    return structured::printTemplateArguments(print, decl, *this);
}

fmt::Formatter &ClangPrinter::printTemplateArgumentList(
    CoqPrinter &print, const TemplateArgumentList &args, loc::loc loc) {
    if (trace(Trace::Name))
        trace("printTemplateArgumentList", loc);
    return structured::printTemplateArgumentList(print, args, *this, loc);
}

fmt::Formatter &
ClangPrinter::printTemplateArgumentList(CoqPrinter &print,
                                        ArrayRef<TemplateArgument> args) {
    if (trace(Trace::Name))
        trace("printTemplateArgumentList", loc::none);
    auto &cprint = *this;
    return print.list(args, [&](auto &arg) {
        structured::printTemplateArgument(print, arg, cprint, loc::none);
    });
}

fmt::Formatter &
ClangPrinter::printTemplateArgumentList(CoqPrinter &print,
                                        ArrayRef<TemplateArgumentLoc> args) {
    if (trace(Trace::Name))
        trace("printTemplateArgumentList", loc::none);
    auto &cprint = *this;
    return print.list(args, [&](auto &arg) {
        structured::printTemplateArgument(print, arg.getArgument(), cprint,
                                          loc::of(arg));
    });
}

namespace {
fmt::Formatter &printDeclarationName(CoqPrinter &print,
                                     const DeclarationName &name,
                                     ClangPrinter &cprint) {
    /*
      TODO: This seems

      - A bit limited --- compare to/share code with
      structured::printFunctionName

      - A bit off --- `name.getAsString` does not account for `Ndtor` etc
      */
    switch (name.getNameKind()) {
    case DeclarationName::NameKind::Identifier: {
        guard::ctor _(print, "Nid", false);
        print.str(name.getAsString());
        break;
    }

    default:
        llvm::errs() << "printDeclarationName(" << name.getNameKind() << ")";
        name.dump();
        print.output() << "(Nunsupported \"printDeclarationName("
                       << name.getNameKind() << ")\")";
    }
    return print.output();
}
} // namespace

fmt::Formatter &ClangPrinter::printNestedName(CoqPrinter &print,
                                              const NestedNameSpecifier *spec,
                                              loc::loc loc) {
    if (auto ns = spec->getAsNamespace()) {
        printName(print, ns, loc);
    } else if (auto nsa = spec->getAsNamespaceAlias()) {
        printName(print, nsa, loc);
    } else if (auto type = spec->getAsType()) {
        guard::ctor _(print, "Ndependent", false);
        printType(print, type, loc);
    } else if (auto id = spec->getAsIdentifier()) {
        bool is_global = not spec->getPrefix() ||
                         spec->getPrefix()->getKind() ==
                             NestedNameSpecifier::SpecifierKind::Global;

        guard::ctor _(print, is_global ? "Nglobal" : "Nscoped", false);
        if (not is_global) {
            printNestedName(print, spec->getPrefix(), loc) << fmt::nbsp;
        }
        // TODO: this is incorrect. i need to print an atomic name, possibly
        // with specializations.
        guard::ctor __(print, "Nid", false);
        print.str(id->getName());
    } else {
        unsupported(*this, loc, true)
            << "unsupported NestedNameSpecifier " << spec->getKind() << "\n";
        guard::ctor _{print, "Nunsupported", false};
        print.output() << "\"NestedNameSpecifier(" << spec->getKind() << ")\"";
    }
    return print.output();
}

fmt::Formatter &ClangPrinter::printUnresolvedName(CoqPrinter &print,
                                                  const NestedNameSpecifier *nn,
                                                  const DeclarationName &name,
                                                  loc::loc loc) {

    if (not nn) {
        // There is no prefix. Incomplete!
        guard::ctor _(print, "Nlocal", false);
        return printDeclarationName(print, name, *this);
    } else if (nn->getKind() == NestedNameSpecifier::Global) {
        guard::ctor _(print, "Nglobal", false);
        return printDeclarationName(print, name, *this);
    } else {
        guard::ctor _(print, "Nscoped", false);
        printNestedName(print, nn, loc) << fmt::nbsp;
        return printDeclarationName(print, name, *this);
    }
}

fmt::Formatter &ClangPrinter::printUnresolvedName(
    CoqPrinter &print, const NestedNameSpecifier *nn,
    const DeclarationName &name,
    llvm::ArrayRef<clang::TemplateArgumentLoc> template_args, loc::loc loc) {
    if (template_args.empty())
        return printUnresolvedName(print, nn, name, loc);
    else {
        guard::ctor _(print, "Ninst", false);
        printUnresolvedName(print, nn, name, loc) << fmt::nbsp;
        return printTemplateArgumentList(print, template_args);
    }
}

fmt::Formatter &ClangPrinter::printUnresolvedName(
    CoqPrinter &print, const NestedNameSpecifier *nn,
    const DeclarationName &name,
    llvm::ArrayRef<clang::TemplateArgument> template_args, loc::loc loc) {
    if (template_args.empty())
        return printUnresolvedName(print, nn, name, loc);
    else {
        guard::ctor _(print, "Ninst", false);
        printUnresolvedName(print, nn, name, loc) << fmt::nbsp;
        return printTemplateArgumentList(print, template_args);
    }
}
