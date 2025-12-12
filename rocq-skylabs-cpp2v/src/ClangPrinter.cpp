/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "Assert.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/AST/TemplateBase.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Sema/Sema.h>
#include <optional>

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
                           clang::ASTContext *context, Trace::Mask trace,
                           bool comment, bool typedefs)
    : compiler_(compiler), context_(context), trace_(trace), comment_{comment},
      typedefs_{typedefs} {
    mangleContext_ =
        ItaniumMangleContext::create(*context, compiler->getDiagnostics());
}

unsigned ClangPrinter::getTypeSize(const BuiltinType *t) const {
    return this->context_->getTypeSize(t);
}

std::optional<std::pair<const CXXRecordDecl *, clang::Qualifiers>>
ClangPrinter::getLambdaClass() const {
    if (auto md = dyn_cast_or_null<CXXMethodDecl>(getDecl())) {
        auto lambda = md->getParent();
        if (lambda->isLambda()) {
            Qualifiers cv;
            if (md->isConst())
                cv.addConst();
            if (md->isVolatile())
                cv.addVolatile();
            return {{lambda, cv}};
        }
    }
    return std::nullopt;
}

fmt::Formatter &ClangPrinter::printParamName(CoqPrinter &print,
                                             const ParmVarDecl *decl) {
    if (trace(Trace::Name))
        trace("printParamName", loc::of(decl));

    always_assert(decl->getDeclContext()->isFunctionOrMethod() &&
                  "function or method");
    if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
        int i = 0;
        clang::IdentifierInfo *info = nullptr;
        unsigned offset = 0;
        for (auto p : fd->parameters()) {
            if (p->getIdentifier() == info) {
                offset++;
            } else
                offset = 0;
            if (p == decl) {
                if (decl->getIdentifier()) {
                    print.output() << "\"";
                    decl->printName(print.output().nobreak());
                    if (offset)
                        print.output() << "..." << offset;
                    return print.output() << "\"";
                } else {
                    return print.output() << "(localname.anon " << i << ")";
                }
            }
            info = p->getIdentifier();
            ++i;
        }
    }
    llvm::errs() << "failed to find parameter\n";
    auto loc = loc::of(decl);
    error_prefix(logging::fatal(), loc) << "error: cannot find parameter\n";
    debug_dump(loc);
    logging::die();
    return print.output();
}

fmt::Formatter &ClangPrinter::printValCat(CoqPrinter &print, const Expr *d) {
    if (trace(Trace::Type))
        trace("printValCat", loc::of(d));

    // note(gmm): Classify doesn't work on dependent types which occur in
    // templates that clang can't completely eliminate.

    if (print.templates()) {
        if (d->isLValue())
            print.output() << "Lvalue";
        else if (d->isPRValue())
            print.output() << "Prvalue";
        else if (d->isXValue())
            print.output() << "Xvalue";
        else {
            auto loc = loc::of(d);
            error_prefix(logging::fatal(), loc)
                << "error: cannot determine value category\n";
            debug_dump(loc);
            logging::die();
        }
        return print.output();
    }

    auto Class = d->Classify(*this->context_);
    if (Class.isLValue()) {
        print.output() << "Lvalue";
    } else if (Class.isXValue()) {
        print.output() << "Xvalue";
    } else if (Class.isPRValue()) {
        print.output() << "Prvalue";
    } else {
        always_assert(false);
        // fatal("unknown value category");
    }
    return print.output();
}

// TODO: this function has a lot of issues with it.
fmt::Formatter &ClangPrinter::printTemplateParam(CoqPrinter &print,
                                                 unsigned depth, unsigned index,
                                                 bool is_type, loc::loc loc) {
    if (trace(Trace::Name)) {
        trace("printTemplateParam", loc)
            << " depth=" << depth << " index=" << index << "\n";
    }

    auto process = [&](const TemplateParameterList *list) {
        if (list) {
            for (auto i : list->asArray()) {
                if (auto tpd = dyn_cast<TemplateTypeParmDecl>(i)) {
                    if (tpd->getDepth() != depth)
                        continue;
                    if (tpd->getIndex() == index) {
                        always_assert(print.templates());
                        guard::ctor _{print, "Tparam", false};
                        print.str(tpd->getName());
                        return true;
                    }
                } else if (auto tpd = dyn_cast<NonTypeTemplateParmDecl>(i)) {
                    if (tpd->getDepth() != depth)
                        continue;
                    if (tpd->getIndex() == index) {
                        always_assert(print.templates());
                        guard::ctor _{print, "Eparam", false};
                        print.str(tpd->getName());
                        return true;
                    }
                }
            }
        }
        return false;
    };

    auto up = [](const Decl *d) {
        auto dc = d->getDeclContext();
        return dc == nullptr ? nullptr : Decl::castFromDeclContext(dc);
    };

    for (auto d = decl_; d; d = up(d)) {
        if (auto psd = dyn_cast<ClassTemplatePartialSpecializationDecl>(d)) {
            if (process(psd->getTemplateParameters()))
                return print.output();
        } else if (auto fd = dyn_cast<FunctionDecl>(d)) {
            if (auto y = fd->getTemplateSpecializationArgs()) {
                auto ary = y->asArray();
                if (index >= ary.size()) {
                    // NOTE: this is debugging code
                    llvm::errs() << "Looking for depth=" << depth
                                 << " index=" << index << "\n";
                    for (auto xx = d; xx;
                         xx = Decl::castFromDeclContext(xx->getDeclContext())) {
                        llvm::errs() << xx->getDeclKindName();
                        if (auto nd = dyn_cast<NamedDecl>(xx))
                            llvm::errs() << " " << nd->getNameAsString();
                        llvm::errs() << "\n";
                    }
                    always_assert(false);
                } else {
                    auto &&v = ary[index];
                    switch (v.getKind()) {
                    case TemplateArgument::ArgKind::Type:
                        return printQualType(print, ary[index].getAsType(),
                                             loc);

                    case TemplateArgument::ArgKind::Integral: {
                        guard::ctor _{print, "Eint"};
                        print.output() << v.getAsIntegral() << fmt::nbsp;
                        return printQualType(print, v.getIntegralType(), loc);
                    }
                    case TemplateArgument::ArgKind::Expression: {
                        return printExpr(print, ary[index].getAsExpr());
                    }
                    default: {
                        guard::ctor _{print, "Eunsupported"};
                        print.output()
                            << "\"NonTypeTemplateParam " << v.getKind() << "\"";
                        return print.output();
                    }
                    }
                }

            } else if (auto x = fd->getDescribedTemplateParams()) {
                if (process(x))
                    return print.output();
            }
        } else if (auto rd = dyn_cast<CXXRecordDecl>(d)) {
            if (process(rd->getDescribedTemplateParams()))
                return print.output();
        } else if (auto tad = dyn_cast<TypeAliasDecl>(d)) {
            if (process(tad->getDescribedTemplateParams()))
                return print.output();
        } else if (auto vd = dyn_cast<VarDecl>(d)) {
            if (process(vd->getDescribedTemplateParams()))
                return print.output();
        } else {
            logging::verbose()
                << "Skipping over: " << d->getDeclKindName() << "\n";
        }
    }

    error_prefix(logging::debug(), loc)
        << "error: could not infer template parameter name at depth " << depth
        << ", index " << index << "\n";
    debug_dump(loc);
    // logging::die();

    if (is_type) {
        guard::ctor _{print, "Tunsupported"};
        return print.str("type template parameter");
    } else {
        guard::ctor _{print, "Eunsupported"};
        return print.str("template parameter)");
    }
}

fmt::Formatter &ClangPrinter::printField(CoqPrinter &print,
                                         const ValueDecl *decl) {
    if (trace(Trace::Decl))
        trace("printField", loc::of(decl));

    return printName(print, *decl);
}

std::string ClangPrinter::sourceLocation(const SourceLocation loc) const {
    return loc.printToString(this->context_->getSourceManager());
}

std::string ClangPrinter::sourceRange(const SourceRange sr) const {
    return sr.printToString(this->context_->getSourceManager());
}

const Decl *ClangPrinter::getDecl() const { return decl_; }

llvm::raw_ostream &ClangPrinter::debug_dump(loc::loc loc) {
    return logging::debug() << loc::dump(loc, getContext(), getDecl());
}

llvm::raw_ostream &ClangPrinter::error_prefix(llvm::raw_ostream &os,
                                              loc::loc loc) {
    return os << loc::prefix(loc, getContext(), getDecl());
}

llvm::raw_ostream &ClangPrinter::trace(StringRef whence, loc::loc loc) {
    auto &os = llvm::errs();
    os << "[TRACE] " << whence;
    auto decl = getDecl();
    if (loc::can_trace(loc, decl))
        os << " " << loc::trace(loc, getContext(), decl);
    return os << "\n";
}

fmt::Formatter &ClangPrinter::printVariadic(CoqPrinter &print, bool va) const {
    return print.output() << (va ? "Ar_Variadic" : "Ar_Definite");
}

fmt::Formatter &
ClangPrinter::printExceptionSpec(CoqPrinter &print,
                                 const clang::FunctionDecl &decl) {
    static constexpr auto NO_THROW = "exception_spec.NoThrow";
    static constexpr auto MAY_THROW = "exception_spec.MayThrow";
    static constexpr auto UNKNOWN = "exception_spec.Unknown";
    int retries = 0;
    auto fpt = decl.getFunctionType()->getAs<FunctionProtoType>();

    auto defaults_to_noexcept = [&]() {
        if (isa<CXXDestructorDecl>(decl))
            return true;
        if (auto ctor = dyn_cast<CXXConstructorDecl>(&decl)) {
            return ctor->isDefaultConstructor() || ctor->isCopyConstructor() ||
                   ctor->isMoveConstructor();
        }
        if (auto mem = dyn_cast<CXXMethodDecl>(&decl)) {
            return mem->isCopyAssignmentOperator() ||
                   mem->isMoveAssignmentOperator();
        }
        return false;
    };

    while (fpt && retries++ <= 1) {
        if constexpr (ClangPrinter::debug) {
            llvm::errs() << decl.getQualifiedNameAsString() << "@"
                         << (void *)(&decl) << " exception info "
                         << fpt->getExceptionSpecType() << "\n";
        }

        switch (fpt->getExceptionSpecType()) {
        case EST_Dynamic: {
            // This is incorrect
            logging::unsupported() << "UNSUPPORTED: throws() at "
                                   << decl.getLocation().printToString(
                                          compiler_->getSourceManager())
                                   << ".\n";
            return print.output() << UNKNOWN;
        }

        case EST_None: {
            // In C++, certain functions are implicitly declared no-throw, e.g.
            // default constructors.
            // For concrete functions, [EST_BasicNoexcept] is used to track
            // these, but this not the case for templates.
            // To make the decision robust we use [UNKNOWN] when we are in
            // a dependent context for these functions
            if (decl.isDependentContext() && defaults_to_noexcept()) {
                return print.output() << UNKNOWN;
            }
        }
            [[fallthrough]];
        case EST_MSAny:
            [[fallthrough]];
        case EST_NoexceptFalse:
            return print.output() << MAY_THROW;

        case EST_DynamicNone: // throw(), not enforced
            [[fallthrough]];
        case EST_NoThrow: // __declspec(nothrow); throwing exceptions from such
                          // functions is UB.
            // -
            // https://learn.microsoft.com/en-us/cpp/cpp/nothrow-cpp?view=msvc-170
            // - https://archive.is/frXcn /
            // https://devblogs.microsoft.com/oldnewthing/20180928-00/?p=99855
            [[fallthrough]];
        case EST_BasicNoexcept:
            [[fallthrough]];
        case EST_NoexceptTrue:
            return print.output() << NO_THROW;

            // TODO: The remaining cases are instances where clang has not
            // resolved the exception specification yet. This information
            // can be filled in via the [Sema] object, in particular:
            // - sema.EvaluateImplicitExceptionSpec,
            // - sema.ResolveExceptionSpec

        case EST_DependentNoexcept:
            [[fallthrough]];
        case EST_Unevaluated: {
            auto &sema = this->getCompiler().getSema();
            fpt = sema.ResolveExceptionSpec(decl.getLocation(), fpt);
            // if (decl.isImplicit()) {
            // 	sema.EvaluateImplicitExceptionSpec(
            // 		decl.getLocation(), const_cast<FunctionDecl *>(&decl));
            // } else {
            // sema.ResolveExceptionSpec(
            // 	decl.getLocation(),
            // 	decl.getFunctionType()->getAs<FunctionProtoType>());
            // }
            break;
        }

        case EST_Uninstantiated:
            break;

        case EST_Unparsed:
            return print.output() << UNKNOWN;
        }
    };
    logging::log(logging::Level::VERBOSER)
        << "Unresolved exception specification on "
        << decl.getQualifiedNameAsString()
        << " (clang value = " << decl.getExceptionSpecType() << ")"
        << "\n";

    return print.output() << UNKNOWN;
}

fmt::Formatter &ClangPrinter::printCallingConv(CoqPrinter &print,
                                               clang::CallingConv cc,
                                               loc::loc loc) {
#define PRINT(x)                                                               \
    case CallingConv::x:                                                       \
        print.output() << #x;                                                  \
        break;
#define OVERRIDE(x, y)                                                         \
    case CallingConv::x:                                                       \
        print.output() << #y;                                                  \
        break;
    switch (cc) {
        PRINT(CC_C);
        OVERRIDE(CC_X86RegCall, CC_RegCall);
        OVERRIDE(CC_Win64, CC_MsAbi);
#if 0
	PRINT(CC_X86StdCall);
	PRINT(CC_X86FastCall);
	PRINT(CC_X86ThisCall);
	PRINT(CC_X86VectorCall);
	PRINT(CC_X86Pascal);
	PRINT(CC_X86_64SysV);
	PRINT(CC_AAPCS);
	PRINT(CC_AAPCS_VFP);
	PRINT(CC_IntelOclBicc);
	PRINT(CC_SpirFunction);
	PRINT(CC_OpenCLKernel);
	PRINT(CC_Swift);
	PRINT(CC_PreserveMost);
	PRINT(CC_PreserveAll);
	PRINT(CC_AArch64VectorCall);
#endif
    default:
        error_prefix(logging::fatal(), loc)
            << "error: unsupported calling convention\n";
        debug_dump(loc);
        logging::die();
    }
    return print.output();
}

ClangPrinter ClangPrinter::withDecl(const clang::Decl *decl) const {
    return {*this, decl};
}
