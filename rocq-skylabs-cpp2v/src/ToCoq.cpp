/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "Filter.hpp"
#include "IRBuilder.hpp"
#include "LocationEmitter.hpp"
#include "ModuleBuilder.hpp"
#include "RocqEmitter.hpp"
#include "Sharing.hpp"
#include "SpecCollector.hpp"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include "clang/Basic/AddressSpaces.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/Version.inc"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include <Formatter.hpp>
#include <cerrno>
#include <cstdio>
#include <list>
#include <sstream>
#include <system_error>

// Declares clang::SyntaxOnlyAction.
#include "SpecCollector.hpp"
#include "ToCoq.hpp"
#include "clang/Frontend/FrontendActions.h"

using namespace clang;
using namespace fmt;

static void writeIRLines(Formatter &fmt, const std::string &text,
                         bool listElements = false) {
    std::istringstream input(text);
    std::string line;
    while (std::getline(input, line)) {
        if (line.empty())
            continue;
        fmt << line;
        if (listElements)
            fmt << " ::";
        fmt << fmt::line;
    }
}

[[noreturn]] static void failIR(llvm::Error failure,
                                llvm::StringRef operation) {
    logging::fatal() << operation << ": " << llvm::toString(std::move(failure))
                     << "\n";
    logging::die();
}

template <typename CLOSURE>
void with_open_file(const std::optional<std::string> path,
                    CLOSURE f /* void f(Formatter&) */) {
    if (path.has_value()) {
        const auto &target = *path;
        auto write_path = target == "-" ? target : target + ".partial";
        std::error_code ec;
        llvm::raw_fd_ostream output(write_path, ec);
        if (ec.value()) {
            logging::fatal() << write_path << ": " << ec.message() << "\n";
            logging::die();
        } else {
            Formatter fmt{output};
            f(fmt);
            fmt.flush();
            output.close();
            if (output.has_error()) {
                logging::fatal()
                    << write_path << ": " << output.error().message() << "\n";
                logging::die();
            }
            if (target != "-") {
                if (std::rename(write_path.c_str(), target.c_str()) != 0) {
                    std::error_code ec(errno, std::generic_category());
                    logging::fatal() << write_path << ": could not rename to "
                                     << target << ": " << ec.message() << "\n";
                    logging::die();
                }
            }
        }
    }
}

namespace name_test {
static void bug(ClangPrinter &cprint, loc::loc loc, const std::string what) {
    cprint.error_prefix(logging::fatal(), loc) << "BUG: " << what << "\n";
    cprint.debug_dump(loc);
    logging::die();
}

static void test(const clang::Decl *decl, CoqPrinter &print,
                 ClangPrinter &cprint) {
    if (decl && decl->isImplicit() && isa<TypedefDecl>(decl))
        // Suppress clang's implicit typedefs
        return;
    else if (decl) {
        print.output() << fmt::line;
        std::string cmt;
        llvm::raw_string_ostream os{cmt};
        os << loc::trace(loc::of(decl), cprint.getContext());
        print.cmt(cmt) << fmt::nbsp;
        cprint.printName(print, *decl);
        print.output() << " ::" << fmt::line;
    } else
        bug(cprint, loc::none, "null declaration");
}
} // namespace name_test

void ToCoqConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
    if (Context.getDiagnostics().getClient()->getNumErrors() == 0) {
        toCoqModule(&Context, Context.getTranslationUnitDecl());
    }
}

static const char *toCoqIntRank(clang::TargetInfo::IntType ty) {
    switch (ty) {
    case clang::TargetInfo::SignedChar:
    case clang::TargetInfo::UnsignedChar:
        return "int_rank.Ichar";
    case clang::TargetInfo::SignedShort:
    case clang::TargetInfo::UnsignedShort:
        return "int_rank.Ishort";
    case clang::TargetInfo::SignedInt:
    case clang::TargetInfo::UnsignedInt:
        return "int_rank.Iint";
    case clang::TargetInfo::SignedLong:
    case clang::TargetInfo::UnsignedLong:
        return "int_rank.Ilong";
    case clang::TargetInfo::SignedLongLong:
    case clang::TargetInfo::UnsignedLongLong:
        return "int_rank.Ilonglong";
    case clang::TargetInfo::NoInt:
        logging::fatal() << "TargetInfo has no integer type for uintptr_t\n";
        logging::die();
    }
    logging::fatal() << "Unknown TargetInfo integer type\n";
    logging::die();
}

static const char *toCoqSigned(bool isSigned) {
    return isSigned ? "Signed" : "Unsigned";
}

static const char *toCoqEndian(const clang::TargetInfo &target) {
    if (target.isBigEndian())
        return "Big";
    always_assert(target.isLittleEndian());
    return "Little";
}

static const char *toCoqLangVersion(const clang::LangOptions &lang) {
    if (lang.CPlusPlus26)
        return "lang_version.Cpp26";
    if (lang.CPlusPlus23)
        return "lang_version.Cpp23";
    if (lang.CPlusPlus20)
        return "lang_version.Cpp20";
    if (lang.CPlusPlus17)
        return "lang_version.Cpp17";
    if (lang.CPlusPlus14)
        return "lang_version.Cpp14";
    if (lang.CPlusPlus11)
        return "lang_version.Cpp11";
    if (lang.CPlusPlus)
        return "lang_version.Cpp03";

    logging::fatal() << "cpp2v requires a C++ language mode\n";
    logging::die();
}

static fmt::Formatter &printAbi(fmt::Formatter &out,
                                const clang::ASTContext &ctxt) {
    const auto &target = ctxt.getTargetInfo();
    return out << "(abi.mkT " << toCoqIntRank(target.getUIntPtrType())
               << fmt::nbsp << toCoqSigned(ctxt.getLangOpts().CharIsSigned)
               << fmt::nbsp
               << toCoqSigned(
                      clang::TargetInfo::isTypeSigned(target.getWCharType()))
               << fmt::nbsp << toCoqEndian(target) << fmt::nbsp
               << toCoqLangVersion(ctxt.getLangOpts()) << ")";
}

void ToCoqConsumer::toCoqModule(clang::ASTContext *ctxt,
                                clang::TranslationUnitDecl *decl) {

#if 0
    NoInclude noInclude(ctxt->getSourceManager());
    FromComment fromComment(ctxt);
    std::list<Filter*> filters;
    filters.push_back(&noInclude);
    filters.push_back(&fromComment);
    Combine<Filter::What::NOTHING, Filter::max> filter(filters);
#endif
    SpecCollector specs;
    Default filter(Filter::What::DEFINITION);

    ::Module mod(trace_);

    bool templates = templates_file_.has_value() ||
                     (output_file_.has_value() && output_templates_) ||
                     name_test_file_.has_value();
    build_module(decl, mod, filter, specs, compiler_, elaborate_, templates);

    std::unique_ptr<ir::TranslationUnitIR> ownedUnit;
    std::optional<ir::SharingPlan> ownedSharing;
    const bool semanticOutput = output_file_.has_value() ||
                                locations_file_.has_value() ||
                                templates_file_.has_value();
    if (semanticOutput) {
        auto built = ir::IRBuilder::buildModule(
            *ctxt, mod, &compiler_->getSema(), typedefs_, comment_);
        if (!built)
            failIR(built.takeError(), "owned IR construction failed");
        ownedUnit = std::move(built->unit);
        if (sharing_) {
            auto plan = ir::IRSharing::analyze(
                *ownedUnit, ir::IRSharing::productionSeeds(*ownedUnit));
            if (!plan)
                failIR(plan.takeError(), "owned IR sharing analysis failed");
            ownedSharing = std::move(*plan);
        }
    }

    auto parser = [&](CoqPrinter &print) -> auto & {
        StringRef coqmod(print.templates() ? "skylabs.lang.cpp.mparser"
                                           : "skylabs.lang.cpp.parser");
        return print.output()
               << (interactive_.has_value() ? "Import " : "Require Import ")
               << coqmod << "." << fmt::line << fmt::line;
    };

    auto bytestring = [&](CoqPrinter &print) -> auto & {
        return print.output()
               << "#[local] Open Scope pstring_scope." << fmt::line;
    };

    auto check_types = [&](Formatter &fmt, const char *name) {
        if (!interactive_.has_value()) {
            fmt << fmt::line << "Require skylabs.lang.cpp.syntax.typed.";
        }
        fmt << fmt::line << "Goal typed.decltype.check_tu "
            << interactive_.value_or("source")
            << " = trace.Success tt. Proof. vm_compute; reflexivity. Abort."
            << fmt::line;
    };

    ir::SemanticRocqEmitter irEmitter({sharing_, true, false});
    auto irSharingDefinitions = [&](Formatter &fmt, bool noimport = false) {
        if (!ownedSharing)
            return;
        if (!noimport)
            fmt << "Import skylabs.lang.cpp.parser." << fmt::line << fmt::line;
        auto definitions =
            irEmitter.emitSharingDefinitions(*ownedUnit, *ownedSharing);
        if (!definitions)
            failIR(definitions.takeError(), "owned IR sharing emission failed");
        writeIRLines(fmt, *definitions);
    };
    auto writeStaticIR = [&](const char *name, Formatter &fmt,
                             bool noimport = false) {
        if (!noimport)
            fmt << "Import skylabs.lang.cpp.parser." << fmt::line
                << "#[local] Open Scope pstring_scope." << fmt::line
                << fmt::line;
        if (attributes_)
            fmt << "#[" << *attributes_ << "]" << fmt::line;
        fmt << "cpp.prog " << name << fmt::indent << fmt::line << "abi ";
        printAbi(fmt, *ctxt) << fmt::line;
        fmt << "defns" << fmt::indent;
        llvm::Expected<std::string> events =
            ownedSharing ? irEmitter.emitOrdinary(*ownedUnit, *ownedSharing)
                         : irEmitter.emitOrdinary(*ownedUnit);
        if (!events)
            failIR(events.takeError(), "owned ordinary emission failed");
        writeIRLines(fmt, *events);
        fmt << "." << fmt::outdent << fmt::outdent << fmt::line;
    };
    auto writeTemplatesIR = [&](const char *name, Formatter &fmt,
                                const ir::SharingPlan *plan = nullptr,
                                bool noimport = false) {
        if (!noimport)
            fmt << "Import skylabs.lang.cpp.mparser." << fmt::line
                << "#[local] Open Scope pstring_scope." << fmt::line
                << fmt::line;
        fmt << "Definition " << name << " : Mtranslation_unit :=" << fmt::indent
            << fmt::line
            << "Eval reduce_translation_unit in Mtranslation_unit.decls ("
            << fmt::indent << fmt::line;
        llvm::Expected<std::string> events =
            plan ? irEmitter.emitTemplates(*ownedUnit, *plan)
                 : irEmitter.emitTemplates(*ownedUnit);
        if (!events)
            failIR(events.takeError(), "owned template emission failed");
        writeIRLines(fmt, *events, true);
        fmt << "nil)." << fmt::outdent << fmt::outdent << fmt::line;
    };

    auto static_and_templates = [&](Formatter &fmt) {
        /* This block generates the following setup:

        ```
        (* top-level Require & Import *)
        (* pre-printing *)
        Section static.
          (* non-template definitions *)
        End static.

        Section meta.
          Import skylabs.lang.cpp.mparser."
          (* template definitions *)
        End meta.

        Definition source := with_templates static_tu meta_tu.
        #[deprecated]
        Abbreviation module := source.
        ```

        */
        if (interactive_.has_value()) {
            fmt << "Require skylabs.lang.cpp.parser." << fmt::line
                << "Require skylabs.lang.cpp.mparser." << fmt::line
                << "Section __cpp_prog." << fmt::line << fmt::indent
                << "Import skylabs.lang.cpp.parser." << fmt::line;

        } else {
            fmt << "Require Import skylabs.lang.cpp.parser.plugin.cpp2v."
                << fmt::line << "Require Import skylabs.lang.cpp.parser."
                << fmt::line << "Require skylabs.lang.cpp.mparser." << fmt::line
                << fmt::line;
        }
        fmt << "#[local] Open Scope pstring_scope." << fmt::line;

        irSharingDefinitions(fmt, true);

        // BEGIN: Section static
        // fmt << "Section static." << fmt::indent << fmt::line;

        std::string static_name{"static__"};
        static_name += interactive_.value_or("source");

        writeStaticIR(static_name.c_str(), fmt, true);

        // fmt << fmt::outdent << "End static." << fmt::line << fmt::line;
        // END: Section static

        // BEGIN: Section meta
        // fmt << "Section meta." << fmt::indent << fmt::line;

        std::string meta_name{"meta__"};
        meta_name += interactive_.value_or("source");

        writeTemplatesIR(meta_name.c_str(), fmt,
                         ownedSharing ? &*ownedSharing : nullptr);

        // fmt << fmt::outdent << "End meta." << fmt::line << fmt::line;
        // END: Section meta

        if (interactive_.has_value()) {
            fmt << fmt::outdent << "End __cpp_prog." << fmt::line;
        }

        fmt << "Definition " << interactive_.value_or("source")
            << " := skylabs.lang.cpp.mparser.tu.with_templates " << static_name
            << " " << meta_name << "." << fmt::line;

        if (!interactive_.has_value()) {
            // NOTE: Backwards compatibility
            fmt << "#[deprecated(note=\"use [source] instead.\")]" << fmt::line
                << "Abbreviation module := source (only parsing)." << fmt::line;
        }

        if (check_types_) {
            check_types(fmt, interactive_.value_or("source").c_str());
        }
    };

    auto static_only = [&](Formatter &fmt) {
        if (interactive_.has_value()) {
            // The interactive host already loaded the parser. Limit all
            // command side effects to a deterministic section.
            fmt << "Section cpp_prog__" << interactive_.value() << "__."
                << fmt::line;
        } else {
            fmt << "Require Import skylabs.lang.cpp.parser.plugin.cpp2v."
                << fmt::line;
        }

        irSharingDefinitions(fmt);
        writeStaticIR(interactive_.value_or("source").c_str(), fmt);

        if (interactive_.has_value()) {
            fmt << "End cpp_prog__" << interactive_.value() << "__."
                << fmt::line;
        } else {
            // NOTE: Backwards compatibility
            fmt << "Abbreviation module := source (only parsing)." << fmt::line;
        }

        if (check_types_)
            check_types(fmt, interactive_.value_or("source").c_str());
    };

    auto templates_only = [&](Formatter &fmt) {
        fmt << "Require skylabs.lang.cpp.mparser." << fmt::line;
        writeTemplatesIR("templates", fmt);
    };

    if (output_templates_) {
        with_open_file(output_file_, static_and_templates);
    } else {
        with_open_file(output_file_, static_only);
    }

    if (locations_file_) {
        ir::LocationRocqEmitter locationEmitter({output_templates_});
        auto companion = locationEmitter.emit(*ownedUnit);
        if (!companion)
            failIR(companion.takeError(),
                   "owned source-location emission failed");
        with_open_file(locations_file_,
                       [&](Formatter &fmt) { writeIRLines(fmt, *companion); });
    }

    with_open_file(templates_file_, templates_only);

    with_open_file(name_test_file_, [&](Formatter &fmt) {
        Cache c;
        CoqPrinter print(fmt, /*templates*/ true, c);
        ClangPrinter cprint(compiler_, ctxt, trace_, comment_);

        auto testnames = [&](const std::string id,
                             std::function<void()> k) -> auto & {
            print.output() << fmt::line << "Definition " << id
                           << " : list Mname :=" << fmt::indent << fmt::line;
            print.begin_list();
            k();
            print.end_list();
            return print.output() << "." << fmt::outdent << fmt::line;
        };

        parser(print);
        bytestring(print);

        testnames("module_names", [&]() {
            for (auto decl : mod.declarations()) {
                name_test::test(decl, print, cprint);
            }
            for (auto decl : mod.definitions()) {
                name_test::test(decl, print, cprint);
            }
        });
        testnames("template_names", [&]() {
            for (auto decl : mod.template_declarations()) {
                name_test::test(decl, print, cprint);
            }
            for (auto decl : mod.template_definitions()) {
                name_test::test(decl, print, cprint);
            }
        });
    });
}
