/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Assert.hpp"
#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "DefaultTemplateAlias.hpp"
#include "Filter.hpp"
#include "ModuleBuilder.hpp"
#include "PrePrint.hpp"
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
#include <system_error>

// Declares clang::SyntaxOnlyAction.
#include "SpecCollector.hpp"
#include "ToCoq.hpp"
#include "clang/Frontend/FrontendActions.h"

using namespace clang;
using namespace fmt;

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

bool printDecl(const clang::Decl *decl, CoqPrinter &print,
               ClangPrinter &cprint) {
    return cprint.withDecl(decl).printDecl(print, decl);
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

static std::list<::Module::AliasEntry>
sortAliasList(const ::Module::AliasSet &al) {
    std::set<std::tuple<std::string, std::string, ::Module::AliasEntry>> sorted;
    auto into_string = [](const clang::NamedDecl *d) -> std::string {
        if (not d)
            return "";
        return d->getQualifiedNameAsString();
    };

    for (auto i : al) {
        sorted.insert(
            std::tuple<std::string, std::string, ::Module::AliasEntry>(
                into_string(i.first), into_string(i.second), i));
    }
    std::list<::Module::AliasEntry> result;
    for (auto i : sorted)
        result.push_front(std::move(std::get<2>(i)));
    return result;
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

void printCache(::Module &mod, Cache &cache, CoqPrinter &print,
                ClangPrinter &cprint, bool noimport = false) {

    auto preprint = [&](const Decl *decl) {
        auto cp = cprint.withDecl(decl);
        PRINTER<clang::Type> type_fn = [&](auto prefix, auto num, auto *type) {
            print.output() << "#[local] Definition " << prefix << num
                           << " : type := ";
            cp.printType(print, type, loc::of(type));
            print.output() << "." << fmt::line;
        };
        PRINTER<clang::NamedDecl> name_fn = [&](auto prefix, auto num,
                                                auto *decl) {
            print.output() << "#[local] Definition " << prefix << num
                           << " : name := ";
            cp.printName(print, decl, loc::of(decl));
            print.output() << "." << fmt::line;
        };
        prePrintDecl(decl, cache, type_fn, name_fn);
    };

    if (not noimport) {
        print.output() << "Import skylabs.lang.cpp.parser." << fmt::line
                       << fmt::line;
    }

    for (auto decl : mod.declarations()) {
        preprint(decl);
    }
    for (auto decl : mod.definitions()) {
        preprint(decl);
    }
    print.output() << fmt::line;
}

void ToCoqConsumer::writeTemplates(const char *name, Cache &cache,
                                   fmt::Formatter &fmt, clang::ASTContext &ctxt,
                                   ::Module &mod, bool noimport) {
    CoqPrinter print(fmt, /*templates*/ true, cache);
    ClangPrinter cprint(compiler_, &ctxt, trace_, comment_, typedefs_);

    if (not noimport) {
        print.output() << "Import skylabs.lang.cpp.mparser." << fmt::line
                       << "#[local] Open Scope pstring_scope." << fmt::line
                       << fmt::line;
    }

    print.output() << "Definition " << name
                   << " : Mtranslation_unit :=" << fmt::indent << fmt::line
                   << "Eval reduce_translation_unit in Mtranslation_unit.decls"
                   << fmt::nbsp;

    print.begin_list();
    for (auto decl : mod.template_declarations()) {
        // if (sharing)
        //     prePrintDecl(decl, c, print, cprint);
        if (printDecl(decl, print, cprint))
            print.cons();
        if (print.templates() && cprint.printTypedefs())
            default_template_alias::printDefaultTemplateAliases(decl, print,
                                                                cprint);
    }
    for (auto decl : mod.template_definitions()) {
        if (printDecl(decl, print, cprint))
            print.cons();
        if (print.templates() && cprint.printTypedefs())
            default_template_alias::printDefaultTemplateAliases(decl, print,
                                                                cprint);
    }
    print.end_list();

    print.output() << "." << fmt::outdent << fmt::line;
}

/**
 * Assumes that the plugin is already `Require`d.
 */
void ToCoqConsumer::writeStatic(const char *name, Cache &cache,
                                fmt::Formatter &fmt, clang::ASTContext &ctxt,
                                ::Module &mod, bool noimport) {
    CoqPrinter print(fmt, /*templates*/ false, cache);
    ClangPrinter cprint(compiler_, &ctxt, trace_, comment_, typedefs_);

    if (not noimport) {
        print.output() << "Import skylabs.lang.cpp.parser." << fmt::line
                       << "#[local] Open Scope pstring_scope." << fmt::line
                       << fmt::line;
    }

    if (attributes_.has_value()) {
        print.output() << "#[" << attributes_.value() << "]" << fmt::line;
    }
    print.output() << "cpp.prog " << name << fmt::indent << fmt::line;
    print.output() << "abi ";
    printAbi(print.output(), ctxt) << fmt::line;
    print.output() << "defns" << fmt::indent;

    for (auto decl : mod.declarations()) {
        printDecl(decl, print, cprint);
    }
    for (auto decl : mod.definitions()) {
        printDecl(decl, print, cprint);
    }
    for (auto &[from, to] : sortAliasList(mod.aliases())) {
        if (from) {
            guard::ctor _{print, "Dusing_namespace"};
            cprint.printName(print, *from) << fmt::nbsp;
            cprint.printName(print, *to);
        } else {
            guard::ctor _{print, "Dglobal_using_namespace"};
            cprint.printName(print, *to);
        }
    }
    for (auto decl : mod.asserts()) {
        printDecl(decl, print, cprint);
    }

    // TODO I still need to generate the initializer

    print.output() << "." << fmt::outdent << fmt::outdent << fmt::line;
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

    auto check_types = [&](Formatter &fmt, const char* name) {
      if (!interactive_.has_value()) {
        fmt << fmt::line << "Require skylabs.lang.cpp.syntax.typed.";
      }
      fmt << fmt::line
          << "Goal typed.decltype.check_tu "
          << interactive_.value_or("source")
          << " = trace.Success tt. Proof. vm_compute; reflexivity. Abort."
          << fmt::line;
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
        Cache cache;

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

        if (this->sharing_) {
            CoqPrinter static_print(fmt, /*templates*/ false, cache);
            ClangPrinter static_cprint(compiler_, ctxt, trace_, comment_,
                                       typedefs_);
            printCache(mod, cache, static_print, static_cprint, true);
        }

        // BEGIN: Section static
        // fmt << "Section static." << fmt::indent << fmt::line;

        std::string static_name{"static__"};
        static_name += interactive_.value_or("source");

        writeStatic(static_name.c_str(), cache, fmt, *ctxt, mod, true);

        // fmt << fmt::outdent << "End static." << fmt::line << fmt::line;
        // END: Section static

        // BEGIN: Section meta
        // fmt << "Section meta." << fmt::indent << fmt::line;

        std::string meta_name{"meta__"};
        meta_name += interactive_.value_or("source");

        writeTemplates(meta_name.c_str(), cache, fmt, *ctxt, mod);

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

    auto static_only =
        [&](Formatter &fmt) {
            Cache cache;
            CoqPrinter print(fmt, /*templates*/ false, cache);
            ClangPrinter cprint(compiler_, ctxt, trace_, comment_, typedefs_);

            if (interactive_.has_value()) {
                // Since we are in interactive mode, the parser is already
                // loaded; however, it is important that we limit our
                // side-effects
                print.output() << "Section cpp_prog__" << interactive_.value()
                               << "__." << fmt::line;
            } else {
                print.output()
                    << "Require Import skylabs.lang.cpp.parser.plugin.cpp2v."
                    << fmt::line;
            }
            // parser(print);
            // bytestring(print) << fmt::line;

            if (this->sharing_) {
                printCache(mod, cache, print, cprint);
            }

            writeStatic(interactive_.value_or("source").c_str(), cache, fmt,
                        *ctxt, mod);

            // Close the section if we opened one
            if (interactive_.has_value()) {
                print.output() << "End cpp_prog__" << interactive_.value()
                               << "__." << fmt::line;
            } else {
                // NOTE: Backwards compatibility
                print.output()
                    << "Abbreviation module := source (only parsing)."
                    << fmt::line;
            }

            if (check_types_) {
                check_types(fmt, interactive_.value_or("source").c_str());
            }
        };

    auto templates_only = [&](Formatter &fmt) {
        Cache cache;
        fmt << "Require skylabs.lang.cpp.mparser." << fmt::line;

        writeTemplates("templates", cache, fmt, *ctxt, mod);
    };

    if (output_templates_) {
        with_open_file(output_file_, static_and_templates);
    } else {
        with_open_file(output_file_, static_only);
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
