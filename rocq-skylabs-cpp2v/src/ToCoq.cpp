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
#include "ModuleBuilder.hpp"
#include "PrePrint.hpp"
#include "SpecCollector.hpp"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Type.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/Version.inc"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include <Formatter.hpp>
#include <list>

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
        std::error_code ec;
        llvm::raw_fd_ostream output(*path, ec);
        if (ec.value()) {
            llvm::errs() << *path << ": " << ec.message() << "\n";
        } else {
            Formatter fmt{output};
            f(fmt);
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

    bool templates = templates_file_.has_value() || name_test_file_.has_value();
    build_module(decl, mod, filter, specs, compiler_, elaborate_, templates);

    auto parser = [&](CoqPrinter &print) -> auto & {
        StringRef coqmod(print.templates() ? "bluerock.lang.cpp.mparser"
                                           : "bluerock.lang.cpp.parser");
        return print.output()
               << (interactive_.has_value() ? "Import " : "Require Import ")
               << coqmod << "." << fmt::line << fmt::line;
    };

    auto bytestring = [&](CoqPrinter &print) -> auto & {
        return print.output()
               << "#[local] Open Scope pstring_scope." << fmt::line;
    };

    with_open_file(
        output_file_, [&](Formatter &fmt) {
            Cache cache;
            CoqPrinter print(fmt, /*templates*/ false, cache);
            ClangPrinter cprint(compiler_, ctxt, trace_, comment_, typedefs_);

            parser(print);
            if (interactive_.has_value()) {
                print.output() << "Section cpp_prog__" << interactive_.value()
                               << "__." << fmt::line;
            }
            bytestring(print) << fmt::line;

            if (this->sharing_) {
                auto preprint = [&](const Decl *decl) {
                    auto cp = cprint.withDecl(decl);
                    PRINTER<clang::Type> type_fn = [&](auto prefix, auto num,
                                                       auto *type) {
                        print.output() << "#[local] Definition " << prefix
                                       << num << " : type := ";
                        cp.printType(print, type, loc::of(type));
                        print.output() << "." << fmt::line;
                    };
                    PRINTER<clang::NamedDecl> name_fn =
                        [&](auto prefix, auto num, auto *decl) {
                            print.output() << "#[local] Definition " << prefix
                                           << num << " : name := ";
                            cp.printName(print, decl, loc::of(decl));
                            print.output() << "." << fmt::line;
                        };
                    prePrintDecl(decl, cache, type_fn, name_fn);
                };

                for (auto decl : mod.declarations()) {
                    preprint(decl);
                }
                for (auto decl : mod.definitions()) {
                    preprint(decl);
                }
                print.output() << fmt::line;
            }

            if (!interactive_.has_value()) {
                print.output()
                    << "Require Import bluerock.lang.cpp.parser.plugin.cpp2v."
                    << fmt::line;
            }
            if (attributes_.has_value()) {
                print.output()
                    << "#[" << attributes_.value() << "]" << fmt::line;
            }
            print.output() << "cpp.prog " << interactive_.value_or("source")
                           << fmt::indent << fmt::line;
            if (ctxt->getTargetInfo().isBigEndian()) {
                print.output() << "abi Big" << fmt::line;
            } else {
                always_assert(ctxt->getTargetInfo().isLittleEndian());
                print.output() << "abi Little" << fmt::line;
            }
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

            // Close the section if we opened one
            if (this->interactive_.has_value()) {
                print.output() << "End cpp_prog__" << interactive_.value()
                               << "__." << fmt::line;
            }

            if (!interactive_.has_value()) {
                print.output()
                    << "Notation module := source (only parsing)." << fmt::line;
            }

            if (check_types_) {
                print.output()
                    << fmt::line << "Require bluerock.lang.cpp.syntax.typed."
                    << fmt::line
                    << "Succeed Example well_typed : "
                       "typed.decltype.check_tu module = trace.Success tt"
                       " := ltac:(vm_compute; reflexivity)."
                    << fmt::line;
            }
        });

    with_open_file(notations_file_, [&](Formatter &spec_fmt) {
        Cache c;
        CoqPrinter print(spec_fmt, /*templates*/ false, c);
        ClangPrinter cprint(compiler_, ctxt, trace_, comment_, typedefs_);
        // PrintSpec printer(ctxt);

        NoInclude source(ctxt->getSourceManager());

        parser(print);

        // generate all of the record fields
        write_globals(mod, print, cprint);
    });

    with_open_file(templates_file_, [&](Formatter &fmt) {
        Cache c;
        CoqPrinter print(fmt, /*templates*/ true, c);
        ClangPrinter cprint(compiler_, ctxt, trace_, comment_, typedefs_);

        parser(print);
        bytestring(print) << fmt::line;

        print.output()
            << "Definition templates : Mtranslation_unit :=" << fmt::indent
            << fmt::line
            << "Eval reduce_translation_unit in Mtranslation_unit.decls"
            << fmt::nbsp;

        print.begin_list();
        for (auto decl : mod.template_declarations()) {
            // if (sharing)
            //     prePrintDecl(decl, c, print, cprint);
            if (printDecl(decl, print, cprint))
                print.cons();
        }
        for (auto decl : mod.template_definitions()) {
            if (printDecl(decl, print, cprint))
                print.cons();
        }
        print.end_list();

        print.output() << "." << fmt::outdent << fmt::line;
    });

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
