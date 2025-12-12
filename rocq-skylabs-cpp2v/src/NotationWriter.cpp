/*
 * Copyright (c) 2021-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Basic/Version.inc"

// TODO this should be replaced by something else.
bool print_path(llvm::raw_string_ostream &print, const DeclContext *dc,
                bool end = true) {
    if (dc == nullptr || isa<TranslationUnitDecl>(dc)) {
        if (end)
            print << "::";
        return true;
    } else {
        if (not print_path(print, dc->getParent())) {
            return false;
        }
        if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
            print << ts->getNameAsString() << "<";
            bool first = true;
            for (auto i : ts->getTemplateArgs().asArray()) {
                if (!first) {
                    print << ",";
                }
                first = false;
                switch (i.getKind()) {
                case TemplateArgument::ArgKind::Integral:
                    print << i.getAsIntegral();
                    break;
                case TemplateArgument::ArgKind::Type: {
                    // TODO: this is still somewhat of a hack
                    auto s = i.getAsType().getAsString();
                    if (find(s.begin(), s.end(), '/') != s.end() or
                        find(s.begin(), s.end(), '\\') != s.end()) {
                        // a heuristic to determine if a path is being generated
                        return false;
                    } else {
                        replace(s.begin(), s.end(), ' ', '_');
                        print << s;
                        break;
                    }
                }
                default:
                    return false;
                }
            }
            print << (end ? ">::" : ">");
        } else if (auto td = dyn_cast<TagDecl>(dc)) {
            if (td->getName() != "") {
                print << td->getNameAsString() << (end ? "::" : "");
            } else
                return false;
        } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
            if (!ns->isAnonymousNamespace()) {
                print << ns->getNameAsString() << (end ? "::" : "");
            } else
                return false;
        } else {
            using namespace logging;
            // logging::log() << "unknown declaration while printing path "
            //                << dc->getDeclKindName() << "\n";
            return false;
        }
    }
    return true;
}

static inline bool starts_with(llvm::StringRef &s, const char *what) {
#if 19 <= CLANG_VERSION_MAJOR
    return s.starts_with(what);
#else
    return s.startswith(what);
#endif
}

void write_globals(::Module &mod, CoqPrinter &print, ClangPrinter &cprint) {
    print.output() << "Module _'." << fmt::indent << fmt::line;

    auto write_notations = [&](const clang::NamedDecl *def) {
        if (!def->getIdentifier())
            return;
        std::string s_notation;
        llvm::raw_string_ostream notation{s_notation};
        llvm::StringRef def_name = def->getName();
        if (def_name == "__builtin_va_list" || starts_with(def_name, "__SV") ||
            starts_with(def_name, "__clang_sv"))
            return;
        if (const FieldDecl *fd = dyn_cast<FieldDecl>(def)) {
            if (not print_path(notation, fd->getParent(), true))
                return;

            notation << fd->getNameAsString();
            print.output() << "Notation \"'" << s_notation;
            print.output() << fd->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printField(print, fd);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (const RecordDecl *rd = dyn_cast<RecordDecl>(def)) {
            if (not print_path(notation, rd, false))
                return;

            if (!rd->isAnonymousStructOrUnion() &&
                rd->getNameAsString() != "") {
                print.output()
                    << "Notation \"'" << s_notation << "'\" :=" << fmt::nbsp;

                cprint.printName(print, *rd);
                print.output()
                    << "%bs (in custom cppglobal at level 0)." << fmt::line;
            }

            for (auto fd : rd->fields()) {
                if (fd->getName() != "") {
                    print.output() << "Notation \"'" << s_notation << "::";
                    print.output()
                        << fd->getNameAsString() << "'\" :=" << fmt::nbsp;
                    cprint.printField(print, fd);
                    print.output()
                        << " (in custom cppglobal at level 0)." << fmt::line;
                }
            }
        } else if (isa<FunctionDecl>(def)) {
            // todo(gmm): skipping due to function overloading
        } else if (const TypedefDecl *td = dyn_cast<TypedefDecl>(def)) {
            if (td->isTemplated())
                return;
            if (not print_path(notation, td->getDeclContext(), true))
                return;

            print.output() << "Notation \"'" << s_notation;
            print.output() << td->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(print, td->getUnderlyingType(), loc::of(td));
            print.output() << " (only parsing, in custom cppglobal at level 0)."
                           << fmt::line;
        } else if (const auto *ta = dyn_cast<TypeAliasDecl>(def)) {
            if (ta->isTemplated())
                return;
            if (not print_path(notation, ta->getDeclContext(), true))
                return;

            print.output() << "Notation \"'" << s_notation;
            print.output() << ta->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(print, ta->getUnderlyingType(), loc::of(ta));
            print.output() << " (only parsing, in custom cppglobal at level 0)."
                           << fmt::line;
        } else if (isa<VarDecl>(def) || isa<EnumDecl>(def) ||
                   isa<EnumConstantDecl>(def)) {
        } else {
            using namespace logging;
            log(Level::VERBOSE) << "unknown declaration type "
                                << def->getDeclKindName() << "\n";
        }
    };

    // todo(gmm): i would like to generate function names.
    for (auto def : mod.definitions())
        write_notations(def);
    for (auto def : mod.declarations())
        write_notations(def);

    print.output() << fmt::outdent << "End _'." << fmt::line;
    print.output() << "Export _'." << fmt::line << fmt::line;
}
