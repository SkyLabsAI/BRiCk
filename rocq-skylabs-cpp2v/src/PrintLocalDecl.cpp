/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "OpaqueNames.hpp"
#include "clang/Frontend/CompilerInstance.h"

using namespace clang;

class PrintLocalDecl : public ConstDeclVisitorArgs<PrintLocalDecl, bool> {
public:
    PrintLocalDecl(CoqPrinter &print, ClangPrinter &cprint, OpaqueNames &names)
        : print(print), cprint(cprint), names(names) {}

private:
    CoqPrinter &print;
    ClangPrinter &cprint;
    OpaqueNames &names;

    CXXDestructorDecl *get_dtor(QualType qt) {
        if (auto rd = qt->getAsCXXRecordDecl()) {
            return rd->getDestructor();
        } else if (auto ary = qt->getAsArrayTypeUnsafe()) {
            return get_dtor(ary->getElementType());
        } else {
            return nullptr;
        }
    }

    void printDestructor(QualType qt) {
        // TODO when destructors move to classes, we can change this
        if (auto dest = get_dtor(qt)) {
            print.some();
            cprint.printName(print, *dest);
            print.end_ctor();
        } else {
            print.none();
        }
    }

public:
    bool Visit(const Decl *decl) {
        if (decl->isInvalidDecl()) {
            print.output() << "Derror";
            return true;
        } else
            return ConstDeclVisitorArgs<PrintLocalDecl, bool>::Visit(decl);
    }

    bool VisitVarDecl(const VarDecl *decl) {
        // TODO: The following seems to be unsupported by parser.v
        if (decl->hasExternalStorage()) {
            return false;

        } else if (decl->isStaticLocal()) {
            bool thread_safe =
                cprint.getCompiler().getLangOpts().ThreadsafeStatics;
            print.ctor("Dinit");
            print.output() << fmt::BOOL(thread_safe) << fmt::nbsp;
            cprint.printName(print, *decl);
            print.output() << fmt::nbsp;
        } else {
            print.ctor("Dvar");
            print.str(decl->getNameAsString()) << fmt::nbsp;
        }

        auto declty = decl->getType();
        cprint.printQualType(print, declty, loc::of(decl));
        print.output() << fmt::nbsp;

        if (auto init = decl->getInit()) {
            print.some();
            cprint.printExpr(print, init, names);
            print.end_ctor();
        } else {
            print.none();
        }

        print.end_ctor();
        return true;
    }

    bool VisitTypeDecl(const TypeDecl *decl) {
        using namespace logging;
        debug() << "local type declarations are (currently) not well supported "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }

    bool VisitStaticAssertDecl(const StaticAssertDecl *decl) { return false; }

    bool VisitDecl(const Decl *decl) {
        using namespace logging;
        debug() << "unexpected local declaration while printing local decl "
                << decl->getDeclKindName() << " (at "
                << cprint.sourceRange(decl->getSourceRange()) << ")\n";
        return false;
    }

    bool VisitDecompositionDecl(const DecompositionDecl *decl) {
        print.ctor("Ddecompose");

        cprint.printExpr(print, decl->getInit(), names);

        int index = names.push_anon(decl);
        print.output() << fmt::nbsp << "(localname.anon " << index << ")";

        print.output() << fmt::nbsp;

        print.list(decl->bindings(), [&](const BindingDecl *b) -> void {
            if (auto *var = b->getHoldingVar()) {
                guard::ctor _{print, "Bvar"};
                print.str(var->getName()) << fmt::nbsp;
                auto declty = var->getType();
                cprint.printQualType(print, declty, loc::of(decl)) << fmt::nbsp;

                auto init = var->getInit();
                always_assert(init &&
                              "binding variables must have initializers");
                cprint.printExpr(print, init, names);
            } else {
                // If there is no holding variable, then there is no allocation
                // here.
                guard::ctor _{print, "Bbind"};
                print.str(b->getName()) << fmt::nbsp;
                cprint.printQualType(print, b->getType(), loc::of(b))
                    << fmt::nbsp;
                cprint.printExpr(print, b->getBinding(), names);
            }
        });

        names.pop_anon(decl);

        print.end_ctor();
        return true;
    }
};

bool ClangPrinter::printLocalDecl(CoqPrinter &print, const clang::Decl *decl) {
    if (trace(Trace::Local))
        trace("printLocalDecl", loc::of(decl));
    OpaqueNames names;
    return PrintLocalDecl{print, *this, names}.Visit(decl);
}
