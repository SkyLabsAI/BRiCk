/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/Type.h>
#include <llvm/ADT/DenseMap.h>

using namespace clang;

namespace {
llvm::raw_ostream &unsupported(ClangPrinter &printer, loc::loc location,
                               const llvm::Twine &message) {
    auto &output = printer.error_prefix(logging::unsupported(), location)
                   << "warning: unsupported " << message << "\n";
    printer.debug_dump(location);
    return output;
}

const RecordDecl *getTypeAsRecord(const ValueDecl &declaration) {
    if (const Type *type = declaration.getType().getTypePtrOrNull()) {
        if (const TagDecl *tag = type->getAsTagDecl())
            return llvm::dyn_cast<RecordDecl>(tag);
    }
    return nullptr;
}

fmt::Formatter &printAnonymousFieldName(CoqPrinter &print,
                                        const FieldDecl &field,
                                        ClangPrinter &printer) {
    if (const auto *record = llvm::dyn_cast<CXXRecordDecl>(field.getParent())) {
        if (record->isLambda()) {
            guard::ctor constructor(print, "field_name.CaptureVar");
            llvm::DenseMap<const ValueDecl *, FieldDecl *> captures;
            FieldDecl *thisCapture = nullptr;
            record->getCaptureFields(captures, thisCapture);
            if (thisCapture == &field)
                return print.str("this");
            for (const auto &capture : captures)
                if (capture.second == &field)
                    return print.str(capture.first->getName());
        }
    }
    if (const RecordDecl *record = getTypeAsRecord(field))
        return printer.printName(print, record, loc::of(field), false);

    unsupported(printer, loc::of(field), "anonymous field not of record type");
    guard::ctor constructor(print, "field_name.Id", false);
    return print.str("<anonymous field not of record type>");
}
} // namespace

fmt::Formatter &ClangPrinter::printFieldName(CoqPrinter &print,
                                             const FieldDecl &field, loc::loc) {
    if (const IdentifierInfo *identifier = field.getIdentifier()) {
        guard::ctor constructor(print, "field_name.Id", false);
        return print.str(identifier->getName());
    }
    return printAnonymousFieldName(print, field, *this);
}
