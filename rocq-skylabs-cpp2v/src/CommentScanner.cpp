/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "CommentScanner.hpp"
#include <Formatter.hpp>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclBase.h>
#include <list>

using namespace clang;
using namespace comment;

static SourceLocation getStartSourceLocWithComment(clang::ASTContext *ctxt,
                                                   const Decl *d) {
    auto comment = ctxt->getRawCommentForDeclNoCache(d);
    return comment ? comment->getBeginLoc() : d->getBeginLoc();
}

static Decl *getPreviousDeclInContext(const Decl *d) {
    auto dc = d->getLexicalDeclContext();

    Decl *prev = nullptr;
    for (auto it : dc->decls()) {
        if (it == d) {
            return prev;
        } else {
            prev = it;
        }
    }
    return nullptr;
}

static SourceLocation getPrevSourceLoc(SourceManager &sm, const Decl *d) {
    auto pd = getPreviousDeclInContext(d);
    return (pd && pd->getEndLoc().isValid())
               ? pd->getEndLoc()
               : sm.getLocForStartOfFile(
                     sm.getFileID(d->getSourceRange().getBegin()));
}

CommentScanner CommentScanner::decl_comments(const clang::Decl *decl,
                                             clang::ASTContext *ctxt) {
    SourceManager &sm = ctxt->getSourceManager();
    auto start = getPrevSourceLoc(sm, decl);
    auto end = getStartSourceLocWithComment(ctxt, decl);

    llvm::errs() << "start/end: " << start.printToString(sm) << " "
                 << end.printToString(sm) << "\n";

    if (start.isValid() && end.isValid()) {
        llvm::errs() << StringRef(sm.getCharacterData(start),
                                  sm.getCharacterData(end) -
                                      sm.getCharacterData(start))
                     << "\n";
        return comment::CommentScanner(
            StringRef(sm.getCharacterData(start),
                      sm.getCharacterData(end) - sm.getCharacterData(start)));
    } else {

        return comment::CommentScanner("");
    }
}
