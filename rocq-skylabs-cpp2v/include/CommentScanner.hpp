/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "clang/AST/Comment.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/StringRef.h"

namespace comment {
using namespace clang;
using namespace llvm;

class CommentScanner {
private:
    StringRef block;
    size_t offset;

    size_t parseLineComment(size_t first) {
        // this is a line comment, keep getting the next line until there is a
        // line that is not a comment.

        auto eol = block.find("\n", first);
        assert(eol != StringRef::npos && "end of line necessary");
        auto next_comment = block.find("//", eol + 1);
        while (next_comment != StringRef::npos &&
               block.find("\n", eol + 1) > next_comment) {
            eol = block.find("\n", next_comment);
            next_comment = block.find("//", eol + 1);
        }

        return eol;
    }

    size_t parseBlockComment(size_t first) {
        // this is a paragraph comment, find the next closing '*/'
        auto closing = block.find("*/", first);
        assert(closing != StringRef::npos &&
               "open block comment without close");

        return closing + 2;
    }

public:
    CommentScanner(StringRef _block) : block(_block), offset(0) {}

    bool next(StringRef &result) {
        auto first_line = block.find("//", offset);
        auto first_para = block.find("/*", offset);

        if (first_line == StringRef::npos && first_para == StringRef::npos) {
            return false;
        } else if (first_line < first_para) {
            // this is a line comment, keep getting the next line until there is
            // a line that is not a comment.
            auto end = parseLineComment(first_line);

            result = block.substr(first_line, end - first_line);
            offset = end;

            return true;
        } else if (first_para < first_line) {
            // this is a paragraph comment, find the next closing '*/'
            auto end = parseBlockComment(first_para);

            result = block.substr(first_para, end - first_para);
            offset = end;
            return true;
        } else {
            assert(false);
            return false;
        }
    }

    static CommentScanner decl_comments(const clang::Decl *decl,
                                        clang::ASTContext *ctxt);
};

} // namespace comment
