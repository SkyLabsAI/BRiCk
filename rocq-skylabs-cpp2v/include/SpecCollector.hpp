/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "Filter.hpp"
#include "Formatter.hpp"
#include "ModuleBuilder.hpp"
#include "clang/AST/Comment.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RawCommentList.h"
#include <list>
#include <map>
#include <optional>
#include <utility>

namespace clang {
class CompilerInstance;
}

class CoqPrinter;
class ClangPrinter;

class SpecCollector {
public:
    SpecCollector() {}

    void add_specification(const clang::NamedDecl *decl, clang::RawComment *ref,
                           clang::ASTContext &context) {
        ref->setAttached();
        this->comment_decl_.insert(std::make_pair(ref, decl));
        if (auto comment = context.getCommentForDecl(decl, nullptr)) {
            this->specifications_.push_back(std::make_pair(decl, comment));
        }
    }

    std::list<std::pair<const clang::NamedDecl *,
                        clang::comments::FullComment *>>::const_iterator
    begin() const {
        return this->specifications_.begin();
    }

    std::list<std::pair<const clang::NamedDecl *,
                        clang::comments::FullComment *>>::const_iterator
    end() const {
        return this->specifications_.end();
    }

    std::optional<const clang::NamedDecl *>
    decl_for_comment(clang::RawComment *cmt) const {
        auto result = comment_decl_.find(cmt);
        if (result == comment_decl_.end()) {
            return {};
        }
        return result->second;
    }

private:
    std::list<
        std::pair<const clang::NamedDecl *, clang::comments::FullComment *>>
        specifications_;
    std::map<clang::RawComment *, const clang::NamedDecl *> comment_decl_;
};

void write_spec(clang::CompilerInstance *compiler, ::Module *mod,
                const SpecCollector &specs,
                const clang::TranslationUnitDecl *tu, Filter &filter,
                fmt::Formatter &output);
