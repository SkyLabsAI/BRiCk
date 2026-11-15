/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/Basic/Version.inc"

namespace clang_compat {

inline clang::RawComment *getRawCommentNoCache(const clang::ASTContext &context,
                                               const clang::Decl *decl) {
#if CLANG_VERSION_MAJOR >= 23
    return context.getRawCommentNoCache(decl);
#else
    return context.getRawCommentForDeclNoCache(decl);
#endif
}

} // namespace clang_compat
