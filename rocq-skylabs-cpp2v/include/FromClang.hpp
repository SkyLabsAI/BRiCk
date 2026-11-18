/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once
#include "clang/Basic/Builtins.h"
#include "clang/Sema/Sema.h"

void GenerateUndeprecatedImplicitMembers(clang::CXXRecordDecl *decl,
                                         clang::Sema &sema);

// The C-linkage declaration of the library function that the builtin [id]
// calls (`memcpy` for `__builtin_memcpy`), if [id] is a library builtin
// (attribute `F`) and the translation unit declares that function.
const clang::FunctionDecl *libFunctionDecl(clang::ASTContext &ctxt,
                                           unsigned id);

// Declares, as clang would implicitly, the library function of every library
// builtin in [tu] whose library function [tu] does not declare.
void DeclareLibFunctions(clang::TranslationUnitDecl *tu, clang::Sema &sema);
