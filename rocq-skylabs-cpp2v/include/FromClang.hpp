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
