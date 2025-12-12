/*
 * Copyright (c) 2020-2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *
 * This work is derived from code in the LLVM Project licensed under Apache
 * License v2.0 with LLVM Exceptions. See https://llvm.org/LICENSE.txt for
 * license information. SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */
#include "clang/Basic/Builtins.h"
#include "clang/Sema/Sema.h"

using namespace clang;

// The following code is based on [ForceDeclarationOfImplicitMembers]
// except that it does not generate deprecated members.
// See
// https://github.com/llvm/llvm-project/blob/ed4afd1bba8347e1d7ea943c242fccabf606489c/clang/lib/Sema/SemaLookup.cpp#L992
void GenerateUndeprecatedImplicitMembers(CXXRecordDecl *decl, Sema &sema) {
    if (decl->needsImplicitDefaultConstructor())
        sema.DeclareImplicitDefaultConstructor(decl);

    if (decl->needsImplicitCopyConstructor() and
        not decl->hasUserDeclaredCopyAssignment())
        sema.DeclareImplicitCopyConstructor(decl);

    if (decl->needsImplicitCopyAssignment() and
        not decl->hasUserDeclaredCopyConstructor())
        sema.DeclareImplicitCopyAssignment(decl);

    if (sema.getLangOpts().CPlusPlus11) {
        // NOTE: It seems like these should have similar checks to
        // the copy versions, but apparently they are not deprecated.
        if (decl->needsImplicitMoveConstructor())
            sema.DeclareImplicitMoveConstructor(decl);

        if (decl->needsImplicitMoveAssignment())
            sema.DeclareImplicitMoveAssignment(decl);
    }

    if (decl->needsImplicitDestructor())
        sema.DeclareImplicitDestructor(decl);
}
