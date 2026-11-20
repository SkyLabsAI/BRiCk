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
#include <optional>

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

// The library function a library builtin calls, as in clang CodeGen's
// [getBuiltinLibFunction]: `__builtin_memcpy` calls `memcpy`. `va_end` and
// `va_copy` are macros, not functions (CodeGen emits intrinsics for them).
static std::optional<std::string> libFunctionName(const ASTContext &ctxt,
                                                  unsigned id) {
    if (not ctxt.BuiltinInfo.isLibFunction(id) or
        id == Builtin::BI__builtin_va_end or id == Builtin::BI__builtin_va_copy)
        return {};
    return ctxt.BuiltinInfo.getName(id).substr(StringRef("__builtin_").size());
}

static const FunctionDecl *lookupExternC(ASTContext &ctxt, StringRef name) {
    for (auto d : ctxt.getTranslationUnitDecl()->lookup(&ctxt.Idents.get(name)))
        if (auto fd = dyn_cast<FunctionDecl>(d); fd and fd->isExternC())
            return fd;
    return nullptr;
}

const FunctionDecl *libFunctionDecl(ASTContext &ctxt, unsigned id) {
    auto name = libFunctionName(ctxt, id);
    return name ? lookupExternC(ctxt, *name) : nullptr;
}

void DeclareLibFunctions(TranslationUnitDecl *tu, Sema &sema) {
    auto &ctxt = sema.getASTContext();
    // Clang declares the builtins that the code uses at the top level, in
    // implicit `extern "C"` blocks.
    std::vector<const FunctionDecl *> builtins;
    auto collect = [&](const DeclContext *dc) {
        for (auto d : dc->decls())
            if (auto fd = dyn_cast<FunctionDecl>(d); fd and fd->getBuiltinID())
                builtins.push_back(fd);
    };
    collect(tu);
    for (auto d : tu->decls())
        if (auto ls = dyn_cast<LinkageSpecDecl>(d))
            collect(ls);

    for (auto builtin : builtins) {
        auto name = libFunctionName(ctxt, builtin->getBuiltinID());
        if (not name or lookupExternC(ctxt, *name))
            continue;
        // The type clang gives the library function's own builtin (`memcpy`;
        // `noexcept` if it is nothrow). Without one (`__memcpy_chk`, or under
        // `-fno-builtin`), the type of the `__builtin_` function.
        auto &id = ctxt.Idents.get(*name);
        unsigned lib = id.getBuiltinID();
        ASTContext::GetBuiltinTypeError error = ASTContext::GE_None;
        QualType type =
            lib ? ctxt.GetBuiltinType(lib, error) : builtin->getType();
        if (error != ASTContext::GE_None) {
            lib = 0;
            type = builtin->getType();
        }
        auto fd =
            sema.CreateBuiltin(&id, type, lib ? lib : builtin->getBuiltinID(),
                               builtin->getLocation());
        // No `Builtin` body: BRiCk orders declarations with a body by their
        // parameter names too, and ours differ from the headers'; without a
        // body, the declaration is compatible with a header's.
        fd->dropAttr<BuiltinAttr>();
        fd->getDeclContext()->addDecl(fd);
    }
}
