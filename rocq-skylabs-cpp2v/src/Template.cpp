/*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */

#include "Template.hpp"
#include <clang/AST/DeclTemplate.h>

using namespace clang;

SDeclO recoverSpecialization(const Decl &decl) {
    auto ret = [&](auto *temp, auto *args) -> SDeclO {
        if (temp && args) {
            SDecl sd{*temp, *args};
            return {sd};
        } else
            return std::nullopt;
    };
    if (auto d = dyn_cast<ClassTemplateSpecializationDecl>(&decl)) {
        auto *temp = d->getSpecializedTemplate();
        auto &args = d->getTemplateArgs();
        return ret(temp, &args);
    } else if (auto d = dyn_cast<FunctionDecl>(&decl)) {
        auto *temp = d->getPrimaryTemplate();
        auto *args = d->getTemplateSpecializationArgs();
        return ret(temp, args);
    } else if (auto d = dyn_cast<VarTemplateSpecializationDecl>(&decl)) {
        auto *temp = d->getSpecializedTemplate();
        auto &args = d->getTemplateArgs();
        return ret(temp, &args);
    } else
        return std::nullopt;
}
