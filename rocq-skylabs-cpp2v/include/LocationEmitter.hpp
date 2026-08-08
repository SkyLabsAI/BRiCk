/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"
#include "RocqEmitter.hpp"

#include <string>

#include <llvm/Support/Error.h>

namespace ir {

struct LocationRocqEmitterOptions {
    bool includeTemplates = true;
};

/// Emit one standalone source-location companion from a finished semantic IR.
class LocationRocqEmitter {
public:
    explicit LocationRocqEmitter(LocationRocqEmitterOptions options = {})
        : options_(options) {}

    llvm::Expected<std::string> emit(const TranslationUnitIR &unit) const;
    llvm::Expected<std::string> renderTree(const TranslationUnitIR &unit,
                                           NodeId root) const;

private:
    llvm::Expected<std::string>
    renderTreeUnchecked(const TranslationUnitIR &unit, NodeId root) const;

    LocationRocqEmitterOptions options_;
    SemanticRocqEmitter semantic_;
};

} // namespace ir
