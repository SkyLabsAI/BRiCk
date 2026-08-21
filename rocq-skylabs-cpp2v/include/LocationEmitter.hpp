/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"
#include "LocationDAGEncoding.hpp"
#include "RocqEmitter.hpp"

#include <optional>
#include <string>
#include <vector>

#include <llvm/Support/Error.h>

namespace ir {

enum class LocationScope { MainFile, AllFiles };

struct LocationSourceRoot {
    std::string name;
    std::string path;
};

struct LocationRocqEmitterOptions {
    bool includeTemplates = true;
    LocationScope scope = LocationScope::MainFile;
    /// Final AST [.v] path. Relative paths are interpreted from cpp2v's
    /// working directory. Separate companions deliberately use this path too.
    std::optional<std::string> astPath;
    /// Stable external roots whose absolute paths are replaced by [name].
    std::vector<LocationSourceRoot> sourceRoots;
};

/// Emit one standalone source-location companion from a finished semantic IR.
class LocationRocqEmitter {
public:
    explicit LocationRocqEmitter(LocationRocqEmitterOptions options = {})
        : options_(options) {}

    llvm::Expected<std::string> emit(const TranslationUnitIR &unit) const;
    /// Expanded-tree oracle retained only by pure unit tests. Production
    /// companions use LocationDAGEncoding and never call this method.
    llvm::Expected<std::string> renderTree(const TranslationUnitIR &unit,
                                           NodeId root) const;
    /// Serialize a prevalidated synthetic DAG for chunk-boundary tests.
    llvm::Expected<std::string> renderLocationDagForTest(
        const location::encoding::EncodedLocations &locations) const;

private:
    llvm::Error appendTreeUnchecked(std::string &output,
                                    const TranslationUnitIR &unit,
                                    NodeId root) const;
    llvm::Expected<std::string>
    renderTreeUnchecked(const TranslationUnitIR &unit, NodeId root) const;

    LocationRocqEmitterOptions options_;
    SemanticRocqEmitter semantic_;
};

} // namespace ir
