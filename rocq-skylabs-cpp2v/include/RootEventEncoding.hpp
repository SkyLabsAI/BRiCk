/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"

#include <cstddef>
#include <vector>

#include <llvm/Support/Error.h>

namespace ir::root_event::encoding {

/// A selected root either needs the existing Rocq semantic-selection path, or
/// can carry only its static location IDs. Filtered template roots are absent.
enum class EventClass { Excluded, Singleton, Residual };

struct EncodingStats {
    /// Events selected after template filtering.
    std::size_t selectedEvents = 0;
    /// Selected value-free events whose (root kind, exact semantic name) group
    /// has one member. Conservatively retained typedef roots are residual.
    std::size_t singletonEvents = 0;
    /// Selected events which must retain a semantic value: every duplicate
    /// group member plus singleton [Gtypedef] type roots.
    std::size_t residualEvents = 0;
    std::size_t duplicateGroups = 0;
    std::size_t duplicateEvents = 0;
    /// Singleton [Gtypedef] type roots retained so Rocq remains authoritative
    /// for self-alias filtering.
    std::size_t conservativeTypedefResiduals = 0;
};

struct EncodedRootEvents {
    /// Indexed exactly like [TranslationUnitIR::rootEvents].
    std::vector<EventClass> eventClasses;
    EncodingStats stats;
};

struct EncodeOptions {
    /// Narrow test seam: hashes choose buckets only, so results must remain
    /// byte-for-byte equivalent to ordinary hashing under forced collisions.
    bool forceHashCollisions = false;
};

/// Validate a finished owned IR, select root events using authoritative ordered
/// traversal, and group them by RootKind plus exact semantic-name equality.
/// Equality is decided by [IRSharing::semanticallyEqual]; a memoized structural
/// hash only narrows equality buckets. Singleton [Gtypedef] roots remain
/// residual conservatively, while every other singleton is value-free.
llvm::Expected<EncodedRootEvents> encode(const TranslationUnitIR &unit,
                                         bool includeTemplates,
                                         EncodeOptions options = {});

} // namespace ir::root_event::encoding
