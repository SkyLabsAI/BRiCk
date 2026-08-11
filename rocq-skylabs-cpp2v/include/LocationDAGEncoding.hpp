/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"

#include <cstddef>
#include <optional>
#include <vector>

#include <llvm/Support/Error.h>

namespace ir::location::encoding {

struct ShapeTag;
struct LocationNodeTag;
using ShapeId = source::StrongIndex<ShapeTag>;
using LocationNodeId = source::StrongIndex<LocationNodeTag>;

struct EncodedShape {
    std::vector<ShapeId> children;
};

/// Exact location-node identity is [origins, children]. The shape ID is derived
/// metadata used to certify duplicate-root composition without reading the
/// location-node table during Rocq construction.
struct EncodedLocationNode {
    ShapeId shape;
    std::vector<source::OriginId> origins;
    std::vector<LocationNodeId> children;
};

struct EncodedRoot {
    LocationNodeId node;
    ShapeId shape;
};

struct EncodingStats {
    std::size_t selectedRootEvents = 0;
    std::size_t visitedSemanticNodes = 0;
    std::size_t shapeRows = 0;
    std::size_t locationNodeRows = 0;
};

struct EncodedLocations {
    std::vector<EncodedShape> shapes;
    std::vector<EncodedLocationNode> nodes;
    /// Indexed by TranslationUnitIR::rootEvents(). Filtered template events are
    /// [None]; selected roots carry their exact static node and shape IDs.
    std::vector<std::optional<EncodedRoot>> eventRoots;
    std::size_t sourceOriginCount = 0;
    EncodingStats stats;
};

struct EncodeOptions {
    bool forceHashCollisions = false;
};

/// Validate the finished owned IR, then hash-cons complete location nodes in
/// authoritative ordered-root order and left-to-right child postorder. Hashes
/// only select equality-checked buckets; first completed values determine IDs.
llvm::Expected<EncodedLocations> encode(const TranslationUnitIR &unit,
                                        bool includeTemplates,
                                        EncodeOptions options = {});

/// Full eager validation for focused tests and producer-side defense. Generated
/// Rocq lookup performs corresponding checks lazily on reached rows.
llvm::Error validate(const EncodedLocations &locations);

bool operator==(const EncodedShape &lhs, const EncodedShape &rhs);
bool operator==(const EncodedLocationNode &lhs, const EncodedLocationNode &rhs);
bool operator==(const EncodedRoot &lhs, const EncodedRoot &rhs);

} // namespace ir::location::encoding
