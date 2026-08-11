/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "SourceInfo.hpp"

#include <cstddef>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include <llvm/Support/Error.h>

namespace source::encoding {

struct FilenameTag;
struct PhysicalPointTag;
struct PresumedPointTag;
struct RangeTag;
struct MacroFrameTag;
using FilenameId = StrongIndex<FilenameTag>;
using PhysicalPointId = StrongIndex<PhysicalPointTag>;
using PresumedPointId = StrongIndex<PresumedPointTag>;
using RangeId = StrongIndex<RangeTag>;
using MacroFrameId = StrongIndex<MacroFrameTag>;

struct EncodedPresumedPoint {
    FilenameId file;
    std::uint32_t line = 0;
    std::uint32_t column = 0;
};

struct RawRange {
    std::optional<PhysicalPointId> begin;
    std::optional<PhysicalPointId> end;
    RangeKind endSemantics = RangeKind::Token;
};

/// The common normalized form: the normalized begin is the original begin.
struct SameBeginNormalizedRange {
    PhysicalPointId begin;
    PhysicalPointId end;
    RangeKind endSemantics = RangeKind::Token;
    PhysicalPointId normalizedEnd;
};

/// The validator permits this less common form, so it must remain
/// representable.
struct GeneralNormalizedRange {
    PhysicalPointId begin;
    PhysicalPointId end;
    RangeKind endSemantics = RangeKind::Token;
    PhysicalPointId normalizedBegin;
    PhysicalPointId normalizedEnd;
};

using EncodedRange =
    std::variant<RawRange, SameBeginNormalizedRange, GeneralNormalizedRange>;

struct EncodedMacroFrame {
    std::optional<std::string> name;
    MacroOriginKind kind = MacroOriginKind::Body;
    std::optional<RangeId> spelling;
    std::optional<RangeId> expansion;
};

struct EncodedOrigin {
    OriginKind kind = OriginKind::Explicit;
    std::optional<RangeId> spelling;
    std::optional<RangeId> expansion;
    std::optional<PresumedPointId> presumedBegin;
    std::optional<PresumedPointId> presumedEnd;
    /// Nearest-first, matching Origin::macroStack exactly.
    std::vector<MacroFrameId> macroStack;
    std::optional<PhysicalPointId> pointOfInstantiation;
    std::optional<OriginId> anchor;
    std::vector<OriginId> derivedFrom;
};

struct EncodingStats {
    std::size_t sourceOrigins = 0;
    std::size_t presumedFilenameRows = 0;
    std::size_t physicalPointRows = 0;
    std::size_t presumedPointRows = 0;
    std::size_t rangeRows = 0;
    std::size_t macroFrameRows = 0;
    std::size_t rawRanges = 0;
    std::size_t sameBeginNormalizedRanges = 0;
    std::size_t generalNormalizedRanges = 0;
    std::size_t macroFrameOccurrences = 0;
};

/// The tables are ordered exclusively by first source occurrence. Origin row i
/// is always the existing source OriginId(i); origin IDs are never remapped.
struct EncodedTables {
    std::vector<std::string> presumedFilenames;
    std::vector<PhysicalPoint> physicalPoints;
    std::vector<EncodedPresumedPoint> presumedPoints;
    std::vector<EncodedRange> ranges;
    std::vector<EncodedMacroFrame> macroFrames;
    std::vector<EncodedOrigin> origins;
    EncodingStats stats;
};

/// A narrow test seam for collision-equality coverage. It must never affect
/// output ordering: buckets remain accelerators and equality decides reuse.
struct EncodeOptions {
    bool forceHashCollisions = false;
};

/// Validate the full source tables then normalize nested values. This does not
/// decode the finished rows; callers needing a round trip may use decodeOrigin
/// in focused tests only.
llvm::Expected<EncodedTables> encode(const source::Tables &source,
                                     EncodeOptions options = {});

/// Decode one encoded row and diagnose malformed private table references.
/// Production construction deliberately does not call this eagerly.
llvm::Expected<Origin> decodeOrigin(const EncodedTables &tables, OriginId id);

bool operator==(const EncodedPresumedPoint &lhs,
                const EncodedPresumedPoint &rhs);
bool operator==(const RawRange &lhs, const RawRange &rhs);
bool operator==(const SameBeginNormalizedRange &lhs,
                const SameBeginNormalizedRange &rhs);
bool operator==(const GeneralNormalizedRange &lhs,
                const GeneralNormalizedRange &rhs);
bool operator==(const EncodedMacroFrame &lhs, const EncodedMacroFrame &rhs);
bool operator==(const EncodedOrigin &lhs, const EncodedOrigin &rhs);

} // namespace source::encoding
