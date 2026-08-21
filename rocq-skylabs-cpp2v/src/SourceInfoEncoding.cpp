/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "SourceInfoEncoding.hpp"

#include <functional>
#include <limits>
#include <system_error>
#include <type_traits>
#include <unordered_map>
#include <utility>

#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/Error.h>

namespace source::encoding {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

void combineHash(std::size_t &seed, std::size_t value) {
    seed ^= value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
            (seed << 6U) + (seed >> 2U);
}

template <typename T, typename Hash>
void hashOptional(std::size_t &seed, const std::optional<T> &value, Hash hash) {
    combineHash(seed, value.has_value());
    if (value)
        hash(seed, *value);
}

void hashId(std::size_t &seed, std::uint32_t value) {
    combineHash(seed, value);
}

void hashPhysicalPoint(std::size_t &seed, const PhysicalPoint &point) {
    hashId(seed, point.file.value());
    combineHash(seed, std::hash<std::uint64_t>{}(point.byteOffset));
    combineHash(seed, point.line);
    combineHash(seed, point.byteColumn);
}

std::size_t hashString(const std::string &value) {
    return std::hash<std::string>{}(value);
}

std::size_t hashSourceName(const SourceName &value) {
    std::size_t seed = 0;
    combineHash(seed, static_cast<std::size_t>(value.kind));
    combineHash(seed, hashString(value.value));
    return seed;
}

std::size_t hashEncodedPresumed(const EncodedPresumedPoint &point) {
    std::size_t seed = 0;
    hashId(seed, point.file.value());
    combineHash(seed, point.line);
    combineHash(seed, point.column);
    return seed;
}

std::size_t hashRawRange(const RawRange &range) {
    std::size_t seed = 0;
    combineHash(seed, 0);
    hashOptional(seed, range.begin,
                 [](std::size_t &nested, PhysicalPointId id) {
                     hashId(nested, id.value());
                 });
    hashOptional(seed, range.end, [](std::size_t &nested, PhysicalPointId id) {
        hashId(nested, id.value());
    });
    combineHash(seed, static_cast<std::size_t>(range.endSemantics));
    return seed;
}

std::size_t hashSameBeginRange(const SameBeginNormalizedRange &range) {
    std::size_t seed = 0;
    combineHash(seed, 1);
    hashId(seed, range.begin.value());
    hashId(seed, range.end.value());
    combineHash(seed, static_cast<std::size_t>(range.endSemantics));
    hashId(seed, range.normalizedEnd.value());
    return seed;
}

std::size_t hashGeneralRange(const GeneralNormalizedRange &range) {
    std::size_t seed = 0;
    combineHash(seed, 2);
    hashId(seed, range.begin.value());
    hashId(seed, range.end.value());
    combineHash(seed, static_cast<std::size_t>(range.endSemantics));
    hashId(seed, range.normalizedBegin.value());
    hashId(seed, range.normalizedEnd.value());
    return seed;
}

std::size_t hashRange(const EncodedRange &range) {
    return std::visit(
        [](const auto &value) {
            using T = std::decay_t<decltype(value)>;
            if constexpr (std::is_same_v<T, RawRange>)
                return hashRawRange(value);
            else if constexpr (std::is_same_v<T, SameBeginNormalizedRange>)
                return hashSameBeginRange(value);
            else
                return hashGeneralRange(value);
        },
        range);
}

std::size_t hashFrame(const EncodedMacroFrame &frame) {
    std::size_t seed = 0;
    hashOptional(seed, frame.name,
                 [](std::size_t &nested, const std::string &name) {
                     combineHash(nested, hashString(name));
                 });
    combineHash(seed, static_cast<std::size_t>(frame.kind));
    hashOptional(seed, frame.spelling, [](std::size_t &nested, RangeId id) {
        hashId(nested, id.value());
    });
    hashOptional(seed, frame.expansion, [](std::size_t &nested, RangeId id) {
        hashId(nested, id.value());
    });
    return seed;
}

template <typename Id, typename Value, typename Hash> class Interner {
public:
    explicit Interner(bool forceHashCollisions) : force_(forceHashCollisions) {}

    llvm::Expected<Id> intern(Value value) {
        const std::size_t hash = force_ ? 0 : Hash{}(value);
        auto found = buckets_.find(hash);
        if (found != buckets_.end())
            for (Id candidate : found->second)
                if (values_[candidate.value()] == value)
                    return candidate;
        if (values_.size() >= std::numeric_limits<std::uint32_t>::max())
            return error("too many normalized provenance table entries");
        const Id id(static_cast<std::uint32_t>(values_.size()));
        values_.push_back(std::move(value));
        buckets_[hash].push_back(id);
        return id;
    }

    std::vector<Value> takeValues() && { return std::move(values_); }

private:
    bool force_;
    std::vector<Value> values_;
    std::unordered_map<std::size_t, llvm::SmallVector<Id, 1>> buckets_;
};

struct SourceNameHash {
    std::size_t operator()(const SourceName &value) const {
        return hashSourceName(value);
    }
};
struct PhysicalPointHash {
    std::size_t operator()(const PhysicalPoint &value) const {
        std::size_t seed = 0;
        hashPhysicalPoint(seed, value);
        return seed;
    }
};
struct PresumedPointHash {
    std::size_t operator()(const EncodedPresumedPoint &value) const {
        return hashEncodedPresumed(value);
    }
};
struct RangeHash {
    std::size_t operator()(const EncodedRange &value) const {
        return hashRange(value);
    }
};
struct FrameHash {
    std::size_t operator()(const EncodedMacroFrame &value) const {
        return hashFrame(value);
    }
};

template <typename Id, typename Value>
llvm::Expected<const Value *> checkedAt(const std::vector<Value> &values, Id id,
                                        const char *table) {
    if (!id.valid() || id.value() >= values.size())
        return error(std::string("malformed ") + table + " ID " +
                     std::to_string(id.value()));
    return &values[id.value()];
}

llvm::Expected<PhysicalPoint> decodePoint(const EncodedTables &tables,
                                          PhysicalPointId id) {
    auto point = checkedAt(tables.physicalPoints, id, "physical-point table");
    if (!point)
        return point.takeError();
    return **point;
}

llvm::Expected<PresumedPoint> decodePresumedPoint(const EncodedTables &tables,
                                                  PresumedPointId id) {
    auto point = checkedAt(tables.presumedPoints, id, "presumed-point table");
    if (!point)
        return point.takeError();
    auto file = checkedAt(tables.presumedFilenames, (*point)->file,
                          "presumed-filename table");
    if (!file)
        return file.takeError();
    return PresumedPoint{**file, (*point)->line, (*point)->column};
}

llvm::Expected<Range> decodeRange(const EncodedTables &tables, RangeId id) {
    auto encoded = checkedAt(tables.ranges, id, "range table");
    if (!encoded)
        return encoded.takeError();
    return std::visit(
        [&](const auto &range) -> llvm::Expected<Range> {
            using T = std::decay_t<decltype(range)>;
            if constexpr (std::is_same_v<T, RawRange>) {
                Range result;
                result.endSemantics = range.endSemantics;
                if (range.begin) {
                    auto point = decodePoint(tables, *range.begin);
                    if (!point)
                        return point.takeError();
                    result.begin = std::move(*point);
                }
                if (range.end) {
                    auto point = decodePoint(tables, *range.end);
                    if (!point)
                        return point.takeError();
                    result.end = std::move(*point);
                }
                return result;
            } else {
                auto begin = decodePoint(tables, range.begin);
                if (!begin)
                    return begin.takeError();
                auto end = decodePoint(tables, range.end);
                if (!end)
                    return end.takeError();
                auto normalizedEnd = decodePoint(tables, range.normalizedEnd);
                if (!normalizedEnd)
                    return normalizedEnd.takeError();
                PhysicalPoint normalizedBegin;
                if constexpr (std::is_same_v<T, SameBeginNormalizedRange>)
                    normalizedBegin = *begin;
                else {
                    auto decoded = decodePoint(tables, range.normalizedBegin);
                    if (!decoded)
                        return decoded.takeError();
                    normalizedBegin = std::move(*decoded);
                }
                return Range{std::move(*begin), std::move(*end),
                             range.endSemantics,
                             std::make_pair(std::move(normalizedBegin),
                                            std::move(*normalizedEnd))};
            }
        },
        **encoded);
}

} // namespace

bool operator==(const EncodedPresumedPoint &lhs,
                const EncodedPresumedPoint &rhs) {
    return lhs.file == rhs.file && lhs.line == rhs.line &&
           lhs.column == rhs.column;
}

bool operator==(const RawRange &lhs, const RawRange &rhs) {
    return lhs.begin == rhs.begin && lhs.end == rhs.end &&
           lhs.endSemantics == rhs.endSemantics;
}

bool operator==(const SameBeginNormalizedRange &lhs,
                const SameBeginNormalizedRange &rhs) {
    return lhs.begin == rhs.begin && lhs.end == rhs.end &&
           lhs.endSemantics == rhs.endSemantics &&
           lhs.normalizedEnd == rhs.normalizedEnd;
}

bool operator==(const GeneralNormalizedRange &lhs,
                const GeneralNormalizedRange &rhs) {
    return lhs.begin == rhs.begin && lhs.end == rhs.end &&
           lhs.endSemantics == rhs.endSemantics &&
           lhs.normalizedBegin == rhs.normalizedBegin &&
           lhs.normalizedEnd == rhs.normalizedEnd;
}

bool operator==(const EncodedMacroFrame &lhs, const EncodedMacroFrame &rhs) {
    return lhs.name == rhs.name && lhs.kind == rhs.kind &&
           lhs.spelling == rhs.spelling && lhs.expansion == rhs.expansion;
}

bool operator==(const EncodedOrigin &lhs, const EncodedOrigin &rhs) {
    return lhs.kind == rhs.kind && lhs.spelling == rhs.spelling &&
           lhs.expansion == rhs.expansion &&
           lhs.presumedBegin == rhs.presumedBegin &&
           lhs.presumedEnd == rhs.presumedEnd &&
           lhs.macroStack == rhs.macroStack &&
           lhs.pointOfInstantiation == rhs.pointOfInstantiation &&
           lhs.anchor == rhs.anchor && lhs.derivedFrom == rhs.derivedFrom;
}

llvm::Expected<EncodedTables> encode(const source::Tables &source,
                                     EncodeOptions options) {
    if (auto failure = source::validate(source))
        return std::move(failure);

    Interner<FilenameId, SourceName, SourceNameHash> filenames(
        options.forceHashCollisions);
    Interner<PhysicalPointId, PhysicalPoint, PhysicalPointHash> points(
        options.forceHashCollisions);
    Interner<PresumedPointId, EncodedPresumedPoint, PresumedPointHash> presumed(
        options.forceHashCollisions);
    Interner<RangeId, EncodedRange, RangeHash> ranges(
        options.forceHashCollisions);
    Interner<MacroFrameId, EncodedMacroFrame, FrameHash> frames(
        options.forceHashCollisions);

    auto internPoint = [&](const PhysicalPoint &point) {
        return points.intern(point);
    };
    auto internPresumed =
        [&](const PresumedPoint &point) -> llvm::Expected<PresumedPointId> {
        auto file = filenames.intern(point.file);
        if (!file)
            return file.takeError();
        return presumed.intern({*file, point.line, point.column});
    };
    auto internRange = [&](const Range &range) -> llvm::Expected<RangeId> {
        std::optional<PhysicalPointId> begin;
        std::optional<PhysicalPointId> end;
        if (range.begin) {
            auto id = internPoint(*range.begin);
            if (!id)
                return id.takeError();
            begin = *id;
        }
        if (range.end) {
            auto id = internPoint(*range.end);
            if (!id)
                return id.takeError();
            end = *id;
        }
        EncodedRange encoded;
        if (!range.normalizedHalfOpen) {
            encoded = RawRange{begin, end, range.endSemantics};
        } else {
            // Full source validation above establishes both original endpoints.
            auto normalizedBegin = internPoint(range.normalizedHalfOpen->first);
            if (!normalizedBegin)
                return normalizedBegin.takeError();
            auto normalizedEnd = internPoint(range.normalizedHalfOpen->second);
            if (!normalizedEnd)
                return normalizedEnd.takeError();
            if (*normalizedBegin == *begin)
                encoded = SameBeginNormalizedRange{
                    *begin, *end, range.endSemantics, *normalizedEnd};
            else
                encoded =
                    GeneralNormalizedRange{*begin, *end, range.endSemantics,
                                           *normalizedBegin, *normalizedEnd};
        }
        return ranges.intern(std::move(encoded));
    };
    auto internFrame =
        [&](const MacroFrame &frame) -> llvm::Expected<MacroFrameId> {
        std::optional<RangeId> spelling;
        std::optional<RangeId> expansion;
        if (frame.spelling) {
            auto id = internRange(*frame.spelling);
            if (!id)
                return id.takeError();
            spelling = *id;
        }
        if (frame.expansion) {
            auto id = internRange(*frame.expansion);
            if (!id)
                return id.takeError();
            expansion = *id;
        }
        return frames.intern({frame.name, frame.kind, spelling, expansion});
    };

    EncodedTables result;
    result.origins.reserve(source.origins.size());
    for (const Origin &origin : source.origins) {
        EncodedOrigin encoded;
        encoded.kind = origin.kind;
        if (origin.spelling) {
            auto id = internRange(*origin.spelling);
            if (!id)
                return id.takeError();
            encoded.spelling = *id;
        }
        if (origin.expansion) {
            auto id = internRange(*origin.expansion);
            if (!id)
                return id.takeError();
            encoded.expansion = *id;
        }
        if (origin.presumedBegin) {
            auto id = internPresumed(*origin.presumedBegin);
            if (!id)
                return id.takeError();
            encoded.presumedBegin = *id;
        }
        if (origin.presumedEnd) {
            auto id = internPresumed(*origin.presumedEnd);
            if (!id)
                return id.takeError();
            encoded.presumedEnd = *id;
        }
        encoded.macroStack.reserve(origin.macroStack.size());
        for (const MacroFrame &frame : origin.macroStack) {
            auto id = internFrame(frame);
            if (!id)
                return id.takeError();
            encoded.macroStack.push_back(*id);
        }
        if (origin.pointOfInstantiation) {
            auto id = internPoint(*origin.pointOfInstantiation);
            if (!id)
                return id.takeError();
            encoded.pointOfInstantiation = *id;
        }
        encoded.anchor = origin.anchor;
        encoded.derivedFrom = origin.derivedFrom;
        result.origins.push_back(std::move(encoded));
    }

    result.presumedFilenames = std::move(filenames).takeValues();
    result.physicalPoints = std::move(points).takeValues();
    result.presumedPoints = std::move(presumed).takeValues();
    result.ranges = std::move(ranges).takeValues();
    result.macroFrames = std::move(frames).takeValues();
    result.stats.sourceOrigins = result.origins.size();
    result.stats.presumedFilenameRows = result.presumedFilenames.size();
    result.stats.physicalPointRows = result.physicalPoints.size();
    result.stats.presumedPointRows = result.presumedPoints.size();
    result.stats.rangeRows = result.ranges.size();
    result.stats.macroFrameRows = result.macroFrames.size();
    for (const EncodedRange &range : result.ranges)
        std::visit(
            [&](const auto &value) {
                using T = std::decay_t<decltype(value)>;
                if constexpr (std::is_same_v<T, RawRange>)
                    ++result.stats.rawRanges;
                else if constexpr (std::is_same_v<T, SameBeginNormalizedRange>)
                    ++result.stats.sameBeginNormalizedRanges;
                else
                    ++result.stats.generalNormalizedRanges;
            },
            range);
    for (const EncodedOrigin &origin : result.origins)
        result.stats.macroFrameOccurrences += origin.macroStack.size();
    return result;
}

llvm::Expected<Origin> decodeOrigin(const EncodedTables &tables, OriginId id) {
    auto encoded = checkedAt(tables.origins, id, "origin table");
    if (!encoded)
        return encoded.takeError();
    Origin result;
    result.kind = (*encoded)->kind;
    if ((*encoded)->spelling) {
        auto range = decodeRange(tables, *(*encoded)->spelling);
        if (!range)
            return range.takeError();
        result.spelling = std::move(*range);
    }
    if ((*encoded)->expansion) {
        auto range = decodeRange(tables, *(*encoded)->expansion);
        if (!range)
            return range.takeError();
        result.expansion = std::move(*range);
    }
    if ((*encoded)->presumedBegin) {
        auto point = decodePresumedPoint(tables, *(*encoded)->presumedBegin);
        if (!point)
            return point.takeError();
        result.presumedBegin = std::move(*point);
    }
    if ((*encoded)->presumedEnd) {
        auto point = decodePresumedPoint(tables, *(*encoded)->presumedEnd);
        if (!point)
            return point.takeError();
        result.presumedEnd = std::move(*point);
    }
    result.macroStack.reserve((*encoded)->macroStack.size());
    for (MacroFrameId id : (*encoded)->macroStack) {
        auto frame = checkedAt(tables.macroFrames, id, "macro-frame table");
        if (!frame)
            return frame.takeError();
        MacroFrame decoded;
        decoded.name = (*frame)->name;
        decoded.kind = (*frame)->kind;
        if ((*frame)->spelling) {
            auto range = decodeRange(tables, *(*frame)->spelling);
            if (!range)
                return range.takeError();
            decoded.spelling = std::move(*range);
        }
        if ((*frame)->expansion) {
            auto range = decodeRange(tables, *(*frame)->expansion);
            if (!range)
                return range.takeError();
            decoded.expansion = std::move(*range);
        }
        result.macroStack.push_back(std::move(decoded));
    }
    if ((*encoded)->pointOfInstantiation) {
        auto point = decodePoint(tables, *(*encoded)->pointOfInstantiation);
        if (!point)
            return point.takeError();
        result.pointOfInstantiation = std::move(*point);
    }
    if ((*encoded)->anchor &&
        (*encoded)->anchor->value() >= tables.origins.size())
        return error("malformed origin anchor ID " +
                     std::to_string((*encoded)->anchor->value()));
    for (OriginId derived : (*encoded)->derivedFrom)
        if (!derived.valid() || derived.value() >= tables.origins.size())
            return error("malformed origin derivation ID " +
                         std::to_string(derived.value()));
    result.anchor = (*encoded)->anchor;
    result.derivedFrom = (*encoded)->derivedFrom;
    return result;
}

} // namespace source::encoding
