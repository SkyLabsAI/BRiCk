/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "SourceInfo.hpp"

#include <algorithm>
#include <functional>
#include <system_error>

#include <llvm/Support/Error.h>

namespace source {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

template <typename T>
bool equalOptional(const std::optional<T> &lhs, const std::optional<T> &rhs) {
    if (lhs.has_value() != rhs.has_value())
        return false;
    return !lhs || *lhs == *rhs;
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

void hashPhysicalPoint(std::size_t &seed, const PhysicalPoint &point) {
    combineHash(seed, point.file.value());
    combineHash(seed, std::hash<std::uint64_t>{}(point.byteOffset));
    combineHash(seed, point.line);
    combineHash(seed, point.byteColumn);
}

void hashPresumedPoint(std::size_t &seed, const PresumedPoint &point) {
    combineHash(seed, std::hash<std::string>{}(point.file));
    combineHash(seed, point.line);
    combineHash(seed, point.column);
}

void hashRange(std::size_t &seed, const Range &range) {
    hashOptional(seed, range.begin, hashPhysicalPoint);
    hashOptional(seed, range.end, hashPhysicalPoint);
    combineHash(seed, static_cast<std::size_t>(range.endSemantics));
    hashOptional(seed, range.normalizedHalfOpen,
                 [](std::size_t &nested,
                    const std::pair<PhysicalPoint, PhysicalPoint> &points) {
                     hashPhysicalPoint(nested, points.first);
                     hashPhysicalPoint(nested, points.second);
                 });
}

void hashMacroFrame(std::size_t &seed, const MacroFrame &frame) {
    hashOptional(seed, frame.name,
                 [](std::size_t &nested, const std::string &name) {
                     combineHash(nested, std::hash<std::string>{}(name));
                 });
    combineHash(seed, static_cast<std::size_t>(frame.kind));
    hashOptional(seed, frame.spelling, hashRange);
    hashOptional(seed, frame.expansion, hashRange);
}

std::size_t hashOrigin(const Origin &origin) {
    std::size_t seed = 0;
    combineHash(seed, static_cast<std::size_t>(origin.kind));
    hashOptional(seed, origin.spelling, hashRange);
    hashOptional(seed, origin.expansion, hashRange);
    hashOptional(seed, origin.presumedBegin, hashPresumedPoint);
    hashOptional(seed, origin.presumedEnd, hashPresumedPoint);
    combineHash(seed, origin.macroStack.size());
    for (const MacroFrame &frame : origin.macroStack)
        hashMacroFrame(seed, frame);
    hashOptional(seed, origin.pointOfInstantiation, hashPhysicalPoint);
    hashOptional(seed, origin.anchor, [](std::size_t &nested, OriginId id) {
        combineHash(nested, id.value());
    });
    combineHash(seed, origin.derivedFrom.size());
    for (OriginId id : origin.derivedFrom)
        combineHash(seed, id.value());
    return seed;
}

bool validFile(FileId id, const Tables &tables) {
    return id.valid() && id.value() < tables.files.size();
}

llvm::Error validatePoint(const PhysicalPoint &point, const Tables &tables,
                          const char *where) {
    if (!validFile(point.file, tables))
        return error(std::string(where) + " has an out-of-range file ID");
    return llvm::Error::success();
}

llvm::Error validateRange(const Range &range, const Tables &tables,
                          const char *where) {
    if (range.begin)
        if (auto failure = validatePoint(*range.begin, tables, where))
            return failure;
    if (range.end)
        if (auto failure = validatePoint(*range.end, tables, where))
            return failure;
    // Independently projected macro endpoints can be non-contiguous or even
    // reverse in one physical file (for example, a declaration beginning at a
    // use site and ending in an earlier macro definition). Keep those points
    // honest. Only a claimed normalized half-open range must be ordered.
    if (range.normalizedHalfOpen) {
        if (!range.begin || !range.end)
            return error(std::string(where) +
                         " normalizes a range with a missing endpoint");
        const auto &[begin, end] = *range.normalizedHalfOpen;
        if (auto failure = validatePoint(begin, tables, where))
            return failure;
        if (auto failure = validatePoint(end, tables, where))
            return failure;
        if (range.begin->file != range.end->file)
            return error(std::string(where) +
                         " normalizes cross-file original endpoints");
        if (begin.file != end.file || begin.file != range.begin->file ||
            end.file != range.end->file || begin.byteOffset > end.byteOffset)
            return error(std::string(where) +
                         " has an incoherent normalized half-open range");
    }
    return llvm::Error::success();
}

} // namespace

bool operator==(const PhysicalPoint &lhs, const PhysicalPoint &rhs) {
    return lhs.file == rhs.file && lhs.byteOffset == rhs.byteOffset &&
           lhs.line == rhs.line && lhs.byteColumn == rhs.byteColumn;
}

bool operator==(const PresumedPoint &lhs, const PresumedPoint &rhs) {
    return lhs.file == rhs.file && lhs.line == rhs.line &&
           lhs.column == rhs.column;
}

bool operator==(const Range &lhs, const Range &rhs) {
    return equalOptional(lhs.begin, rhs.begin) &&
           equalOptional(lhs.end, rhs.end) &&
           lhs.endSemantics == rhs.endSemantics &&
           equalOptional(lhs.normalizedHalfOpen, rhs.normalizedHalfOpen);
}

bool operator==(const MacroFrame &lhs, const MacroFrame &rhs) {
    return lhs.name == rhs.name && lhs.kind == rhs.kind &&
           equalOptional(lhs.spelling, rhs.spelling) &&
           equalOptional(lhs.expansion, rhs.expansion);
}

bool operator==(const Origin &lhs, const Origin &rhs) {
    return lhs.kind == rhs.kind && equalOptional(lhs.spelling, rhs.spelling) &&
           equalOptional(lhs.expansion, rhs.expansion) &&
           equalOptional(lhs.presumedBegin, rhs.presumedBegin) &&
           equalOptional(lhs.presumedEnd, rhs.presumedEnd) &&
           lhs.macroStack == rhs.macroStack &&
           equalOptional(lhs.pointOfInstantiation, rhs.pointOfInstantiation) &&
           lhs.anchor == rhs.anchor && lhs.derivedFrom == rhs.derivedFrom;
}

bool operator==(const File &lhs, const File &rhs) {
    return lhs.physicalName == rhs.physicalName &&
           lhs.requestedName == rhs.requestedName && lhs.kind == rhs.kind &&
           lhs.isMain == rhs.isMain && lhs.includeParent == rhs.includeParent;
}

llvm::Expected<FileId> TableBuilder::internFile(File file) {
    if (finished_)
        return error("cannot intern a file after source tables are finished");
    auto found = std::find(tables_.files.begin(), tables_.files.end(), file);
    if (found != tables_.files.end())
        return FileId(static_cast<FileId::value_type>(
            std::distance(tables_.files.begin(), found)));
    if (tables_.files.size() >= std::numeric_limits<FileId::value_type>::max())
        return error("too many source files");
    auto id = FileId(static_cast<FileId::value_type>(tables_.files.size()));
    tables_.files.push_back(std::move(file));
    return id;
}

llvm::Expected<FileId> TableBuilder::appendDistinctFile(File file) {
    if (finished_)
        return error("cannot append a file after source tables are finished");
    if (tables_.files.size() >= std::numeric_limits<FileId::value_type>::max())
        return error("too many source files");
    auto id = FileId(static_cast<FileId::value_type>(tables_.files.size()));
    tables_.files.push_back(std::move(file));
    return id;
}

llvm::Expected<OriginId> TableBuilder::internOrigin(Origin origin) {
    if (finished_)
        return error(
            "cannot intern an origin after source tables are finished");
    const std::size_t hash = hashOrigin(origin);
    auto indexed = originIndex_.find(hash);
    if (indexed != originIndex_.end())
        for (OriginId candidate : indexed->second)
            if (tables_.origins[candidate.value()] == origin)
                return candidate;
    if (tables_.origins.size() >=
        std::numeric_limits<OriginId::value_type>::max())
        return error("too many source origins");
    auto id =
        OriginId(static_cast<OriginId::value_type>(tables_.origins.size()));
    tables_.origins.push_back(std::move(origin));
    originIndex_[hash].push_back(id);
    return id;
}

llvm::Expected<Tables> TableBuilder::finish() && {
    if (finished_)
        return error("source tables were already finished");
    if (auto failure = validate(tables_))
        return std::move(failure);
    finished_ = true;
    return std::move(tables_);
}

void appendOriginStable(std::vector<OriginId> &origins, OriginId origin) {
    if (std::find(origins.begin(), origins.end(), origin) == origins.end())
        origins.push_back(origin);
}

void appendOriginsStable(std::vector<OriginId> &origins,
                         const std::vector<OriginId> &additions) {
    for (OriginId origin : additions)
        appendOriginStable(origins, origin);
}

llvm::Error validate(const Tables &tables) {
    for (std::size_t i = 0; i < tables.files.size(); ++i) {
        const auto &file = tables.files[i];
        if (file.includeParent && !validFile(file.includeParent->first, tables))
            return error("source file " + std::to_string(i) +
                         " has an out-of-range include parent");
    }

    auto validOrigin = [&](OriginId id) {
        return id.valid() && id.value() < tables.origins.size();
    };
    for (std::size_t i = 0; i < tables.origins.size(); ++i) {
        const auto &origin = tables.origins[i];
        if (origin.spelling)
            if (auto failure = validateRange(*origin.spelling, tables,
                                             "origin spelling range"))
                return failure;
        if (origin.expansion)
            if (auto failure = validateRange(*origin.expansion, tables,
                                             "origin expansion range"))
                return failure;
        if (origin.pointOfInstantiation)
            if (auto failure = validatePoint(*origin.pointOfInstantiation,
                                             tables, "point of instantiation"))
                return failure;
        for (const auto &frame : origin.macroStack) {
            if (frame.spelling)
                if (auto failure = validateRange(*frame.spelling, tables,
                                                 "macro spelling range"))
                    return failure;
            if (frame.expansion)
                if (auto failure = validateRange(*frame.expansion, tables,
                                                 "macro expansion range"))
                    return failure;
        }
        if (origin.anchor && !validOrigin(*origin.anchor))
            return error("origin " + std::to_string(i) +
                         " has an out-of-range anchor");
        for (OriginId derived : origin.derivedFrom)
            if (!validOrigin(derived))
                return error("origin " + std::to_string(i) +
                             " has an out-of-range derivation");
    }

    // Check the whole provenance graph, including disconnected components.
    std::vector<unsigned char> color(tables.origins.size(), 0);
    std::function<llvm::Error(OriginId)> visit =
        [&](OriginId id) -> llvm::Error {
        auto &state = color[id.value()];
        if (state == 1)
            return error("source provenance graph contains a cycle");
        if (state == 2)
            return llvm::Error::success();
        state = 1;
        const auto &origin = tables.origins[id.value()];
        if (origin.anchor)
            if (auto failure = visit(*origin.anchor))
                return failure;
        for (OriginId next : origin.derivedFrom)
            if (auto failure = visit(next))
                return failure;
        state = 2;
        return llvm::Error::success();
    };
    for (std::size_t i = 0; i < tables.origins.size(); ++i)
        if (auto failure = visit(OriginId(static_cast<std::uint32_t>(i))))
            return failure;
    return llvm::Error::success();
}

llvm::Expected<MainFileProjection> projectMainFile(const Tables &source) {
    if (auto failure = validate(source))
        return std::move(failure);

    std::optional<FileId> mainFile;
    for (std::size_t index = 0; index < source.files.size(); ++index) {
        if (!source.files[index].isMain)
            continue;
        if (mainFile)
            return error("source tables contain more than one main file");
        mainFile = FileId(static_cast<FileId::value_type>(index));
    }

    MainFileProjection result;
    result.oldToNewOrigin.resize(source.origins.size());
    result.directlyRelevant.assign(source.origins.size(), false);
    if (mainFile) {
        File file = source.files[mainFile->value()];
        // A main file should not have an include parent. More importantly, an
        // included parent is deliberately absent from this filtered table.
        file.includeParent.reset();
        result.tables.files.push_back(std::move(file));
    }

    auto keepPoint = [&](const std::optional<PhysicalPoint> &point)
        -> std::optional<PhysicalPoint> {
        if (!point || !mainFile || point->file != *mainFile)
            return std::nullopt;
        PhysicalPoint kept = *point;
        kept.file = FileId(0);
        return kept;
    };
    auto projectRange =
        [&](const std::optional<Range> &range) -> std::optional<Range> {
        if (!range)
            return std::nullopt;
        Range kept;
        kept.begin = keepPoint(range->begin);
        kept.end = keepPoint(range->end);
        kept.endSemantics = range->endSemantics;
        if (!kept.begin && !kept.end)
            return std::nullopt;
        if (range->normalizedHalfOpen && kept.begin && kept.end) {
            const auto &[begin, end] = *range->normalizedHalfOpen;
            auto normalizedBegin = keepPoint(begin);
            auto normalizedEnd = keepPoint(end);
            if (normalizedBegin && normalizedEnd &&
                normalizedBegin->file == normalizedEnd->file &&
                normalizedBegin->file == kept.begin->file &&
                normalizedEnd->file == kept.end->file &&
                normalizedBegin->byteOffset <= normalizedEnd->byteOffset)
                kept.normalizedHalfOpen =
                    std::make_pair(*normalizedBegin, *normalizedEnd);
        }
        return kept;
    };
    auto hasPoint = [](const std::optional<Range> &range) {
        return range && (range->begin || range->end);
    };
    auto expansionEndpoint = [](const std::optional<Range> &range,
                                bool begin) -> bool {
        if (!range)
            return false;
        return begin ? range->begin.has_value() : range->end.has_value();
    };

    std::vector<Origin> projected(source.origins.size());
    std::vector<bool> retain(source.origins.size(), false);
    std::vector<std::size_t> pending;
    for (std::size_t index = 0; index < source.origins.size(); ++index) {
        const Origin &origin = source.origins[index];
        Origin kept;
        kept.kind = origin.kind;
        kept.spelling = projectRange(origin.spelling);
        kept.expansion = projectRange(origin.expansion);
        // Presumed locations describe expansion locations in Clang. Preserve
        // only the corresponding display coordinate when that physical
        // expansion endpoint survives the main-file filter.
        if (expansionEndpoint(kept.expansion, true))
            kept.presumedBegin = origin.presumedBegin;
        if (expansionEndpoint(kept.expansion, false))
            kept.presumedEnd = origin.presumedEnd;
        kept.pointOfInstantiation = keepPoint(origin.pointOfInstantiation);
        // Main-file mode intentionally does not leak header spelling through
        // macro backtraces.
        kept.macroStack.clear();
        kept.anchor = origin.anchor;
        kept.derivedFrom = origin.derivedFrom;
        const bool direct = hasPoint(kept.spelling) ||
                            hasPoint(kept.expansion) || kept.presumedBegin ||
                            kept.presumedEnd || kept.pointOfInstantiation;
        projected[index] = std::move(kept);
        result.directlyRelevant[index] = direct;
        if (direct) {
            retain[index] = true;
            pending.push_back(index);
        }
    }

    // Keep the established directed anchor/derivation closure. The complete
    // source graph was validated above, so this only selects rows; it cannot
    // make a malformed dangling link disappear.
    for (std::size_t cursor = 0; cursor < pending.size(); ++cursor) {
        const Origin &origin = projected[pending[cursor]];
        auto retainOrigin = [&](OriginId id) {
            const std::size_t target = id.value();
            if (!retain[target]) {
                retain[target] = true;
                pending.push_back(target);
            }
        };
        if (origin.anchor)
            retainOrigin(*origin.anchor);
        for (OriginId id : origin.derivedFrom)
            retainOrigin(id);
    }

    for (std::size_t index = 0; index < retain.size(); ++index)
        if (retain[index]) {
            const OriginId id(static_cast<OriginId::value_type>(
                result.tables.origins.size()));
            result.oldToNewOrigin[index] = id;
            result.tables.origins.push_back(projected[index]);
        }

    for (std::size_t old = 0; old < source.origins.size(); ++old) {
        if (!result.oldToNewOrigin[old])
            continue;
        Origin &origin =
            result.tables.origins[result.oldToNewOrigin[old]->value()];
        if (origin.anchor)
            origin.anchor = result.oldToNewOrigin[origin.anchor->value()];
        for (OriginId &id : origin.derivedFrom)
            id = *result.oldToNewOrigin[id.value()];
    }
    for (std::size_t old = 0; old < result.directlyRelevant.size(); ++old)
        if (result.directlyRelevant[old] && !result.oldToNewOrigin[old])
            return error("main-file projection omitted a directly relevant "
                         "origin");
    if (auto failure = validate(result.tables))
        return std::move(failure);
    return result;
}

} // namespace source
