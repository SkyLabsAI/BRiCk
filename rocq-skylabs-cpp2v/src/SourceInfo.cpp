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
    auto found =
        std::find(tables_.origins.begin(), tables_.origins.end(), origin);
    if (found != tables_.origins.end())
        return OriginId(static_cast<OriginId::value_type>(
            std::distance(tables_.origins.begin(), found)));
    if (tables_.origins.size() >=
        std::numeric_limits<OriginId::value_type>::max())
        return error("too many source origins");
    auto id =
        OriginId(static_cast<OriginId::value_type>(tables_.origins.size()));
    tables_.origins.push_back(std::move(origin));
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

} // namespace source
