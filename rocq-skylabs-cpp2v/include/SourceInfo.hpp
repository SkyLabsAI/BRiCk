/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/Error.h>

namespace source {

template <typename Tag> class StrongIndex {
public:
    using value_type = std::uint32_t;

    StrongIndex() : value_(std::numeric_limits<value_type>::max()) {}
    explicit StrongIndex(value_type value) : value_(value) {}

    value_type value() const { return value_; }
    bool valid() const {
        return value_ != std::numeric_limits<value_type>::max();
    }

    friend bool operator==(StrongIndex lhs, StrongIndex rhs) {
        return lhs.value_ == rhs.value_;
    }
    friend bool operator!=(StrongIndex lhs, StrongIndex rhs) {
        return !(lhs == rhs);
    }
    friend bool operator<(StrongIndex lhs, StrongIndex rhs) {
        return lhs.value_ < rhs.value_;
    }

private:
    value_type value_;
};

struct FileTag;
struct OriginTag;
using FileId = StrongIndex<FileTag>;
using OriginId = StrongIndex<OriginTag>;

enum class FileKind {
    User,
    System,
    ExternCSystem,
    UserModuleMap,
    SystemModuleMap,
    Builtin,
    CommandLine,
    Scratch,
    Predefined,
    Other,
};

enum class RangeKind { Token, Character };
enum class MacroOriginKind { Body, Argument };
enum class OriginKind {
    Explicit,
    Implicit,
    ClangTransformed,
    Cpp2vSynthesized,
    Inherited,
};

struct PhysicalPoint {
    FileId file;
    std::uint64_t byteOffset = 0;
    std::uint32_t line = 0;
    std::uint32_t byteColumn = 0;
};

struct PresumedPoint {
    std::string file;
    std::uint32_t line = 0;
    std::uint32_t column = 0;
};

struct Range {
    std::optional<PhysicalPoint> begin;
    std::optional<PhysicalPoint> end;
    RangeKind endSemantics = RangeKind::Token;
    std::optional<std::pair<PhysicalPoint, PhysicalPoint>> normalizedHalfOpen;
};

struct MacroFrame {
    std::optional<std::string> name;
    MacroOriginKind kind = MacroOriginKind::Body;
    std::optional<Range> spelling;
    std::optional<Range> expansion;
};

struct Origin {
    OriginKind kind = OriginKind::Explicit;
    std::optional<Range> spelling;
    std::optional<Range> expansion;
    std::optional<PresumedPoint> presumedBegin;
    std::optional<PresumedPoint> presumedEnd;
    std::vector<MacroFrame> macroStack;
    std::optional<PhysicalPoint> pointOfInstantiation;
    std::optional<OriginId> anchor;
    std::vector<OriginId> derivedFrom;
};

struct File {
    std::string physicalName;
    std::optional<std::string> requestedName;
    FileKind kind = FileKind::Other;
    bool isMain = false;
    std::optional<std::pair<FileId, std::uint64_t>> includeParent;
};

struct Tables {
    std::vector<File> files;
    std::vector<Origin> origins;
};

/** Main-file projection for compact location companions. [oldToNewOrigin]
    contains dense, first-seen IDs for every retained origin; [directlyRelevant]
    identifies the old rows whose main-file source data is attached to semantic
    nodes (rather than retained solely to close provenance links). */
struct MainFileProjection {
    Tables tables;
    std::vector<std::optional<OriginId>> oldToNewOrigin;
    std::vector<bool> directlyRelevant;
};

bool operator==(const PhysicalPoint &lhs, const PhysicalPoint &rhs);
bool operator==(const PresumedPoint &lhs, const PresumedPoint &rhs);
bool operator==(const Range &lhs, const Range &rhs);
bool operator==(const MacroFrame &lhs, const MacroFrame &rhs);
bool operator==(const Origin &lhs, const Origin &rhs);
bool operator==(const File &lhs, const File &rhs);

/// Owned, deterministic first-seen interning. Origins use a full-value hash
/// index with equality-checked collision buckets; table order and IDs remain
/// first-seen. Clang-backed extraction wraps this pure builder in
/// ClangSourceInfo and never stores SourceManager state in the resulting
/// values.
class TableBuilder {
public:
    /// Intern by serialized value. Pure/manual producers normally want this.
    llvm::Expected<FileId> internFile(File file);
    /// Append even when an equal serialized File already exists. Clang-backed
    /// extraction uses this after comparing its non-serialized live identity.
    llvm::Expected<FileId> appendDistinctFile(File file);
    llvm::Expected<OriginId> internOrigin(Origin origin);
    llvm::Expected<Tables> finish() &&;

private:
    Tables tables_;
    std::unordered_map<std::size_t, llvm::SmallVector<OriginId, 1>>
        originIndex_;
    bool finished_ = false;
};

/// Append/deduplicate origin references without sorting, preserving the first
/// producer occurrence and therefore derivation order.
void appendOriginStable(std::vector<OriginId> &origins, OriginId origin);
void appendOriginsStable(std::vector<OriginId> &origins,
                         const std::vector<OriginId> &additions);

llvm::Error validate(const Tables &tables);

/// Validate [source], retain only physical main-file source data, clear macro
/// stacks, and deterministically remap retained files/origins. This is pure and
/// deliberately does not retain Clang SourceManager state.
llvm::Expected<MainFileProjection> projectMainFile(const Tables &source);

} // namespace source
