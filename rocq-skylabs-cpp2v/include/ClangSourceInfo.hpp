/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "SourceInfo.hpp"

#include <memory>
#include <optional>
#include <vector>

#include <clang/Basic/SourceLocation.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/Support/Error.h>

namespace clang {
class Decl;
class LangOptions;
class QualType;
class SourceManager;
class TypeLoc;
class TypeSourceInfo;
} // namespace clang

namespace source {

enum class LocationProjection { Spelling, Expansion };

/// A bare semantic QualType has no written location. Callers must explicitly
/// choose whether it has no origin or inherits a use-site/owner origin.
enum class SemanticTypeOriginPolicy { Empty, Inherited };

/// Clang-backed extraction around the pure TableBuilder. The implementation's
/// FileID and SourceManager references are ephemeral; finish destroys them and
/// returns only owned source::Tables.
class ClangTableBuilder {
public:
    ClangTableBuilder(const clang::SourceManager &sourceManager,
                      const clang::LangOptions &langOptions);
    ~ClangTableBuilder();

    ClangTableBuilder(const ClangTableBuilder &) = delete;
    ClangTableBuilder &operator=(const ClangTableBuilder &) = delete;
    ClangTableBuilder(ClangTableBuilder &&) noexcept;
    ClangTableBuilder &operator=(ClangTableBuilder &&) noexcept;

    llvm::Expected<std::optional<PhysicalPoint>>
    physicalPoint(clang::SourceLocation location,
                  LocationProjection projection);
    std::optional<PresumedPoint>
    presumedPoint(clang::SourceLocation location) const;

    /// Extract endpoints independently. NormalizedHalfOpen is populated only
    /// when both projected endpoints are in one file and
    /// Lexer::makeFileCharRange succeeds.
    llvm::Expected<Range> range(clang::CharSourceRange sourceRange,
                                LocationProjection projection);

    llvm::Expected<OriginId>
    explicitNode(clang::CharSourceRange sourceRange,
                 std::optional<clang::SourceLocation> pointOfInstantiation =
                     std::nullopt,
                 llvm::ArrayRef<OriginId> derivedFrom = {});
    llvm::Expected<OriginId>
    explicitNode(clang::SourceRange sourceRange,
                 std::optional<clang::SourceLocation> pointOfInstantiation =
                     std::nullopt,
                 llvm::ArrayRef<OriginId> derivedFrom = {});
    llvm::Expected<OriginId>
    implicitNode(clang::CharSourceRange sourceRange,
                 llvm::ArrayRef<OriginId> derivedFrom = {});
    llvm::Expected<OriginId>
    anchoredImplicitNode(clang::CharSourceRange sourceRange, OriginId anchor,
                         llvm::ArrayRef<OriginId> derivedFrom = {});
    llvm::Expected<OriginId>
    transformedNode(clang::CharSourceRange sourceRange,
                    llvm::ArrayRef<OriginId> derivedFrom);
    llvm::Expected<OriginId>
    synthesizedNode(std::optional<OriginId> anchor,
                    llvm::ArrayRef<OriginId> derivedFrom = {});
    llvm::Expected<OriginId>
    inheritedNode(std::optional<OriginId> anchor,
                  llvm::ArrayRef<OriginId> derivedFrom = {});

    /// Records the declaration's spelling range and, for Clang declaration
    /// families that expose one, its POI as a separate expansion point. A
    /// supplied POI supports additional declaration families without folding
    /// it into the spelling range.
    llvm::Expected<OriginId>
    declarationNode(const clang::Decl &declaration,
                    std::optional<clang::SourceLocation> pointOfInstantiation =
                        std::nullopt,
                    OriginKind kind = OriginKind::Explicit);
    llvm::Expected<OriginId>
    typeLocNode(const clang::TypeLoc &typeLoc,
                OriginKind kind = OriginKind::Explicit);
    llvm::Expected<OriginId>
    typeSourceInfoNode(const clang::TypeSourceInfo *typeSourceInfo,
                       OriginKind kind = OriginKind::Explicit);
    llvm::Expected<std::vector<OriginId>>
    semanticQualTypeOrigins(const clang::QualType &type,
                            SemanticTypeOriginPolicy policy,
                            std::optional<OriginId> inheritedFrom);

    llvm::Expected<Tables> finish() &&;

private:
    class Impl;
    std::unique_ptr<Impl> impl_;
};

} // namespace source
