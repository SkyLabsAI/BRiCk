/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"

#include <optional>
#include <string>
#include <vector>

#include <llvm/ADT/ArrayRef.h>
#include <llvm/Support/Error.h>

namespace ir {

/// Future production roots provide one ordered seed each. Only Ordinary seeds
/// create definitions. Dependencies in semanticValue are visited before the
/// semanticName, matching legacy declaration preprinting.
enum class SharingSeedKind { Ordinary, TemplateOnly };
struct SharingSeed {
    SharingSeedKind kind = SharingSeedKind::Ordinary;
    NodeId semanticValue;
    /// Present only when legacy PrePrint visits the root declaration's name.
    /// In particular, ordinary VarDecl roots leave this absent: their value
    /// dependencies are seeded, but their root names are not cached.
    std::optional<NodeId> semanticName;
};

struct SharingDefinition {
    ShareClassId shareClass;
    ShareClassKind kind = ShareClassKind::Type;
    NodeId representative;
    std::string localName;
};

class SharingPlan {
public:
    const std::vector<SharingDefinition> &definitions() const {
        return definitions_;
    }
    const SharingDefinition *lookup(ShareClassId shareClass) const;

    /// Construct an unvalidated plan for decoding and negative tests. Every
    /// consumer must call IRSharing::validate before using its definitions.
    static SharingPlan
    fromUnvalidatedDefinitions(std::vector<SharingDefinition> definitions);

private:
    friend class IRSharing;
    std::vector<SharingDefinition> definitions_;
};

class IRSharing {
public:
    /// Derive the exact production seed stream from ordered root events.
    static std::vector<SharingSeed>
    productionSeeds(const TranslationUnitIR &unit);

    /// Analyze finished, owned IR without mutating it. Template-only seeds are
    /// deliberately ignored for definition creation; terms from either mode
    /// may subsequently reference definitions created by ordinary seeds.
    static llvm::Expected<SharingPlan>
    analyze(const TranslationUnitIR &unit, llvm::ArrayRef<SharingSeed> seeds);
    /// Compare owned semantic structure while ignoring origins and sharing
    /// metadata. This is valid during construction and does not finish the IR.
    static llvm::Expected<bool> semanticallyEqual(const TranslationUnitIR &unit,
                                                  NodeId lhs, NodeId rhs);
    static llvm::Error validate(const TranslationUnitIR &unit,
                                const SharingPlan &plan);
};

} // namespace ir
