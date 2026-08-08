/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"
#include "Sharing.hpp"

#include <string>

#include <llvm/Support/Error.h>

namespace ir {

class LocationRocqEmitter;

struct RocqEmitterOptions {
    bool sharing = true;
    bool localSharingDefinitions = false;
    bool metaSharingTypes = true;
};

/// Phase-2 validated fragment emitter for manually built IR. Standalone module
/// imports, ABI/source composition, and the default cpp2v path remain Phase 5.
class SemanticRocqEmitter {
public:
    explicit SemanticRocqEmitter(RocqEmitterOptions options = {})
        : options_(options) {}

    llvm::Expected<std::string> emit(const TranslationUnitIR &unit) const;
    llvm::Expected<std::string>
    emitOrdinary(const TranslationUnitIR &unit) const;
    llvm::Expected<std::string> emitOrdinary(const TranslationUnitIR &unit,
                                             const SharingPlan &plan) const;
    llvm::Expected<std::string>
    emitTemplates(const TranslationUnitIR &unit) const;
    llvm::Expected<std::string> emitTemplates(const TranslationUnitIR &unit,
                                              const SharingPlan &plan) const;
    llvm::Expected<std::string> renderNode(const TranslationUnitIR &unit,
                                           NodeId id) const;
    llvm::Expected<std::string> renderNode(const TranslationUnitIR &unit,
                                           NodeId id,
                                           const SharingPlan &plan) const;
    llvm::Expected<std::string>
    emitSharingDefinitions(const TranslationUnitIR &unit,
                           const SharingPlan &plan) const;

private:
    friend class LocationRocqEmitter;

    llvm::Expected<std::string>
    emitEvents(const TranslationUnitIR &unit,
               std::optional<bool> templatePartition,
               const SharingPlan *plan) const;
    llvm::Expected<std::string> renderNodeUnchecked(
        const TranslationUnitIR &unit, NodeId id,
        const SharingPlan *plan = nullptr,
        std::optional<ShareClassId> suppressed = std::nullopt) const;
    llvm::Expected<std::string>
    renderValue(const TranslationUnitIR &unit, const Value &value,
                const std::vector<NodeId> &projectedChildren,
                std::size_t &nextChild, const SharingPlan *plan,
                std::optional<ShareClassId> suppressed) const;
    std::string renderScalar(const ScalarTerm &scalar) const;

    RocqEmitterOptions options_;
};

} // namespace ir
