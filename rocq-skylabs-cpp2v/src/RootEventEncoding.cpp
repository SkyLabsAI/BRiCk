/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "RootEventEncoding.hpp"

#include "Sharing.hpp"

#include <functional>
#include <optional>
#include <string>
#include <system_error>
#include <unordered_map>
#include <utility>
#include <vector>

#include <llvm/Support/Error.h>

namespace ir::root_event::encoding {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

void combineHash(std::size_t &seed, std::size_t value) {
    seed ^= value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
            (seed << 6U) + (seed >> 2U);
}

std::size_t hashString(const std::string &value) {
    return std::hash<std::string>{}(value);
}

/// The hash mirrors [IRSharing::semanticallyEqual] exactly: it deliberately
/// excludes source origins, node identities, and sharing annotations. Finished
/// IR is acyclic, as required by IRValidator, so one memoized hash per node is
/// sufficient and keeps repeated semantic names inexpensive.
class SemanticHasher {
public:
    explicit SemanticHasher(const TranslationUnitIR &unit)
        : unit_(unit), memo_(unit.nodes().size()) {}

    llvm::Expected<std::size_t> node(NodeId id) {
        if (!id.valid() || id.value() >= memo_.size())
            return error(
                "root-event semantic hash received an invalid node ID");
        if (memo_[id.value()])
            return *memo_[id.value()];
        auto current = unit_.nodes().get(id);
        if (!current)
            return current.takeError();
        std::size_t seed = 0;
        combineHash(seed, static_cast<std::size_t>((*current)->category));
        combineHash(seed, static_cast<std::size_t>((*current)->constructor));
        combineHash(seed, (*current)->arguments.size());
        for (const Value &argument : (*current)->arguments) {
            auto valueHash = value(argument);
            if (!valueHash)
                return valueHash.takeError();
            combineHash(seed, *valueHash);
        }
        memo_[id.value()] = seed;
        return seed;
    }

private:
    llvm::Expected<std::size_t> scalar(const ScalarTerm &value) {
        std::size_t seed = 0;
        combineHash(seed, static_cast<std::size_t>(value.kind));
        combineHash(seed, hashString(value.text));
        return seed;
    }

    llvm::Expected<std::size_t> value(const Value &term) {
        std::size_t seed = term.payload.index();
        if (const auto *scalarValue = std::get_if<ScalarTerm>(&term.payload)) {
            auto nested = scalar(*scalarValue);
            if (!nested)
                return nested.takeError();
            combineHash(seed, *nested);
        } else if (const auto *reference =
                       std::get_if<NodeRef>(&term.payload)) {
            auto nested = node(reference->value);
            if (!nested)
                return nested.takeError();
            combineHash(seed, *nested);
        } else if (const auto *optional =
                       std::get_if<OptionalValue>(&term.payload)) {
            combineHash(seed, optional->value ? 1 : 0);
            if (optional->value) {
                auto nested = value(*optional->value);
                if (!nested)
                    return nested.takeError();
                combineHash(seed, *nested);
            }
        } else if (const auto *sequence =
                       std::get_if<SequenceValue>(&term.payload)) {
            combineHash(seed, sequence->elements.size());
            for (const Value &element : sequence->elements) {
                auto nested = value(element);
                if (!nested)
                    return nested.takeError();
                combineHash(seed, *nested);
            }
        } else if (const auto *product =
                       std::get_if<ProductValue>(&term.payload)) {
            combineHash(seed, product->constructor ? 1 : 0);
            if (product->constructor) {
                auto constructor = scalar(*product->constructor);
                if (!constructor)
                    return constructor.takeError();
                combineHash(seed, *constructor);
            }
            combineHash(seed, product->fields.size());
            for (const Value &field : product->fields) {
                auto nested = value(field);
                if (!nested)
                    return nested.takeError();
                combineHash(seed, *nested);
            }
        } else if (const auto *sum = std::get_if<SumValue>(&term.payload)) {
            auto constructor = scalar(sum->activeConstructor);
            if (!constructor)
                return constructor.takeError();
            combineHash(seed, *constructor);
            combineHash(seed, sum->payload ? 1 : 0);
            if (sum->payload) {
                auto nested = value(*sum->payload);
                if (!nested)
                    return nested.takeError();
                combineHash(seed, *nested);
            }
        } else {
            const auto &opaque = std::get<OpaqueValue>(term.payload);
            combineHash(seed, hashString(opaque.diagnostic));
        }
        return seed;
    }

    const TranslationUnitIR &unit_;
    std::vector<std::optional<std::size_t>> memo_;
};

bool selectedRoot(const RootEvent &root, bool includeTemplates) {
    const bool isTemplate = root.kind == RootKind::TemplateSymbol ||
                            root.kind == RootKind::TemplateType;
    return includeTemplates || !isTemplate;
}

bool conservativeTypedef(const TranslationUnitIR &unit, const RootEvent &root) {
    if (root.kind != RootKind::Type)
        return false;
    auto value = unit.nodes().get(root.semanticValue);
    return value && (*value)->constructor == Constructor::GlobalTypedef;
}

struct Group {
    RootKind kind;
    NodeId representativeName;
    std::vector<std::size_t> events;
};

} // namespace

llvm::Expected<EncodedRootEvents> encode(const TranslationUnitIR &unit,
                                         bool includeTemplates,
                                         EncodeOptions options) {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);

    EncodedRootEvents result;
    result.eventClasses.assign(unit.rootEvents().size(), EventClass::Excluded);
    SemanticHasher hasher(unit);
    std::unordered_map<std::size_t, std::vector<std::size_t>> buckets;
    std::vector<Group> groups;
    groups.reserve(unit.rootEvents().size());

    for (const OrderedEventRef &ordered : unit.orderedEvents()) {
        if (ordered.kind != OrderedEventKind::Root)
            continue;
        if (ordered.index >= unit.rootEvents().size())
            return error("root-event encoder received an invalid root index");
        const RootEvent &root = unit.rootEvents()[ordered.index];
        if (!selectedRoot(root, includeTemplates))
            continue;
        ++result.stats.selectedEvents;

        auto nameHash = hasher.node(root.semanticName);
        if (!nameHash)
            return nameHash.takeError();
        std::size_t keyHash = options.forceHashCollisions ? 0 : *nameHash;
        if (!options.forceHashCollisions)
            combineHash(keyHash, static_cast<std::size_t>(root.kind));

        std::optional<std::size_t> group;
        auto found = buckets.find(keyHash);
        if (found != buckets.end()) {
            for (std::size_t candidate : found->second) {
                const Group &existing = groups[candidate];
                if (existing.kind != root.kind)
                    continue;
                auto equal = IRSharing::semanticallyEqual(
                    unit, existing.representativeName, root.semanticName);
                if (!equal)
                    return equal.takeError();
                if (*equal) {
                    group = candidate;
                    break;
                }
            }
        }
        if (!group) {
            group = groups.size();
            groups.push_back({root.kind, root.semanticName, {}});
            buckets[keyHash].push_back(*group);
        }
        groups[*group].events.push_back(ordered.index);
    }

    for (const Group &group : groups) {
        if (group.events.size() > 1) {
            ++result.stats.duplicateGroups;
            result.stats.duplicateEvents += group.events.size();
            result.stats.residualEvents += group.events.size();
            for (std::size_t event : group.events)
                result.eventClasses[event] = EventClass::Residual;
            continue;
        }

        const std::size_t event = group.events.front();
        const RootEvent &root = unit.rootEvents()[event];
        if (conservativeTypedef(unit, root)) {
            ++result.stats.conservativeTypedefResiduals;
            ++result.stats.residualEvents;
            result.eventClasses[event] = EventClass::Residual;
        } else {
            ++result.stats.singletonEvents;
            result.eventClasses[event] = EventClass::Singleton;
        }
    }
    return result;
}

} // namespace ir::root_event::encoding
