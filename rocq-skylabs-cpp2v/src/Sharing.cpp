/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "Sharing.hpp"

#include <functional>
#include <set>
#include <system_error>
#include <utility>

namespace ir {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

bool scalarEqual(const ScalarTerm &lhs, const ScalarTerm &rhs) {
    return lhs.kind == rhs.kind && lhs.text == rhs.text;
}

bool shareEligible(const Node &node, ShareClassKind kind) {
    if (kind == ShareClassKind::Name)
        return node.category == Category::Name;
    switch (node.constructor) {
    case Constructor::TypeNamed:
    case Constructor::TypeEnum:
    case Constructor::TypePointer:
    case Constructor::TypeLvalueReference:
    case Constructor::TypeRvalueReference:
    case Constructor::TypeArray:
    case Constructor::TypeIncompleteArray:
    case Constructor::TypeFunction:
        return true;
    default:
        return false;
    }
}

bool valueEqual(const TranslationUnitIR &unit, const Value &lhs,
                const Value &rhs,
                std::set<std::pair<std::uint32_t, std::uint32_t>> &active);

bool nodeEqual(const TranslationUnitIR &unit, NodeId lhs, NodeId rhs,
               std::set<std::pair<std::uint32_t, std::uint32_t>> &active) {
    if (lhs == rhs)
        return true;
    const auto key = std::make_pair(lhs.value(), rhs.value());
    if (!active.insert(key).second)
        return true;
    auto left = unit.nodes().get(lhs);
    auto right = unit.nodes().get(rhs);
    if (!left || !right)
        return false;
    bool equal = (*left)->category == (*right)->category &&
                 (*left)->constructor == (*right)->constructor &&
                 (*left)->arguments.size() == (*right)->arguments.size();
    for (std::size_t i = 0; equal && i < (*left)->arguments.size(); ++i)
        equal = valueEqual(unit, (*left)->arguments[i], (*right)->arguments[i],
                           active);
    active.erase(key);
    return equal;
}

bool valueEqual(const TranslationUnitIR &unit, const Value &lhs,
                const Value &rhs,
                std::set<std::pair<std::uint32_t, std::uint32_t>> &active) {
    if (lhs.payload.index() != rhs.payload.index())
        return false;
    if (const auto *left = std::get_if<ScalarTerm>(&lhs.payload))
        return scalarEqual(*left, std::get<ScalarTerm>(rhs.payload));
    if (const auto *left = std::get_if<NodeRef>(&lhs.payload))
        return nodeEqual(unit, left->value,
                         std::get<NodeRef>(rhs.payload).value, active);
    if (const auto *left = std::get_if<OptionalValue>(&lhs.payload)) {
        const auto &right = std::get<OptionalValue>(rhs.payload);
        if (static_cast<bool>(left->value) != static_cast<bool>(right.value))
            return false;
        return !left->value ||
               valueEqual(unit, *left->value, *right.value, active);
    }
    if (const auto *left = std::get_if<SequenceValue>(&lhs.payload)) {
        const auto &right = std::get<SequenceValue>(rhs.payload);
        if (left->elements.size() != right.elements.size())
            return false;
        for (std::size_t i = 0; i < left->elements.size(); ++i)
            if (!valueEqual(unit, left->elements[i], right.elements[i], active))
                return false;
        return true;
    }
    if (const auto *left = std::get_if<ProductValue>(&lhs.payload)) {
        const auto &right = std::get<ProductValue>(rhs.payload);
        if (left->constructor.has_value() != right.constructor.has_value() ||
            left->fields.size() != right.fields.size())
            return false;
        if (left->constructor &&
            !scalarEqual(*left->constructor, *right.constructor))
            return false;
        for (std::size_t i = 0; i < left->fields.size(); ++i)
            if (!valueEqual(unit, left->fields[i], right.fields[i], active))
                return false;
        return true;
    }
    if (const auto *left = std::get_if<SumValue>(&lhs.payload)) {
        const auto &right = std::get<SumValue>(rhs.payload);
        return scalarEqual(left->activeConstructor, right.activeConstructor) &&
               static_cast<bool>(left->payload) ==
                   static_cast<bool>(right.payload) &&
               (!left->payload ||
                valueEqual(unit, *left->payload, *right.payload, active));
    }
    const auto &left = std::get<OpaqueValue>(lhs.payload);
    return left.diagnostic == std::get<OpaqueValue>(rhs.payload).diagnostic;
}

llvm::Error validateClassSemantics(const TranslationUnitIR &unit) {
    std::vector<std::optional<NodeId>> representatives(
        unit.shareClasses().size());
    for (std::size_t index = 0; index < unit.nodes().size(); ++index) {
        const NodeId id(static_cast<NodeId::value_type>(index));
        auto node = unit.nodes().get(id);
        if (!node)
            return node.takeError();
        if (!(*node)->shareClass)
            continue;
        const std::size_t share = (*node)->shareClass->value();
        if (!representatives[share]) {
            representatives[share] = id;
            continue;
        }
        std::set<std::pair<std::uint32_t, std::uint32_t>> active;
        if (!nodeEqual(unit, *representatives[share], id, active)) {
            auto representative = unit.nodes().get(*representatives[share]);
            if (!representative)
                return representative.takeError();
            return error(
                "sharing class " + std::to_string(share) +
                " contains unequal semantic occurrences at nodes " +
                std::to_string(representatives[share]->value()) + " (" +
                constructorSpec((*representative)->constructor).rocqSpelling +
                ") and " + std::to_string(id.value()) + " (" +
                constructorSpec((*node)->constructor).rocqSpelling + ")");
        }
    }
    return llvm::Error::success();
}

} // namespace

const SharingDefinition *SharingPlan::lookup(ShareClassId shareClass) const {
    for (const SharingDefinition &definition : definitions_)
        if (definition.shareClass == shareClass)
            return &definition;
    return nullptr;
}

SharingPlan SharingPlan::fromUnvalidatedDefinitions(
    std::vector<SharingDefinition> definitions) {
    SharingPlan result;
    result.definitions_ = std::move(definitions);
    return result;
}

std::vector<SharingSeed>
IRSharing::productionSeeds(const TranslationUnitIR &unit) {
    std::vector<SharingSeed> seeds;
    seeds.reserve(unit.rootEvents().size());
    for (const RootEvent &root : unit.rootEvents()) {
        if (!root.seedValue)
            continue;
        const bool templateOnly = root.kind == RootKind::TemplateSymbol ||
                                  root.kind == RootKind::TemplateType;
        seeds.push_back({templateOnly ? SharingSeedKind::TemplateOnly
                                      : SharingSeedKind::Ordinary,
                         root.semanticValue,
                         root.seedName
                             ? std::optional<NodeId>(root.semanticName)
                             : std::nullopt});
    }
    return seeds;
}

llvm::Expected<bool> IRSharing::semanticallyEqual(const TranslationUnitIR &unit,
                                                  NodeId lhs, NodeId rhs) {
    auto left = unit.nodes().get(lhs);
    if (!left)
        return left.takeError();
    auto right = unit.nodes().get(rhs);
    if (!right)
        return right.takeError();
    std::set<std::pair<std::uint32_t, std::uint32_t>> active;
    return nodeEqual(unit, lhs, rhs, active);
}

llvm::Expected<SharingPlan>
IRSharing::analyze(const TranslationUnitIR &unit,
                   llvm::ArrayRef<SharingSeed> seeds) {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);

    if (auto failure = validateClassSemantics(unit))
        return std::move(failure);

    SharingPlan plan;
    std::vector<bool> visited(unit.nodes().size(), false);
    std::vector<bool> defined(unit.shareClasses().size(), false);
    unsigned nextType = 1;
    unsigned nextName = 1;
    std::function<llvm::Error(NodeId)> visit = [&](NodeId id) -> llvm::Error {
        auto node = unit.nodes().get(id);
        if (!node)
            return node.takeError();
        if (visited[id.value()])
            return llvm::Error::success();
        visited[id.value()] = true;
        auto children = unit.nodes().children(id);
        if (!children)
            return children.takeError();
        for (NodeId child : *children)
            if (auto failure = visit(child))
                return failure;
        if ((*node)->shareClass) {
            const ShareClassId share = *(*node)->shareClass;
            const ShareClassKind kind = unit.shareClasses()[share.value()].kind;
            if (!defined[share.value()] && shareEligible(**node, kind)) {
                const std::string local =
                    std::string(kind == ShareClassKind::Type ? "t" : "n") +
                    std::to_string(kind == ShareClassKind::Type ? nextType++
                                                                : nextName++);
                plan.definitions_.push_back({share, kind, id, local});
                defined[share.value()] = true;
            }
        }
        return llvm::Error::success();
    };

    for (const SharingSeed &seed : seeds) {
        auto value = unit.nodes().get(seed.semanticValue);
        if (!value)
            return error("sharing seed has an invalid value node ID");
        if (seed.semanticName) {
            auto name = unit.nodes().get(*seed.semanticName);
            if (!name)
                return error("sharing seed has an invalid name node ID");
            if ((*name)->category != Category::Name)
                return error("sharing seed name has the wrong category");
        }
        if (seed.kind == SharingSeedKind::TemplateOnly)
            continue;
        if (auto failure = visit(seed.semanticValue))
            return std::move(failure);
        if (seed.semanticName)
            if (auto failure = visit(*seed.semanticName))
                return std::move(failure);
    }
    if (auto failure = validate(unit, plan))
        return std::move(failure);
    return plan;
}

llvm::Error IRSharing::validate(const TranslationUnitIR &unit,
                                const SharingPlan &plan) {
    if (auto failure = IRValidator::validate(unit))
        return failure;
    // Plans are intentionally not digest-bound to a unit. Recheck semantic
    // class coherence on every use so a stale/cross-unit plan cannot replace
    // unequal occurrences merely because IDs happen to line up.
    if (auto failure = validateClassSemantics(unit))
        return failure;
    std::vector<int> positions(unit.shareClasses().size(), -1);
    unsigned nextType = 1;
    unsigned nextName = 1;
    for (std::size_t index = 0; index < plan.definitions().size(); ++index) {
        const SharingDefinition &definition = plan.definitions()[index];
        if (!definition.shareClass.valid() ||
            definition.shareClass.value() >= unit.shareClasses().size())
            return error("sharing plan has an invalid class ID");
        if (positions[definition.shareClass.value()] >= 0)
            return error("sharing plan defines one class more than once");
        if (unit.shareClasses()[definition.shareClass.value()].kind !=
            definition.kind)
            return error("sharing plan class kind is inconsistent");
        auto representative = unit.nodes().get(definition.representative);
        if (!representative)
            return representative.takeError();
        if (!(*representative)->shareClass ||
            *(*representative)->shareClass != definition.shareClass)
            return error("sharing plan representative has the wrong class");
        if (!shareEligible(**representative, definition.kind))
            return error("sharing plan representative is not eligible");
        const std::string expected =
            std::string(definition.kind == ShareClassKind::Type ? "t" : "n") +
            std::to_string(definition.kind == ShareClassKind::Type
                               ? nextType++
                               : nextName++);
        if (definition.localName != expected)
            return error("sharing plan local names are not stable");
        positions[definition.shareClass.value()] = static_cast<int>(index);
    }

    for (std::size_t index = 0; index < plan.definitions().size(); ++index) {
        std::vector<NodeId> pending;
        auto children =
            unit.nodes().children(plan.definitions()[index].representative);
        if (!children)
            return children.takeError();
        pending.assign(children->begin(), children->end());
        std::vector<bool> seen(unit.nodes().size(), false);
        while (!pending.empty()) {
            NodeId id = pending.back();
            pending.pop_back();
            if (seen[id.value()])
                continue;
            seen[id.value()] = true;
            auto node = unit.nodes().get(id);
            if (!node)
                return node.takeError();
            if ((*node)->shareClass) {
                const int position = positions[(*node)->shareClass->value()];
                if (position >= static_cast<int>(index))
                    return error(
                        "sharing plan violates child-before-parent order");
            }
            auto nested = unit.nodes().children(id);
            if (!nested)
                return nested.takeError();
            pending.insert(pending.end(), nested->begin(), nested->end());
        }
    }
    return llvm::Error::success();
}

} // namespace ir
