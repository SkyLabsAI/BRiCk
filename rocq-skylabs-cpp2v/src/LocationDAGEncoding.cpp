/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "LocationDAGEncoding.hpp"

#include <limits>
#include <string>
#include <system_error>
#include <unordered_map>
#include <utility>

#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/Error.h>

namespace ir::location::encoding {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

void combineHash(std::size_t &seed, std::size_t value) {
    seed ^= value + static_cast<std::size_t>(0x9e3779b97f4a7c15ULL) +
            (seed << 6U) + (seed >> 2U);
}

struct ShapeHash {
    std::size_t operator()(const EncodedShape &shape) const {
        std::size_t seed = shape.children.size();
        for (ShapeId child : shape.children)
            combineHash(seed, child.value());
        return seed;
    }
};

struct LocationNodeHash {
    std::size_t operator()(const EncodedLocationNode &node) const {
        // [shape] is deliberately absent: it is derived from [children] and is
        // not part of exact location-node identity.
        std::size_t seed = node.origins.size();
        for (source::OriginId origin : node.origins)
            combineHash(seed, origin.value());
        combineHash(seed, node.children.size());
        for (LocationNodeId child : node.children)
            combineHash(seed, child.value());
        return seed;
    }
};

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
            return error("too many exact location-DAG rows");
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

struct TraversalFrame {
    NodeId node;
    std::vector<NodeId> children;
    std::size_t nextChild = 0;
};

bool selectedRoot(const RootEvent &root, bool includeTemplates) {
    const bool isTemplate = root.kind == RootKind::TemplateSymbol ||
                            root.kind == RootKind::TemplateType;
    return includeTemplates || !isTemplate;
}

} // namespace

bool operator==(const EncodedShape &lhs, const EncodedShape &rhs) {
    return lhs.children == rhs.children;
}

bool operator==(const EncodedLocationNode &lhs,
                const EncodedLocationNode &rhs) {
    return lhs.origins == rhs.origins && lhs.children == rhs.children;
}

bool operator==(const EncodedRoot &lhs, const EncodedRoot &rhs) {
    return lhs.node == rhs.node && lhs.shape == rhs.shape;
}

llvm::Expected<EncodedLocations> encode(const TranslationUnitIR &unit,
                                        bool includeTemplates,
                                        EncodeOptions options) {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);
    if (options.includedEvents &&
        options.includedEvents->size() != unit.rootEvents().size())
        return error("location-DAG inclusion table has the wrong size");
    if (options.projection && (options.projection->oldToNewOrigin.size() !=
                                   unit.sources().origins.size() ||
                               options.projection->directlyRelevant.size() !=
                                   unit.sources().origins.size()))
        return error("location-DAG source projection has the wrong size");

    Interner<ShapeId, EncodedShape, ShapeHash> shapes(
        options.forceHashCollisions);
    Interner<LocationNodeId, EncodedLocationNode, LocationNodeHash> nodes(
        options.forceHashCollisions);
    std::vector<std::optional<EncodedRoot>> memo(unit.nodes().size());
    std::vector<bool> memoHasLocation(unit.nodes().size(), false);
    std::vector<bool> memoAtRoot(unit.nodes().size(), false);
    std::vector<unsigned char> color(unit.nodes().size(), 0);

    EncodedLocations result;
    result.eventRoots.resize(unit.rootEvents().size());
    result.eventHasLocation.assign(unit.rootEvents().size(), false);
    result.eventAtRoot.assign(unit.rootEvents().size(), false);
    result.sourceOriginCount = options.projection
                                   ? options.projection->tables.origins.size()
                                   : unit.sources().origins.size();

    auto childrenOf = [&](NodeId id) -> llvm::Expected<std::vector<NodeId>> {
        auto children = unit.nodes().children(id);
        if (!children)
            return children.takeError();
        return std::vector<NodeId>(children->begin(), children->end());
    };

    for (const OrderedEventRef &ordered : unit.orderedEvents()) {
        if (ordered.kind != OrderedEventKind::Root)
            continue;
        if (ordered.index >= unit.rootEvents().size())
            return error("location-DAG encoder received an invalid root event");
        const RootEvent &event = unit.rootEvents()[ordered.index];
        if (!selectedRoot(event, includeTemplates))
            continue;
        if (options.includedEvents && !(*options.includedEvents)[ordered.index])
            continue;
        ++result.stats.selectedRootEvents;
        const NodeId root = event.semanticValue;
        if (!root.valid() || root.value() >= memo.size())
            return error("location-DAG encoder received an invalid root node");

        if (!memo[root.value()]) {
            auto rootChildren = childrenOf(root);
            if (!rootChildren)
                return rootChildren.takeError();
            color[root.value()] = 1;
            std::vector<TraversalFrame> stack;
            stack.push_back(TraversalFrame{root, std::move(*rootChildren), 0});

            while (!stack.empty()) {
                TraversalFrame &frame = stack.back();
                if (frame.nextChild < frame.children.size()) {
                    const NodeId child = frame.children[frame.nextChild++];
                    if (!child.valid() || child.value() >= memo.size())
                        return error(
                            "location-DAG encoder reached an invalid child ID");
                    if (memo[child.value()])
                        continue;
                    if (color[child.value()] == 1)
                        return error(
                            "location-DAG encoder reached a semantic cycle");
                    auto childChildren = childrenOf(child);
                    if (!childChildren)
                        return childChildren.takeError();
                    color[child.value()] = 1;
                    stack.push_back(
                        TraversalFrame{child, std::move(*childChildren), 0});
                    continue;
                }

                std::vector<ShapeId> childShapes;
                std::vector<LocationNodeId> childNodes;
                childShapes.reserve(frame.children.size());
                childNodes.reserve(frame.children.size());
                for (NodeId child : frame.children) {
                    const auto &encoded = memo[child.value()];
                    if (!encoded)
                        return error(
                            "location-DAG postorder memoization is incomplete");
                    childShapes.push_back(encoded->shape);
                    childNodes.push_back(encoded->node);
                }
                auto shape =
                    shapes.intern(EncodedShape{std::move(childShapes)});
                if (!shape)
                    return shape.takeError();
                auto semantic = unit.nodes().get(frame.node);
                if (!semantic)
                    return semantic.takeError();
                std::vector<source::OriginId> origins;
                if (options.projection) {
                    for (source::OriginId old : (*semantic)->origins) {
                        if (options.projection->directlyRelevant[old.value()]) {
                            const auto remapped =
                                options.projection->oldToNewOrigin[old.value()];
                            if (!remapped)
                                return error(
                                    "location-DAG source projection omits a "
                                    "directly relevant origin");
                            origins.push_back(*remapped);
                        }
                    }
                } else {
                    origins = (*semantic)->origins;
                }
                const bool atRoot = !origins.empty();
                const bool hasLocation =
                    atRoot ||
                    std::any_of(frame.children.begin(), frame.children.end(),
                                [&](NodeId child) {
                                    return memoHasLocation[child.value()];
                                });
                auto locationNode = nodes.intern(EncodedLocationNode{
                    *shape, std::move(origins), std::move(childNodes)});
                if (!locationNode)
                    return locationNode.takeError();
                memo[frame.node.value()] = EncodedRoot{*locationNode, *shape};
                memoHasLocation[frame.node.value()] = hasLocation;
                memoAtRoot[frame.node.value()] = atRoot;
                color[frame.node.value()] = 2;
                ++result.stats.visitedSemanticNodes;
                stack.pop_back();
            }
        }
        result.eventRoots[ordered.index] = memo[root.value()];
        result.eventHasLocation[ordered.index] = memoHasLocation[root.value()];
        result.eventAtRoot[ordered.index] = memoAtRoot[root.value()];
    }

    result.shapes = std::move(shapes).takeValues();
    result.nodes = std::move(nodes).takeValues();
    result.stats.shapeRows = result.shapes.size();
    result.stats.locationNodeRows = result.nodes.size();
    if (auto failure = validate(result))
        return std::move(failure);
    return result;
}

llvm::Error validate(const EncodedLocations &locations) {
    for (std::size_t index = 0; index < locations.shapes.size(); ++index) {
        const EncodedShape &shape = locations.shapes[index];
        for (ShapeId child : shape.children)
            if (!child.valid() || child.value() >= index)
                return error(
                    "location shape DAG has a non-backward child edge");
    }

    for (std::size_t index = 0; index < locations.nodes.size(); ++index) {
        const EncodedLocationNode &node = locations.nodes[index];
        if (!node.shape.valid() ||
            node.shape.value() >= locations.shapes.size())
            return error("location node has an invalid shape ID");
        const EncodedShape &shape = locations.shapes[node.shape.value()];
        if (node.children.size() != shape.children.size())
            return error("location node and shape arities differ");
        for (std::size_t childIndex = 0; childIndex < node.children.size();
             ++childIndex) {
            const LocationNodeId child = node.children[childIndex];
            if (!child.valid() || child.value() >= index)
                return error("location node DAG has a non-backward child edge");
            if (locations.nodes[child.value()].shape !=
                shape.children[childIndex])
                return error("location node child has the wrong shape");
        }
        for (source::OriginId origin : node.origins)
            if (!origin.valid() ||
                origin.value() >= locations.sourceOriginCount)
                return error("location node has an invalid origin ID");
    }

    for (const std::optional<EncodedRoot> &root : locations.eventRoots) {
        if (!root)
            continue;
        if (!root->node.valid() || root->node.value() >= locations.nodes.size())
            return error("location root has an invalid node ID");
        if (!root->shape.valid() ||
            root->shape.value() >= locations.shapes.size())
            return error("location root has an invalid shape ID");
        if (locations.nodes[root->node.value()].shape != root->shape)
            return error("location root node and shape disagree");
    }
    return llvm::Error::success();
}

} // namespace ir::location::encoding
