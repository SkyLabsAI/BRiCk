/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "SourceInfo.hpp"

#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/Error.h>

namespace ir {

struct NodeTag;
using NodeId = source::StrongIndex<NodeTag>;
struct ShareClassTag;
using ShareClassId = source::StrongIndex<ShareClassTag>;

enum class ShareClassKind { Type, Name };
struct ShareClassInfo {
    ShareClassKind kind = ShareClassKind::Type;
};

enum class Category {
    AtomicName,
    Name,
    TemplateArgument,
    TemplateParameter,
    Type,
    Expression,
    Statement,
    VariableDeclaration,
    BindingDeclaration,
    Cast,
    GlobalInitializer,
    FunctionBody,
    DefaultStatementBody,
    ConstructorBody,
    Function,
    Method,
    InitializerPath,
    Initializer,
    Constructor,
    Destructor,
    LayoutInfo,
    Member,
    Struct,
    Union,
    ObjectValue,
    GlobalDeclaration,
    Template,
    TemplatePreInstantiation,
    Auxiliary,
};

/// Enum values and all mechanical constructor facts come from the checked-in
/// registry. Shape descriptors and semantic lowering remain readable C++.
enum class Constructor {
#define IR_CONSTRUCTOR(NAME, SPELLING, CATEGORY, ROOTS, STATUS, SHAPE) NAME,
#include "IRConstructors.def"
#undef IR_CONSTRUCTOR
    Count,
};

enum class ScalarKind {
    Symbol,
    String,
    Numeral,
    Natural,
    Boolean,
    ByteString,
    SwitchBranch,
    LocalName
};

struct ScalarTerm {
    ScalarKind kind = ScalarKind::Symbol;
    std::string text;

    static ScalarTerm symbol(std::string value);
    static ScalarTerm string(std::string value);
    static ScalarTerm numeral(std::string value);
    static ScalarTerm natural(std::uint64_t value);
    static ScalarTerm boolean(bool value);
    static ScalarTerm byteString(std::string value);
    static ScalarTerm switchBranchExact(std::string value);
    static ScalarTerm switchBranchRange(std::string low, std::string high);
    static ScalarTerm localIdentifier(std::string value);
    static ScalarTerm anonymousLocal(std::uint64_t value);
};

struct NodeRef {
    NodeId value;
};

struct Value;
struct OptionalValue {
    OptionalValue() = default;
    OptionalValue(const OptionalValue &other);
    OptionalValue &operator=(const OptionalValue &other);
    OptionalValue(OptionalValue &&) noexcept = default;
    OptionalValue &operator=(OptionalValue &&) noexcept = default;

    std::unique_ptr<Value> value;
};
struct SequenceValue {
    std::vector<Value> elements;
};
struct ProductValue {
    /// Present for a transparent non-AST record/constructor application such
    /// as [FunctionType]. Its recursive fields still project directly into
    /// the owning semantic node's location children.
    std::optional<ScalarTerm> constructor;
    std::vector<Value> fields;
};
struct SumValue {
    SumValue() = default;
    SumValue(ScalarTerm constructor, std::unique_ptr<Value> value);
    SumValue(const SumValue &other);
    SumValue &operator=(const SumValue &other);
    SumValue(SumValue &&) noexcept = default;
    SumValue &operator=(SumValue &&) noexcept = default;

    ScalarTerm activeConstructor;
    std::unique_ptr<Value> payload;
};
struct OpaqueValue {
    std::string diagnostic;
};
using ValuePayload =
    std::variant<ScalarTerm, NodeRef, OptionalValue, SequenceValue,
                 ProductValue, SumValue, OpaqueValue>;

struct Value {
    ValuePayload payload;

    static Value scalar(ScalarTerm value);
    static Value node(NodeId value);
    static Value optional(std::optional<Value> value);
    static Value sequence(std::vector<Value> elements);
    static Value product(std::vector<Value> fields);
    static Value constructedProduct(ScalarTerm constructor,
                                    std::vector<Value> fields);
    static Value sum(ScalarTerm constructor, Value payload);
    static Value opaque(std::string diagnostic);
};

struct Node {
    Category category = Category::Auxiliary;
    Constructor constructor = Constructor::ProductFixture;
    std::vector<source::OriginId> origins;
    std::vector<Value> arguments;
    /// Owned semantic-identity metadata only. It never affects children or
    /// provenance and is assigned only while the arena is mutable.
    std::optional<ShareClassId> shareClass;
};

enum class ShapeKind {
    Scalar,
    Node,
    Optional,
    Sequence,
    Product,
    Sum,
    Opaque,
};

struct ValueShape {
    ShapeKind kind = ShapeKind::Scalar;
    std::optional<Category> nodeCategory;
    std::optional<ScalarKind> scalarKind;
    std::vector<ValueShape> children;
    std::optional<std::string> sumConstructor;
    std::optional<std::string> productConstructor;
};

using RootKindMask = std::uint8_t;

struct ConstructorSpec {
    Constructor constructor;
    const char *rocqSpelling;
    Category category;
    RootKindMask allowedRoots;
    bool testOnly;
    std::vector<ValueShape> arguments;
};

/// Single source of mechanical constructor facts. When BRiCk AST constructors
/// evolve, update this registry and the path/grouping tests together; otherwise
/// semantic output and the public location-path ABI can silently diverge.
const ConstructorSpec *findConstructorSpec(Constructor constructor);
const ConstructorSpec &constructorSpec(Constructor constructor);
const std::vector<ConstructorSpec> &constructorRegistry();

class Arena {
public:
    Arena() = default;
    Arena(const Arena &) = delete;
    Arena &operator=(const Arena &) = delete;
    Arena(Arena &&) = delete;
    Arena &operator=(Arena &&) = delete;

    llvm::Expected<NodeId> add(Node node);
    llvm::Error setShareClass(NodeId node, ShareClassId shareClass);
    llvm::Expected<const Node *> get(NodeId id) const;
    llvm::Expected<std::vector<NodeId>> children(NodeId id) const;
    std::size_t size() const { return nodes_.size(); }
    bool finished() const { return finished_; }

private:
    friend class TranslationUnitIR;
    friend class IRValidator;
    void markFinished() { finished_ = true; }

    std::vector<Node> nodes_;
    bool finished_ = false;
};

enum class RootKind { Symbol, Type, TemplateSymbol, TemplateType, Count };

struct TemplateParameterEntry {
    NodeId parameter;
    std::optional<NodeId> defaultArgument;
};

struct RootEvent {
    RootKind kind;
    NodeId semanticName;
    NodeId semanticValue;
    /// Legacy PrePrint intentionally omits ordinary variable root names.
    bool seedName = true;
    /// Parser-generated sibling roots do not introduce extra PrePrint visits.
    bool seedValue = true;
    /// Optional owned diagnostic spelling used only for --comment output.
    std::optional<std::string> diagnosticName;
};

struct NamespaceAliasEvent {
    std::optional<NodeId> from;
    NodeId to;
    std::vector<source::OriginId> origins;
};
struct StaticAssertEvent {
    std::optional<ScalarTerm> message;
    NodeId condition;
    std::vector<source::OriginId> origins;
};
struct TemplateAliasEvent {
    NodeId semanticName;
    NodeId templateValue;
    std::vector<source::OriginId> origins;
    std::optional<std::string> diagnosticName;
};
struct TemplateInstanceEvent {
    NodeId canonicalKey;
    NodeId value;
    std::vector<source::OriginId> origins;
    std::optional<std::string> diagnosticKey;
    std::optional<std::string> diagnosticTarget;
};
using NonRootEvent = std::variant<NamespaceAliasEvent, StaticAssertEvent,
                                  TemplateAliasEvent, TemplateInstanceEvent>;

enum class OrderedEventKind { Root, NonRoot };
struct OrderedEventRef {
    OrderedEventKind kind = OrderedEventKind::Root;
    std::size_t index = 0;
};

struct AbiInfo {
    std::vector<std::pair<std::string, ScalarTerm>> fields;
};

class TranslationUnitIR {
public:
    Arena &buildingArena() { return nodes_; }
    llvm::Error setSources(source::Tables sources);
    llvm::Expected<ShareClassId> addShareClass(ShareClassKind kind);
    llvm::Error addRoot(RootEvent event);
    llvm::Error addNonRoot(NonRootEvent event);
    llvm::Error setAbi(AbiInfo abi);
    llvm::Error finish();

    const Arena &nodes() const { return nodes_; }
    const source::Tables &sources() const { return sources_; }
    const std::vector<ShareClassInfo> &shareClasses() const {
        return shareClasses_;
    }
    const std::vector<RootEvent> &rootEvents() const { return rootEvents_; }
    const std::vector<NonRootEvent> &nonRootEvents() const {
        return nonRootEvents_;
    }
    const std::vector<OrderedEventRef> &orderedEvents() const {
        return orderedEvents_;
    }
    const AbiInfo &abi() const { return abi_; }
    bool finished() const { return finished_; }

private:
    friend class IRValidator;
    Arena nodes_;
    source::Tables sources_;
    std::vector<ShareClassInfo> shareClasses_;
    std::vector<RootEvent> rootEvents_;
    std::vector<NonRootEvent> nonRootEvents_;
    std::vector<OrderedEventRef> orderedEvents_;
    AbiInfo abi_;
    bool finished_ = false;
};

class IRValidator {
public:
    /// Validate caller-selected entry nodes that are not yet TU roots/events.
    /// This keeps experimental builder selections inside the same pure IR
    /// boundary as the final translation-unit validator.
    static llvm::Error validateSelected(const Arena &arena,
                                        llvm::ArrayRef<NodeId> selected,
                                        Category expected,
                                        llvm::StringRef label);
    static llvm::Error validate(const TranslationUnitIR &unit,
                                bool requireFinished = true);
};

} // namespace ir
