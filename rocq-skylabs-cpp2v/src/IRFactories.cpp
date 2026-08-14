/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRFactories.hpp"

#include <initializer_list>
#include <system_error>

namespace ir {
namespace factory {
namespace {

llvm::Error error(const char *message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s", message);
}

llvm::Error requireCategory(const Arena &arena, NodeId id, Category wanted) {
    auto node = arena.get(id);
    if (!node)
        return node.takeError();
    if ((*node)->category != wanted)
        return error("IR factory argument has the wrong category");
    return llvm::Error::success();
}

llvm::Error requireOperation(const ScalarTerm &operation,
                             std::initializer_list<llvm::StringRef> supported,
                             const char *message) {
    if (operation.kind != ScalarKind::Symbol)
        return error(message);
    for (llvm::StringRef candidate : supported)
        if (operation.text == candidate)
            return llvm::Error::success();
    return error(message);
}

llvm::Error requireUnaryOperation(const ScalarTerm &operation) {
    return requireOperation(operation, {"Uplus", "Uminus", "Ubnot", "Unot"},
                            "unary-expression operation is not a built-in "
                            "unary operation");
}

llvm::Error requireBinaryOperation(const ScalarTerm &operation) {
    return requireOperation(
        operation,
        {"Badd", "Band", "Bcmp", "Bdiv", "Beq", "Bge", "Bgt", "Ble", "Blt",
         "Bmul", "Bneq", "Bor", "Bmod", "Bshl", "Bshr", "Bsub", "Bxor", "Bdotp",
         "Bdotip"},
        "binary-expression operation is not a built-in binary operation");
}

llvm::Error requireCompoundAssignmentOperation(const ScalarTerm &operation) {
    return requireOperation(
        operation,
        {"Badd", "Band", "Bdiv", "Bmul", "Bor", "Bmod", "Bshl", "Bshr", "Bsub",
         "Bxor"},
        "compound-assignment operation is not a built-in compound "
        "assignment operation");
}

llvm::Error requireDispatch(const ScalarTerm &dispatch) {
    return requireOperation(
        dispatch, {"Static_dispatch", "Virtual", "Direct"},
        "call dispatch is not Static_dispatch, Virtual, or Direct");
}

llvm::Error requireValueCategory(const ScalarTerm &category) {
    return requireOperation(category, {"Lvalue", "Prvalue", "Xvalue"},
                            "temporary value category is invalid");
}

llvm::Error requireOverloadableOperator(const ScalarTerm &operation) {
    return requireOperation(
        operation,
        {"OOTilde",
         "OOExclaim",
         "OOPlusPlus",
         "OOMinusMinus",
         "OOStar",
         "OOPlus",
         "OOMinus",
         "OOSlash",
         "OOPercent",
         "OOCaret",
         "OOAmp",
         "OOPipe",
         "OOEqual",
         "OOLessLess",
         "OOGreaterGreater",
         "OOPlusEqual",
         "OOMinusEqual",
         "OOStarEqual",
         "OOSlashEqual",
         "OOPercentEqual",
         "OOCaretEqual",
         "OOAmpEqual",
         "OOPipeEqual",
         "OOLessLessEqual",
         "OOGreaterGreaterEqual",
         "OOEqualEqual",
         "OOExclaimEqual",
         "OOLess",
         "OOGreater",
         "OOLessEqual",
         "OOGreaterEqual",
         "OOSpaceship",
         "OOComma",
         "OOArrowStar",
         "OOArrow",
         "OOSubscript",
         "OOAmpAmp",
         "OOPipePipe",
         "OOCall",
         "OOCoawait"},
        "operator call operation is not a supported overloadable operator");
}

llvm::Error checkValue(const Arena &arena, const Value &value,
                       const ValueShape &shape) {
    switch (shape.kind) {
    case ShapeKind::Scalar: {
        const auto *scalar = std::get_if<ScalarTerm>(&value.payload);
        if (!scalar || !shape.scalarKind || scalar->kind != *shape.scalarKind)
            return error("IR factory scalar has the wrong kind");
        return llvm::Error::success();
    }
    case ShapeKind::Node: {
        const auto *node = std::get_if<NodeRef>(&value.payload);
        if (!node)
            return error("IR factory expected a node argument");
        auto actual = arena.get(node->value);
        if (!actual)
            return actual.takeError();
        if (shape.nodeCategory && (*actual)->category != *shape.nodeCategory)
            return error("IR factory node has the wrong category");
        return llvm::Error::success();
    }
    case ShapeKind::Optional: {
        const auto *optional = std::get_if<OptionalValue>(&value.payload);
        if (!optional || shape.children.size() != 1)
            return error("IR factory optional has the wrong shape");
        return optional->value
                   ? checkValue(arena, *optional->value, shape.children[0])
                   : llvm::Error::success();
    }
    case ShapeKind::Sequence: {
        const auto *sequence = std::get_if<SequenceValue>(&value.payload);
        if (!sequence || shape.children.size() != 1)
            return error("IR factory sequence has the wrong shape");
        for (const Value &element : sequence->elements)
            if (auto failure = checkValue(arena, element, shape.children[0]))
                return failure;
        return llvm::Error::success();
    }
    case ShapeKind::Product: {
        const auto *product = std::get_if<ProductValue>(&value.payload);
        if (!product || product->fields.size() != shape.children.size())
            return error("IR factory product has the wrong shape");
        if (shape.productConstructor) {
            if (!product->constructor ||
                product->constructor->kind != ScalarKind::Symbol ||
                product->constructor->text != *shape.productConstructor)
                return error("IR factory product has the wrong constructor");
        } else if (product->constructor) {
            return error("IR factory tuple unexpectedly has a constructor");
        }
        for (std::size_t i = 0; i < product->fields.size(); ++i)
            if (auto failure =
                    checkValue(arena, product->fields[i], shape.children[i]))
                return failure;
        return llvm::Error::success();
    }
    case ShapeKind::Sum: {
        const auto *sum = std::get_if<SumValue>(&value.payload);
        if (!sum || !sum->payload || shape.children.size() != 1 ||
            (shape.sumConstructor &&
             (sum->activeConstructor.kind != ScalarKind::Symbol ||
              sum->activeConstructor.text != *shape.sumConstructor)))
            return error("IR factory sum has the wrong shape");
        return checkValue(arena, *sum->payload, shape.children[0]);
    }
    case ShapeKind::Opaque:
        return std::holds_alternative<OpaqueValue>(value.payload)
                   ? llvm::Error::success()
                   : error("IR factory opaque value has the wrong shape");
    }
    return error("IR factory encountered an unknown shape");
}

llvm::Expected<NodeId> addChecked(Arena &arena, Constructor constructor,
                                  OriginList origins,
                                  std::vector<Value> arguments) {
    const auto *spec = findConstructorSpec(constructor);
    if (!spec)
        return error("IR factory used an unregistered constructor");
    if (arguments.size() != spec->arguments.size())
        return error("IR factory assembled the wrong constructor arity");
    for (std::size_t i = 0; i < arguments.size(); ++i)
        if (auto failure = checkValue(arena, arguments[i], spec->arguments[i]))
            return std::move(failure);
    OriginList stable;
    source::appendOriginsStable(stable, origins);
    return arena.add(Node{spec->category, constructor, std::move(stable),
                          std::move(arguments)});
}

llvm::Error requireNodes(const Arena &arena, const std::vector<NodeId> &values,
                         Category wanted) {
    for (NodeId value : values)
        if (auto failure = requireCategory(arena, value, wanted))
            return failure;
    return llvm::Error::success();
}

std::vector<Value> nodes(std::vector<NodeId> ids) {
    std::vector<Value> result;
    result.reserve(ids.size());
    for (NodeId id : ids)
        result.push_back(Value::node(id));
    return result;
}

llvm::Expected<Value>
packDeclarationParameters(const Arena &arena,
                          std::vector<DeclarationParameter> parameters) {
    std::vector<Value> result;
    result.reserve(parameters.size());
    for (DeclarationParameter &parameter : parameters) {
        if (parameter.name.kind != ScalarKind::LocalName)
            return error("declaration parameter name is not a local name");
        if (auto failure =
                requireCategory(arena, parameter.type, Category::Type))
            return std::move(failure);
        result.push_back(
            Value::product({Value::scalar(std::move(parameter.name)),
                            Value::node(parameter.type)}));
    }
    return Value::sequence(std::move(result));
}

llvm::Expected<NodeId> oneNode(Arena &arena, Constructor constructor,
                               OriginList origins, NodeId value,
                               Category wanted) {
    if (auto failure = requireCategory(arena, value, wanted))
        return std::move(failure);
    return addChecked(arena, constructor, std::move(origins),
                      {Value::node(value)});
}

} // namespace

llvm::Expected<TemplateParameters>
packTemplateParameters(const Arena &arena,
                       const std::vector<TemplateParameterEntry> &entries) {
    TemplateParameters result;
    result.reserve(entries.size());
    for (const TemplateParameterEntry &entry : entries) {
        if (auto failure = requireCategory(arena, entry.parameter,
                                           Category::TemplateParameter))
            return std::move(failure);
        if (entry.defaultArgument)
            if (auto failure = requireCategory(arena, *entry.defaultArgument,
                                               Category::TemplateArgument))
                return std::move(failure);
        result.push_back(Value::product(
            {Value::node(entry.parameter),
             Value::optional(
                 entry.defaultArgument
                     ? std::optional<Value>(Value::node(*entry.defaultArgument))
                     : std::nullopt)}));
    }
    return result;
}

llvm::Expected<NodeId> makeAtomicIdentifier(Arena &arena, OriginList origins,
                                            std::string name) {
    return addChecked(arena, Constructor::AtomicIdentifier, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeAtomicAnonymousIndex(Arena &arena,
                                                OriginList origins,
                                                std::uint64_t index) {
    return addChecked(
        arena, Constructor::AtomicAnonymousIndex, std::move(origins),
        {Value::scalar(ScalarTerm::numeral(std::to_string(index)))});
}
llvm::Expected<NodeId> makeAtomicAnonymousNamespace(Arena &arena,
                                                    OriginList origins) {
    return addChecked(arena, Constructor::AtomicAnonymousNamespace,
                      std::move(origins), {});
}
llvm::Expected<NodeId>
makeAtomicFirstDeclaration(Arena &arena, OriginList origins, std::string name) {
    return addChecked(arena, Constructor::AtomicFirstDeclaration,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeAtomicFirstChild(Arena &arena, OriginList origins,
                                            std::string name) {
    return addChecked(arena, Constructor::AtomicFirstChild, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeAtomicUnsupported(Arena &arena, OriginList origins,
                                             std::string message) {
    return addChecked(arena, Constructor::AtomicUnsupported, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}
llvm::Expected<NodeId> makeAtomicFunction(Arena &arena, OriginList origins,
                                          ScalarTerm qualifiers,
                                          std::string identifier,
                                          std::vector<NodeId> parameters) {
    if (qualifiers.kind != ScalarKind::Symbol)
        return error("function qualifiers are not a symbol");
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::AtomicFunction, std::move(origins),
                      {Value::scalar(std::move(qualifiers)),
                       Value::scalar(ScalarTerm::string(std::move(identifier))),
                       Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId> makeAtomicConstructor(Arena &arena, OriginList origins,
                                             std::vector<NodeId> parameters) {
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::AtomicConstructor, std::move(origins),
                      {Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId> makeAtomicDestructor(Arena &arena, OriginList origins) {
    return addChecked(arena, Constructor::AtomicDestructor, std::move(origins),
                      {});
}
llvm::Expected<NodeId> makeAtomicOperator(Arena &arena, OriginList origins,
                                          ScalarTerm qualifiers,
                                          ScalarTerm operation,
                                          std::vector<NodeId> parameters) {
    if (qualifiers.kind != ScalarKind::Symbol ||
        operation.kind != ScalarKind::Symbol)
        return error("operator name leaves are not symbols");
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::AtomicOperator, std::move(origins),
                      {Value::scalar(std::move(qualifiers)),
                       Value::scalar(std::move(operation)),
                       Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId>
makeAtomicAllocationOperator(Arena &arena, OriginList origins,
                             ScalarTerm qualifiers, bool isDelete, bool isArray,
                             std::vector<NodeId> parameters) {
    if (qualifiers.kind != ScalarKind::Symbol)
        return error("allocation operator qualifiers are not a symbol");
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    const Constructor constructor = isDelete ? Constructor::AtomicDeleteOperator
                                             : Constructor::AtomicNewOperator;
    const char *operation = isDelete ? "OODelete" : "OONew";
    return addChecked(arena, constructor, std::move(origins),
                      {Value::scalar(std::move(qualifiers)),
                       Value::constructedProduct(
                           ScalarTerm::symbol(operation),
                           {Value::scalar(ScalarTerm::boolean(isArray))}),
                       Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId> makeAtomicConversion(Arena &arena, OriginList origins,
                                            ScalarTerm qualifiers,
                                            NodeId type) {
    if (qualifiers.kind != ScalarKind::Symbol)
        return error("conversion qualifiers are not a symbol");
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::AtomicConversion, std::move(origins),
        {Value::scalar(std::move(qualifiers)), Value::node(type)});
}
llvm::Expected<NodeId>
makeAtomicLiteralOperator(Arena &arena, OriginList origins,
                          std::string identifier,
                          std::vector<NodeId> parameters) {
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::AtomicLiteralOperator,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(identifier))),
                       Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId> makeGlobalName(Arena &arena, OriginList origins,
                                      NodeId atomic) {
    return oneNode(arena, Constructor::NameFromAtomic, std::move(origins),
                   atomic, Category::AtomicName);
}
llvm::Expected<NodeId> makeScopedName(Arena &arena, OriginList origins,
                                      NodeId scope, NodeId atomic) {
    if (auto failure = requireCategory(arena, scope, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, atomic, Category::AtomicName))
        return std::move(failure);
    return addChecked(arena, Constructor::NameScoped, std::move(origins),
                      {Value::node(scope), Value::node(atomic)});
}
llvm::Expected<NodeId> makeInstantiatedName(Arena &arena, OriginList origins,
                                            NodeId base,
                                            std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, base, Category::Name))
        return std::move(failure);
    if (auto failure =
            requireNodes(arena, arguments, Category::TemplateArgument))
        return std::move(failure);
    return addChecked(
        arena, Constructor::NameInstantiation, std::move(origins),
        {Value::node(base), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeDependentName(Arena &arena, OriginList origins,
                                         NodeId type) {
    return oneNode(arena, Constructor::NameDependent, std::move(origins), type,
                   Category::Type);
}
llvm::Expected<NodeId> makeUnsupportedName(Arena &arena, OriginList origins,
                                           std::string message) {
    return addChecked(arena, Constructor::NameUnsupported, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}
llvm::Expected<NodeId> makeNamedType(Arena &arena, OriginList origins,
                                     NodeId name) {
    return oneNode(arena, Constructor::TypeNamed, std::move(origins), name,
                   Category::Name);
}
llvm::Expected<NodeId> makeEnumType(Arena &arena, OriginList origins,
                                    NodeId name) {
    return oneNode(arena, Constructor::TypeEnum, std::move(origins), name,
                   Category::Name);
}
llvm::Expected<NodeId> makeTypeParameter(Arena &arena, OriginList origins,
                                         std::string name) {
    return addChecked(arena, Constructor::TypeParameter, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeResultGlobalType(Arena &arena, OriginList origins,
                                            NodeId name) {
    return oneNode(arena, Constructor::TypeResultGlobal, std::move(origins),
                   name, Category::Name);
}
llvm::Expected<NodeId> makeResultCallType(Arena &arena, OriginList origins,
                                          NodeId name,
                                          std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    for (NodeId argument : arguments)
        if (auto failure = requireCategory(arena, argument, Category::Type))
            return std::move(failure);
    std::vector<Value> values;
    values.reserve(arguments.size());
    for (NodeId argument : arguments)
        values.push_back(Value::node(argument));
    return addChecked(arena, Constructor::TypeResultCall, std::move(origins),
                      {Value::node(name), Value::sequence(std::move(values))});
}
llvm::Expected<NodeId> makeResultUnarySyntaxType(Arena &arena,
                                                 OriginList origins,
                                                 ScalarTerm operation,
                                                 NodeId type) {
    if (auto failure = requireOperation(
            operation,
            {"Rarrow", "Rstar", "Rpreinc", "Rpostinc", "Rpredec", "Rpostdec"},
            "result-unary operation is not supported"))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeResultUnarySyntax,
                      std::move(origins),
                      {Value::scalar(std::move(operation)), Value::node(type)});
}
llvm::Expected<NodeId> makeResultMemberType(Arena &arena, OriginList origins,
                                            NodeId type, NodeId name) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeResultMember, std::move(origins),
                      {Value::node(type), Value::node(name)});
}
llvm::Expected<NodeId> makeNumberType(Arena &arena, OriginList origins,
                                      ScalarTerm rank, ScalarTerm sign) {
    if (rank.kind != ScalarKind::Symbol || sign.kind != ScalarKind::Symbol)
        return error("number type leaves are not symbols");
    return addChecked(
        arena, Constructor::TypeNumber, std::move(origins),
        {Value::scalar(std::move(rank)), Value::scalar(std::move(sign))});
}
llvm::Expected<NodeId> makeLeafType(Arena &arena, Constructor constructor,
                                    OriginList origins,
                                    std::optional<ScalarTerm> leaf) {
    const auto *spec = findConstructorSpec(constructor);
    if (!spec || spec->category != Category::Type)
        return error("leaf type factory received a non-type constructor");
    std::vector<Value> arguments;
    if (leaf)
        arguments.push_back(Value::scalar(std::move(*leaf)));
    return addChecked(arena, constructor, std::move(origins),
                      std::move(arguments));
}
llvm::Expected<NodeId> makeUnaryType(Arena &arena, Constructor constructor,
                                     OriginList origins, NodeId type) {
    return oneNode(arena, constructor, std::move(origins), type,
                   Category::Type);
}
llvm::Expected<NodeId> makeArrayType(Arena &arena, OriginList origins,
                                     NodeId element, std::uint64_t size) {
    if (auto failure = requireCategory(arena, element, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeArray, std::move(origins),
                      {Value::node(element), Value::scalar(ScalarTerm::numeral(
                                                 std::to_string(size)))});
}
llvm::Expected<NodeId> makeVariableArrayType(Arena &arena, OriginList origins,
                                             NodeId element, NodeId bound) {
    if (auto failure = requireCategory(arena, element, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, bound, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeVariableArray, std::move(origins),
                      {Value::node(element), Value::node(bound)});
}
llvm::Expected<NodeId> makeQualifiedType(Arena &arena, OriginList origins,
                                         ScalarTerm qualifiers, NodeId type) {
    if (qualifiers.kind != ScalarKind::Symbol)
        return error("type qualifiers are not a symbol");
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::TypeQualified, std::move(origins),
        {Value::scalar(std::move(qualifiers)), Value::node(type)});
}
llvm::Expected<NodeId> makeFunctionType(Arena &arena, OriginList origins,
                                        ScalarTerm callingConvention,
                                        ScalarTerm arity, NodeId result,
                                        std::vector<NodeId> parameters) {
    if (callingConvention.kind != ScalarKind::Symbol ||
        arity.kind != ScalarKind::Symbol)
        return error("function type leaves are not symbols");
    if (auto failure = requireCategory(arena, result, Category::Type))
        return std::move(failure);
    if (auto failure = requireNodes(arena, parameters, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeFunction, std::move(origins),
                      {Value::constructedProduct(
                          ScalarTerm::symbol("@FunctionType"),
                          {Value::scalar(ScalarTerm::symbol("_")),
                           Value::scalar(std::move(callingConvention)),
                           Value::scalar(std::move(arity)), Value::node(result),
                           Value::sequence(nodes(std::move(parameters)))})});
}
llvm::Expected<NodeId> makeMemberPointerType(Arena &arena, OriginList origins,
                                             NodeId classType,
                                             NodeId pointeeType) {
    if (auto failure = requireCategory(arena, classType, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, pointeeType, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::TypeMemberPointer, std::move(origins),
                      {Value::node(classType), Value::node(pointeeType)});
}
llvm::Expected<NodeId> makeExpressionType(Arena &arena, Constructor constructor,
                                          OriginList origins,
                                          NodeId expression) {
    return oneNode(arena, constructor, std::move(origins), expression,
                   Category::Expression);
}
llvm::Expected<NodeId> makeArchitectureType(Arena &arena, OriginList origins,
                                            std::string name) {
    return addChecked(arena, Constructor::TypeArchitecture, std::move(origins),
                      {Value::optional(std::nullopt),
                       Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeUnsupportedType(Arena &arena, OriginList origins,
                                           std::string message) {
    return addChecked(arena, Constructor::TypeUnsupported, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}
llvm::Expected<NodeId> makeIntegerExpression(Arena &arena, OriginList origins,
                                             std::string value, NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionInteger, std::move(origins),
                      {Value::scalar(ScalarTerm::numeral(std::move(value))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeBooleanExpression(Arena &arena, OriginList origins,
                                             bool value) {
    return addChecked(arena, Constructor::ExpressionBoolean, std::move(origins),
                      {Value::scalar(ScalarTerm::boolean(value))});
}
llvm::Expected<NodeId>
makeStringExpression(Arena &arena, OriginList origins,
                     std::vector<std::uint64_t> characters, NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    std::vector<Value> values;
    values.reserve(characters.size());
    for (std::uint64_t character : characters)
        values.push_back(Value::scalar(ScalarTerm::natural(character)));
    return addChecked(arena, Constructor::ExpressionString, std::move(origins),
                      {Value::constructedProduct(
                           ScalarTerm::symbol("literal_string.of_list_N"),
                           {Value::sequence(std::move(values))}),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeStringExpression(Arena &arena, OriginList origins,
                                            std::string bytes, NodeId type) {
    std::vector<std::uint64_t> characters;
    characters.reserve(bytes.size());
    for (unsigned char byte : bytes)
        characters.push_back(byte);
    return makeStringExpression(arena, std::move(origins),
                                std::move(characters), type);
}
llvm::Expected<NodeId> makeCharacterExpression(Arena &arena, OriginList origins,
                                               std::uint64_t character,
                                               NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionCharacter, std::move(origins),
        {Value::scalar(ScalarTerm::natural(character)), Value::node(type)});
}
llvm::Expected<NodeId> makeFloatExpression(Arena &arena, OriginList origins,
                                           ScalarTerm floatType,
                                           std::string bits) {
    if (floatType.kind != ScalarKind::Symbol)
        return error("float-expression type is not a symbol");
    ScalarTerm repeated = floatType;
    return addChecked(
        arena, Constructor::ExpressionFloat, std::move(origins),
        {Value::scalar(std::move(floatType)),
         Value::constructedProduct(
             ScalarTerm::symbol("float_value.of_bits"),
             {Value::scalar(std::move(repeated)),
              Value::scalar(ScalarTerm::numeral(std::move(bits)))})});
}
llvm::Expected<NodeId> makeUnsupportedExpression(Arena &arena,
                                                 OriginList origins,
                                                 std::string diagnostic,
                                                 NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionUnsupported,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(diagnostic))),
                       Value::node(type)});
}
llvm::Expected<NodeId>
makeUnresolvedStringExpression(Arena &arena, OriginList origins, NodeId type) {
    return oneNode(arena, Constructor::ExpressionUnresolvedString,
                   std::move(origins), type, Category::Type);
}
llvm::Expected<NodeId> makeNullExpression(Arena &arena, OriginList origins) {
    return addChecked(arena, Constructor::ExpressionNull, std::move(origins),
                      {});
}
llvm::Expected<NodeId> makeParameterExpression(Arena &arena, OriginList origins,
                                               std::string name) {
    return addChecked(arena, Constructor::ExpressionParameter,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeGlobalExpression(Arena &arena, OriginList origins,
                                            NodeId name, NodeId type,
                                            bool unresolved) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (unresolved)
        return addChecked(arena, Constructor::ExpressionUnresolvedGlobal,
                          std::move(origins), {Value::node(name)});
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionGlobal, std::move(origins),
                      {Value::node(name), Value::node(type)});
}
llvm::Expected<NodeId> makeGlobalMemberExpression(Arena &arena,
                                                  OriginList origins,
                                                  NodeId name, NodeId type) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionGlobalMember,
                      std::move(origins),
                      {Value::node(name), Value::node(type)});
}
llvm::Expected<NodeId> makeEnumConstantExpression(Arena &arena,
                                                  OriginList origins,
                                                  NodeId enumName,
                                                  std::string constant) {
    if (auto failure = requireCategory(arena, enumName, Category::Name))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionEnumConstant,
                      std::move(origins),
                      {Value::node(enumName),
                       Value::scalar(ScalarTerm::string(std::move(constant)))});
}
llvm::Expected<NodeId> makeAddressOfExpression(Arena &arena, OriginList origins,
                                               NodeId expression) {
    return oneNode(arena, Constructor::ExpressionAddressOf, std::move(origins),
                   expression, Category::Expression);
}
llvm::Expected<NodeId> makeLocalExpression(Arena &arena, OriginList origins,
                                           std::string name, NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionLocalNamed,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeAnonymousLocalExpression(Arena &arena,
                                                    OriginList origins,
                                                    std::uint64_t index,
                                                    NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionLocalAnonymous, std::move(origins),
        {Value::constructedProduct(
             ScalarTerm::symbol("localname.anon"),
             {Value::scalar(ScalarTerm::numeral(std::to_string(index)))}),
         Value::node(type)});
}
llvm::Expected<NodeId> makeUnaryExpression(Arena &arena, OriginList origins,
                                           ScalarTerm operation, NodeId value,
                                           std::optional<NodeId> type) {
    if (auto failure = requireUnaryOperation(operation))
        return std::move(failure);
    if (auto failure = requireCategory(arena, value, Category::Expression))
        return std::move(failure);
    if (type) {
        if (auto failure = requireCategory(arena, *type, Category::Type))
            return std::move(failure);
        return addChecked(arena, Constructor::ExpressionUnary,
                          std::move(origins),
                          {Value::scalar(std::move(operation)),
                           Value::node(value), Value::node(*type)});
    }
    return addChecked(
        arena, Constructor::ExpressionUnresolvedUnary, std::move(origins),
        {Value::constructedProduct(ScalarTerm::symbol("Runop"),
                                   {Value::scalar(std::move(operation))}),
         Value::node(value)});
}
llvm::Expected<NodeId>
makeUnsupportedUnaryExpression(Arena &arena, OriginList origins,
                               std::string operation, NodeId value,
                               std::optional<NodeId> type) {
    if (auto failure = requireCategory(arena, value, Category::Expression))
        return std::move(failure);
    Value unsupported = Value::constructedProduct(
        ScalarTerm::symbol("Uunsupported"),
        {Value::scalar(ScalarTerm::string(std::move(operation)))});
    if (type) {
        if (auto failure = requireCategory(arena, *type, Category::Type))
            return std::move(failure);
        return addChecked(
            arena, Constructor::ExpressionUnsupportedUnary, std::move(origins),
            {std::move(unsupported), Value::node(value), Value::node(*type)});
    }
    return addChecked(arena, Constructor::ExpressionUnresolvedUnsupportedUnary,
                      std::move(origins),
                      {Value::constructedProduct(ScalarTerm::symbol("Runop"),
                                                 {std::move(unsupported)}),
                       Value::node(value)});
}
llvm::Expected<NodeId> makeUnresolvedBinaryExpression(Arena &arena,
                                                      OriginList origins,
                                                      ScalarTerm operation,
                                                      NodeId lhs, NodeId rhs) {
    if (auto failure = requireBinaryOperation(operation))
        return std::move(failure);
    for (NodeId value : {lhs, rhs})
        if (auto failure = requireCategory(arena, value, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionUnresolvedBinary, std::move(origins),
        {Value::constructedProduct(ScalarTerm::symbol("Rbinop"),
                                   {Value::scalar(std::move(operation))}),
         Value::node(lhs), Value::node(rhs)});
}
llvm::Expected<NodeId> makeUnresolvedUnarySyntaxExpression(Arena &arena,
                                                           OriginList origins,
                                                           ScalarTerm operation,
                                                           NodeId expression) {
    if (auto failure = requireOperation(
            operation,
            {"Rstar", "Rarrow", "Rpreinc", "Rpostinc", "Rpredec", "Rpostdec"},
            "unresolved unary syntax operation is not supported"))
        return std::move(failure);
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionUnresolvedUnarySyntax, std::move(origins),
        {Value::scalar(std::move(operation)), Value::node(expression)});
}
llvm::Expected<NodeId>
makeUnresolvedBinarySyntaxExpression(Arena &arena, OriginList origins,
                                     ScalarTerm operation, NodeId lhs,
                                     NodeId rhs) {
    if (auto failure = requireOperation(
            operation, {"Rassign", "Rsubscript", "Rcomma", "Rand", "Ror"},
            "unresolved binary syntax operation is not supported"))
        return std::move(failure);
    for (NodeId value : {lhs, rhs})
        if (auto failure = requireCategory(arena, value, Category::Expression))
            return std::move(failure);
    return addChecked(arena, Constructor::ExpressionUnresolvedBinarySyntax,
                      std::move(origins),
                      {Value::scalar(std::move(operation)), Value::node(lhs),
                       Value::node(rhs)});
}
llvm::Expected<NodeId>
makeUnresolvedCompoundAssignmentExpression(Arena &arena, OriginList origins,
                                           ScalarTerm operation, NodeId lhs,
                                           NodeId rhs) {
    if (auto failure = requireCompoundAssignmentOperation(operation))
        return std::move(failure);
    for (NodeId value : {lhs, rhs})
        if (auto failure = requireCategory(arena, value, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionUnresolvedCompoundAssignment,
        std::move(origins),
        {Value::constructedProduct(ScalarTerm::symbol("Rassign_op"),
                                   {Value::scalar(std::move(operation))}),
         Value::node(lhs), Value::node(rhs)});
}
llvm::Expected<NodeId> makeNullaryCast(Arena &arena, Constructor constructor,
                                       OriginList origins) {
    const auto *spec = findConstructorSpec(constructor);
    if (!spec || spec->category != Category::Cast || !spec->arguments.empty())
        return error("nullary-cast factory received the wrong constructor");
    return addChecked(arena, constructor, std::move(origins), {});
}
llvm::Expected<NodeId> makeTypeCast(Arena &arena, Constructor constructor,
                                    OriginList origins, NodeId type) {
    const auto *spec = findConstructorSpec(constructor);
    if (!spec || spec->category != Category::Cast ||
        spec->arguments.size() != 1)
        return error("type-cast factory received the wrong constructor");
    return oneNode(arena, constructor, std::move(origins), type,
                   Category::Type);
}
llvm::Expected<NodeId> makePathCast(Arena &arena, Constructor constructor,
                                    OriginList origins,
                                    std::vector<NodeId> path, NodeId end) {
    if (constructor != Constructor::CastDerivedToBase &&
        constructor != Constructor::CastBaseToDerived)
        return error("path-cast factory received the wrong constructor");
    if (auto failure = requireNodes(arena, path, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, end, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::sequence(nodes(std::move(path))), Value::node(end)});
}
llvm::Expected<NodeId> makeUnsupportedCast(Arena &arena, OriginList origins,
                                           std::string diagnostic,
                                           NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::CastUnsupported, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(diagnostic))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeBuiltinToFunctionCast(Arena &arena,
                                                 OriginList origins,
                                                 NodeId pointerType) {
    return makeTypeCast(arena, Constructor::CastBuiltinToFunction,
                        std::move(origins), pointerType);
}
llvm::Expected<NodeId> makeLvalueToRvalueCast(Arena &arena,
                                              OriginList origins) {
    return makeNullaryCast(arena, Constructor::CastLvalueToRvalue,
                           std::move(origins));
}
llvm::Expected<NodeId> makeIntegralCast(Arena &arena, OriginList origins,
                                        NodeId type) {
    return makeTypeCast(arena, Constructor::CastIntegral, std::move(origins),
                        type);
}
llvm::Expected<NodeId> makeCastExpression(Arena &arena, OriginList origins,
                                          NodeId cast, NodeId expression) {
    if (auto failure = requireCategory(arena, cast, Category::Cast))
        return std::move(failure);
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionCast, std::move(origins),
                      {Value::node(cast), Value::node(expression)});
}
llvm::Expected<NodeId>
makeExplicitCastExpression(Arena &arena, OriginList origins, ScalarTerm style,
                           NodeId writtenType, NodeId castExpression) {
    if (style.kind != ScalarKind::Symbol)
        return error("explicit-cast style is not a symbol");
    bool supportedStyle = false;
    for (llvm::StringRef supported :
         {"cast_style.functional", "cast_style.c", "cast_style.static",
          "cast_style.dynamic", "cast_style.reinterpret", "cast_style.const"})
        supportedStyle |= style.text == supported;
    if (!supportedStyle)
        return error("explicit-cast style is not a BRiCk cast_style");
    if (auto failure = requireCategory(arena, writtenType, Category::Type))
        return std::move(failure);
    if (auto failure =
            requireCategory(arena, castExpression, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionExplicitCast,
                      std::move(origins),
                      {Value::scalar(std::move(style)),
                       Value::node(writtenType), Value::node(castExpression)});
}
llvm::Expected<NodeId> makeBinaryExpression(Arena &arena, OriginList origins,
                                            ScalarTerm operation, NodeId lhs,
                                            NodeId rhs, NodeId resultType) {
    if (auto failure = requireBinaryOperation(operation))
        return std::move(failure);
    for (NodeId operand : {lhs, rhs})
        if (auto failure =
                requireCategory(arena, operand, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, resultType, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionBinary, std::move(origins),
                      {Value::scalar(std::move(operation)), Value::node(lhs),
                       Value::node(rhs), Value::node(resultType)});
}
llvm::Expected<NodeId> makeDerefExpression(Arena &arena, OriginList origins,
                                           NodeId expression, NodeId type) {
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionDeref, std::move(origins),
                      {Value::node(expression), Value::node(type)});
}
llvm::Expected<NodeId> makeAssignmentExpression(Arena &arena,
                                                OriginList origins, NodeId lhs,
                                                NodeId rhs, NodeId type) {
    if (auto failure = requireCategory(arena, lhs, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, rhs, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    // The final core Eassign omits an operation leaf.
    return addChecked(arena, Constructor::ExpressionAssign, std::move(origins),
                      {Value::node(lhs), Value::node(rhs), Value::node(type)});
}
llvm::Expected<NodeId> makeCompoundAssignmentExpression(Arena &arena,
                                                        OriginList origins,
                                                        ScalarTerm operation,
                                                        NodeId lhs, NodeId rhs,
                                                        NodeId type) {
    if (auto failure = requireCompoundAssignmentOperation(operation))
        return std::move(failure);
    if (auto failure = requireCategory(arena, lhs, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, rhs, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionAssignOp,
                      std::move(origins),
                      {Value::scalar(std::move(operation)), Value::node(lhs),
                       Value::node(rhs), Value::node(type)});
}
llvm::Expected<NodeId> makeIncrementExpression(Arena &arena, OriginList origins,
                                               Constructor constructor,
                                               NodeId expression, NodeId type) {
    switch (constructor) {
    case Constructor::ExpressionPreIncrement:
    case Constructor::ExpressionPostIncrement:
    case Constructor::ExpressionPreDecrement:
    case Constructor::ExpressionPostDecrement:
        break;
    default:
        return error("increment factory received the wrong constructor");
    }
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, constructor, std::move(origins),
                      {Value::node(expression), Value::node(type)});
}
llvm::Expected<NodeId> makeSequencingExpression(Arena &arena,
                                                OriginList origins,
                                                Constructor constructor,
                                                NodeId lhs, NodeId rhs) {
    switch (constructor) {
    case Constructor::ExpressionSequenceAnd:
    case Constructor::ExpressionSequenceOr:
    case Constructor::ExpressionComma:
        break;
    default:
        return error("sequencing factory received the wrong constructor");
    }
    if (auto failure = requireCategory(arena, lhs, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, rhs, Category::Expression))
        return std::move(failure);
    return addChecked(arena, constructor, std::move(origins),
                      {Value::node(lhs), Value::node(rhs)});
}
llvm::Expected<NodeId> makeSubscriptExpression(Arena &arena, OriginList origins,
                                               NodeId base, NodeId index,
                                               NodeId type) {
    if (auto failure = requireCategory(arena, base, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, index, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionSubscript, std::move(origins),
        {Value::node(base), Value::node(index), Value::node(type)});
}
llvm::Expected<NodeId> makeTraitExpression(Arena &arena, OriginList origins,
                                           Constructor constructor,
                                           std::optional<NodeId> typeArgument,
                                           NodeId resultType) {
    if (constructor != Constructor::ExpressionSizeofType &&
        constructor != Constructor::ExpressionSizeofExpression &&
        constructor != Constructor::ExpressionAlignofType &&
        constructor != Constructor::ExpressionAlignofExpression)
        return error("trait factory received the wrong constructor");
    if (auto failure = requireCategory(arena, resultType, Category::Type))
        return std::move(failure);
    const bool wantsType = constructor == Constructor::ExpressionSizeofType ||
                           constructor == Constructor::ExpressionAlignofType;
    if (!typeArgument)
        return error("trait factory requires an argument");
    if (auto failure =
            requireCategory(arena, *typeArgument,
                            wantsType ? Category::Type : Category::Expression))
        return std::move(failure);
    return addChecked(arena, constructor, std::move(origins),
                      {Value::sum(ScalarTerm::symbol(wantsType ? "inl" : "inr"),
                                  Value::node(*typeArgument)),
                       Value::node(resultType)});
}
llvm::Expected<NodeId> makeUnresolvedSizeofPackExpression(Arena &arena,
                                                          OriginList origins,
                                                          std::string pack,
                                                          NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionUnresolvedSizeofPack,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(pack))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeCallExpression(Arena &arena, OriginList origins,
                                          NodeId callee,
                                          std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, callee, Category::Expression))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionCall, std::move(origins),
        {Value::node(callee), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId>
makeUnresolvedCallExpression(Arena &arena, OriginList origins, NodeId callee,
                             std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, callee, Category::Name))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionUnresolvedCall, std::move(origins),
        {Value::node(callee), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeMemberExpression(Arena &arena, OriginList origins,
                                            bool arrow, NodeId object,
                                            NodeId field, bool isMutable,
                                            NodeId type) {
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, field, Category::AtomicName))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionMember, std::move(origins),
                      {Value::scalar(ScalarTerm::boolean(arrow)),
                       Value::node(object), Value::node(field),
                       Value::scalar(ScalarTerm::boolean(isMutable)),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeMemberIgnoreExpression(Arena &arena,
                                                  OriginList origins,
                                                  bool arrow, NodeId object,
                                                  NodeId result) {
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, result, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionMemberIgnore,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::boolean(arrow)),
                       Value::node(object), Value::node(result)});
}
llvm::Expected<NodeId> makeUnresolvedMemberExpression(Arena &arena,
                                                      OriginList origins,
                                                      NodeId object,
                                                      NodeId name) {
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionUnresolvedMember,
                      std::move(origins),
                      {Value::node(object), Value::node(name)});
}
llvm::Expected<NodeId>
makeDirectMemberCallExpression(Arena &arena, OriginList origins, bool arrow,
                               NodeId name, ScalarTerm dispatch, NodeId type,
                               NodeId object, std::vector<NodeId> arguments) {
    if (auto failure = requireDispatch(dispatch))
        return std::move(failure);
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionMemberCallDirect, std::move(origins),
        {Value::scalar(ScalarTerm::boolean(arrow)),
         Value::sum(ScalarTerm::symbol("inl"),
                    Value::product({Value::node(name),
                                    Value::scalar(std::move(dispatch)),
                                    Value::node(type)})),
         Value::node(object), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId>
makePointerMemberCallExpression(Arena &arena, OriginList origins, bool arrow,
                                NodeId member, NodeId object,
                                std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, member, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionMemberCallPointer, std::move(origins),
        {Value::scalar(ScalarTerm::boolean(arrow)),
         Value::sum(ScalarTerm::symbol("inr"), Value::node(member)),
         Value::node(object), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId>
makeFunctionOperatorCallExpression(Arena &arena, OriginList origins,
                                   ScalarTerm operation, NodeId name,
                                   NodeId type, std::vector<NodeId> arguments) {
    if (auto failure = requireOverloadableOperator(operation))
        return std::move(failure);
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionOperatorCallFunction, std::move(origins),
        {Value::scalar(std::move(operation)),
         Value::constructedProduct(ScalarTerm::symbol("operator_impl.Func"),
                                   {Value::node(name), Value::node(type)}),
         Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeMethodOperatorCallExpression(
    Arena &arena, OriginList origins, ScalarTerm operation, NodeId name,
    ScalarTerm dispatch, NodeId type, std::vector<NodeId> arguments) {
    if (auto failure = requireOverloadableOperator(operation))
        return std::move(failure);
    if (auto failure = requireDispatch(dispatch))
        return std::move(failure);
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionOperatorCallMethod, std::move(origins),
        {Value::scalar(std::move(operation)),
         Value::constructedProduct(ScalarTerm::symbol("operator_impl.MFunc"),
                                   {Value::node(name),
                                    Value::scalar(std::move(dispatch)),
                                    Value::node(type)}),
         Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeThisExpression(Arena &arena, OriginList origins,
                                          NodeId type) {
    return oneNode(arena, Constructor::ExpressionThis, std::move(origins), type,
                   Category::Type);
}
llvm::Expected<NodeId> makeImplicitExpression(Arena &arena, OriginList origins,
                                              NodeId expression) {
    return oneNode(arena, Constructor::ExpressionImplicit, std::move(origins),
                   expression, Category::Expression);
}
llvm::Expected<NodeId>
makeConstructorExpression(Arena &arena, OriginList origins, NodeId name,
                          std::vector<NodeId> arguments, NodeId type) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionConstructor, std::move(origins),
        {Value::node(name), Value::sequence(nodes(std::move(arguments))),
         Value::node(type)});
}
llvm::Expected<NodeId>
makeInheritedConstructorExpression(Arena &arena, OriginList origins,
                                   NodeId name, std::size_t argumentCount,
                                   NodeId type) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    std::vector<Value> arguments;
    arguments.reserve(argumentCount);
    for (std::size_t index = 0; index < argumentCount; ++index)
        arguments.push_back(Value::constructedProduct(
            ScalarTerm::symbol("localname.anon"),
            {Value::scalar(ScalarTerm::numeral(std::to_string(index)))}));
    return addChecked(arena, Constructor::ExpressionInheritedConstructor,
                      std::move(origins),
                      {Value::node(name), Value::sequence(std::move(arguments)),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeUnresolvedInitializerListExpression(
    Arena &arena, OriginList origins, Constructor constructor,
    std::optional<NodeId> type, std::vector<NodeId> expressions) {
    if (constructor != Constructor::ExpressionUnresolvedParenList &&
        constructor != Constructor::ExpressionUnresolvedInitList)
        return error("unresolved initializer-list factory received the wrong "
                     "constructor");
    if (type)
        if (auto failure = requireCategory(arena, *type, Category::Type))
            return std::move(failure);
    if (auto failure = requireNodes(arena, expressions, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::optional(type ? std::optional<Value>(Value::node(*type))
                              : std::nullopt),
         Value::sequence(nodes(std::move(expressions)))});
}
llvm::Expected<NodeId> makeInitListExpression(Arena &arena, OriginList origins,
                                              std::vector<NodeId> initializers,
                                              std::optional<NodeId> filler,
                                              NodeId type) {
    if (auto failure = requireNodes(arena, initializers, Category::Expression))
        return std::move(failure);
    if (filler)
        if (auto failure =
                requireCategory(arena, *filler, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionInitList, std::move(origins),
        {Value::sequence(nodes(std::move(initializers))),
         Value::optional(filler ? std::optional<Value>(Value::node(*filler))
                                : std::nullopt),
         Value::node(type)});
}
llvm::Expected<NodeId>
makeUnionInitListExpression(Arena &arena, OriginList origins, NodeId field,
                            std::optional<NodeId> initializer, NodeId type) {
    if (auto failure = requireCategory(arena, field, Category::AtomicName))
        return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionInitListUnion, std::move(origins),
        {Value::node(field),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt),
         Value::node(type)});
}
llvm::Expected<NodeId> makeAndCleanExpression(Arena &arena, OriginList origins,
                                              NodeId expression) {
    return oneNode(arena, Constructor::ExpressionAndClean, std::move(origins),
                   expression, Category::Expression);
}
llvm::Expected<NodeId>
makeMaterializeTemporaryExpression(Arena &arena, OriginList origins,
                                   NodeId expression,
                                   ScalarTerm valueCategory) {
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    if (auto failure = requireValueCategory(valueCategory))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionMaterializeTemporary, std::move(origins),
        {Value::node(expression), Value::scalar(std::move(valueCategory))});
}
llvm::Expected<NodeId>
makeImplicitInitExpression(Arena &arena, OriginList origins, NodeId type) {
    return oneNode(arena, Constructor::ExpressionImplicitInit,
                   std::move(origins), type, Category::Type);
}
llvm::Expected<NodeId> makeArrayLoopInitExpression(
    Arena &arena, OriginList origins, std::uint64_t opaqueName, NodeId source,
    std::uint64_t level, std::string length, NodeId initializer, NodeId type) {
    if (auto failure = requireCategory(arena, source, Category::Expression))
        return std::move(failure);
    if (auto failure =
            requireCategory(arena, initializer, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionArrayLoopInit, std::move(origins),
        {Value::scalar(ScalarTerm::numeral(std::to_string(opaqueName))),
         Value::node(source),
         Value::scalar(ScalarTerm::numeral(std::to_string(level))),
         Value::scalar(ScalarTerm::numeral(std::move(length))),
         Value::node(initializer), Value::node(type)});
}
llvm::Expected<NodeId> makeArrayLoopIndexExpression(Arena &arena,
                                                    OriginList origins,
                                                    std::uint64_t level,
                                                    NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionArrayLoopIndex, std::move(origins),
        {Value::scalar(ScalarTerm::numeral(std::to_string(level))),
         Value::node(type)});
}
llvm::Expected<NodeId> makeOpaqueReferenceExpression(Arena &arena,
                                                     OriginList origins,
                                                     std::uint64_t name,
                                                     NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionOpaqueReference,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::numeral(std::to_string(name))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeNewExpression(Arena &arena, OriginList origins,
                                         NodeId name, NodeId functionType,
                                         std::vector<NodeId> placementArguments,
                                         bool nonAllocating, bool passAlignment,
                                         NodeId allocatedType,
                                         std::optional<NodeId> arraySize,
                                         std::optional<NodeId> initializer) {
    if (nonAllocating && passAlignment)
        return error("non-allocating new cannot pass alignment");
    if (nonAllocating && placementArguments.size() != 1)
        return error("non-allocating new requires one placement argument");
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, functionType, Category::Type))
        return std::move(failure);
    if (auto failure =
            requireNodes(arena, placementArguments, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, allocatedType, Category::Type))
        return std::move(failure);
    if (arraySize)
        if (auto failure =
                requireCategory(arena, *arraySize, Category::Expression))
            return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    const Constructor constructor =
        nonAllocating ? Constructor::ExpressionNewNonAllocating
                      : Constructor::ExpressionNewAllocating;
    Value form =
        nonAllocating
            ? Value::scalar(ScalarTerm::symbol("new_form.NonAllocating"))
            : Value::constructedProduct(
                  ScalarTerm::symbol("new_form.Allocating"),
                  {Value::scalar(ScalarTerm::boolean(passAlignment))});
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::product({Value::node(name), Value::node(functionType)}),
         Value::sequence(nodes(std::move(placementArguments))), std::move(form),
         Value::node(allocatedType),
         Value::optional(arraySize
                             ? std::optional<Value>(Value::node(*arraySize))
                             : std::nullopt),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt)});
}
llvm::Expected<NodeId> makeDeleteExpression(Arena &arena, OriginList origins,
                                            bool isArray, NodeId name,
                                            NodeId argument, NodeId type) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, argument, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionDelete, std::move(origins),
                      {Value::scalar(ScalarTerm::boolean(isArray)),
                       Value::node(name), Value::node(argument),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeFunctionAllocationOperatorCallExpression(
    Arena &arena, OriginList origins, bool isDelete, bool isArray, NodeId name,
    NodeId type, std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    const Constructor constructor =
        isDelete ? Constructor::ExpressionAllocationOperatorCallFunctionDelete
                 : Constructor::ExpressionAllocationOperatorCallFunctionNew;
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::constructedProduct(
             ScalarTerm::symbol(isDelete ? "OODelete" : "OONew"),
             {Value::scalar(ScalarTerm::boolean(isArray))}),
         Value::constructedProduct(ScalarTerm::symbol("operator_impl.Func"),
                                   {Value::node(name), Value::node(type)}),
         Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeMethodAllocationOperatorCallExpression(
    Arena &arena, OriginList origins, bool isDelete, bool isArray, NodeId name,
    ScalarTerm dispatch, NodeId type, std::vector<NodeId> arguments) {
    if (auto failure = requireDispatch(dispatch))
        return std::move(failure);
    if (dispatch.text != "Static_dispatch")
        return error(
            "allocation operator member dispatch must be Static_dispatch");
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    const Constructor constructor =
        isDelete ? Constructor::ExpressionAllocationOperatorCallMethodDelete
                 : Constructor::ExpressionAllocationOperatorCallMethodNew;
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::constructedProduct(
             ScalarTerm::symbol(isDelete ? "OODelete" : "OONew"),
             {Value::scalar(ScalarTerm::boolean(isArray))}),
         Value::constructedProduct(ScalarTerm::symbol("operator_impl.MFunc"),
                                   {Value::node(name),
                                    Value::scalar(std::move(dispatch)),
                                    Value::node(type)}),
         Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeAtomicExpression(Arena &arena, OriginList origins,
                                            std::string operation,
                                            std::vector<NodeId> arguments,
                                            NodeId type) {
    if (operation.empty())
        return error("atomic expression operation is empty");
    if (auto failure = requireNodes(arena, arguments, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionAtomic, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(operation))),
                       Value::sequence(nodes(std::move(arguments))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeVaArgExpression(Arena &arena, OriginList origins,
                                           NodeId argument, NodeId type) {
    if (auto failure = requireCategory(arena, argument, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionVaArg, std::move(origins),
                      {Value::node(argument), Value::node(type)});
}
llvm::Expected<NodeId> makeLambdaExpression(Arena &arena, OriginList origins,
                                            NodeId name,
                                            std::vector<NodeId> captures) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireNodes(arena, captures, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionLambda, std::move(origins),
        {Value::node(name), Value::sequence(nodes(std::move(captures)))});
}
llvm::Expected<NodeId>
makeConditionalExpression(Arena &arena, OriginList origins, NodeId condition,
                          NodeId whenTrue, NodeId whenFalse, NodeId type) {
    for (NodeId expression : {condition, whenTrue, whenFalse})
        if (auto failure =
                requireCategory(arena, expression, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionConditional,
                      std::move(origins),
                      {Value::node(condition), Value::node(whenTrue),
                       Value::node(whenFalse), Value::node(type)});
}
llvm::Expected<NodeId> makeBinaryConditionalExpression(
    Arena &arena, OriginList origins, std::uint64_t opaqueIndex, NodeId common,
    NodeId condition, NodeId whenTrue, NodeId whenFalse, NodeId type) {
    for (NodeId expression : {common, condition, whenTrue, whenFalse})
        if (auto failure =
                requireCategory(arena, expression, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::ExpressionBinaryConditional, std::move(origins),
        {Value::scalar(ScalarTerm::natural(opaqueIndex)), Value::node(common),
         Value::node(condition), Value::node(whenTrue), Value::node(whenFalse),
         Value::node(type)});
}
llvm::Expected<NodeId> makeOffsetOfExpression(Arena &arena, OriginList origins,
                                              NodeId parentType,
                                              std::string field, NodeId type) {
    if (field.empty())
        return error("offsetof field is empty");
    if (auto failure = requireCategory(arena, parentType, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionOffsetOf,
                      std::move(origins),
                      {Value::node(parentType),
                       Value::scalar(ScalarTerm::string(std::move(field))),
                       Value::node(type)});
}
llvm::Expected<NodeId> makeStatementBlockExpression(Arena &arena,
                                                    OriginList origins,
                                                    NodeId statement,
                                                    NodeId type) {
    if (auto failure = requireCategory(arena, statement, Category::Statement))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionStatementBlock,
                      std::move(origins),
                      {Value::node(statement), Value::node(type)});
}
llvm::Expected<NodeId> makePseudoDestructorExpression(Arena &arena,
                                                      OriginList origins,
                                                      bool arrow, NodeId type,
                                                      NodeId object) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, object, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::ExpressionPseudoDestructor,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::boolean(arrow)),
                       Value::node(type), Value::node(object)});
}
llvm::Expected<NodeId> makeGlobalInitializer(Arena &arena,
                                             Constructor constructor,
                                             OriginList origins,
                                             std::optional<NodeId> expression) {
    if (constructor == Constructor::GlobalInitExpression) {
        if (!expression)
            return error("global_init.Init requires an expression");
        return oneNode(arena, constructor, std::move(origins), *expression,
                       Category::Expression);
    }
    switch (constructor) {
    case Constructor::GlobalInitImplicit:
    case Constructor::GlobalInitNone:
    case Constructor::GlobalInitDelayed:
    case Constructor::GlobalInitExtern:
        if (expression)
            return error("nullary global initializer has an expression");
        return addChecked(arena, constructor, std::move(origins), {});
    default:
        return error("constructor is not a global initializer");
    }
}

llvm::Expected<NodeId> makeFunctionBody(Arena &arena, Constructor constructor,
                                        OriginList origins,
                                        std::optional<NodeId> statement,
                                        std::string builtin) {
    if (constructor == Constructor::FunctionBodyImplementation) {
        if (!statement || !builtin.empty())
            return error("Impl requires only a statement");
        return oneNode(arena, constructor, std::move(origins), *statement,
                       Category::Statement);
    }
    if (constructor == Constructor::FunctionBodyBuiltin) {
        if (statement || builtin.empty())
            return error("Builtin requires only a nonempty name");
        return addChecked(
            arena, constructor, std::move(origins),
            {Value::scalar(ScalarTerm::string(std::move(builtin)))});
    }
    return error("constructor is not a function body");
}

llvm::Expected<NodeId>
makeDefaultStatementBody(Arena &arena, Constructor constructor,
                         OriginList origins, std::optional<NodeId> statement) {
    if (constructor == Constructor::DefaultStatementBodyDefaulted) {
        if (statement)
            return error("Defaulted statement body is nullary");
        return addChecked(arena, constructor, std::move(origins), {});
    }
    if (constructor != Constructor::DefaultStatementBodyCompilerProvided &&
        constructor != Constructor::DefaultStatementBodyUserDefined)
        return error("constructor is not an OrDefault statement body");
    if (!statement)
        return error("defined OrDefault body requires a statement");
    return oneNode(arena, constructor, std::move(origins), *statement,
                   Category::Statement);
}

llvm::Expected<NodeId> makeConstructorBody(Arena &arena,
                                           Constructor constructor,
                                           OriginList origins,
                                           std::vector<NodeId> initializers,
                                           std::optional<NodeId> statement) {
    if (constructor == Constructor::ConstructorBodyDefaulted) {
        if (statement || !initializers.empty())
            return error("Defaulted constructor body is nullary");
        return addChecked(arena, constructor, std::move(origins), {});
    }
    if (constructor != Constructor::ConstructorBodyCompilerProvided &&
        constructor != Constructor::ConstructorBodyUserDefined)
        return error("constructor is not an OrDefault constructor body");
    if (!statement)
        return error("defined constructor body requires a statement");
    if (auto failure = requireNodes(arena, initializers, Category::Initializer))
        return std::move(failure);
    if (auto failure = requireCategory(arena, *statement, Category::Statement))
        return std::move(failure);
    return addChecked(
        arena, constructor, std::move(origins),
        {Value::product({Value::sequence(nodes(std::move(initializers))),
                         Value::node(*statement)})});
}

llvm::Expected<NodeId>
makeFunctionRecord(Arena &arena, OriginList origins, NodeId returnType,
                   std::vector<DeclarationParameter> parameters,
                   ScalarTerm callingConvention, ScalarTerm arity,
                   ScalarTerm exceptionSpec, std::optional<NodeId> body) {
    if (auto failure = requireCategory(arena, returnType, Category::Type))
        return std::move(failure);
    auto packed = packDeclarationParameters(arena, std::move(parameters));
    if (!packed)
        return packed.takeError();
    if (body)
        if (auto failure =
                requireCategory(arena, *body, Category::FunctionBody))
            return std::move(failure);
    return addChecked(
        arena, Constructor::FunctionRecord, std::move(origins),
        {Value::node(returnType), std::move(*packed),
         Value::scalar(std::move(callingConvention)),
         Value::scalar(std::move(arity)),
         Value::scalar(std::move(exceptionSpec)),
         Value::optional(body ? std::optional<Value>(Value::node(*body))
                              : std::nullopt)});
}

llvm::Expected<NodeId>
makeMethodRecord(Arena &arena, OriginList origins, NodeId returnType,
                 NodeId className, ScalarTerm thisQualifier,
                 std::vector<DeclarationParameter> parameters,
                 ScalarTerm callingConvention, ScalarTerm arity,
                 ScalarTerm exceptionSpec, std::optional<NodeId> body) {
    if (auto failure = requireCategory(arena, returnType, Category::Type))
        return std::move(failure);
    if (auto failure = requireCategory(arena, className, Category::Name))
        return std::move(failure);
    auto packed = packDeclarationParameters(arena, std::move(parameters));
    if (!packed)
        return packed.takeError();
    if (body)
        if (auto failure =
                requireCategory(arena, *body, Category::DefaultStatementBody))
            return std::move(failure);
    return addChecked(
        arena, Constructor::MethodRecord, std::move(origins),
        {Value::node(returnType), Value::node(className),
         Value::scalar(std::move(thisQualifier)), std::move(*packed),
         Value::scalar(std::move(callingConvention)),
         Value::scalar(std::move(arity)),
         Value::scalar(std::move(exceptionSpec)),
         Value::optional(body ? std::optional<Value>(Value::node(*body))
                              : std::nullopt)});
}

llvm::Expected<NodeId> makeInitializerPath(Arena &arena,
                                           Constructor constructor,
                                           OriginList origins,
                                           std::optional<NodeId> value) {
    if (constructor == Constructor::InitializerThisPath) {
        if (value)
            return error("InitThis is nullary");
        return addChecked(arena, constructor, std::move(origins), {});
    }
    if (!value)
        return error("initializer path requires a value");
    if (constructor == Constructor::InitializerBasePath)
        return oneNode(arena, constructor, std::move(origins), *value,
                       Category::Name);
    if (constructor == Constructor::InitializerFieldPath)
        return oneNode(arena, constructor, std::move(origins), *value,
                       Category::AtomicName);
    return error("constructor is not a simple initializer path");
}

llvm::Expected<NodeId> makeInitializerRecord(Arena &arena, OriginList origins,
                                             NodeId path, NodeId expression) {
    if (auto failure = requireCategory(arena, path, Category::InitializerPath))
        return std::move(failure);
    if (auto failure = requireCategory(arena, expression, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::InitializerRecord, std::move(origins),
                      {Value::node(path), Value::node(expression)});
}

llvm::Expected<NodeId>
makeConstructorRecord(Arena &arena, OriginList origins, NodeId className,
                      std::vector<DeclarationParameter> parameters,
                      ScalarTerm callingConvention, ScalarTerm arity,
                      ScalarTerm exceptionSpec, std::optional<NodeId> body) {
    if (auto failure = requireCategory(arena, className, Category::Name))
        return std::move(failure);
    auto packed = packDeclarationParameters(arena, std::move(parameters));
    if (!packed)
        return packed.takeError();
    if (body)
        if (auto failure =
                requireCategory(arena, *body, Category::ConstructorBody))
            return std::move(failure);
    return addChecked(
        arena, Constructor::ConstructorRecord, std::move(origins),
        {Value::node(className), std::move(*packed),
         Value::scalar(std::move(callingConvention)),
         Value::scalar(std::move(arity)),
         Value::scalar(std::move(exceptionSpec)),
         Value::optional(body ? std::optional<Value>(Value::node(*body))
                              : std::nullopt)});
}

llvm::Expected<NodeId> makeDestructorRecord(Arena &arena, OriginList origins,
                                            NodeId className,
                                            ScalarTerm callingConvention,
                                            ScalarTerm exceptionSpec,
                                            std::optional<NodeId> body) {
    if (auto failure = requireCategory(arena, className, Category::Name))
        return std::move(failure);
    if (body)
        if (auto failure =
                requireCategory(arena, *body, Category::DefaultStatementBody))
            return std::move(failure);
    return addChecked(
        arena, Constructor::DestructorRecord, std::move(origins),
        {Value::node(className), Value::scalar(std::move(callingConvention)),
         Value::scalar(std::move(exceptionSpec)),
         Value::optional(body ? std::optional<Value>(Value::node(*body))
                              : std::nullopt)});
}

llvm::Expected<NodeId> makeExpressionStatement(Arena &arena, OriginList origins,
                                               NodeId expression) {
    return oneNode(arena, Constructor::StatementExpression, std::move(origins),
                   expression, Category::Expression);
}
llvm::Expected<NodeId> makeReturnStatement(Arena &arena, OriginList origins,
                                           std::optional<NodeId> expression) {
    if (expression)
        if (auto failure =
                requireCategory(arena, *expression, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::StatementReturn, std::move(origins),
        {Value::optional(expression
                             ? std::optional<Value>(Value::node(*expression))
                             : std::nullopt)});
}
llvm::Expected<NodeId> makeStatementSequence(Arena &arena, OriginList origins,
                                             std::vector<NodeId> statements) {
    if (auto failure = requireNodes(arena, statements, Category::Statement))
        return std::move(failure);
    return addChecked(arena, Constructor::StatementSequence, std::move(origins),
                      {Value::sequence(nodes(std::move(statements)))});
}
llvm::Expected<NodeId>
makeDeclarationStatement(Arena &arena, OriginList origins,
                         std::vector<NodeId> declarations) {
    if (auto failure =
            requireNodes(arena, declarations, Category::VariableDeclaration))
        return std::move(failure);
    return addChecked(arena, Constructor::StatementDeclaration,
                      std::move(origins),
                      {Value::sequence(nodes(std::move(declarations)))});
}
llvm::Expected<NodeId> makeIfStatement(Arena &arena, OriginList origins,
                                       std::optional<NodeId> init,
                                       std::optional<NodeId> declaration,
                                       NodeId condition, NodeId whenTrue,
                                       NodeId whenFalse) {
    if (init)
        if (auto failure = requireCategory(arena, *init, Category::Statement))
            return std::move(failure);
    if (declaration)
        if (auto failure = requireCategory(arena, *declaration,
                                           Category::VariableDeclaration))
            return std::move(failure);
    if (auto failure = requireCategory(arena, condition, Category::Expression))
        return std::move(failure);
    for (NodeId statement : {whenTrue, whenFalse})
        if (auto failure =
                requireCategory(arena, statement, Category::Statement))
            return std::move(failure);
    return addChecked(
        arena, Constructor::StatementIf, std::move(origins),
        {Value::optional(init ? std::optional<Value>(Value::node(*init))
                              : std::nullopt),
         Value::optional(declaration
                             ? std::optional<Value>(Value::node(*declaration))
                             : std::nullopt),
         Value::node(condition), Value::node(whenTrue),
         Value::node(whenFalse)});
}
llvm::Expected<NodeId> makeIfConstevalStatement(Arena &arena,
                                                OriginList origins,
                                                NodeId whenTrue,
                                                NodeId whenFalse) {
    for (NodeId statement : {whenTrue, whenFalse})
        if (auto failure =
                requireCategory(arena, statement, Category::Statement))
            return std::move(failure);
    return addChecked(arena, Constructor::StatementIfConsteval,
                      std::move(origins),
                      {Value::node(whenTrue), Value::node(whenFalse)});
}
llvm::Expected<NodeId> makeWhileStatement(Arena &arena, OriginList origins,
                                          std::optional<NodeId> declaration,
                                          NodeId condition, NodeId body) {
    if (declaration)
        if (auto failure = requireCategory(arena, *declaration,
                                           Category::VariableDeclaration))
            return std::move(failure);
    if (auto failure = requireCategory(arena, condition, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, body, Category::Statement))
        return std::move(failure);
    return addChecked(
        arena, Constructor::StatementWhile, std::move(origins),
        {Value::optional(declaration
                             ? std::optional<Value>(Value::node(*declaration))
                             : std::nullopt),
         Value::node(condition), Value::node(body)});
}
llvm::Expected<NodeId> makeForStatement(Arena &arena, OriginList origins,
                                        std::optional<NodeId> init,
                                        std::optional<NodeId> condition,
                                        std::optional<NodeId> increment,
                                        NodeId body) {
    if (init)
        if (auto failure = requireCategory(arena, *init, Category::Statement))
            return std::move(failure);
    for (std::optional<NodeId> expression : {condition, increment})
        if (expression)
            if (auto failure =
                    requireCategory(arena, *expression, Category::Expression))
                return std::move(failure);
    if (auto failure = requireCategory(arena, body, Category::Statement))
        return std::move(failure);
    return addChecked(
        arena, Constructor::StatementFor, std::move(origins),
        {Value::optional(init ? std::optional<Value>(Value::node(*init))
                              : std::nullopt),
         Value::optional(condition
                             ? std::optional<Value>(Value::node(*condition))
                             : std::nullopt),
         Value::optional(increment
                             ? std::optional<Value>(Value::node(*increment))
                             : std::nullopt),
         Value::node(body)});
}
llvm::Expected<NodeId> makeDoStatement(Arena &arena, OriginList origins,
                                       NodeId body, NodeId condition) {
    if (auto failure = requireCategory(arena, body, Category::Statement))
        return std::move(failure);
    if (auto failure = requireCategory(arena, condition, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::StatementDo, std::move(origins),
                      {Value::node(body), Value::node(condition)});
}
llvm::Expected<NodeId> makeSwitchStatement(Arena &arena, OriginList origins,
                                           std::optional<NodeId> init,
                                           std::optional<NodeId> declaration,
                                           NodeId condition, NodeId body) {
    if (init)
        if (auto failure = requireCategory(arena, *init, Category::Statement))
            return std::move(failure);
    if (declaration)
        if (auto failure = requireCategory(arena, *declaration,
                                           Category::VariableDeclaration))
            return std::move(failure);
    if (auto failure = requireCategory(arena, condition, Category::Expression))
        return std::move(failure);
    if (auto failure = requireCategory(arena, body, Category::Statement))
        return std::move(failure);
    return addChecked(
        arena, Constructor::StatementSwitch, std::move(origins),
        {Value::optional(init ? std::optional<Value>(Value::node(*init))
                              : std::nullopt),
         Value::optional(declaration
                             ? std::optional<Value>(Value::node(*declaration))
                             : std::nullopt),
         Value::node(condition), Value::node(body)});
}
llvm::Expected<NodeId> makeCaseStatement(Arena &arena, OriginList origins,
                                         ScalarTerm branch) {
    if (branch.kind != ScalarKind::SwitchBranch || branch.text.empty())
        return error("case branch must be a structured switch branch");
    return addChecked(arena, Constructor::StatementCase, std::move(origins),
                      {Value::scalar(std::move(branch))});
}
llvm::Expected<NodeId> makeLeafStatement(Arena &arena, Constructor constructor,
                                         OriginList origins) {
    switch (constructor) {
    case Constructor::StatementDefault:
    case Constructor::StatementBreak:
    case Constructor::StatementContinue:
        return addChecked(arena, constructor, std::move(origins), {});
    default:
        return error("constructor is not a leaf statement");
    }
}
llvm::Expected<NodeId>
makeAttributeStatement(Arena &arena, OriginList origins,
                       std::vector<std::string> attributes, NodeId statement) {
    if (auto failure = requireCategory(arena, statement, Category::Statement))
        return std::move(failure);
    std::vector<Value> values;
    values.reserve(attributes.size());
    for (std::string &attribute : attributes) {
        if (attribute.empty())
            return error("statement attribute is empty");
        values.push_back(
            Value::scalar(ScalarTerm::string(std::move(attribute))));
    }
    return addChecked(
        arena, Constructor::StatementAttribute, std::move(origins),
        {Value::sequence(std::move(values)), Value::node(statement)});
}
llvm::Expected<NodeId>
makeAsmStatement(Arena &arena, OriginList origins, std::string assembly,
                 bool isVolatile,
                 std::vector<std::pair<std::string, NodeId>> inputs,
                 std::vector<std::pair<std::string, NodeId>> outputs,
                 std::vector<std::string> clobbers) {
    auto operands = [&](std::vector<std::pair<std::string, NodeId>> values)
        -> llvm::Expected<Value> {
        std::vector<Value> result;
        result.reserve(values.size());
        for (auto &[constraint, expression] : values) {
            if (auto failure =
                    requireCategory(arena, expression, Category::Expression))
                return std::move(failure);
            result.push_back(Value::product(
                {Value::scalar(ScalarTerm::string(std::move(constraint))),
                 Value::node(expression)}));
        }
        return Value::sequence(std::move(result));
    };
    auto inputValues = operands(std::move(inputs));
    if (!inputValues)
        return inputValues.takeError();
    auto outputValues = operands(std::move(outputs));
    if (!outputValues)
        return outputValues.takeError();
    std::vector<Value> clobberValues;
    clobberValues.reserve(clobbers.size());
    for (std::string &clobber : clobbers)
        clobberValues.push_back(
            Value::scalar(ScalarTerm::string(std::move(clobber))));
    return addChecked(arena, Constructor::StatementAsm, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(assembly))),
                       Value::scalar(ScalarTerm::boolean(isVolatile)),
                       std::move(*inputValues), std::move(*outputValues),
                       Value::sequence(std::move(clobberValues))});
}
llvm::Expected<NodeId> makeLabeledStatement(Arena &arena, OriginList origins,
                                            std::string label,
                                            NodeId statement) {
    if (label.empty())
        return error("statement label is empty");
    if (auto failure = requireCategory(arena, statement, Category::Statement))
        return std::move(failure);
    return addChecked(arena, Constructor::StatementLabeled, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(label))),
                       Value::node(statement)});
}
llvm::Expected<NodeId> makeGotoStatement(Arena &arena, OriginList origins,
                                         std::string label) {
    if (label.empty())
        return error("goto label is empty");
    return addChecked(arena, Constructor::StatementGoto, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(label)))});
}
llvm::Expected<NodeId> makeUnsupportedStatement(Arena &arena,
                                                OriginList origins,
                                                std::string diagnostic) {
    if (diagnostic.empty())
        return error("unsupported statement diagnostic is empty");
    return addChecked(
        arena, Constructor::StatementUnsupported, std::move(origins),
        {Value::scalar(ScalarTerm::string(std::move(diagnostic)))});
}
llvm::Expected<NodeId> makeLayoutInfo(Arena &arena, OriginList origins,
                                      std::string offset) {
    if (offset.empty())
        return error("layout offset is empty");
    return addChecked(arena, Constructor::LayoutInfoRecord, std::move(origins),
                      {Value::scalar(ScalarTerm::numeral(std::move(offset)))});
}

llvm::Expected<NodeId> makeMemberRecord(Arena &arena, OriginList origins,
                                        NodeId name, NodeId type,
                                        bool isMutable,
                                        std::optional<NodeId> initializer,
                                        NodeId layout) {
    if (auto failure = requireCategory(arena, name, Category::AtomicName))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    if (auto failure = requireCategory(arena, layout, Category::LayoutInfo))
        return std::move(failure);
    return addChecked(
        arena, Constructor::MemberRecord, std::move(origins),
        {Value::node(name), Value::node(type),
         Value::scalar(ScalarTerm::boolean(isMutable)),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt),
         Value::node(layout)});
}

llvm::Expected<NodeId> makeStructRecord(
    Arena &arena, OriginList origins, std::vector<StructBaseValue> bases,
    std::vector<NodeId> members, std::vector<StructVirtualValue> virtuals,
    std::vector<StructOverrideValue> overrides, NodeId destructorName,
    bool triviallyDestructible, std::optional<NodeId> deleteName,
    ScalarTerm layoutKind, std::string size, std::string alignment) {
    std::vector<Value> baseValues;
    baseValues.reserve(bases.size());
    for (auto &base : bases) {
        if (auto failure = requireCategory(arena, base.name, Category::Name))
            return std::move(failure);
        if (auto failure =
                requireCategory(arena, base.layout, Category::LayoutInfo))
            return std::move(failure);
        baseValues.push_back(
            Value::product({Value::node(base.name), Value::node(base.layout)}));
    }
    if (auto failure = requireNodes(arena, members, Category::Member))
        return std::move(failure);
    std::vector<Value> virtualValues;
    virtualValues.reserve(virtuals.size());
    for (const StructVirtualValue &method : virtuals) {
        if (auto failure = requireCategory(arena, method.name, Category::Name))
            return std::move(failure);
        if (method.implementation)
            if (auto failure = requireCategory(arena, *method.implementation,
                                               Category::Name))
                return std::move(failure);
        virtualValues.push_back(Value::product(
            {Value::node(method.name),
             Value::optional(
                 method.implementation
                     ? std::optional<Value>(Value::node(*method.implementation))
                     : std::nullopt)}));
    }
    std::vector<Value> overrideValues;
    overrideValues.reserve(overrides.size());
    for (const StructOverrideValue &method : overrides) {
        if (auto failure =
                requireCategory(arena, method.overridden, Category::Name))
            return std::move(failure);
        if (auto failure =
                requireCategory(arena, method.overriding, Category::Name))
            return std::move(failure);
        overrideValues.push_back(Value::product(
            {Value::node(method.overridden), Value::node(method.overriding)}));
    }
    if (auto failure = requireCategory(arena, destructorName, Category::Name))
        return std::move(failure);
    if (deleteName)
        if (auto failure = requireCategory(arena, *deleteName, Category::Name))
            return std::move(failure);
    if (size.empty() || alignment.empty())
        return error("structure size/alignment is empty");
    return addChecked(
        arena, Constructor::StructRecord, std::move(origins),
        {Value::sequence(std::move(baseValues)),
         Value::sequence(nodes(std::move(members))),
         Value::sequence(std::move(virtualValues)),
         Value::sequence(std::move(overrideValues)),
         Value::node(destructorName),
         Value::scalar(ScalarTerm::boolean(triviallyDestructible)),
         Value::optional(deleteName
                             ? std::optional<Value>(Value::node(*deleteName))
                             : std::nullopt),
         Value::scalar(std::move(layoutKind)),
         Value::scalar(ScalarTerm::numeral(std::move(size))),
         Value::scalar(ScalarTerm::numeral(std::move(alignment)))});
}

llvm::Expected<NodeId>
makeUnionRecord(Arena &arena, OriginList origins, std::vector<NodeId> members,
                NodeId destructorName, bool triviallyDestructible,
                std::optional<NodeId> deleteName, std::string size,
                std::string alignment) {
    if (auto failure = requireNodes(arena, members, Category::Member))
        return std::move(failure);
    if (auto failure = requireCategory(arena, destructorName, Category::Name))
        return std::move(failure);
    if (deleteName)
        if (auto failure = requireCategory(arena, *deleteName, Category::Name))
            return std::move(failure);
    if (size.empty() || alignment.empty())
        return error("union size/alignment is empty");
    return addChecked(
        arena, Constructor::UnionRecord, std::move(origins),
        {Value::sequence(nodes(std::move(members))),
         Value::node(destructorName),
         Value::scalar(ScalarTerm::boolean(triviallyDestructible)),
         Value::optional(deleteName
                             ? std::optional<Value>(Value::node(*deleteName))
                             : std::nullopt),
         Value::scalar(ScalarTerm::numeral(std::move(size))),
         Value::scalar(ScalarTerm::numeral(std::move(alignment)))});
}

llvm::Expected<NodeId> makeObjectValue(Arena &arena, Constructor constructor,
                                       OriginList origins, NodeId value) {
    Category wanted;
    switch (constructor) {
    case Constructor::ObjectFunction:
        wanted = Category::Function;
        break;
    case Constructor::ObjectMethod:
        wanted = Category::Method;
        break;
    case Constructor::ObjectConstructor:
        wanted = Category::Constructor;
        break;
    case Constructor::ObjectDestructor:
        wanted = Category::Destructor;
        break;
    default:
        return error("constructor is not a unary object value");
    }
    return oneNode(arena, constructor, std::move(origins), value, wanted);
}

llvm::Expected<NodeId> makeVariableObjectValue(Arena &arena, OriginList origins,
                                               NodeId type,
                                               NodeId initializer) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure =
            requireCategory(arena, initializer, Category::GlobalInitializer))
        return std::move(failure);
    return addChecked(arena, Constructor::ObjectVariable, std::move(origins),
                      {Value::node(type), Value::node(initializer)});
}

llvm::Expected<NodeId> makeGlobalDeclaration(Arena &arena,
                                             Constructor constructor,
                                             OriginList origins,
                                             std::optional<NodeId> value) {
    if (constructor == Constructor::GlobalType) {
        if (value)
            return error("Gtype is nullary");
        return addChecked(arena, constructor, std::move(origins), {});
    }
    Category wanted;
    switch (constructor) {
    case Constructor::GlobalUnion:
        wanted = Category::Union;
        break;
    case Constructor::GlobalStruct:
        wanted = Category::Struct;
        break;
    case Constructor::GlobalTypedef:
        wanted = Category::Type;
        break;
    default:
        return error("constructor is not a simple global declaration");
    }
    if (!value)
        return error("global declaration requires a value");
    return oneNode(arena, constructor, std::move(origins), *value, wanted);
}

llvm::Expected<NodeId>
makeEnumGlobalDeclaration(Arena &arena, OriginList origins, NodeId type,
                          std::vector<std::string> enumerators) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    std::vector<Value> values;
    values.reserve(enumerators.size());
    for (std::string &enumerator : enumerators)
        values.push_back(
            Value::scalar(ScalarTerm::string(std::move(enumerator))));
    return addChecked(arena, Constructor::GlobalEnum, std::move(origins),
                      {Value::node(type), Value::sequence(std::move(values))});
}

llvm::Expected<NodeId>
makeConstantGlobalDeclaration(Arena &arena, OriginList origins, NodeId type,
                              std::optional<NodeId> initializer) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::GlobalConstant, std::move(origins),
        {Value::node(type),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt)});
}

llvm::Expected<NodeId> makeUnsupportedGlobalDeclaration(Arena &arena,
                                                        OriginList origins,
                                                        std::string message) {
    if (message.empty())
        return error("unsupported global declaration message is empty");
    return addChecked(arena, Constructor::GlobalUnsupported, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}

llvm::Expected<NodeId>
makeVariableDeclaration(Arena &arena, OriginList origins, std::string name,
                        NodeId type, std::optional<NodeId> initializer) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::VariableDeclaration, std::move(origins),
        {Value::scalar(ScalarTerm::string(std::move(name))), Value::node(type),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt)});
}
llvm::Expected<NodeId> makeVariableDecomposition(Arena &arena,
                                                 OriginList origins,
                                                 NodeId initializer,
                                                 std::uint64_t anonymousIndex,
                                                 std::vector<NodeId> bindings) {
    if (auto failure =
            requireCategory(arena, initializer, Category::Expression))
        return std::move(failure);
    if (auto failure =
            requireNodes(arena, bindings, Category::BindingDeclaration))
        return std::move(failure);
    return addChecked(
        arena, Constructor::VariableDecomposition, std::move(origins),
        {Value::node(initializer),
         Value::scalar(ScalarTerm::anonymousLocal(anonymousIndex)),
         Value::sequence(nodes(std::move(bindings)))});
}
llvm::Expected<NodeId>
makeStaticVariableDeclaration(Arena &arena, OriginList origins, bool threadSafe,
                              NodeId name, NodeId type,
                              std::optional<NodeId> initializer) {
    if (auto failure = requireCategory(arena, name, Category::Name))
        return std::move(failure);
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (initializer)
        if (auto failure =
                requireCategory(arena, *initializer, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::VariableStaticInit, std::move(origins),
        {Value::scalar(ScalarTerm::boolean(threadSafe)), Value::node(name),
         Value::node(type),
         Value::optional(initializer
                             ? std::optional<Value>(Value::node(*initializer))
                             : std::nullopt)});
}
llvm::Expected<NodeId> makeBindingDeclaration(Arena &arena,
                                              Constructor constructor,
                                              OriginList origins,
                                              std::string name, NodeId type,
                                              NodeId initializer) {
    if (constructor != Constructor::BindingVariable &&
        constructor != Constructor::BindingReference)
        return error("constructor is not a binding declaration");
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    if (auto failure =
            requireCategory(arena, initializer, Category::Expression))
        return std::move(failure);
    return addChecked(arena, constructor, std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name))),
                       Value::node(type), Value::node(initializer)});
}
llvm::Expected<NodeId>
makeTypeTemplateParameter(Arena &arena, OriginList origins, std::string name) {
    return addChecked(arena, Constructor::TemplateParameterType,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeValueTemplateParameter(Arena &arena,
                                                  OriginList origins,
                                                  std::string name,
                                                  NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(arena, Constructor::TemplateParameterValue,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name))),
                       Value::node(type)});
}
llvm::Expected<NodeId>
makeTemplateTemplateParameter(Arena &arena, OriginList origins,
                              std::string name,
                              std::vector<NodeId> parameters) {
    if (auto failure =
            requireNodes(arena, parameters, Category::TemplateParameter))
        return std::move(failure);
    return addChecked(arena, Constructor::TemplateParameterTemplate,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name))),
                       Value::sequence(nodes(std::move(parameters)))});
}
llvm::Expected<NodeId> makeUnsupportedTemplateParameter(Arena &arena,
                                                        OriginList origins,
                                                        std::string message) {
    return addChecked(arena, Constructor::TemplateParameterUnsupported,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}
llvm::Expected<NodeId>
makeTypeTemplateArgument(Arena &arena, OriginList origins, NodeId type) {
    return oneNode(arena, Constructor::TemplateArgumentType, std::move(origins),
                   type, Category::Type);
}
llvm::Expected<NodeId>
makeValueTemplateArgument(Arena &arena, OriginList origins, NodeId expression) {
    return oneNode(arena, Constructor::TemplateArgumentValue,
                   std::move(origins), expression, Category::Expression);
}
llvm::Expected<NodeId> makePackTemplateArgument(Arena &arena,
                                                OriginList origins,
                                                std::vector<NodeId> values) {
    if (auto failure = requireNodes(arena, values, Category::TemplateArgument))
        return std::move(failure);
    return addChecked(arena, Constructor::TemplateArgumentPack,
                      std::move(origins),
                      {Value::sequence(nodes(std::move(values)))});
}
llvm::Expected<NodeId>
makeNamedTemplateArgument(Arena &arena, OriginList origins, NodeId name) {
    return oneNode(arena, Constructor::TemplateArgumentTemplate,
                   std::move(origins), name, Category::Name);
}
llvm::Expected<NodeId> makeTemplateParameterArgument(Arena &arena,
                                                     OriginList origins,
                                                     std::string name) {
    return addChecked(arena, Constructor::TemplateArgumentTemplateParameter,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(name)))});
}
llvm::Expected<NodeId> makeUnsupportedTemplateArgument(Arena &arena,
                                                       OriginList origins,
                                                       std::string message) {
    return addChecked(arena, Constructor::TemplateArgumentUnsupported,
                      std::move(origins),
                      {Value::scalar(ScalarTerm::string(std::move(message)))});
}
llvm::Expected<NodeId> makeObjectVariable(Arena &arena, OriginList origins,
                                          NodeId type, NodeId initializer) {
    return makeVariableObjectValue(arena, std::move(origins), type,
                                   initializer);
}
llvm::Expected<NodeId> makeGlobalTypedef(Arena &arena, OriginList origins,
                                         NodeId type) {
    return makeGlobalDeclaration(arena, Constructor::GlobalTypedef,
                                 std::move(origins), type);
}
llvm::Expected<NodeId> makeGlobalConstant(Arena &arena, OriginList origins,
                                          NodeId type,
                                          std::optional<NodeId> initializer) {
    return makeConstantGlobalDeclaration(arena, std::move(origins), type,
                                         initializer);
}
llvm::Expected<NodeId> makeTemplateObjectRoot(Arena &arena, OriginList origins,
                                              TemplateParameters parameters,
                                              NodeId object) {
    if (auto failure = requireCategory(arena, object, Category::ObjectValue))
        return std::move(failure);
    return addChecked(
        arena, Constructor::TemplateObjectRoot, std::move(origins),
        {Value::sequence(std::move(parameters)), Value::node(object)});
}
llvm::Expected<NodeId> makeTemplateGlobalRoot(Arena &arena, OriginList origins,
                                              TemplateParameters parameters,
                                              NodeId global) {
    if (auto failure =
            requireCategory(arena, global, Category::GlobalDeclaration))
        return std::move(failure);
    return addChecked(
        arena, Constructor::TemplateGlobalRoot, std::move(origins),
        {Value::sequence(std::move(parameters)), Value::node(global)});
}
llvm::Expected<NodeId> makeTemplateAlias(Arena &arena, OriginList origins,
                                         TemplateParameters parameters,
                                         NodeId type) {
    if (auto failure = requireCategory(arena, type, Category::Type))
        return std::move(failure);
    return addChecked(
        arena, Constructor::TemplateAliasValue, std::move(origins),
        {Value::sequence(std::move(parameters)), Value::node(type)});
}
llvm::Expected<NodeId>
makeTemplatePreInstantiation(Arena &arena, OriginList origins, NodeId target,
                             std::vector<NodeId> arguments) {
    if (auto failure = requireCategory(arena, target, Category::Name))
        return std::move(failure);
    for (NodeId argument : arguments)
        if (auto failure =
                requireCategory(arena, argument, Category::TemplateArgument))
            return std::move(failure);
    return addChecked(
        arena, Constructor::TemplatePreInstantiationValue, std::move(origins),
        {Value::node(target), Value::sequence(nodes(std::move(arguments)))});
}
llvm::Expected<NodeId> makeInitIndirectPath(Arena &arena, OriginList origins,
                                            std::vector<Value> qualifiers,
                                            NodeId finalName) {
    if (auto failure = requireCategory(arena, finalName, Category::AtomicName))
        return std::move(failure);
    return addChecked(
        arena, Constructor::InitIndirectPath, std::move(origins),
        {Value::sequence(std::move(qualifiers)), Value::node(finalName)});
}

llvm::Expected<NodeId> makeOptionalFixture(Arena &arena, OriginList origins,
                                           std::optional<NodeId> value) {
    if (value)
        if (auto failure = requireCategory(arena, *value, Category::Expression))
            return std::move(failure);
    return addChecked(
        arena, Constructor::OptionalFixture, std::move(origins),
        {Value::optional(value ? std::optional<Value>(Value::node(*value))
                               : std::nullopt)});
}
llvm::Expected<NodeId> makeSequenceFixture(Arena &arena, OriginList origins,
                                           std::vector<NodeId> values) {
    for (NodeId value : values)
        if (auto failure = requireCategory(arena, value, Category::Expression))
            return std::move(failure);
    return addChecked(arena, Constructor::SequenceFixture, std::move(origins),
                      {Value::sequence(nodes(std::move(values)))});
}
llvm::Expected<NodeId> makeProductFixture(Arena &arena, OriginList origins,
                                          ScalarTerm scalar, NodeId value) {
    if (scalar.kind != ScalarKind::Symbol)
        return error("product fixture scalar is not a symbol");
    if (auto failure = requireCategory(arena, value, Category::Expression))
        return std::move(failure);
    return addChecked(arena, Constructor::ProductFixture, std::move(origins),
                      {Value::product({Value::scalar(std::move(scalar)),
                                       Value::node(value)})});
}
llvm::Expected<NodeId> makeSumFixture(Arena &arena, OriginList origins,
                                      NodeId value) {
    if (auto failure = requireCategory(arena, value, Category::Expression))
        return std::move(failure);
    return addChecked(
        arena, Constructor::SumFixture, std::move(origins),
        {Value::sum(ScalarTerm::symbol("inl"), Value::node(value))});
}
#define SIMPLE_SEQUENCE_FACTORY(NAME, CTOR)                                    \
    llvm::Expected<NodeId> NAME(Arena &arena, OriginList origins,              \
                                std::vector<Value> values) {                   \
        return addChecked(arena, Constructor::CTOR, std::move(origins),        \
                          {Value::sequence(std::move(values))});               \
    }
SIMPLE_SEQUENCE_FACTORY(makeIdentTypeListFixture, IdentTypeList)
SIMPLE_SEQUENCE_FACTORY(makeNameOptionalNameListFixture, NameOptionalNameList)
SIMPLE_SEQUENCE_FACTORY(makeStructureVirtualsFixture, StructureVirtuals)
SIMPLE_SEQUENCE_FACTORY(makeStructureOverridesFixture, StructureOverrides)
#undef SIMPLE_SEQUENCE_FACTORY
llvm::Expected<NodeId> makeOpaqueFixture(Arena &arena, OriginList origins,
                                         std::string diagnostic) {
    return addChecked(arena, Constructor::OpaqueFixture, std::move(origins),
                      {Value::opaque(std::move(diagnostic))});
}

llvm::Expected<NodeId> cloneWithOrigins(Arena &arena, NodeId child,
                                        const OriginList &addedOrigins) {
    auto source = arena.get(child);
    if (!source)
        return source.takeError();
    Node clone = **source;
    source::appendOriginsStable(clone.origins, addedOrigins);
    return arena.add(std::move(clone));
}

} // namespace factory
} // namespace ir
