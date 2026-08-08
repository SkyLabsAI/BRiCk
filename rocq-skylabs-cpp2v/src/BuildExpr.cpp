/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include "AtomicOp.hpp"

#include <algorithm>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/ExprConcepts.h>
#include <clang/AST/ParentMapContext.h>
#include <clang/Basic/Version.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/Support/Endian.h>
#include <llvm/Support/raw_ostream.h>

namespace ir {
namespace builder {
namespace {

llvm::Error expressionError(const clang::Expr &expression,
                            llvm::StringRef branch) {
    return llvm::createStringError(
        std::errc::not_supported,
        "migration incomplete: %s expression branch (%s)", branch.str().c_str(),
        expression.getStmtClassName());
}

llvm::Expected<ScalarTerm> unaryOperation(const clang::UnaryOperator &value) {
    switch (value.getOpcode()) {
    case clang::UO_Plus:
        return ScalarTerm::symbol("Uplus");
    case clang::UO_Minus:
        return ScalarTerm::symbol("Uminus");
    case clang::UO_Not:
        return ScalarTerm::symbol("Ubnot");
    case clang::UO_LNot:
        return ScalarTerm::symbol("Unot");
    default:
        return llvm::createStringError(
            std::errc::not_supported,
            "migration incomplete: unary expression kernel operation %s",
            clang::UnaryOperator::getOpcodeStr(value.getOpcode())
                .str()
                .c_str());
    }
}

llvm::Expected<ScalarTerm>
overloadedOperatorTerm(clang::OverloadedOperatorKind operation) {
    switch (operation) {
#define OVERLOADED_OPERATOR(Name, Spelling, Token, Unary, Binary, MemberOnly)  \
    case clang::OO_##Name:                                                     \
        return ScalarTerm::symbol("OO" #Name);
#include <clang/Basic/OperatorKinds.def>
#undef OVERLOADED_OPERATOR
#undef OVERLOADED_OPERATOR_MULTI
    default:
        return llvm::createStringError(
            std::errc::not_supported,
            "migration incomplete: unknown overloaded operator call");
    }
}

llvm::Expected<ScalarTerm> binaryOperation(const clang::BinaryOperator &value) {
    switch (value.getOpcode()) {
#define BINARY_CASE(KIND, TERM)                                                \
    case clang::BO_##KIND:                                                     \
        return ScalarTerm::symbol(#TERM)
        BINARY_CASE(Add, Badd);
        BINARY_CASE(And, Band);
        BINARY_CASE(Cmp, Bcmp);
        BINARY_CASE(Div, Bdiv);
        BINARY_CASE(EQ, Beq);
        BINARY_CASE(GE, Bge);
        BINARY_CASE(GT, Bgt);
        BINARY_CASE(LE, Ble);
        BINARY_CASE(LT, Blt);
        BINARY_CASE(Mul, Bmul);
        BINARY_CASE(NE, Bneq);
        BINARY_CASE(Or, Bor);
        BINARY_CASE(Rem, Bmod);
        BINARY_CASE(Shl, Bshl);
        BINARY_CASE(Shr, Bshr);
        BINARY_CASE(Sub, Bsub);
        BINARY_CASE(Xor, Bxor);
        BINARY_CASE(PtrMemD, Bdotp);
        BINARY_CASE(PtrMemI, Bdotip);
#undef BINARY_CASE
    default:
        return llvm::createStringError(
            std::errc::not_supported,
            "migration incomplete: binary expression kernel operation %s",
            value.getOpcodeStr().str().c_str());
    }
}

class ExpressionBuildScope {
public:
    explicit ExpressionBuildScope(State &state) : state(state) {
        if (state.expressionBuildDepth++ == 0) {
            state.nextOpaqueName = 0;
            state.arrayLoopIndexDepth = -1;
            state.activeCaptureInitializerClosures.clear();
            state.opaqueNames.clear();
            state.opaqueOrigins.clear();
            state.opaqueAnchors.clear();
            state.arrayLoopOrigins.clear();
        }
    }

    ~ExpressionBuildScope() { --state.expressionBuildDepth; }

private:
    State &state;
};

llvm::Expected<ScalarTerm> valueCategory(const clang::Expr &expression) {
    if (expression.isLValue())
        return ScalarTerm::symbol("Lvalue");
    if (expression.isPRValue())
        return ScalarTerm::symbol("Prvalue");
    if (expression.isXValue())
        return ScalarTerm::symbol("Xvalue");
    return llvm::createStringError(std::errc::not_supported,
                                   "cannot determine expression value "
                                   "category");
}

std::uint64_t anonymousLocalIndex(const clang::ValueDecl &target) {
    std::uint64_t index = 0;
    if (const auto *parameter = llvm::dyn_cast<clang::ParmVarDecl>(&target))
        if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(
                parameter->getDeclContext())) {
            for (const clang::ParmVarDecl *candidate : function->parameters()) {
                if (candidate == parameter)
                    return index;
                ++index;
            }
            return index;
        }
    if (const clang::DeclContext *context = target.getDeclContext())
        for (const clang::Decl *declaration : context->decls()) {
            if (declaration == &target)
                break;
            if (const auto *value =
                    llvm::dyn_cast<clang::ValueDecl>(declaration))
                if (!value->getIdentifier())
                    ++index;
        }
    return index;
}

std::string localIdentifier(const clang::ValueDecl &target) {
    std::string result = target.getNameAsString();
    const auto *parameter = llvm::dyn_cast<clang::ParmVarDecl>(&target);
    const auto *function =
        parameter
            ? llvm::dyn_cast<clang::FunctionDecl>(parameter->getDeclContext())
            : nullptr;
    if (!function)
        return result;
    const clang::IdentifierInfo *previous = nullptr;
    unsigned duplicateOffset = 0;
    for (const clang::ParmVarDecl *candidate : function->parameters()) {
        if (candidate->getIdentifier() == previous)
            ++duplicateOffset;
        else
            duplicateOffset = 0;
        if (candidate == parameter) {
            if (duplicateOffset)
                result += "..." + std::to_string(duplicateOffset);
            return result;
        }
        previous = candidate->getIdentifier();
    }
    return result;
}

bool ownedNodeIsDependent(State &state, NodeId node) {
    auto value = state.unit->buildingArena().get(node);
    if (!value)
        return true;
    switch ((*value)->constructor) {
    case Constructor::TypeParameter:
    case Constructor::TypeResultGlobal:
    case Constructor::TypeResultCall:
    case Constructor::TypeResultUnarySyntax:
    case Constructor::TypeResultMember:
    case Constructor::TypeAuto:
    case Constructor::ExpressionParameter:
    case Constructor::ExpressionUnresolvedGlobal:
    case Constructor::ExpressionUnresolvedUnary:
    case Constructor::ExpressionUnresolvedUnsupportedUnary:
    case Constructor::ExpressionUnresolvedUnarySyntax:
    case Constructor::ExpressionUnresolvedBinary:
    case Constructor::ExpressionUnresolvedBinarySyntax:
    case Constructor::ExpressionUnresolvedCompoundAssignment:
    case Constructor::ExpressionUnresolvedCall:
    case Constructor::ExpressionUnresolvedMember:
    case Constructor::ExpressionUnresolvedSizeofPack:
    case Constructor::ExpressionUnresolvedParenList:
    case Constructor::ExpressionUnresolvedInitList:
        return true;
    case Constructor::TypeUnsupported:
    case Constructor::NameUnsupported:
    case Constructor::TemplateArgumentTemplateParameter:
    case Constructor::TemplateArgumentUnsupported:
        return false;
    default:
        break;
    }
    auto children = state.unit->buildingArena().children(node);
    if (!children)
        return true;
    for (NodeId child : *children)
        if (ownedNodeIsDependent(state, child))
            return true;
    return false;
}

bool ownedTypeIsUnresolved(State &state, NodeId type) {
    auto value = state.unit->buildingArena().get(type);
    if (!value)
        return true;
    switch ((*value)->constructor) {
    case Constructor::TypeDecltype:
    case Constructor::TypeExpressionType:
    case Constructor::TypeAuto:
    case Constructor::TypeParameter:
    case Constructor::TypeResultCall:
    case Constructor::TypeResultUnarySyntax:
    case Constructor::TypeResultMember:
        return true;
    case Constructor::TypeQualified:
        if ((*value)->arguments.size() == 2)
            if (const auto *nested =
                    std::get_if<NodeRef>(&(*value)->arguments[1].payload))
                return ownedTypeIsUnresolved(state, nested->value);
        return true;
    case Constructor::TypeLvalueReference:
    case Constructor::TypeRvalueReference:
        if ((*value)->arguments.size() == 1)
            if (const auto *nested =
                    std::get_if<NodeRef>(&(*value)->arguments[0].payload))
                return ownedTypeIsUnresolved(state, nested->value);
        return true;
    default:
        return false;
    }
}

bool expressionTypeIsUnresolved(State &state, NodeId expression,
                                clang::QualType fallback) {
    auto value = state.unit->buildingArena().get(expression);
    if (!value)
        return true;
    switch ((*value)->constructor) {
    case Constructor::ExpressionParameter:
    case Constructor::ExpressionUnresolvedUnary:
    case Constructor::ExpressionUnresolvedUnsupportedUnary:
    case Constructor::ExpressionUnresolvedUnarySyntax:
    case Constructor::ExpressionUnresolvedBinary:
    case Constructor::ExpressionUnresolvedBinarySyntax:
    case Constructor::ExpressionUnresolvedCompoundAssignment:
    case Constructor::ExpressionUnresolvedCall:
    case Constructor::ExpressionUnresolvedMember:
        return true;
    case Constructor::ExpressionUnresolvedGlobal:
    case Constructor::ExpressionSequenceAnd:
    case Constructor::ExpressionSequenceOr:
        return false;
    case Constructor::ExpressionComma: {
        auto children = state.unit->buildingArena().children(expression);
        if (!children || children->empty())
            return true;
        return expressionTypeIsUnresolved(state, children->back(), {});
    }
    default:
        break;
    }
    for (auto argument = (*value)->arguments.rbegin();
         argument != (*value)->arguments.rend(); ++argument)
        if (const auto *reference = std::get_if<NodeRef>(&argument->payload)) {
            auto child = state.unit->buildingArena().get(reference->value);
            if (!child)
                return true;
            if ((*child)->category == Category::Type)
                return ownedTypeIsUnresolved(state, reference->value);
        }
    if (fallback.isNull())
        return true;
    fallback = fallback.getCanonicalType().getUnqualifiedType();
    if (!fallback->isDependentType())
        return false;
    if (fallback->isPointerType() || fallback->isArrayType() ||
        fallback->isMemberPointerType() || fallback->isFunctionType() ||
        fallback->isRecordType() || fallback->isEnumeralType() ||
        llvm::isa<clang::DependentNameType, clang::TemplateSpecializationType>(
            fallback.getTypePtr()))
        return false;
    return true;
}

llvm::Expected<NodeId> dropOwnedReference(State &state, NodeId type) {
    auto node = state.unit->buildingArena().get(type);
    if (!node)
        return node.takeError();
    if (((*node)->constructor == Constructor::TypeLvalueReference ||
         (*node)->constructor == Constructor::TypeRvalueReference) &&
        (*node)->arguments.size() == 1)
        if (const auto *nested =
                std::get_if<NodeRef>(&(*node)->arguments[0].payload))
            return nested->value;
    return type;
}

llvm::Expected<NodeId> ownedExpressionDecltype(State &state, NodeId expression,
                                               factory::OriginList origins) {
    auto node = state.unit->buildingArena().get(expression);
    if (!node)
        return node.takeError();
    auto directType =
        [&](const Node &value) -> llvm::Expected<std::optional<NodeId>> {
        for (auto argument = value.arguments.rbegin();
             argument != value.arguments.rend(); ++argument)
            if (const auto *reference =
                    std::get_if<NodeRef>(&argument->payload)) {
                auto child = state.unit->buildingArena().get(reference->value);
                if (!child)
                    return child.takeError();
                if ((*child)->category == Category::Type)
                    return std::optional<NodeId>{reference->value};
            }
        return std::nullopt;
    };
    auto lvalueReference = [&](NodeId type) -> llvm::Expected<NodeId> {
        auto value = state.unit->buildingArena().get(type);
        if (!value)
            return value.takeError();
        if ((*value)->constructor == Constructor::TypeLvalueReference)
            return type;
        if ((*value)->constructor == Constructor::TypeRvalueReference &&
            (*value)->arguments.size() == 1)
            if (const auto *nested =
                    std::get_if<NodeRef>(&(*value)->arguments[0].payload))
                type = nested->value;
        return factory::makeUnaryType(state.unit->buildingArena(),
                                      Constructor::TypeLvalueReference, origins,
                                      type);
    };
    switch ((*node)->constructor) {
    case Constructor::ExpressionLocalNamed:
    case Constructor::ExpressionLocalAnonymous:
    case Constructor::ExpressionGlobal:
    case Constructor::ExpressionPreIncrement:
    case Constructor::ExpressionPreDecrement: {
        auto type = directType(**node);
        if (!type)
            return type.takeError();
        if (*type)
            return lvalueReference(**type);
        break;
    }
    case Constructor::ExpressionDeref: {
        if ((*node)->arguments.empty())
            break;
        const auto *operand =
            std::get_if<NodeRef>(&(*node)->arguments[0].payload);
        if (!operand)
            break;
        auto operandType =
            ownedExpressionDecltype(state, operand->value, origins);
        if (!operandType)
            return operandType.takeError();
        auto pointerType = dropOwnedReference(state, *operandType);
        if (!pointerType)
            return pointerType.takeError();
        auto pointer = state.unit->buildingArena().get(*pointerType);
        if (!pointer)
            return pointer.takeError();
        if ((*pointer)->constructor == Constructor::TypePointer &&
            (*pointer)->arguments.size() == 1)
            if (const auto *pointee =
                    std::get_if<NodeRef>(&(*pointer)->arguments[0].payload))
                return lvalueReference(pointee->value);
        auto type = directType(**node);
        if (!type)
            return type.takeError();
        if (*type)
            return lvalueReference(**type);
        break;
    }
    case Constructor::ExpressionMember: {
        if ((*node)->arguments.size() != 5)
            break;
        const auto *object =
            std::get_if<NodeRef>(&(*node)->arguments[1].payload);
        const auto *isMutable =
            std::get_if<ScalarTerm>(&(*node)->arguments[3].payload);
        auto fieldType = directType(**node);
        if (!fieldType)
            return fieldType.takeError();
        if (!object || !isMutable || !*fieldType)
            break;
        auto objectDeclarationType =
            ownedExpressionDecltype(state, object->value, origins);
        if (!objectDeclarationType)
            return objectDeclarationType.takeError();
        auto objectType = dropOwnedReference(state, *objectDeclarationType);
        if (!objectType)
            return objectType.takeError();
        const auto *arrow =
            std::get_if<ScalarTerm>(&(*node)->arguments[0].payload);
        if (arrow && arrow->text == "true") {
            auto pointer = state.unit->buildingArena().get(*objectType);
            if (!pointer)
                return pointer.takeError();
            if ((*pointer)->constructor == Constructor::TypePointer &&
                (*pointer)->arguments.size() == 1)
                if (const auto *pointee =
                        std::get_if<NodeRef>(&(*pointer)->arguments[0].payload))
                    objectType = pointee->value;
        }
        unsigned qualifiers = 0;
        auto qualifiedObject = state.unit->buildingArena().get(*objectType);
        if (!qualifiedObject)
            return qualifiedObject.takeError();
        if ((*qualifiedObject)->constructor == Constructor::TypeQualified &&
            !(*qualifiedObject)->arguments.empty())
            if (const auto *qualifier = std::get_if<ScalarTerm>(
                    &(*qualifiedObject)->arguments[0].payload))
                qualifiers = qualifier->text == "QC"   ? 1U
                             : qualifier->text == "QV" ? 2U
                                                       : 3U;
        if (isMutable->text == "true")
            qualifiers &= ~1U;
        NodeId memberType = **fieldType;
        if (qualifiers) {
            auto qualifiedField = state.unit->buildingArena().get(memberType);
            if (!qualifiedField)
                return qualifiedField.takeError();
            if ((*qualifiedField)->constructor == Constructor::TypeQualified &&
                (*qualifiedField)->arguments.size() == 2) {
                if (const auto *qualifier = std::get_if<ScalarTerm>(
                        &(*qualifiedField)->arguments[0].payload))
                    qualifiers |= qualifier->text == "QC"   ? 1U
                                  : qualifier->text == "QV" ? 2U
                                                            : 3U;
                if (const auto *nested = std::get_if<NodeRef>(
                        &(*qualifiedField)->arguments[1].payload))
                    memberType = nested->value;
            }
            const char *qualifier = qualifiers == 1   ? "QC"
                                    : qualifiers == 2 ? "QV"
                                                      : "QCV";
            auto combined = factory::makeQualifiedType(
                state.unit->buildingArena(), origins,
                ScalarTerm::symbol(qualifier), memberType);
            if (!combined)
                return combined.takeError();
            memberType = *combined;
        }
        return lvalueReference(memberType);
    }
    case Constructor::ExpressionCast: {
        if ((*node)->arguments.size() != 2)
            break;
        const auto *cast = std::get_if<NodeRef>(&(*node)->arguments[0].payload);
        const auto *operand =
            std::get_if<NodeRef>(&(*node)->arguments[1].payload);
        if (!cast || !operand)
            break;
        auto castNode = state.unit->buildingArena().get(cast->value);
        if (!castNode)
            return castNode.takeError();
        auto castType = directType(**castNode);
        if (!castType)
            return castType.takeError();
        if (*castType)
            return **castType;
        auto operandType =
            ownedExpressionDecltype(state, operand->value, origins);
        if (!operandType)
            return operandType.takeError();
        switch ((*castNode)->constructor) {
        case Constructor::CastLvalueToRvalue: {
            auto type = dropOwnedReference(state, *operandType);
            if (!type)
                return type.takeError();
            auto value = state.unit->buildingArena().get(*type);
            if (!value)
                return value.takeError();
            if ((*value)->constructor == Constructor::TypeQualified &&
                (*value)->arguments.size() == 2)
                if (const auto *nested =
                        std::get_if<NodeRef>(&(*value)->arguments[1].payload))
                    return nested->value;
            return *type;
        }
        case Constructor::CastUserDefinedConversion:
            return *operandType;
        case Constructor::CastFunctionToPointer: {
            auto function = dropOwnedReference(state, *operandType);
            if (!function)
                return function.takeError();
            return factory::makeUnaryType(state.unit->buildingArena(),
                                          Constructor::TypePointer, origins,
                                          *function);
        }
        default:
            break;
        }
        break;
    }
    default:
        break;
    }
    auto type = directType(**node);
    if (!type)
        return type.takeError();
    if (*type)
        return **type;
    switch ((*node)->constructor) {
    case Constructor::ExpressionUnresolvedGlobal: {
        if ((*node)->arguments.size() != 1)
            break;
        if (const auto *name =
                std::get_if<NodeRef>(&(*node)->arguments[0].payload))
            return factory::makeResultGlobalType(
                state.unit->buildingArena(), std::move(origins), name->value);
        break;
    }
    case Constructor::ExpressionUnresolvedCall: {
        if ((*node)->arguments.size() != 2)
            break;
        const auto *name = std::get_if<NodeRef>(&(*node)->arguments[0].payload);
        const auto *arguments =
            std::get_if<SequenceValue>(&(*node)->arguments[1].payload);
        if (!name || !arguments)
            break;
        std::vector<NodeId> types;
        types.reserve(arguments->elements.size());
        for (const Value &argument : arguments->elements) {
            const auto *value = std::get_if<NodeRef>(&argument.payload);
            if (!value)
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "unresolved call has a non-expression argument");
            auto type = ownedExpressionDecltype(state, value->value, origins);
            if (!type)
                return type.takeError();
            types.push_back(*type);
        }
        return factory::makeResultCallType(state.unit->buildingArena(),
                                           std::move(origins), name->value,
                                           std::move(types));
    }
    case Constructor::ExpressionUnresolvedMember: {
        if ((*node)->arguments.size() != 2)
            break;
        const auto *object =
            std::get_if<NodeRef>(&(*node)->arguments[0].payload);
        const auto *name = std::get_if<NodeRef>(&(*node)->arguments[1].payload);
        if (!object || !name)
            break;
        auto type = ownedExpressionDecltype(state, object->value, origins);
        if (!type)
            return type.takeError();
        return factory::makeResultMemberType(state.unit->buildingArena(),
                                             std::move(origins), *type,
                                             name->value);
    }
    case Constructor::ExpressionUnresolvedUnarySyntax: {
        if ((*node)->arguments.size() != 2)
            break;
        const auto *operation =
            std::get_if<ScalarTerm>(&(*node)->arguments[0].payload);
        const auto *operand =
            std::get_if<NodeRef>(&(*node)->arguments[1].payload);
        if (!operation || !operand)
            break;
        auto type = ownedExpressionDecltype(state, operand->value, origins);
        if (!type)
            return type.takeError();
        return factory::makeResultUnarySyntaxType(
            state.unit->buildingArena(), std::move(origins), *operation, *type);
    }
    default:
        break;
    }
    return factory::makeLeafType(state.unit->buildingArena(),
                                 Constructor::TypeAuto, std::move(origins));
}

llvm::Expected<factory::OriginList>
expressionOrigins(State &state, const clang::Expr &expression) {
    if (!state.generatedExpressionAnchors.empty()) {
        const source::OriginId anchor = state.generatedExpressionAnchors.back();
        auto implicit = state.sources.anchoredImplicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            anchor, {anchor});
        if (!implicit)
            return implicit.takeError();
        return factory::OriginList{*implicit};
    }
    if (!state.arrayLoopOrigins.empty()) {
        auto implicit = state.sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            {state.arrayLoopOrigins.back()});
        if (!implicit)
            return implicit.takeError();
        return factory::OriginList{*implicit};
    }
    auto origin = state.sources.explicitNode(expression.getSourceRange());
    if (!origin)
        return origin.takeError();
    return factory::OriginList{*origin};
}

llvm::Expected<NodeId>
buildBuiltinReference(State &state, const clang::Expr &written,
                      const clang::DeclRefExpr &reference,
                      clang::QualType functionType, SemanticMode mode) {
    const auto *function =
        llvm::dyn_cast<clang::FunctionDecl>(reference.getDecl());
    if (!function || function->getBuiltinID() == clang::Builtin::NotBuiltin)
        return expressionError(written, "non-builtin reference");
    if (const auto *pointer = functionType->getAs<clang::PointerType>())
        functionType = pointer->getPointeeType();

    auto rootOrigin = state.sources.explicitNode(written.getSourceRange());
    if (!rootOrigin)
        return rootOrigin.takeError();
    auto referenceOrigin =
        state.sources.explicitNode(reference.getSourceRange());
    if (!referenceOrigin)
        return referenceOrigin.takeError();
    auto synthetic = state.sources.synthesizedNode(*rootOrigin, {*rootOrigin});
    if (!synthetic)
        return synthetic.takeError();

    auto inherited = state.inheritedTypeOrigins(functionType, {*rootOrigin});
    if (!inherited)
        return inherited.takeError();
    auto type = state.buildType(functionType, mode, std::move(*inherited));
    if (!type)
        return type.takeError();
    auto name = state.buildName(*function, mode);
    if (!name)
        return name.takeError();
    auto global = factory::makeGlobalExpression(
        state.unit->buildingArena(), {*referenceOrigin}, *name, *type, false);
    if (!global)
        return global.takeError();
    auto pointer =
        factory::makeUnaryType(state.unit->buildingArena(),
                               Constructor::TypePointer, {*synthetic}, *type);
    if (!pointer)
        return pointer.takeError();
    auto cast = factory::makeBuiltinToFunctionCast(state.unit->buildingArena(),
                                                   {*synthetic}, *pointer);
    if (!cast)
        return cast.takeError();
    return factory::makeCastExpression(state.unit->buildingArena(),
                                       {*rootOrigin}, *cast, *global);
}

llvm::Expected<NodeId> forwardExpression(State &state,
                                         const clang::Expr &wrapper,
                                         const clang::Expr &child,
                                         SemanticMode mode) {
    auto value = state.buildExpression(child, mode);
    if (!value)
        return value.takeError();
    auto node = state.unit->buildingArena().get(*value);
    if (!node)
        return node.takeError();
    auto transformed = state.sources.transformedNode(
        clang::CharSourceRange::getTokenRange(wrapper.getSourceRange()),
        (*node)->origins);
    if (!transformed)
        return transformed.takeError();
    return factory::cloneWithOrigins(state.unit->buildingArena(), *value,
                                     {*transformed});
}

llvm::Expected<NodeId> buildDeclType(State &state,
                                     const clang::Expr &expression,
                                     SemanticMode mode,
                                     const factory::OriginList &origins) {
    clang::QualType type = expression.getType();
    if (type.isNull())
        return factory::makeLeafType(state.unit->buildingArena(),
                                     Constructor::TypeAuto, origins);
    auto inherited = state.inheritedTypeOrigins(type, origins);
    if (!inherited)
        return inherited.takeError();
    auto value = state.buildType(type, mode, std::move(*inherited));
    if (!value)
        return value.takeError();
    if (!expression.isLValue() && !expression.isXValue())
        return *value;
    return factory::makeUnaryType(state.unit->buildingArena(),
                                  expression.isLValue()
                                      ? Constructor::TypeLvalueReference
                                      : Constructor::TypeRvalueReference,
                                  origins, *value);
}

llvm::Expected<NodeId> buildUnsupportedExpression(State &state,
                                                  const clang::Expr &expression,
                                                  SemanticMode mode,
                                                  factory::OriginList origins,
                                                  std::string diagnostic) {
    auto type = buildDeclType(state, expression, mode, origins);
    if (!type)
        return type.takeError();
    return factory::makeUnsupportedExpression(state.unit->buildingArena(),
                                              std::move(origins),
                                              std::move(diagnostic), *type);
}

struct LambdaContext {
    const clang::CXXRecordDecl *closure;
    bool isConst;
    bool isVolatile;
};

std::optional<LambdaContext>
enclosingLambda(clang::ASTContext &context, const clang::Expr &expression,
                llvm::ArrayRef<const clang::CXXRecordDecl *> skippedClosures) {
    clang::DynTypedNode current = clang::DynTypedNode::create(expression);
    for (unsigned depth = 0; depth != 64; ++depth) {
        const auto parents = context.getParents(current);
        if (parents.empty())
            return std::nullopt;
        for (const clang::DynTypedNode &parent : parents) {
            if (const auto *lambda = parent.get<clang::LambdaExpr>()) {
                const clang::CXXRecordDecl *closure = lambda->getLambdaClass();
                if (std::find(skippedClosures.begin(), skippedClosures.end(),
                              closure) == skippedClosures.end()) {
                    const clang::CXXMethodDecl *call =
                        lambda->getCallOperator();
                    return LambdaContext{
                        closure, call && call->getMethodQualifiers().hasConst(),
                        call && call->getMethodQualifiers().hasVolatile()};
                }
            }
            if (const auto *method = parent.get<clang::CXXMethodDecl>()) {
                const clang::CXXRecordDecl *closure = method->getParent();
                if (closure && closure->isLambda() &&
                    std::find(skippedClosures.begin(), skippedClosures.end(),
                              closure) == skippedClosures.end())
                    return LambdaContext{
                        closure, method->getMethodQualifiers().hasConst(),
                        method->getMethodQualifiers().hasVolatile()};
            }
        }
        current = parents[0];
    }
    return std::nullopt;
}

const clang::FieldDecl *captureField(const clang::CXXRecordDecl &closure,
                                     const clang::ValueDecl &variable) {
    llvm::DenseMap<const clang::ValueDecl *, clang::FieldDecl *> captures;
    clang::FieldDecl *thisCapture = nullptr;
    closure.getCaptureFields(captures, thisCapture);
    const auto found = captures.find(&variable);
    return found == captures.end() ? nullptr : found->second;
}

const clang::FieldDecl *thisCaptureField(const clang::CXXRecordDecl &closure) {
    llvm::DenseMap<const clang::ValueDecl *, clang::FieldDecl *> captures;
    clang::FieldDecl *thisCapture = nullptr;
    closure.getCaptureFields(captures, thisCapture);
    return thisCapture;
}

ScalarTerm lambdaQualifier(const LambdaContext &lambda) {
    if (lambda.isConst && lambda.isVolatile)
        return ScalarTerm::symbol("QCV");
    if (lambda.isConst)
        return ScalarTerm::symbol("QC");
    if (lambda.isVolatile)
        return ScalarTerm::symbol("QV");
    return ScalarTerm::symbol("QM");
}

llvm::Expected<NodeId> buildLambdaThis(State &state,
                                       const LambdaContext &lambda,
                                       SemanticMode mode,
                                       source::OriginId generated) {
    auto name = state.buildName(*lambda.closure, mode);
    if (!name)
        return name.takeError();
    auto named =
        factory::makeNamedType(state.unit->buildingArena(), {generated}, *name);
    if (!named)
        return named.takeError();
    NodeId objectType = *named;
    if (lambda.isConst || lambda.isVolatile) {
        auto qualified =
            factory::makeQualifiedType(state.unit->buildingArena(), {generated},
                                       lambdaQualifier(lambda), objectType);
        if (!qualified)
            return qualified.takeError();
        objectType = *qualified;
    }
    auto pointer = factory::makeUnaryType(state.unit->buildingArena(),
                                          Constructor::TypePointer, {generated},
                                          objectType);
    if (!pointer)
        return pointer.takeError();
    return factory::makeThisExpression(state.unit->buildingArena(), {generated},
                                       *pointer);
}

llvm::Expected<NodeId>
buildCaptureMember(State &state, const LambdaContext &lambda,
                   const clang::FieldDecl &field, llvm::StringRef fieldName,
                   SemanticMode mode, factory::OriginList memberOrigins,
                   source::OriginId generated) {
    auto object = buildLambdaThis(state, lambda, mode, generated);
    if (!object)
        return object.takeError();
    auto atomic = factory::makeAtomicIdentifier(state.unit->buildingArena(),
                                                {generated}, fieldName.str());
    if (!atomic)
        return atomic.takeError();
    auto inherited = state.inheritedTypeOrigins(field.getType(), {generated});
    if (!inherited)
        return inherited.takeError();
    auto type = state.buildType(field.getType(), mode, std::move(*inherited));
    if (!type)
        return type.takeError();
    return factory::makeMemberExpression(state.unit->buildingArena(),
                                         std::move(memberOrigins), true,
                                         *object, *atomic, false, *type);
}

llvm::Expected<NodeId> applyInitializingTypeValue(State &state,
                                                  NodeId initializer,
                                                  clang::QualType targetType,
                                                  SemanticMode mode,
                                                  source::OriginId generated) {
    auto node = state.unit->buildingArena().get(initializer);
    if (!node)
        return node.takeError();
    const Constructor constructor = (*node)->constructor;
    if (constructor != Constructor::ExpressionUnresolvedParenList &&
        constructor != Constructor::ExpressionUnresolvedInitList)
        return initializer;
    if ((*node)->arguments.size() != 2)
        return llvm::createStringError(
            std::errc::invalid_argument,
            "lambda initializing-type expression has the wrong arity");
    const auto *optional =
        std::get_if<OptionalValue>(&(*node)->arguments[0].payload);
    const auto *sequence =
        std::get_if<SequenceValue>(&(*node)->arguments[1].payload);
    if (!optional || !sequence)
        return llvm::createStringError(
            std::errc::invalid_argument,
            "lambda initializing-type expression has malformed IR");
    if (optional->value)
        return initializer;
    std::vector<NodeId> expressions;
    expressions.reserve(sequence->elements.size());
    for (const Value &value : sequence->elements) {
        const auto *reference = std::get_if<NodeRef>(&value.payload);
        if (!reference)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "lambda initializing-type list has a non-node element");
        expressions.push_back(reference->value);
    }
    const factory::OriginList origins = (*node)->origins;
    auto inherited = state.inheritedTypeOrigins(targetType, {generated});
    if (!inherited)
        return inherited.takeError();
    auto type = state.buildType(targetType, mode, std::move(*inherited));
    if (!type)
        return type.takeError();
    return factory::makeUnresolvedInitializerListExpression(
        state.unit->buildingArena(), origins, constructor, *type,
        std::move(expressions));
}

llvm::Expected<NodeId> buildCastDescriptor(State &state,
                                           const clang::CastExpr &cast,
                                           SemanticMode mode,
                                           factory::OriginList origins) {
    auto typeCast = [&](Constructor constructor) -> llvm::Expected<NodeId> {
        auto type = buildDeclType(state, cast, mode, origins);
        if (!type)
            return type.takeError();
        return factory::makeTypeCast(state.unit->buildingArena(), constructor,
                                     origins, *type);
    };
    auto nullary = [&](Constructor constructor) {
        return factory::makeNullaryCast(state.unit->buildingArena(),
                                        constructor, origins);
    };
    switch (cast.getCastKind()) {
    case clang::CK_BitCast:
        return typeCast(Constructor::CastBit);
    case clang::CK_LValueBitCast:
        return typeCast(Constructor::CastLvalueBit);
    case clang::CK_LValueToRValue:
        return nullary(Constructor::CastLvalueToRvalue);
    case clang::CK_LValueToRValueBitCast:
        return typeCast(Constructor::CastLvalueToRvalueBit);
    case clang::CK_NoOp:
        return typeCast(Constructor::CastNoOp);
    case clang::CK_ArrayToPointerDecay:
        return nullary(Constructor::CastArrayToPointer);
    case clang::CK_FunctionToPointerDecay:
        return nullary(Constructor::CastFunctionToPointer);
    case clang::CK_IntegralToPointer:
        return typeCast(Constructor::CastIntegralToPointer);
    case clang::CK_PointerToIntegral:
        return typeCast(Constructor::CastPointerToIntegral);
    case clang::CK_PointerToBoolean:
        return nullary(Constructor::CastPointerToBoolean);
    case clang::CK_IntegralCast:
        return typeCast(Constructor::CastIntegral);
    case clang::CK_IntegralToBoolean:
        return nullary(Constructor::CastIntegralToBoolean);
    case clang::CK_FloatingToBoolean:
        return nullary(Constructor::CastFloatingToBoolean);
    case clang::CK_NullToPointer:
        return typeCast(Constructor::CastNullToPointer);
    case clang::CK_NullToMemberPointer:
        return typeCast(Constructor::CastNullToMemberPointer);
    case clang::CK_BuiltinFnToFnPtr:
        return typeCast(Constructor::CastBuiltinToFunction);
    case clang::CK_ConstructorConversion:
        return typeCast(Constructor::CastConstructorConversion);
    case clang::CK_UserDefinedConversion:
        return nullary(Constructor::CastUserDefinedConversion);
    case clang::CK_ToVoid:
        return nullary(Constructor::CastToVoid);
    case clang::CK_Dynamic:
        return typeCast(Constructor::CastDynamic);
    case clang::CK_FloatingToIntegral:
        return typeCast(Constructor::CastFloatingToIntegral);
    case clang::CK_IntegralToFloating:
        return typeCast(Constructor::CastIntegralToFloating);
    case clang::CK_FloatingCast:
        return typeCast(Constructor::CastFloating);
    case clang::CK_Dependent:
        return typeCast(Constructor::CastDependent);
    case clang::CK_DerivedToBase:
    case clang::CK_UncheckedDerivedToBase:
    case clang::CK_BaseToDerived: {
        std::vector<NodeId> path;
        const auto begin = cast.path_begin();
        const auto end = cast.path_end();
        if (begin != end)
            for (auto current = begin; current != end - 1; ++current) {
                clang::QualType type = (*current)->getType();
                auto inherited = state.inheritedTypeOrigins(type, origins);
                if (!inherited)
                    return inherited.takeError();
                auto value = state.buildType(type, mode, std::move(*inherited));
                if (!value)
                    return value.takeError();
                path.push_back(*value);
            }
        auto target = buildDeclType(state, cast, mode, origins);
        if (!target)
            return target.takeError();
        const Constructor constructor =
            cast.getCastKind() == clang::CK_BaseToDerived
                ? Constructor::CastBaseToDerived
                : Constructor::CastDerivedToBase;
        return factory::makePathCast(state.unit->buildingArena(), constructor,
                                     std::move(origins), std::move(path),
                                     *target);
    }
    default: {
        auto type = buildDeclType(state, cast, mode, origins);
        if (!type)
            return type.takeError();
        return factory::makeUnsupportedCast(state.unit->buildingArena(),
                                            std::move(origins),
                                            cast.getCastKindName(), *type);
    }
    }
}

std::optional<ScalarTerm>
explicitCastStyle(const clang::ExplicitCastExpr &cast) {
    if (llvm::isa<clang::CStyleCastExpr>(&cast))
        return ScalarTerm::symbol("cast_style.c");
    if (llvm::isa<clang::CXXFunctionalCastExpr>(&cast) ||
        llvm::isa<clang::BuiltinBitCastExpr>(&cast))
        return ScalarTerm::symbol("cast_style.functional");
    if (const auto *named = llvm::dyn_cast<clang::CXXNamedCastExpr>(&cast)) {
        const llvm::StringRef name = named->getCastName();
        if (name == "dynamic_cast")
            return ScalarTerm::symbol("cast_style.dynamic");
        if (name == "static_cast")
            return ScalarTerm::symbol("cast_style.static");
        if (name == "const_cast")
            return ScalarTerm::symbol("cast_style.const");
        if (name == "reinterpret_cast")
            return ScalarTerm::symbol("cast_style.reinterpret");
    }
    return std::nullopt;
}

llvm::Expected<NodeId> buildCastExpression(State &state,
                                           const clang::CastExpr &cast,
                                           SemanticMode mode) {
    const auto *explicitCast = llvm::dyn_cast<clang::ExplicitCastExpr>(&cast);
    std::optional<ScalarTerm> style;
    if (explicitCast) {
        style = explicitCastStyle(*explicitCast);
        if (!style) {
            auto origins = expressionOrigins(state, cast);
            if (!origins)
                return origins.takeError();
            return buildUnsupportedExpression(state, cast, mode,
                                              std::move(*origins),
                                              cast.getStmtClassName());
        }
    }

    auto operand = state.buildExpression(*cast.getSubExpr(), mode);
    if (!operand)
        return operand.takeError();
    auto operandNode = state.unit->buildingArena().get(*operand);
    if (!operandNode)
        return operandNode.takeError();

    if (explicitCast) {
        auto direct = state.sources.explicitNode(cast.getSourceRange());
        if (!direct)
            return direct.takeError();
        auto synthetic = state.sources.synthesizedNode(*direct, {*direct});
        if (!synthetic)
            return synthetic.takeError();
        auto descriptor = buildCastDescriptor(state, cast, mode, {*synthetic});
        if (!descriptor)
            return descriptor.takeError();
        auto inner = factory::makeCastExpression(
            state.unit->buildingArena(), {*synthetic}, *descriptor, *operand);
        if (!inner)
            return inner.takeError();
        const clang::TypeSourceInfo *written =
            explicitCast->getTypeInfoAsWritten();
        if (!written)
            return buildUnsupportedExpression(state, cast, mode, {*direct},
                                              cast.getStmtClassName());
        auto type = state.buildTypeLoc(written->getTypeLoc(), mode, {*direct});
        if (!type)
            return type.takeError();
        return factory::makeExplicitCastExpression(state.unit->buildingArena(),
                                                   {*direct}, std::move(*style),
                                                   *type, *inner);
    }

    auto implicit = state.sources.implicitNode(
        clang::CharSourceRange::getTokenRange(cast.getSourceRange()),
        (*operandNode)->origins);
    if (!implicit)
        return implicit.takeError();
    auto descriptor = buildCastDescriptor(state, cast, mode, {*implicit});
    if (!descriptor)
        return descriptor.takeError();
    return factory::makeCastExpression(state.unit->buildingArena(), {*implicit},
                                       *descriptor, *operand);
}

const char *floatSemanticsName(llvm::APFloatBase::Semantics semantics) {
    switch (semantics) {
    case llvm::APFloatBase::S_IEEEhalf:
        return "IEEEhalf";
    case llvm::APFloatBase::S_BFloat:
        return "BFloat";
    case llvm::APFloatBase::S_IEEEsingle:
        return "IEEEsingle";
    case llvm::APFloatBase::S_IEEEdouble:
        return "IEEEdouble";
    case llvm::APFloatBase::S_IEEEquad:
        return "IEEEquad";
    case llvm::APFloatBase::S_PPCDoubleDouble:
        return "PPCDoubleDouble";
    case llvm::APFloatBase::S_x87DoubleExtended:
        return "x87DoubleExtended";
    default:
        return "unknown";
    }
}

const char *builtinFloatName(const clang::BuiltinType *type) {
    if (!type)
        return "non-builtin";
    switch (type->getKind()) {
    case clang::BuiltinType::Float16:
        return "Float16";
    case clang::BuiltinType::Float:
        return "Float";
    case clang::BuiltinType::Double:
        return "Double";
    case clang::BuiltinType::LongDouble:
        return "LongDouble";
    case clang::BuiltinType::Float128:
        return "Float128";
    default:
        return "other-builtin";
    }
}

std::vector<std::uint64_t>
stringCharacters(const clang::StringLiteral &literal) {
    const llvm::StringRef bytes = literal.getBytes();
    const unsigned width = literal.getCharByteWidth();
    std::vector<std::uint64_t> result;
    result.reserve(width ? literal.getByteLength() / width : 0);
    for (unsigned index = 0; index < literal.getByteLength();) {
        std::uint64_t character = 0;
        if (llvm::endianness::native == llvm::endianness::big) {
            for (unsigned byte = 0; byte < width; ++byte)
                character = (character << 8) |
                            static_cast<unsigned char>(bytes[index++]);
        } else {
            for (unsigned byte = 0; byte < width; ++byte)
                character =
                    (character << 8) |
                    static_cast<unsigned char>(bytes[index + width - byte - 1]);
            index += width;
        }
        result.push_back(character);
    }
    return result;
}

} // namespace

llvm::Expected<NodeId>
State::applyInitializingType(NodeId initializer, clang::QualType targetType,
                             SemanticMode mode, source::OriginId generated) {
    return applyInitializingTypeValue(*this, initializer, targetType, mode,
                                      generated);
}

llvm::Expected<NodeId> State::buildExpression(const clang::Expr &expression,
                                              SemanticMode mode) {
    ExpressionBuildScope expressionScope(*this);
    if (const auto *cast = llvm::dyn_cast<clang::CastExpr>(&expression)) {
        if (cast->getCastKind() == clang::CK_BuiltinFnToFnPtr)
            if (const auto *reference =
                    llvm::dyn_cast<clang::DeclRefExpr>(cast->getSubExpr()))
                if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(
                        reference->getDecl()))
                    if (function->getBuiltinID() != clang::Builtin::NotBuiltin)
                        return buildBuiltinReference(*this, expression,
                                                     *reference,
                                                     cast->getType(), mode);
        return buildCastExpression(*this, *cast, mode);
    }
    if (const auto *rewritten =
            llvm::dyn_cast<clang::CXXRewrittenBinaryOperator>(&expression))
        return forwardExpression(*this, expression,
                                 *rewritten->getSemanticForm(), mode);
    if (const auto *parenthesized =
            llvm::dyn_cast<clang::ParenExpr>(&expression))
        return forwardExpression(*this, expression,
                                 *parenthesized->getSubExpr(), mode);
    if (const auto *constant = llvm::dyn_cast<clang::ConstantExpr>(&expression))
        return forwardExpression(*this, expression, *constant->getSubExpr(),
                                 mode);
    if (const auto *defaultInit =
            llvm::dyn_cast<clang::CXXDefaultInitExpr>(&expression))
        return forwardExpression(*this, expression, *defaultInit->getExpr(),
                                 mode);
    if (const auto *temporary =
            llvm::dyn_cast<clang::CXXBindTemporaryExpr>(&expression))
        return forwardExpression(*this, expression, *temporary->getSubExpr(),
                                 mode);
    if (const auto *transparent =
            llvm::dyn_cast<clang::InitListExpr>(&expression))
        if (transparent->isTransparent()) {
            if (transparent->getNumInits() != 1)
                return expressionError(expression,
                                       "transparent initializer list arity");
            return forwardExpression(*this, expression,
                                     *transparent->getInit(0), mode);
        }
    if (const auto *cleanups =
            llvm::dyn_cast<clang::ExprWithCleanups>(&expression)) {
        auto child = buildExpression(*cleanups->getSubExpr(), mode);
        if (!child)
            return child.takeError();
        auto node = unit->buildingArena().get(*child);
        if (!node)
            return node.takeError();
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            (*node)->origins);
        if (!implicit)
            return implicit.takeError();
        return factory::makeAndCleanExpression(unit->buildingArena(),
                                               {*implicit}, *child);
    }
    if (const auto *materialized =
            llvm::dyn_cast<clang::MaterializeTemporaryExpr>(&expression)) {
        if (materialized->getExtendingDecl()) {
            auto written = sources.explicitNode(expression.getSourceRange());
            if (!written)
                return written.takeError();
            auto implicit =
                sources.implicitNode(clang::CharSourceRange::getTokenRange(
                                         expression.getSourceRange()),
                                     {*written});
            if (!implicit)
                return implicit.takeError();
            return buildUnsupportedExpression(*this, expression, mode,
                                              {*implicit},
                                              expression.getStmtClassName());
        }
        auto child = buildExpression(*materialized->getSubExpr(), mode);
        if (!child)
            return child.takeError();
        auto node = unit->buildingArena().get(*child);
        if (!node)
            return node.takeError();
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            (*node)->origins);
        if (!implicit)
            return implicit.takeError();
        auto category = valueCategory(expression);
        if (!category)
            return category.takeError();
        return factory::makeMaterializeTemporaryExpression(
            unit->buildingArena(), {*implicit}, *child, std::move(*category));
    }
    if (llvm::isa<clang::ImplicitValueInitExpr>(&expression)) {
        auto written = sources.explicitNode(expression.getSourceRange());
        if (!written)
            return written.takeError();
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            {*written});
        if (!implicit)
            return implicit.takeError();
        auto inherited =
            inheritedTypeOrigins(expression.getType(), {*implicit});
        if (!inherited)
            return inherited.takeError();
        auto type =
            buildType(expression.getType(), mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        return factory::makeImplicitInitExpression(unit->buildingArena(),
                                                   {*implicit}, *type);
    }
    if (llvm::isa<clang::ArrayInitIndexExpr>(&expression)) {
        if (arrayLoopIndexDepth < 0 || arrayLoopOrigins.empty())
            return expressionError(expression,
                                   "array initializer index outside loop");
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            {arrayLoopOrigins.back()});
        if (!implicit)
            return implicit.takeError();
        auto inherited =
            inheritedTypeOrigins(expression.getType(), {*implicit});
        if (!inherited)
            return inherited.takeError();
        auto type =
            buildType(expression.getType(), mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        return factory::makeArrayLoopIndexExpression(
            unit->buildingArena(), {*implicit},
            static_cast<std::uint64_t>(arrayLoopIndexDepth), *type);
    }
    if (const auto *opaque =
            llvm::dyn_cast<clang::OpaqueValueExpr>(&expression)) {
        const auto found = opaqueNames.find(opaque);
        const auto origin = opaqueOrigins.find(opaque);
        const auto anchor = opaqueAnchors.find(opaque);
        if (found == opaqueNames.end() || origin == opaqueOrigins.end() ||
            anchor == opaqueAnchors.end())
            return expressionError(expression, "unbound opaque reference");
        auto implicit = sources.anchoredImplicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            anchor->second, {origin->second});
        if (!implicit)
            return implicit.takeError();
        auto type = buildDeclType(*this, expression, mode, {*implicit});
        if (!type)
            return type.takeError();
        return factory::makeOpaqueReferenceExpression(
            unit->buildingArena(), {*implicit}, found->second, *type);
    }
    if (const auto *substitution =
            llvm::dyn_cast<clang::SubstNonTypeTemplateParmExpr>(&expression))
        return forwardExpression(*this, expression,
                                 *substitution->getReplacement(), mode);
    if (const auto *defaultArgument =
            llvm::dyn_cast<clang::CXXDefaultArgExpr>(&expression)) {
        auto value = buildExpression(*defaultArgument->getExpr(), mode);
        if (!value)
            return value.takeError();
        auto node = unit->buildingArena().get(*value);
        if (!node)
            return node.takeError();
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            (*node)->origins);
        if (!implicit)
            return implicit.takeError();
        return factory::makeImplicitExpression(unit->buildingArena(),
                                               {*implicit}, *value);
    }
    if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(&expression)) {
        if (unary->getOpcode() == clang::UO_Extension)
            return forwardExpression(*this, expression, *unary->getSubExpr(),
                                     mode);
    }

    auto origins = expressionOrigins(*this, expression);
    if (!origins)
        return origins.takeError();
    auto semanticType = [&](clang::QualType type) -> llvm::Expected<NodeId> {
        auto inherited = inheritedTypeOrigins(type, *origins);
        if (!inherited)
            return inherited.takeError();
        return buildType(type, mode, std::move(*inherited));
    };
    auto expressionType = [&]() -> llvm::Expected<NodeId> {
        return semanticType(expression.getType());
    };
    auto synthesizedOrigins = [&]() -> llvm::Expected<factory::OriginList> {
        auto synthetic = sources.synthesizedNode(origins->front(), *origins);
        if (!synthetic)
            return synthetic.takeError();
        return factory::OriginList{*synthetic};
    };
    if (const auto *conditional =
            llvm::dyn_cast<clang::ConditionalOperator>(&expression)) {
        auto condition = buildExpression(*conditional->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto whenTrue = buildExpression(*conditional->getTrueExpr(), mode);
        if (!whenTrue)
            return whenTrue.takeError();
        auto whenFalse = buildExpression(*conditional->getFalseExpr(), mode);
        if (!whenFalse)
            return whenFalse.takeError();
        auto type = buildDeclType(*this, expression, mode, *origins);
        if (!type)
            return type.takeError();
        return factory::makeConditionalExpression(
            unit->buildingArena(), std::move(*origins), *condition, *whenTrue,
            *whenFalse, *type);
    }
    if (const auto *conditional =
            llvm::dyn_cast<clang::BinaryConditionalOperator>(&expression)) {
        const clang::OpaqueValueExpr *opaque = conditional->getOpaqueValue();
        if (!opaque)
            return expressionError(expression,
                                   "binary conditional opaque value");
        auto implicit = sources.anchoredImplicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            origins->front(), *origins);
        if (!implicit)
            return implicit.takeError();
        const std::uint64_t opaqueIndex = nextOpaqueName++;
        opaqueNames[opaque] = opaqueIndex;
        opaqueOrigins[opaque] = *implicit;
        opaqueAnchors[opaque] = origins->front();
        auto common = buildExpression(*conditional->getCommon(), mode);
        if (!common)
            return common.takeError();
        auto condition = buildExpression(*conditional->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto whenTrue = buildExpression(*conditional->getTrueExpr(), mode);
        if (!whenTrue)
            return whenTrue.takeError();
        auto whenFalse = buildExpression(*conditional->getFalseExpr(), mode);
        if (!whenFalse)
            return whenFalse.takeError();
        auto type = buildDeclType(*this, expression, mode, *origins);
        if (!type)
            return type.takeError();
        return factory::makeBinaryConditionalExpression(
            unit->buildingArena(), std::move(*origins), opaqueIndex, *common,
            *condition, *whenTrue, *whenFalse, *type);
    }
    auto buildArguments = [&](const clang::CallExpr &call)
        -> llvm::Expected<std::vector<NodeId>> {
        std::vector<NodeId> result;
        result.reserve(call.getNumArgs());
        for (const clang::Expr *argument : call.arguments()) {
            auto built = buildExpression(*argument, mode);
            if (!built)
                return built.takeError();
            result.push_back(*built);
        }
        return result;
    };
    auto buildFunctionType =
        [&](const clang::FunctionDecl &function) -> llvm::Expected<NodeId> {
        if (const clang::TypeSourceInfo *written =
                function.getTypeSourceInfo()) {
            if (!written->getType()->getContainedAutoType())
                return buildTypeLoc(written->getTypeLoc(), mode, *origins);
            auto origin = sources.typeSourceInfoNode(written);
            if (!origin)
                return origin.takeError();
            return buildType(function.getType(), mode, {*origin});
        }
        auto inherited = inheritedTypeOrigins(function.getType(), *origins);
        if (!inherited)
            return inherited.takeError();
        return buildType(function.getType(), mode, std::move(*inherited));
    };
    auto buildPseudoDestructor =
        [&](const clang::CXXPseudoDestructorExpr &value,
            factory::OriginList nodeOrigins) -> llvm::Expected<NodeId> {
        llvm::Expected<NodeId> destroyed = [&]() -> llvm::Expected<NodeId> {
            if (const clang::TypeSourceInfo *written =
                    value.getDestroyedTypeInfo())
                return buildTypeLoc(written->getTypeLoc(), mode, nodeOrigins);
            if (value.getDestroyedType().isNull())
                return expressionError(value,
                                       "pseudo-destructor destroyed type");
            auto inherited =
                inheritedTypeOrigins(value.getDestroyedType(), nodeOrigins);
            if (!inherited)
                return inherited.takeError();
            return buildType(value.getDestroyedType(), mode,
                             std::move(*inherited));
        }();
        if (!destroyed)
            return destroyed.takeError();
        auto base = buildExpression(*value.getBase(), mode);
        if (!base)
            return base.takeError();
        return factory::makePseudoDestructorExpression(
            unit->buildingArena(), std::move(nodeOrigins), value.isArrow(),
            *destroyed, *base);
    };
    auto appendErasedNameOrigin =
        [&](NodeId name, const clang::Expr &wrapper) -> llvm::Expected<NodeId> {
        auto node = unit->buildingArena().get(name);
        if (!node)
            return node.takeError();
        auto transformed = sources.transformedNode(
            clang::CharSourceRange::getTokenRange(wrapper.getSourceRange()),
            (*node)->origins);
        if (!transformed)
            return transformed.takeError();
        return factory::cloneWithOrigins(unit->buildingArena(), name,
                                         {*transformed});
    };
    auto makeUnsupportedCallName =
        [&](const clang::Expr &written,
            llvm::StringRef message) -> llvm::Expected<NodeId> {
        auto direct = expressionOrigins(*this, written);
        if (!direct)
            return direct.takeError();
        auto generated = sources.synthesizedNode(direct->front(), *direct);
        if (!generated)
            return generated.takeError();
        auto name = factory::makeUnsupportedName(unit->buildingArena(),
                                                 {*generated}, message.str());
        if (!name)
            return name.takeError();
        return appendErasedNameOrigin(*name, written);
    };
    auto buildUnresolvedCallName =
        [&](auto &&self, const clang::Expr &callee) -> llvm::Expected<NodeId> {
        if (const auto *parenthesized =
                llvm::dyn_cast<clang::ParenExpr>(&callee)) {
            auto name = self(self, *parenthesized->getSubExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *parenthesized);
        }
        if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(&callee))
            switch (cast->getCastKind()) {
            case clang::CK_FunctionToPointerDecay:
            case clang::CK_BuiltinFnToFnPtr:
            case clang::CK_NoOp:
            case clang::CK_UserDefinedConversion: {
                auto name = self(self, *cast->getSubExpr());
                if (!name)
                    return name.takeError();
                return appendErasedNameOrigin(*name, *cast);
            }
            default:
                return makeUnsupportedCallName(*cast, "Ecast");
            }
        if (const auto *cast = llvm::dyn_cast<clang::ExplicitCastExpr>(&callee))
            switch (cast->getCastKind()) {
            case clang::CK_FunctionToPointerDecay:
            case clang::CK_BuiltinFnToFnPtr:
            case clang::CK_NoOp:
            case clang::CK_UserDefinedConversion: {
                auto name = self(self, *cast->getSubExpr());
                if (!name)
                    return name.takeError();
                return appendErasedNameOrigin(*name, *cast);
            }
            default:
                return makeUnsupportedCallName(*cast, "Ecast");
            }
        if (const auto *constant =
                llvm::dyn_cast<clang::ConstantExpr>(&callee)) {
            auto name = self(self, *constant->getSubExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *constant);
        }
        if (const auto *defaultInit =
                llvm::dyn_cast<clang::CXXDefaultInitExpr>(&callee)) {
            auto name = self(self, *defaultInit->getExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *defaultInit);
        }
        if (const auto *temporary =
                llvm::dyn_cast<clang::CXXBindTemporaryExpr>(&callee)) {
            auto name = self(self, *temporary->getSubExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *temporary);
        }
        if (const auto *cleanups =
                llvm::dyn_cast<clang::ExprWithCleanups>(&callee)) {
            auto name = self(self, *cleanups->getSubExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *cleanups);
        }
        if (const auto *materialized =
                llvm::dyn_cast<clang::MaterializeTemporaryExpr>(&callee)) {
            if (materialized->getExtendingDecl())
                return makeUnsupportedCallName(
                    callee, "Eunsupported: MaterializeTemporaryExpr");
            auto name = self(self, *materialized->getSubExpr());
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, *materialized);
        }
        if (const auto *initializer =
                llvm::dyn_cast<clang::InitListExpr>(&callee)) {
            if (initializer->isTransparent()) {
                if (initializer->getNumInits() != 1)
                    return expressionError(
                        callee, "transparent initializer list arity");
                auto name = self(self, *initializer->getInit(0));
                if (!name)
                    return name.takeError();
                return appendErasedNameOrigin(*name, *initializer);
            }
            auto built = buildExpression(callee, mode);
            if (!built)
                return built.takeError();
            auto node = unit->buildingArena().get(*built);
            if (!node)
                return node.takeError();
            switch ((*node)->constructor) {
            case Constructor::ExpressionUnresolvedInitList:
                return makeUnsupportedCallName(callee, "Eunresolved_initlist");
            case Constructor::ExpressionInitList:
                return makeUnsupportedCallName(callee, "Einitlist");
            case Constructor::ExpressionInitListUnion:
                return makeUnsupportedCallName(callee, "Einitlist_union");
            default:
                return expressionError(callee,
                                       "unresolved initializer-list callee");
            }
        }
        auto calleeOrigins = expressionOrigins(*this, callee);
        if (!calleeOrigins)
            return calleeOrigins.takeError();
        if (const auto *dependent =
                llvm::dyn_cast<clang::DependentScopeDeclRefExpr>(&callee)) {
            return buildUnresolvedName(
                dependent->getQualifier(), dependent->getQualifierLoc(),
                dependent->getDeclName(), dependent->template_arguments(), mode,
                std::move(*calleeOrigins));
        }
        if (const auto *unresolved =
                llvm::dyn_cast<clang::UnresolvedLookupExpr>(&callee)) {
            llvm::ArrayRef<clang::TemplateArgumentLoc> arguments;
            if (unresolved->hasExplicitTemplateArgs())
                arguments = unresolved->template_arguments();
            return buildUnresolvedName(unresolved->getQualifier(),
                                       unresolved->getQualifierLoc(),
                                       unresolved->getName(), arguments, mode,
                                       std::move(*calleeOrigins));
        }
        if (const auto *member =
                llvm::dyn_cast<clang::CXXDependentScopeMemberExpr>(&callee)) {
            // The mparser helper treats explicit and implicit dependent member
            // access uniformly. Clang supplies the implicit object expression;
            // reduce both forms through the same final Tresult_member name.
            auto memberName = buildUnresolvedName(
                member->getQualifier(), member->getQualifierLoc(),
                member->getMember(), member->template_arguments(), mode,
                *calleeOrigins);
            if (!memberName)
                return memberName.takeError();
            auto generated =
                sources.synthesizedNode(calleeOrigins->front(), *calleeOrigins);
            if (!generated)
                return generated.takeError();
            llvm::Expected<NodeId> objectType = [&]() {
                if (member->isImplicitAccess())
                    // getBase() is invalid for implicit access. Its semantic
                    // base is the implicit object expression, whose never-null
                    // BaseType is sufficient after eager helper reduction.
                    return buildType(member->getBaseType(), mode, {*generated});
                auto object = buildExpression(*member->getBase(), mode);
                if (!object)
                    return llvm::Expected<NodeId>(object.takeError());
                return ownedExpressionDecltype(*this, *object, {*generated});
            }();
            if (!objectType)
                return objectType.takeError();
            if (member->isArrow()) {
                auto arrowType = factory::makeResultUnarySyntaxType(
                    unit->buildingArena(), {*generated},
                    ScalarTerm::symbol("Rarrow"), *objectType);
                if (!arrowType)
                    return arrowType.takeError();
                objectType = std::move(arrowType);
            } else {
                objectType = dropOwnedReference(*this, *objectType);
                if (!objectType)
                    return objectType.takeError();
            }
            auto resultType = factory::makeResultMemberType(
                unit->buildingArena(), {*generated}, *objectType, *memberName);
            if (!resultType)
                return resultType.takeError();
            auto name = factory::makeDependentName(unit->buildingArena(),
                                                   {*generated}, *resultType);
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, callee);
        }
        if (llvm::isa<clang::UnresolvedMemberExpr>(&callee))
            return makeUnsupportedCallName(
                callee, "Eunsupported: UnresolvedMemberExpr");
        if (llvm::isa<clang::CXXUnresolvedConstructExpr>(&callee))
            return makeUnsupportedCallName(
                callee, "Eunsupported: CXXUnresolvedConstructExpr");
        if (llvm::isa<clang::CXXConstructExpr>(&callee))
            return makeUnsupportedCallName(callee, "Econstructor");
        // mparser.Eunresolved_call eagerly reduces an Elambda callee through
        // to_unresolved_name; the lambda subtree is erased from final core IR.
        if (llvm::isa<clang::LambdaExpr>(&callee))
            return makeUnsupportedCallName(callee, "Elambda");
        if (const auto *binary =
                llvm::dyn_cast<clang::BinaryOperator>(&callee)) {
            auto operandIsUnresolved = [](const clang::Expr &operand) {
                if (const auto *call = llvm::dyn_cast<clang::CallExpr>(
                        operand.IgnoreParenImpCasts()))
                    if (call->isTypeDependent() || call->isValueDependent() ||
                        call->isInstantiationDependent())
                        return true;
                if (const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(
                        operand.IgnoreParenImpCasts()))
                    if (llvm::isa<clang::NonTypeTemplateParmDecl>(
                            reference->getDecl()))
                        return true;
                clang::QualType type = operand.getType();
                if (type.isNull())
                    return true;
                if (type->isReferenceType())
                    type = type->getPointeeType();
                type = type.getCanonicalType().getUnqualifiedType();
                if (!type->isDependentType())
                    return false;
                if (type->isPointerType() || type->isArrayType() ||
                    type->isMemberPointerType() || type->isFunctionType() ||
                    type->isRecordType() || type->isEnumeralType() ||
                    llvm::isa<clang::DependentNameType,
                              clang::TemplateSpecializationType>(
                        type.getTypePtr()))
                    return false;
                return true;
            };
            const bool unresolved = mode == SemanticMode::Template &&
                                    (operandIsUnresolved(*binary->getLHS()) ||
                                     operandIsUnresolved(*binary->getRHS()));
            return makeUnsupportedCallName(
                callee, unresolved ? "Eunresolved_binop" : "Ebinop");
        }
        if (llvm::isa<clang::CallExpr>(&callee))
            return makeUnsupportedCallName(callee, "Eunresolved_call");
        if (llvm::isa<clang::UnaryOperator>(&callee)) {
            auto built = buildExpression(callee, mode);
            if (!built)
                return built.takeError();
            auto node = unit->buildingArena().get(*built);
            if (!node)
                return node.takeError();
            llvm::StringRef diagnostic;
            switch ((*node)->constructor) {
            case Constructor::ExpressionUnary:
            case Constructor::ExpressionUnsupportedUnary:
                diagnostic = "Eunop";
                break;
            case Constructor::ExpressionUnresolvedUnary:
            case Constructor::ExpressionUnresolvedUnsupportedUnary:
            case Constructor::ExpressionUnresolvedUnarySyntax:
                diagnostic = "Eunresolved_unop";
                break;
            case Constructor::ExpressionDeref:
                diagnostic = "Ederef";
                break;
            case Constructor::ExpressionAddressOf:
                diagnostic = "Eaddrof";
                break;
            case Constructor::ExpressionPreIncrement:
                diagnostic = "Epreinc";
                break;
            case Constructor::ExpressionPostIncrement:
                diagnostic = "Epostinc";
                break;
            case Constructor::ExpressionPreDecrement:
                diagnostic = "Epredec";
                break;
            case Constructor::ExpressionPostDecrement:
                diagnostic = "Epostdec";
                break;
            default:
                return expressionError(callee, "unresolved unary call callee");
            }
            return makeUnsupportedCallName(callee, diagnostic);
        }
        if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(&callee))
            return makeUnsupportedCallName(
                callee, llvm::isa<clang::FieldDecl>(member->getMemberDecl())
                            ? "Emember"
                            : "Emember_ignore");
        if (const auto *reference =
                llvm::dyn_cast<clang::DeclRefExpr>(&callee)) {
            const clang::ValueDecl *declaration = reference->getDecl();
            if (!declaration)
                return expressionError(callee,
                                       "unresolved call null declaration");
            const clang::DeclContext *context = declaration->getDeclContext();
            const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration);
            const bool local =
                llvm::isa<clang::NonTypeTemplateParmDecl>(declaration) ||
                (context && context->isFunctionOrMethod() &&
                 !llvm::isa<clang::FunctionDecl>(declaration) &&
                 !(variable && variable->isStaticLocal()));
            if (!local) {
                auto name = buildName(*declaration, mode);
                if (!name)
                    return name.takeError();
                return appendErasedNameOrigin(*name, callee);
            }
            const clang::IdentifierInfo *identifier =
                declaration->getIdentifier();
            if (!identifier)
                return expressionError(callee,
                                       "anonymous local unresolved callee");
            auto generated =
                sources.synthesizedNode(calleeOrigins->front(), *calleeOrigins);
            if (!generated)
                return generated.takeError();
            auto atomic = factory::makeAtomicIdentifier(
                unit->buildingArena(), {*generated},
                identifier->getName().str());
            if (!atomic)
                return atomic.takeError();
            auto name = factory::makeGlobalName(unit->buildingArena(),
                                                {*generated}, *atomic);
            if (!name)
                return name.takeError();
            return appendErasedNameOrigin(*name, callee);
        }
        return expressionError(callee, "unresolved call callee");
    };

    if (const auto *unresolved =
            llvm::dyn_cast<clang::CXXUnresolvedConstructExpr>(&expression)) {
        const clang::TypeSourceInfo *written = unresolved->getTypeSourceInfo();
        if (!written)
            return buildUnsupportedExpression(*this, expression, mode,
                                              std::move(*origins),
                                              expression.getStmtClassName());
        auto type = buildTypeLoc(written->getTypeLoc(), mode, *origins);
        if (!type)
            return type.takeError();
        return factory::makeUnsupportedExpression(
            unit->buildingArena(), std::move(*origins),
            expression.getStmtClassName(), *type);
    }
    if (const auto *construction =
            llvm::dyn_cast<clang::CXXConstructExpr>(&expression)) {
        const clang::CXXConstructorDecl *declaration =
            construction->getConstructor();
        if (!declaration)
            return expressionError(expression, "constructor declaration");
        auto name = buildName(*declaration, mode);
        if (!name)
            return name.takeError();
        std::vector<NodeId> arguments;
        arguments.reserve(construction->getNumArgs());
        for (const clang::Expr *argument : construction->arguments()) {
            auto value = buildExpression(*argument, mode);
            if (!value)
                return value.takeError();
            arguments.push_back(*value);
        }
        llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
            if (const auto *temporary =
                    llvm::dyn_cast<clang::CXXTemporaryObjectExpr>(construction))
                if (const clang::TypeSourceInfo *written =
                        temporary->getTypeSourceInfo())
                    return buildTypeLoc(written->getTypeLoc(), mode, *origins);
            return expressionType();
        }();
        if (!type)
            return type.takeError();
        return factory::makeConstructorExpression(unit->buildingArena(),
                                                  std::move(*origins), *name,
                                                  std::move(arguments), *type);
    }
    if (const auto *inherited =
            llvm::dyn_cast<clang::CXXInheritedCtorInitExpr>(&expression)) {
        const clang::CXXConstructorDecl *declaration =
            inherited->getConstructor();
        if (!declaration)
            return expressionError(expression,
                                   "inherited constructor declaration");
        auto name = buildName(*declaration, mode);
        if (!name)
            return name.takeError();
        auto implicit = sources.implicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            *origins);
        if (!implicit)
            return implicit.takeError();
        auto inheritedOrigins =
            inheritedTypeOrigins(expression.getType(), {*implicit});
        if (!inheritedOrigins)
            return inheritedOrigins.takeError();
        auto type =
            buildType(expression.getType(), mode, std::move(*inheritedOrigins));
        if (!type)
            return type.takeError();
        return factory::makeInheritedConstructorExpression(
            unit->buildingArena(), {*implicit}, *name,
            declaration->getNumParams(), *type);
    }
    if (const auto *parenthesized =
            llvm::dyn_cast<clang::ParenListExpr>(&expression)) {
        if (mode == SemanticMode::Static)
            return buildUnsupportedExpression(
                *this, expression, SemanticMode::Template, std::move(*origins),
                expression.getStmtClassName());
        std::optional<NodeId> type;
        if (!expression.getType().isNull() &&
            !expression.getType()->isDependentType()) {
            auto value = expressionType();
            if (!value)
                return value.takeError();
            type = *value;
        }
        std::vector<NodeId> values;
        values.reserve(parenthesized->getNumExprs());
        for (unsigned index = 0; index < parenthesized->getNumExprs();
             ++index) {
            auto value = buildExpression(*parenthesized->getExpr(index), mode);
            if (!value)
                return value.takeError();
            values.push_back(*value);
        }
        return factory::makeUnresolvedInitializerListExpression(
            unit->buildingArena(), std::move(*origins),
            Constructor::ExpressionUnresolvedParenList, type,
            std::move(values));
    }
    if (const auto *initializer =
            llvm::dyn_cast<clang::InitListExpr>(&expression)) {
        std::vector<NodeId> values;
        values.reserve(initializer->getNumInits());
        for (const clang::Expr *element : initializer->inits()) {
            auto value = buildExpression(*element, mode);
            if (!value)
                return value.takeError();
            values.push_back(*value);
        }
        if (!expression.getType().isNull() &&
            expression.getType()->isVoidType())
            return factory::makeUnresolvedInitializerListExpression(
                unit->buildingArena(), std::move(*origins),
                Constructor::ExpressionUnresolvedInitList, std::nullopt,
                std::move(values));
        auto type = expressionType();
        if (!type)
            return type.takeError();
        if (const clang::FieldDecl *field =
                initializer->getInitializedFieldInUnion()) {
            if (values.size() > 1 || initializer->getArrayFiller())
                return expressionError(expression,
                                       "union initializer-list shape");
            auto fieldName = buildFieldName(*field, mode, *origins);
            if (!fieldName)
                return fieldName.takeError();
            const std::optional<NodeId> value =
                values.empty() ? std::nullopt
                               : std::optional<NodeId>(values.front());
            return factory::makeUnionInitListExpression(
                unit->buildingArena(), std::move(*origins), *fieldName, value,
                *type);
        }
        std::optional<NodeId> filler;
        if (const clang::Expr *arrayFiller = initializer->getArrayFiller()) {
            auto value = buildExpression(*arrayFiller, mode);
            if (!value)
                return value.takeError();
            filler = *value;
        }
        return factory::makeInitListExpression(
            unit->buildingArena(), std::move(*origins), std::move(values),
            filler, *type);
    }
    if (const auto *scalar =
            llvm::dyn_cast<clang::CXXScalarValueInitExpr>(&expression)) {
        llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
            if (const clang::TypeSourceInfo *written =
                    scalar->getTypeSourceInfo())
                return buildTypeLoc(written->getTypeLoc(), mode, *origins);
            return expressionType();
        }();
        if (!type)
            return type.takeError();
        return factory::makeImplicitInitExpression(unit->buildingArena(),
                                                   std::move(*origins), *type);
    }
    if (const auto *loop =
            llvm::dyn_cast<clang::ArrayInitLoopExpr>(&expression)) {
        const clang::OpaqueValueExpr *common = loop->getCommonExpr();
        if (!common || !common->getSourceExpr())
            return expressionError(expression,
                                   "array initializer common expression");
        auto implicit = sources.anchoredImplicitNode(
            clang::CharSourceRange::getTokenRange(expression.getSourceRange()),
            origins->front(), *origins);
        if (!implicit)
            return implicit.takeError();
        factory::OriginList loopOrigins{*implicit};
        const std::uint64_t opaqueName = nextOpaqueName++;
        opaqueNames[common] = opaqueName;
        opaqueOrigins[common] = *implicit;
        opaqueAnchors[common] = origins->front();
        arrayLoopOrigins.push_back(*implicit);
        auto source = buildExpression(*common->getSourceExpr(), mode);
        if (!source) {
            arrayLoopOrigins.pop_back();
            return source.takeError();
        }
        ++arrayLoopIndexDepth;
        auto value = buildExpression(*loop->getSubExpr(), mode);
        --arrayLoopIndexDepth;
        arrayLoopOrigins.pop_back();
        if (!value)
            return value.takeError();
        auto inherited =
            inheritedTypeOrigins(expression.getType(), loopOrigins);
        if (!inherited)
            return inherited.takeError();
        auto type =
            buildType(expression.getType(), mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        llvm::SmallString<32> arraySize;
        loop->getArraySize().toString(arraySize, 10, false);
        return factory::makeArrayLoopInitExpression(
            unit->buildingArena(), std::move(loopOrigins), opaqueName, *source,
            static_cast<std::uint64_t>(arrayLoopIndexDepth + 1),
            arraySize.str().str(), *value, *type);
    }

    if (const auto *allocation =
            llvm::dyn_cast<clang::CXXNewExpr>(&expression)) {
        const clang::FunctionDecl *function = allocation->getOperatorNew();
        if (!function)
            return buildUnsupportedExpression(*this, expression, mode,
                                              std::move(*origins),
                                              expression.getStmtClassName());
        auto name = buildName(*function, mode);
        if (!name)
            return name.takeError();
        auto functionType = buildFunctionType(*function);
        if (!functionType)
            return functionType.takeError();
        std::vector<NodeId> placementArguments;
        placementArguments.reserve(allocation->getNumPlacementArgs());
        for (const clang::Expr *argument : allocation->placement_arguments()) {
            auto value = buildExpression(*argument, mode);
            if (!value)
                return value.takeError();
            placementArguments.push_back(*value);
        }
        const bool nonAllocating =
            function->isReservedGlobalPlacementOperator();
        if (nonAllocating && (allocation->getNumPlacementArgs() != 1 ||
                              allocation->passAlignment()))
            return expressionError(expression,
                                   "non-allocating new expression shape");
        llvm::Expected<NodeId> allocatedType = [&]() -> llvm::Expected<NodeId> {
            if (const clang::TypeSourceInfo *written =
                    allocation->getAllocatedTypeSourceInfo())
                return buildTypeLoc(written->getTypeLoc(), mode, *origins);
            return semanticType(allocation->getAllocatedType());
        }();
        if (!allocatedType)
            return allocatedType.takeError();
        std::optional<NodeId> arraySize;
        if (std::optional<const clang::Expr *> writtenSize =
                allocation->getArraySize()) {
            auto value = buildExpression(**writtenSize, mode);
            if (!value)
                return value.takeError();
            arraySize = *value;
        }
        if (allocation->isArray() != arraySize.has_value())
            return expressionError(expression, "new array-size invariant");
        std::optional<NodeId> initializer;
        if (const clang::Expr *writtenInitializer =
                allocation->getInitializer()) {
            auto value = buildExpression(*writtenInitializer, mode);
            if (!value)
                return value.takeError();
            initializer = *value;
        }
        return factory::makeNewExpression(
            unit->buildingArena(), std::move(*origins), *name, *functionType,
            std::move(placementArguments), nonAllocating,
            allocation->passAlignment(), *allocatedType, arraySize,
            initializer);
    }
    if (const auto *deallocation =
            llvm::dyn_cast<clang::CXXDeleteExpr>(&expression)) {
        const clang::FunctionDecl *function = deallocation->getOperatorDelete();
        if (!function) {
            if (mode != SemanticMode::Template)
                return expressionError(expression,
                                       "unresolved delete in static mode");
            auto generated =
                sources.synthesizedNode(origins->front(), *origins);
            if (!generated)
                return generated.takeError();
            auto type = factory::makeLeafType(
                unit->buildingArena(), Constructor::TypeVoid, {*generated});
            if (!type)
                return type.takeError();
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), std::move(*origins), "unresolved delete",
                *type);
        }
        auto argument = buildExpression(*deallocation->getArgument(), mode);
        if (!argument)
            return argument.takeError();
        auto name = buildName(*function, mode);
        if (!name)
            return name.takeError();
        if (deallocation->getDestroyedType().isNull())
            return expressionError(expression, "delete destroyed type");
        auto type = semanticType(deallocation->getDestroyedType());
        if (!type)
            return type.takeError();
        return factory::makeDeleteExpression(
            unit->buildingArena(), std::move(*origins),
            deallocation->isArrayForm(), *name, *argument, *type);
    }

    if (const auto *lambda = llvm::dyn_cast<clang::LambdaExpr>(&expression)) {
        const clang::CXXRecordDecl *closure = lambda->getLambdaClass();
        if (!closure)
            return expressionError(expression, "lambda closure");
        auto name = buildName(*closure, mode);
        if (!name)
            return name.takeError();
        auto buildCaptureInitializer =
            [&](const clang::Expr *initializer) -> llvm::Expected<NodeId> {
            if (!initializer)
                return expressionError(expression,
                                       "null lambda capture initializer");
            activeCaptureInitializerClosures.push_back(closure);
            auto value = buildExpression(*initializer, mode);
            activeCaptureInitializerClosures.pop_back();
            return value;
        };
        auto buildVlaCapture =
            [&](const clang::LambdaCapture &capture,
                llvm::StringRef message) -> llvm::Expected<NodeId> {
            const clang::SourceLocation location = capture.getLocation();
            const clang::CharSourceRange sourceRange =
                location.isValid()
                    ? clang::CharSourceRange::getTokenRange(location, location)
                    : clang::CharSourceRange::getTokenRange(
                          lambda->getSourceRange());
            auto implicit = sources.anchoredImplicitNode(
                sourceRange, origins->front(), *origins);
            if (!implicit)
                return implicit.takeError();
            auto generated = sources.synthesizedNode(*implicit, {*implicit});
            if (!generated)
                return generated.takeError();
            auto type = factory::makeLeafType(
                unit->buildingArena(), Constructor::TypeAuto, {*generated});
            if (!type)
                return type.takeError();
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), {*implicit}, message.str(), *type);
        };
        std::vector<NodeId> captures;
        if (mode == SemanticMode::Static) {
            captures.reserve(lambda->capture_size());
            auto capture = lambda->capture_begin();
            auto initializer = lambda->capture_init_begin();
            for (; capture != lambda->capture_end() &&
                   initializer != lambda->capture_init_end();
                 ++capture, ++initializer) {
                if (capture->capturesVLAType()) {
                    auto value =
                        buildVlaCapture(*capture, "empty expression (nullptr)");
                    if (!value)
                        return value.takeError();
                    captures.push_back(*value);
                    continue;
                }
                auto value = buildCaptureInitializer(*initializer);
                if (!value)
                    return value.takeError();
                captures.push_back(*value);
            }
            if (capture != lambda->capture_end() ||
                initializer != lambda->capture_init_end())
                return expressionError(expression,
                                       "lambda capture initializer count");
        } else {
            llvm::DenseMap<const clang::ValueDecl *, clang::FieldDecl *>
                captureFields;
            clang::FieldDecl *thisCapture = nullptr;
            closure->getCaptureFields(captureFields, thisCapture);
            auto capture = lambda->capture_begin();
            auto initializer = lambda->capture_init_begin();
            for (; capture != lambda->capture_end() &&
                   initializer != lambda->capture_init_end();
                 ++capture, ++initializer) {
                const clang::FieldDecl *field = nullptr;
                if (capture->capturesVariable()) {
                    const auto found =
                        captureFields.find(capture->getCapturedVar());
                    if (found != captureFields.end())
                        field = found->second;
                } else if (capture->capturesThis()) {
                    field = thisCapture;
                } else if (capture->capturesVLAType()) {
                    auto value = buildVlaCapture(
                        *capture, "variable length array capture");
                    if (!value)
                        return value.takeError();
                    captures.push_back(*value);
                    continue;
                } else {
                    return expressionError(expression,
                                           "unknown lambda capture kind");
                }
                if (!field)
                    return expressionError(expression, "lambda capture field");
                auto value = buildCaptureInitializer(*initializer);
                if (!value)
                    return value.takeError();
                auto generated =
                    sources.synthesizedNode(origins->front(), *origins);
                if (!generated)
                    return generated.takeError();
                auto initialized = applyInitializingType(
                    *value, field->getType(), mode, *generated);
                if (!initialized)
                    return initialized.takeError();
                captures.push_back(*initialized);
            }
        }
        return factory::makeLambdaExpression(unit->buildingArena(),
                                             std::move(*origins), *name,
                                             std::move(captures));
    }
    if (const auto *atomic = llvm::dyn_cast<clang::AtomicExpr>(&expression)) {
        std::vector<NodeId> arguments;
        arguments.reserve(atomic->getNumSubExprs());
        for (unsigned index = 0; index < atomic->getNumSubExprs(); ++index) {
            auto value = buildExpression(*atomic->getSubExprs()[index], mode);
            if (!value)
                return value.takeError();
            arguments.push_back(*value);
        }
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeAtomicExpression(
            unit->buildingArena(), std::move(*origins),
            AtomicOpBackport::getOpAsString(atomic).str(), std::move(arguments),
            *type);
    }
    if (const auto *vaArg = llvm::dyn_cast<clang::VAArgExpr>(&expression)) {
        auto argument = buildExpression(*vaArg->getSubExpr(), mode);
        if (!argument)
            return argument.takeError();
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeVaArgExpression(
            unit->buildingArena(), std::move(*origins), *argument, *type);
    }

    if (const auto *operatorCall =
            llvm::dyn_cast<clang::CXXOperatorCallExpr>(&expression)) {
        const clang::Decl *calleeDeclaration = operatorCall->getCalleeDecl();
        if (!calleeDeclaration) {
            auto type = expressionType();
            if (!type)
                return type.takeError();
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), std::move(*origins),
                "unsupported operator call (nullptr)", *type);
        }
        const auto *callee =
            llvm::dyn_cast<clang::FunctionDecl>(calleeDeclaration);
        if (!callee) {
            auto type = expressionType();
            if (!type)
                return type.takeError();
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), std::move(*origins),
                "unsupported operator call", *type);
        }
        const clang::OverloadedOperatorKind operationKind =
            operatorCall->getOperator();
        const bool allocationOperation =
            operationKind == clang::OO_New ||
            operationKind == clang::OO_Array_New ||
            operationKind == clang::OO_Delete ||
            operationKind == clang::OO_Array_Delete;
        const bool deleteOperation = operationKind == clang::OO_Delete ||
                                     operationKind == clang::OO_Array_Delete;
        const bool arrayOperation = operationKind == clang::OO_Array_New ||
                                    operationKind == clang::OO_Array_Delete;
        auto name = buildName(*callee, mode);
        if (!name)
            return name.takeError();
        auto type = buildFunctionType(*callee);
        if (!type)
            return type.takeError();
        auto arguments = buildArguments(*operatorCall);
        if (!arguments)
            return arguments.takeError();
        if (const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(callee)) {
            const char *dispatch = method->isStatic()    ? "Static_dispatch"
                                   : method->isVirtual() ? "Virtual"
                                                         : "Direct";
            if (allocationOperation)
                return factory::makeMethodAllocationOperatorCallExpression(
                    unit->buildingArena(), std::move(*origins), deleteOperation,
                    arrayOperation, *name, ScalarTerm::symbol(dispatch), *type,
                    std::move(*arguments));
            auto operation = overloadedOperatorTerm(operationKind);
            if (!operation)
                return operation.takeError();
            return factory::makeMethodOperatorCallExpression(
                unit->buildingArena(), std::move(*origins),
                std::move(*operation), *name, ScalarTerm::symbol(dispatch),
                *type, std::move(*arguments));
        }
        if (allocationOperation)
            return factory::makeFunctionAllocationOperatorCallExpression(
                unit->buildingArena(), std::move(*origins), deleteOperation,
                arrayOperation, *name, *type, std::move(*arguments));
        auto operation = overloadedOperatorTerm(operationKind);
        if (!operation)
            return operation.takeError();
        return factory::makeFunctionOperatorCallExpression(
            unit->buildingArena(), std::move(*origins), std::move(*operation),
            *name, *type, std::move(*arguments));
    }
    if (const auto *memberCall =
            llvm::dyn_cast<clang::CXXMemberCallExpr>(&expression)) {
        const clang::Expr *callee = memberCall->getCallee();
        while (const auto *parenthesized =
                   llvm::dyn_cast<clang::ParenExpr>(callee)) {
            auto transformed =
                sources.transformedNode(clang::CharSourceRange::getTokenRange(
                                            parenthesized->getSourceRange()),
                                        *origins);
            if (!transformed)
                return transformed.takeError();
            source::appendOriginStable(*origins, *transformed);
            callee = parenthesized->getSubExpr();
        }
        auto object =
            buildExpression(*memberCall->getImplicitObjectArgument(), mode);
        if (!object)
            return object.takeError();
        auto arguments = buildArguments(*memberCall);
        if (!arguments)
            return arguments.takeError();
        if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(callee)) {
            const clang::CXXMethodDecl *method = memberCall->getMethodDecl();
            if (!method)
                return expressionError(expression,
                                       "member call without method");
            auto name = buildName(*method, mode);
            if (!name)
                return name.takeError();
            auto type = buildFunctionType(*method);
            if (!type)
                return type.takeError();
            const bool virtualDispatch =
                method->isVirtual() &&
                member->performsVirtualDispatch(context.getLangOpts());
            return factory::makeDirectMemberCallExpression(
                unit->buildingArena(), std::move(*origins), member->isArrow(),
                *name,
                ScalarTerm::symbol(virtualDispatch ? "Virtual" : "Direct"),
                *type, *object, std::move(*arguments));
        }
        if (const auto *binary =
                llvm::dyn_cast<clang::BinaryOperator>(callee)) {
            if (binary->getOpcode() != clang::BO_PtrMemD &&
                binary->getOpcode() != clang::BO_PtrMemI)
                return expressionError(expression,
                                       "member call non-member-pointer binary");
            auto member = buildExpression(*binary->getRHS(), mode);
            if (!member)
                return member.takeError();
            return factory::makePointerMemberCallExpression(
                unit->buildingArena(), std::move(*origins),
                binary->getOpcode() == clang::BO_PtrMemI, *member, *object,
                std::move(*arguments));
        }
        return expressionError(expression, "member call callee");
    }
    if (const auto *call = llvm::dyn_cast<clang::CallExpr>(&expression)) {
        if (const auto *pseudo = llvm::dyn_cast<clang::CXXPseudoDestructorExpr>(
                call->getCallee())) {
            if (call->getNumArgs() != 0)
                return expressionError(expression,
                                       "pseudo-destructor call arguments");
            auto pseudoOrigins = expressionOrigins(*this, *pseudo);
            if (!pseudoOrigins)
                return pseudoOrigins.takeError();
            auto built =
                buildPseudoDestructor(*pseudo, std::move(*pseudoOrigins));
            if (!built)
                return built.takeError();
            auto node = unit->buildingArena().get(*built);
            if (!node)
                return node.takeError();
            auto transformed = sources.transformedNode(
                clang::CharSourceRange::getTokenRange(call->getSourceRange()),
                (*node)->origins);
            if (!transformed)
                return transformed.takeError();
            return factory::cloneWithOrigins(unit->buildingArena(), *built,
                                             {*transformed});
        }
        auto arguments = buildArguments(*call);
        if (!arguments)
            return arguments.takeError();
        const bool dependent =
            static_cast<bool>(expression.getDependence() &
                              clang::ExprDependence::TypeValueInstantiation);
        if (dependent) {
            if (mode == SemanticMode::Static)
                return expressionError(
                    expression,
                    "dependent call requires template semantic mode");
            auto name = buildUnresolvedCallName(buildUnresolvedCallName,
                                                *call->getCallee());
            if (!name)
                return name.takeError();
            return factory::makeUnresolvedCallExpression(
                unit->buildingArena(), std::move(*origins), *name,
                std::move(*arguments));
        }
        auto callee = buildExpression(*call->getCallee(), mode);
        if (!callee)
            return callee.takeError();
        return factory::makeCallExpression(unit->buildingArena(),
                                           std::move(*origins), *callee,
                                           std::move(*arguments));
    }
    if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(&expression)) {
        auto object = buildExpression(*member->getBase(), mode);
        if (!object)
            return object.takeError();
        const clang::ValueDecl *declaration = member->getMemberDecl();
        if (const auto *field = llvm::dyn_cast<clang::FieldDecl>(declaration)) {
            auto generated = synthesizedOrigins();
            if (!generated)
                return generated.takeError();
            auto fieldName = buildFieldName(*field, mode, *generated);
            if (!fieldName)
                return fieldName.takeError();
            auto inherited = inheritedTypeOrigins(field->getType(), *origins);
            if (!inherited)
                return inherited.takeError();
            auto type =
                buildType(field->getType(), mode, std::move(*inherited));
            if (!type)
                return type.takeError();
            return factory::makeMemberExpression(
                unit->buildingArena(), std::move(*origins), member->isArrow(),
                *object, *fieldName, field->isMutable(), *type);
        }
        if (const auto *constant =
                llvm::dyn_cast<clang::EnumConstantDecl>(declaration)) {
            const auto *enumeration =
                llvm::dyn_cast<clang::EnumDecl>(constant->getDeclContext());
            if (!enumeration)
                return expressionError(expression,
                                       "member enum without enumeration");
            auto enumName = buildName(*enumeration, mode);
            if (!enumName)
                return enumName.takeError();
            auto generated = synthesizedOrigins();
            if (!generated)
                return generated.takeError();
            auto result = factory::makeEnumConstantExpression(
                unit->buildingArena(), *generated, *enumName,
                constant->getName().str());
            if (!result)
                return result.takeError();
            return factory::makeMemberIgnoreExpression(
                unit->buildingArena(), std::move(*origins), member->isArrow(),
                *object, *result);
        }
        if (const auto *variable =
                llvm::dyn_cast<clang::VarDecl>(declaration)) {
            if (!variable->isStaticDataMember())
                return expressionError(expression,
                                       "non-static variable member");
        } else if (!llvm::isa<clang::CXXMethodDecl>(declaration)) {
            return expressionError(expression, "unknown member declaration");
        }
        auto name = buildName(*declaration, mode);
        if (!name)
            return name.takeError();
        auto generated = synthesizedOrigins();
        if (!generated)
            return generated.takeError();
        auto inherited =
            inheritedTypeOrigins(declaration->getType(), *generated);
        if (!inherited)
            return inherited.takeError();
        auto type =
            buildType(declaration->getType(), mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        auto result = factory::makeGlobalExpression(
            unit->buildingArena(), *generated, *name, *type, false);
        if (!result)
            return result.takeError();
        return factory::makeMemberIgnoreExpression(
            unit->buildingArena(), std::move(*origins), member->isArrow(),
            *object, *result);
    }
    if (const auto *member =
            llvm::dyn_cast<clang::CXXDependentScopeMemberExpr>(&expression)) {
        if (mode == SemanticMode::Static)
            return expressionError(
                expression, "dependent member requires template semantic mode");
        if (member->isImplicitAccess())
            return expressionError(expression,
                                   "implicit dependent member access");
        auto object = buildExpression(*member->getBase(), mode);
        if (!object)
            return object.takeError();
        if (member->isArrow()) {
            auto generated = synthesizedOrigins();
            if (!generated)
                return generated.takeError();
            auto arrow = factory::makeUnresolvedUnarySyntaxExpression(
                unit->buildingArena(), std::move(*generated),
                ScalarTerm::symbol("Rarrow"), *object);
            if (!arrow)
                return arrow.takeError();
            object = std::move(arrow);
        }
        auto name = buildUnresolvedName(
            member->getQualifier(), member->getQualifierLoc(),
            member->getMember(), member->template_arguments(), mode, *origins);
        if (!name)
            return name.takeError();
        return factory::makeUnresolvedMemberExpression(
            unit->buildingArena(), std::move(*origins), *object, *name);
    }
    if (llvm::isa<clang::CXXThisExpr>(&expression)) {
        if (const auto lambda = enclosingLambda(
                context, expression, activeCaptureInitializerClosures)) {
            const clang::FieldDecl *field = thisCaptureField(*lambda->closure);
            if (!field)
                return expressionError(expression, "uncaptured lambda this");
            auto generated =
                sources.synthesizedNode(origins->front(), *origins);
            if (!generated)
                return generated.takeError();
            auto member = buildCaptureMember(*this, *lambda, *field, ".this",
                                             mode, {*generated}, *generated);
            if (!member)
                return member.takeError();
            auto cast = factory::makeLvalueToRvalueCast(unit->buildingArena(),
                                                        {*generated});
            if (!cast)
                return cast.takeError();
            return factory::makeCastExpression(
                unit->buildingArena(), std::move(*origins), *cast, *member);
        }
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeThisExpression(unit->buildingArena(),
                                           std::move(*origins), *type);
    }
    if (const auto *pseudo =
            llvm::dyn_cast<clang::CXXPseudoDestructorExpr>(&expression))
        return buildPseudoDestructor(*pseudo, std::move(*origins));

    if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(&expression)) {
        if (unary->getOpcode() == clang::UO_AddrOf) {
            // Legacy has a separate Eglobal_member spelling for direct member
            // addresses. Keep that later member family at a recoverable
            // boundary instead of silently producing ordinary Eaddrof.
            if (const auto *reference =
                    llvm::dyn_cast<clang::DeclRefExpr>(unary->getSubExpr())) {
                const clang::ValueDecl *declaration = reference->getDecl();
                const auto *field =
                    llvm::dyn_cast_or_null<clang::FieldDecl>(declaration);
                const auto *method =
                    llvm::dyn_cast_or_null<clang::CXXMethodDecl>(declaration);
                if ((field && field->isCXXInstanceMember()) ||
                    (method && !method->isStatic())) {
                    auto name = buildName(*declaration, mode);
                    if (!name)
                        return name.takeError();
                    auto type = semanticType(declaration->getType());
                    if (!type)
                        return type.takeError();
                    return factory::makeGlobalMemberExpression(
                        unit->buildingArena(), std::move(*origins), *name,
                        *type);
                }
            }
            auto operand = buildExpression(*unary->getSubExpr(), mode);
            if (!operand)
                return operand.takeError();
            return factory::makeAddressOfExpression(
                unit->buildingArena(), std::move(*origins), *operand);
        }

        auto operand = buildExpression(*unary->getSubExpr(), mode);
        if (!operand)
            return operand.takeError();
        const clang::QualType operandType = unary->getSubExpr()->getType();
        const bool needsInference = mode == SemanticMode::Template &&
                                    (expression.getType().isNull() ||
                                     expression.getType()->isDependentType());
        const bool templatePointer = mode == SemanticMode::Template &&
                                     !operandType.isNull() &&
                                     operandType->isPointerType();
        const char *unresolvedOperation = nullptr;
        Constructor finalConstructor = Constructor::Count;
        switch (unary->getOpcode()) {
        case clang::UO_Deref:
            unresolvedOperation = "Rstar";
            finalConstructor = Constructor::ExpressionDeref;
            break;
        case clang::UO_PreInc:
            unresolvedOperation = "Rpreinc";
            finalConstructor = Constructor::ExpressionPreIncrement;
            break;
        case clang::UO_PostInc:
            unresolvedOperation = "Rpostinc";
            finalConstructor = Constructor::ExpressionPostIncrement;
            break;
        case clang::UO_PreDec:
            unresolvedOperation = "Rpredec";
            finalConstructor = Constructor::ExpressionPreDecrement;
            break;
        case clang::UO_PostDec:
            unresolvedOperation = "Rpostdec";
            finalConstructor = Constructor::ExpressionPostDecrement;
            break;
        default:
            break;
        }
        if (unresolvedOperation) {
            const bool dereference = unary->getOpcode() == clang::UO_Deref;
            const bool pointerIncrement = templatePointer && !dereference;
            const bool unresolved =
                needsInference &&
                (dereference ? (ownedNodeIsDependent(*this, *operand) ||
                                !templatePointer)
                             : !templatePointer);
            if (unresolved)
                return factory::makeUnresolvedUnarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol(unresolvedOperation), *operand);
            auto type =
                pointerIncrement ? semanticType(operandType) : expressionType();
            if (!type)
                return type.takeError();
            if (finalConstructor == Constructor::ExpressionDeref)
                return factory::makeDerefExpression(unit->buildingArena(),
                                                    std::move(*origins),
                                                    *operand, *type);
            return factory::makeIncrementExpression(
                unit->buildingArena(), std::move(*origins), finalConstructor,
                *operand, *type);
        }

        switch (unary->getOpcode()) {
        case clang::UO_Real:
        case clang::UO_Imag:
        case clang::UO_Coawait: {
            const std::string operation =
                clang::UnaryOperator::getOpcodeStr(unary->getOpcode()).str();
            if (needsInference)
                return factory::makeUnsupportedUnaryExpression(
                    unit->buildingArena(), std::move(*origins), operation,
                    *operand, std::nullopt);
            auto type = expressionType();
            if (!type)
                return type.takeError();
            return factory::makeUnsupportedUnaryExpression(
                unit->buildingArena(), std::move(*origins), operation, *operand,
                *type);
        }
        default:
            break;
        }
        auto operation = unaryOperation(*unary);
        if (!operation)
            return operation.takeError();
        if (needsInference && templatePointer &&
            unary->getOpcode() == clang::UO_Plus) {
            // mparser resolves this before its general dependent-type test and
            // deliberately assigns unary pointer-plus Tlonglong.
            auto synthetic =
                sources.synthesizedNode(origins->front(), *origins);
            if (!synthetic)
                return synthetic.takeError();
            auto type = buildType(context.LongLongTy, mode, {*synthetic});
            if (!type)
                return type.takeError();
            return factory::makeUnaryExpression(
                unit->buildingArena(), std::move(*origins),
                std::move(*operation), *operand, *type);
        }
        if (needsInference)
            return factory::makeUnaryExpression(
                unit->buildingArena(), std::move(*origins),
                std::move(*operation), *operand, std::nullopt);
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeUnaryExpression(
            unit->buildingArena(), std::move(*origins), std::move(*operation),
            *operand, *type);
    }
    if (const auto *binary =
            llvm::dyn_cast<clang::BinaryOperator>(&expression)) {
        auto lhs = buildExpression(*binary->getLHS(), mode);
        if (!lhs)
            return lhs.takeError();
        auto rhs = buildExpression(*binary->getRHS(), mode);
        if (!rhs)
            return rhs.takeError();

        // Template operators receive no optional result type only when Clang
        // keeps the result dependent. Reproduce mparser's type_of/is_unresolved
        // decisions over the final owned operands rather than substituting
        // Clang's recursively-dependent predicate: Eparam is unresolved,
        // Eunresolved_global deliberately is not, and T*, arrays, named
        // dependent types, functions, and member pointers are outer-resolved.
        auto mparserNumberOrEnum = [](clang::QualType type) {
            if (type.isNull())
                return false;
            type = type.getCanonicalType().getUnqualifiedType();
            if (type->isEnumeralType())
                return true;
            const auto *builtin = type->getAs<clang::BuiltinType>();
            if (!builtin)
                return false;
            using K = clang::BuiltinType::Kind;
            switch (builtin->getKind()) {
            case K::SChar:
            case K::UChar:
            case K::Short:
            case K::UShort:
            case K::Int:
            case K::UInt:
            case K::Long:
            case K::ULong:
            case K::LongLong:
            case K::ULongLong:
            case K::Int128:
            case K::UInt128:
                return true;
            default:
                return false;
            }
        };
        auto synthesizedTypeOrigins =
            [&]() -> llvm::Expected<factory::OriginList> {
            auto origin = sources.synthesizedNode(origins->front(), *origins);
            if (!origin)
                return origin.takeError();
            return factory::OriginList{*origin};
        };
        auto generatedSemanticType =
            [&](clang::QualType type) -> llvm::Expected<NodeId> {
            auto generatedOrigins = synthesizedTypeOrigins();
            if (!generatedOrigins)
                return generatedOrigins.takeError();
            return buildType(type, mode, std::move(*generatedOrigins));
        };
        auto generatedOperandType =
            [&](NodeId node,
                clang::QualType fallback) -> llvm::Expected<NodeId> {
            auto value = unit->buildingArena().get(node);
            if (!value)
                return value.takeError();
            if ((*value)->constructor ==
                Constructor::ExpressionUnresolvedGlobal) {
                auto children = unit->buildingArena().children(node);
                if (!children)
                    return children.takeError();
                if (children->size() != 1)
                    return llvm::createStringError(
                        std::errc::invalid_argument,
                        "unresolved global expression has malformed children");
                auto generatedOrigins = synthesizedTypeOrigins();
                if (!generatedOrigins)
                    return generatedOrigins.takeError();
                return factory::makeResultGlobalType(
                    unit->buildingArena(), std::move(*generatedOrigins),
                    children->front());
            }
            return generatedSemanticType(fallback);
        };
        auto generatedUnsupportedType =
            [&](llvm::StringRef message) -> llvm::Expected<NodeId> {
            auto generatedOrigins = synthesizedTypeOrigins();
            if (!generatedOrigins)
                return generatedOrigins.takeError();
            return factory::makeUnsupportedType(unit->buildingArena(),
                                                std::move(*generatedOrigins),
                                                message.str());
        };
        const clang::QualType lhsType = binary->getLHS()->getType();
        const clang::QualType rhsType = binary->getRHS()->getType();
        const bool needsInference = mode == SemanticMode::Template &&
                                    (expression.getType().isNull() ||
                                     expression.getType()->isDependentType());
        const bool unresolvedSequence =
            mode == SemanticMode::Template &&
            expressionTypeIsUnresolved(*this, *lhs, lhsType);
        switch (binary->getOpcode()) {
        case clang::BO_Comma:
            if (unresolvedSequence)
                return factory::makeUnresolvedBinarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol("Rcomma"), *lhs, *rhs);
            return factory::makeSequencingExpression(
                unit->buildingArena(), std::move(*origins),
                Constructor::ExpressionComma, *lhs, *rhs);
        case clang::BO_LAnd:
            if (unresolvedSequence)
                return factory::makeUnresolvedBinarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol("Rand"), *lhs, *rhs);
            return factory::makeSequencingExpression(
                unit->buildingArena(), std::move(*origins),
                Constructor::ExpressionSequenceAnd, *lhs, *rhs);
        case clang::BO_LOr:
            if (unresolvedSequence)
                return factory::makeUnresolvedBinarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol("Ror"), *lhs, *rhs);
            return factory::makeSequencingExpression(
                unit->buildingArena(), std::move(*origins),
                Constructor::ExpressionSequenceOr, *lhs, *rhs);
        default:
            break;
        }

        const bool unresolved =
            needsInference &&
            (expressionTypeIsUnresolved(*this, *lhs, lhsType) ||
             expressionTypeIsUnresolved(*this, *rhs, rhsType));
        auto resultType = [&]() -> llvm::Expected<NodeId> {
            if (!needsInference)
                return expressionType();
            switch (binary->getOpcode()) {
            case clang::BO_EQ:
            case clang::BO_NE:
            case clang::BO_LT:
            case clang::BO_LE:
            case clang::BO_GT:
            case clang::BO_GE:
            case clang::BO_Cmp:
                return generatedSemanticType(context.BoolTy);
            case clang::BO_Add:
                if (mparserNumberOrEnum(lhsType) && !rhsType.isNull() &&
                    rhsType->isPointerType())
                    return generatedOperandType(*rhs, rhsType);
                return generatedOperandType(*lhs, lhsType);
            case clang::BO_Sub:
                if (!lhsType.isNull() && !rhsType.isNull()) {
                    const auto *lhsPointer =
                        lhsType->getAs<clang::PointerType>();
                    const auto *rhsPointer =
                        rhsType->getAs<clang::PointerType>();
                    if (lhsPointer && rhsPointer) {
                        if (context.hasSameUnqualifiedType(
                                lhsPointer->getPointeeType(),
                                rhsPointer->getPointeeType()))
                            return generatedSemanticType(context.LongTy);
                        return generatedUnsupportedType(
                            "[mparser] Ebinop Bsub: incompatible pointer "
                            "types");
                    }
                }
                return generatedOperandType(*lhs, lhsType);
            case clang::BO_PtrMemD:
            case clang::BO_PtrMemI:
                return generatedUnsupportedType(
                    binary->getOpcode() == clang::BO_PtrMemD
                        ? "[mparser] Ebinop todo: Bdotp"
                        : "[mparser] Ebinop todo: Bdotip");
            default:
                return generatedOperandType(*lhs, lhsType);
            }
        };
        if (binary->getOpcode() == clang::BO_Assign) {
            if (unresolved)
                return factory::makeUnresolvedBinarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol("Rassign"), *lhs, *rhs);
            auto type = resultType();
            if (!type)
                return type.takeError();
            return factory::makeAssignmentExpression(
                unit->buildingArena(), std::move(*origins), *lhs, *rhs, *type);
        }
        switch (binary->getOpcode()) {
#define COMPOUND_ASSIGNMENT(OPCODE, TERM)                                      \
    case clang::BO_##OPCODE##Assign:                                           \
        if (unresolved)                                                        \
            return factory::makeUnresolvedCompoundAssignmentExpression(        \
                unit->buildingArena(), std::move(*origins),                    \
                ScalarTerm::symbol(#TERM), *lhs, *rhs);                        \
        else {                                                                 \
            auto type = resultType();                                          \
            if (!type)                                                         \
                return type.takeError();                                       \
            return factory::makeCompoundAssignmentExpression(                  \
                unit->buildingArena(), std::move(*origins),                    \
                ScalarTerm::symbol(#TERM), *lhs, *rhs, *type);                 \
        }
            COMPOUND_ASSIGNMENT(Add, Badd);
            COMPOUND_ASSIGNMENT(And, Band);
            COMPOUND_ASSIGNMENT(Div, Bdiv);
            COMPOUND_ASSIGNMENT(Mul, Bmul);
            COMPOUND_ASSIGNMENT(Or, Bor);
            COMPOUND_ASSIGNMENT(Rem, Bmod);
            COMPOUND_ASSIGNMENT(Shl, Bshl);
            COMPOUND_ASSIGNMENT(Shr, Bshr);
            COMPOUND_ASSIGNMENT(Sub, Bsub);
            COMPOUND_ASSIGNMENT(Xor, Bxor);
#undef COMPOUND_ASSIGNMENT
        default:
            break;
        }
        auto operation = binaryOperation(*binary);
        if (!operation)
            return operation.takeError();
        if (unresolved)
            return factory::makeUnresolvedBinaryExpression(
                unit->buildingArena(), std::move(*origins),
                std::move(*operation), *lhs, *rhs);
        auto type = resultType();
        if (!type)
            return type.takeError();
        return factory::makeBinaryExpression(
            unit->buildingArena(), std::move(*origins), std::move(*operation),
            *lhs, *rhs, *type);
    }
    if (const auto *subscript =
            llvm::dyn_cast<clang::ArraySubscriptExpr>(&expression)) {
        struct SubscriptOperand {
            const clang::Expr *written;
            NodeId node;
        };
        auto buildUnderArrayDecay =
            [&](const clang::Expr &value) -> llvm::Expected<SubscriptOperand> {
            if (const auto *cast =
                    llvm::dyn_cast<clang::ImplicitCastExpr>(&value))
                if (cast->getCastKind() == clang::CK_ArrayToPointerDecay) {
                    auto node = forwardExpression(*this, *cast,
                                                  *cast->getSubExpr(), mode);
                    if (!node)
                        return node.takeError();
                    return SubscriptOperand{cast->getSubExpr(), *node};
                }
            auto node = buildExpression(value, mode);
            if (!node)
                return node.takeError();
            return SubscriptOperand{&value, *node};
        };
        auto lhs = buildUnderArrayDecay(*subscript->getLHS());
        if (!lhs)
            return lhs.takeError();
        auto rhs = buildUnderArrayDecay(*subscript->getRHS());
        if (!rhs)
            return rhs.takeError();

        if (mode == SemanticMode::Template) {
            // Evaluate mparser's infer_subscript helper here.  It recognizes
            // only a prvalue arithmetic index paired with an lvalue pointer or
            // an lvalue/xvalue array.  A recognized pointer receives the Cl2r
            // that the helper synthesizes; all other dependent spellings stay
            // unresolved.  In particular, using Clang's dependent result type
            // alone would incorrectly reject T* indexing.
            auto lhsType = ownedExpressionDecltype(*this, lhs->node, *origins);
            if (!lhsType)
                return lhsType.takeError();
            auto rhsType = ownedExpressionDecltype(*this, rhs->node, *origins);
            if (!rhsType)
                return rhsType.takeError();
            auto isIndex = [&](NodeId type) {
                auto node = unit->buildingArena().get(type);
                if (!node)
                    return false;
                return (*node)->constructor == Constructor::TypeNumber ||
                       (*node)->constructor == Constructor::TypeCharacter ||
                       (*node)->constructor == Constructor::TypeBoolean;
            };
            enum class ArrayKind { None, Pointer, Array };
            auto arrayKind = [&](NodeId type) {
                auto reference = unit->buildingArena().get(type);
                if (!reference)
                    return ArrayKind::None;
                const bool lvalue = (*reference)->constructor ==
                                    Constructor::TypeLvalueReference;
                const bool xvalue = (*reference)->constructor ==
                                    Constructor::TypeRvalueReference;
                if ((!lvalue && !xvalue) || (*reference)->arguments.size() != 1)
                    return ArrayKind::None;
                const auto *nested =
                    std::get_if<NodeRef>(&(*reference)->arguments[0].payload);
                if (!nested)
                    return ArrayKind::None;
                auto value = unit->buildingArena().get(nested->value);
                if (!value)
                    return ArrayKind::None;
                if (lvalue && (*value)->constructor == Constructor::TypePointer)
                    return ArrayKind::Pointer;
                if ((*value)->constructor == Constructor::TypeArray ||
                    (*value)->constructor == Constructor::TypeIncompleteArray ||
                    (*value)->constructor == Constructor::TypeVariableArray)
                    return ArrayKind::Array;
                return ArrayKind::None;
            };
            SubscriptOperand *array = nullptr;
            ArrayKind kind = ArrayKind::None;
            if (isIndex(*lhsType) &&
                (kind = arrayKind(*rhsType)) != ArrayKind::None)
                array = &*rhs;
            else if (isIndex(*rhsType) &&
                     (kind = arrayKind(*lhsType)) != ArrayKind::None)
                array = &*lhs;
            if (!array)
                return factory::makeUnresolvedBinarySyntaxExpression(
                    unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol("Rsubscript"), lhs->node, rhs->node);

            if (kind == ArrayKind::Pointer) {
                auto synthetic =
                    sources.synthesizedNode(origins->front(), *origins);
                if (!synthetic)
                    return synthetic.takeError();
                auto cast = factory::makeLvalueToRvalueCast(
                    unit->buildingArena(), {*synthetic});
                if (!cast)
                    return cast.takeError();
                auto converted = factory::makeCastExpression(
                    unit->buildingArena(), {*synthetic}, *cast, array->node);
                if (!converted)
                    return converted.takeError();
                array->node = *converted;
            }
        }

        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeSubscriptExpression(unit->buildingArena(),
                                                std::move(*origins), lhs->node,
                                                rhs->node, *type);
    }
    if (const auto *trait =
            llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(&expression)) {
        auto result = expressionType();
        if (!result)
            return result.takeError();
        switch (trait->getKind()) {
        case clang::UETT_PreferredAlignOf:
            // ParserExpr.Ealignof_preferred deliberately discards its source
            // argument. Do not create unreachable operand/type occurrences.
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), std::move(*origins), "alignof_preferred",
                *result);
        case clang::UETT_SizeOf:
        case clang::UETT_AlignOf:
            break;
        default:
            // This includes __builtin_vectorelements (UETT_VecStep). Legacy
            // emits only its exact numeric kind diagnostic and result type.
            return factory::makeUnsupportedExpression(
                unit->buildingArena(), std::move(*origins),
                "UnaryExprOrTypeTraitExpr(" + std::to_string(trait->getKind()) +
                    ")",
                *result);
        }

        std::optional<NodeId> argument;
        const bool typeArgument = trait->isArgumentType();
        if (typeArgument) {
            auto inherited =
                inheritedTypeOrigins(trait->getArgumentType(), *origins);
            if (!inherited)
                return inherited.takeError();
            auto built = buildType(trait->getArgumentType(), mode,
                                   std::move(*inherited));
            if (!built)
                return built.takeError();
            argument = *built;
        } else if (const clang::Expr *value = trait->getArgumentExpr()) {
            auto built = buildExpression(*value, mode);
            if (!built)
                return built.takeError();
            argument = *built;
        } else {
            return expressionError(expression, "trait without argument");
        }
        return factory::makeTraitExpression(
            unit->buildingArena(), std::move(*origins),
            trait->getKind() == clang::UETT_SizeOf
                ? (typeArgument ? Constructor::ExpressionSizeofType
                                : Constructor::ExpressionSizeofExpression)
                : (typeArgument ? Constructor::ExpressionAlignofType
                                : Constructor::ExpressionAlignofExpression),
            argument, *result);
    }
    if (const auto *sizeOfPack =
            llvm::dyn_cast<clang::SizeOfPackExpr>(&expression)) {
        auto result = expressionType();
        if (!result)
            return result.takeError();
        const clang::NamedDecl *pack = sizeOfPack->getPack();
        const std::string name =
            pack && pack->getIdentifier()
                ? pack->getIdentifier()->getName().str()
                : (pack ? pack->getNameAsString() : "<unknown pack>");
        if (sizeOfPack->isValueDependent())
            return factory::makeUnresolvedSizeofPackExpression(
                unit->buildingArena(), std::move(*origins), name, *result);
        return factory::makeIntegerExpression(
            unit->buildingArena(), std::move(*origins),
            std::to_string(sizeOfPack->getPackLength()), *result);
    }

    if (const auto *integer =
            llvm::dyn_cast<clang::IntegerLiteral>(&expression)) {
        llvm::SmallString<32> text;
        if (integer->getType()->isSignedIntegerOrEnumerationType())
            integer->getValue().toStringSigned(text);
        else
            integer->getValue().toStringUnsigned(text);
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeIntegerExpression(unit->buildingArena(),
                                              std::move(*origins),
                                              text.str().str(), *type);
    }
    if (const auto *boolean =
            llvm::dyn_cast<clang::CXXBoolLiteralExpr>(&expression))
        return factory::makeBooleanExpression(
            unit->buildingArena(), std::move(*origins), boolean->getValue());
    if (const auto *character =
            llvm::dyn_cast<clang::CharacterLiteral>(&expression)) {
        auto type = expressionType();
        if (!type)
            return type.takeError();
        return factory::makeCharacterExpression(unit->buildingArena(),
                                                std::move(*origins),
                                                character->getValue(), *type);
    }
    if (const auto *floating =
            llvm::dyn_cast<clang::FloatingLiteral>(&expression)) {
        const clang::BuiltinType *builtin =
            floating->getType()->getAs<clang::BuiltinType>();
        const char *floatType = nullptr;
        if (builtin)
            switch (builtin->getKind()) {
            case clang::BuiltinType::Float16:
                if (floating->getRawSemantics() ==
                    llvm::APFloatBase::S_IEEEhalf)
                    floatType = "float_type.Ffloat16";
                break;
            case clang::BuiltinType::Float:
                if (floating->getRawSemantics() ==
                    llvm::APFloatBase::S_IEEEsingle)
                    floatType = "float_type.Ffloat";
                break;
            case clang::BuiltinType::Double:
                if (floating->getRawSemantics() ==
                    llvm::APFloatBase::S_IEEEdouble)
                    floatType = "float_type.Fdouble";
                break;
            case clang::BuiltinType::Float128:
                if (floating->getRawSemantics() ==
                    llvm::APFloatBase::S_IEEEquad)
                    floatType = "float_type.Ffloat128";
                break;
            default:
                break;
            }
        if (!floatType) {
            std::string reason;
            llvm::raw_string_ostream reasonStream(reason);
            reasonStream << "unsupported floating-point semantics "
                         << floatSemanticsName(floating->getRawSemantics())
                         << " for " << builtinFloatName(builtin);
            std::string diagnostic;
            llvm::raw_string_ostream diagnosticStream(diagnostic);
            diagnosticStream << reasonStream.str() << ": ";
            floating->getValue().print(diagnosticStream);
            return buildUnsupportedExpression(*this, expression, mode,
                                              std::move(*origins),
                                              diagnosticStream.str());
        }
        llvm::SmallString<64> bits;
        floating->getValue().bitcastToAPInt().toStringUnsigned(bits);
        return factory::makeFloatExpression(
            unit->buildingArena(), std::move(*origins),
            ScalarTerm::symbol(floatType), bits.str().str());
    }
    if (const auto *literal =
            llvm::dyn_cast<clang::StringLiteral>(&expression)) {
        const clang::ArrayType *array =
            context.getAsArrayType(literal->getType());
        if (!array)
            return expressionError(expression, "non-array string literal");
        // Legacy print_string_type intentionally emits the unqualified array
        // element type; the semantic Estring adds its own trailing NUL.
        auto type = semanticType(array->getElementType().getUnqualifiedType());
        if (!type)
            return type.takeError();
        return factory::makeStringExpression(unit->buildingArena(),
                                             std::move(*origins),
                                             stringCharacters(*literal), *type);
    }
    if (const auto *predefined =
            llvm::dyn_cast<clang::PredefinedExpr>(&expression)) {
        const clang::StringLiteral *name = predefined->getFunctionName();
        const clang::ArrayType *array =
            context.getAsArrayType(predefined->getType());
        if (!name || !array) {
            auto type = factory::makeLeafType(
                unit->buildingArena(), Constructor::TypeCharacter, *origins,
                ScalarTerm::symbol("char_type.Cchar"));
            if (!type)
                return type.takeError();
            return factory::makeUnresolvedStringExpression(
                unit->buildingArena(), std::move(*origins), *type);
        }
        auto type = semanticType(array->getElementType().getUnqualifiedType());
        if (!type)
            return type.takeError();
        return factory::makeStringExpression(unit->buildingArena(),
                                             std::move(*origins),
                                             stringCharacters(*name), *type);
    }
    if (const auto *source =
            llvm::dyn_cast<clang::SourceLocExpr>(&expression)) {
        clang::APValue value = source->EvaluateInContext(context, nullptr);
        if (source->isIntType()) {
            auto type = expressionType();
            if (!type)
                return type.takeError();
            llvm::SmallString<32> text;
            value.getInt().toString(text);
            auto synthetic =
                sources.synthesizedNode(origins->front(), *origins);
            if (!synthetic)
                return synthetic.takeError();
            auto integer = factory::makeIntegerExpression(
                unit->buildingArena(), {*synthetic}, text.str().str(), *type);
            if (!integer)
                return integer.takeError();
            auto integerNode = unit->buildingArena().get(*integer);
            if (!integerNode)
                return integerNode.takeError();
            auto transformed = sources.transformedNode(
                clang::CharSourceRange::getTokenRange(source->getSourceRange()),
                (*integerNode)->origins);
            if (!transformed)
                return transformed.takeError();
            return factory::cloneWithOrigins(unit->buildingArena(), *integer,
                                             {*transformed});
        }
        const clang::APValue::LValueBase base = value.getLValueBase();
        if (!base.is<const clang::Expr *>())
            return expressionError(expression, "source location lvalue base");
        const auto *literal = llvm::dyn_cast<clang::StringLiteral>(
            base.get<const clang::Expr *>());
        const clang::ArrayType *array =
            literal ? context.getAsArrayType(literal->getType()) : nullptr;
        if (!literal || !array)
            return expressionError(expression,
                                   "source location string evaluation");
        auto synthetic = sources.synthesizedNode(origins->front(), *origins);
        if (!synthetic)
            return synthetic.takeError();
        clang::QualType element = array->getElementType().getUnqualifiedType();
        auto inherited = inheritedTypeOrigins(element, {*synthetic});
        if (!inherited)
            return inherited.takeError();
        auto type = buildType(element, mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        auto string =
            factory::makeStringExpression(unit->buildingArena(), {*synthetic},
                                          stringCharacters(*literal), *type);
        if (!string)
            return string.takeError();
        auto transformed = sources.transformedNode(
            clang::CharSourceRange::getTokenRange(source->getSourceRange()),
            {*synthetic});
        if (!transformed)
            return transformed.takeError();
        return factory::cloneWithOrigins(unit->buildingArena(), *string,
                                         {*transformed});
    }
    if (const auto *offset = llvm::dyn_cast<clang::OffsetOfExpr>(&expression)) {
        if (offset->getNumComponents() != 1 ||
            offset->getComponent(0).getKind() !=
                clang::OffsetOfNode::Kind::Field)
            return buildUnsupportedExpression(*this, expression, mode,
                                              std::move(*origins),
                                              expression.getStmtClassName());
        const clang::FieldDecl *field = offset->getComponent(0).getField();
        const clang::RecordDecl *parent = field ? field->getParent() : nullptr;
        if (!field || !parent)
            return expressionError(expression, "offsetof field");
#if CLANG_VERSION_MAJOR >= 22
        const clang::QualType parentType = context.getTagType(
            clang::ElaboratedTypeKeyword::None, std::nullopt, parent, false);
#else
        const clang::Type *parentTypePointer = parent->getTypeForDecl();
        const clang::QualType parentType(parentTypePointer, 0);
#endif
        if (parentType.isNull())
            return expressionError(expression, "offsetof parent type");
        auto inherited = inheritedTypeOrigins(parentType, *origins);
        if (!inherited)
            return inherited.takeError();
        auto parentNode = buildType(parentType, mode, std::move(*inherited));
        if (!parentNode)
            return parentNode.takeError();
        auto type = buildDeclType(*this, expression, mode, *origins);
        if (!type)
            return type.takeError();
        return factory::makeOffsetOfExpression(unit->buildingArena(),
                                               std::move(*origins), *parentNode,
                                               field->getName().str(), *type);
    }
    if (llvm::isa<clang::GNUNullExpr>(&expression)) {
        auto type = expressionType();
        if (!type)
            return type.takeError();
        auto synthetic = sources.synthesizedNode(origins->front(), *origins);
        if (!synthetic)
            return synthetic.takeError();
        auto descriptor = factory::makeTypeCast(
            unit->buildingArena(), Constructor::CastPointerToIntegral,
            {*synthetic}, *type);
        if (!descriptor)
            return descriptor.takeError();
        auto null =
            factory::makeNullExpression(unit->buildingArena(), {*synthetic});
        if (!null)
            return null.takeError();
        return factory::makeCastExpression(
            unit->buildingArena(), std::move(*origins), *descriptor, *null);
    }
    if (llvm::isa<clang::CXXNullPtrLiteralExpr>(&expression))
        return factory::makeNullExpression(unit->buildingArena(),
                                           std::move(*origins));
    if (const auto *noexceptExpr =
            llvm::dyn_cast<clang::CXXNoexceptExpr>(&expression))
        return factory::makeBooleanExpression(unit->buildingArena(),
                                              std::move(*origins),
                                              noexceptExpr->getValue());
    if (const auto *trait = llvm::dyn_cast<clang::TypeTraitExpr>(&expression)) {
        if (trait->isInstantiationDependent())
            return buildUnsupportedExpression(*this, expression, mode,
                                              std::move(*origins),
                                              "dependent type trait expr");
#if CLANG_VERSION_MAJOR >= 21
        const bool value = trait->getBoolValue();
#else
        const bool value = trait->getValue();
#endif
        return factory::makeBooleanExpression(unit->buildingArena(),
                                              std::move(*origins), value);
    }
    if (const auto *conceptExpression =
            llvm::dyn_cast<clang::ConceptSpecializationExpr>(&expression)) {
        if (conceptExpression->getDependence() &&
            mode == SemanticMode::Template)
            return buildUnsupportedExpression(
                *this, expression, mode, std::move(*origins),
                "potentially dependent concept specialization");
        if (conceptExpression->getDependence())
            return factory::makeBooleanExpression(
                unit->buildingArena(), std::move(*origins),
                conceptExpression->isSatisfied());
        auto generated = sources.synthesizedNode(origins->front(), *origins);
        if (!generated)
            return generated.takeError();
        auto type = factory::makeLeafType(
            unit->buildingArena(), Constructor::TypeBoolean, {*generated});
        if (!type)
            return type.takeError();
        return factory::makeUnsupportedExpression(
            unit->buildingArena(), std::move(*origins),
            "unresolved concept specialization", *type);
    }
    if (llvm::isa<clang::ImaginaryLiteral, clang::FixedPointLiteral>(
            &expression))
        return buildUnsupportedExpression(*this, expression, mode,
                                          std::move(*origins),
                                          expression.getStmtClassName());
    if (const auto *dependent =
            llvm::dyn_cast<clang::DependentScopeDeclRefExpr>(&expression)) {
        if (mode == SemanticMode::Static)
            return expressionError(
                expression,
                "dependent reference requires template semantic mode");
        auto name = buildUnresolvedName(
            dependent->getQualifier(), dependent->getQualifierLoc(),
            dependent->getDeclName(), dependent->template_arguments(), mode,
            *origins);
        if (!name)
            return name.takeError();
        return factory::makeGlobalExpression(
            unit->buildingArena(), std::move(*origins), *name, NodeId{}, true);
    }
    if (const auto *unresolved =
            llvm::dyn_cast<clang::UnresolvedLookupExpr>(&expression)) {
        if (mode == SemanticMode::Static)
            return expressionError(
                expression,
                "unresolved lookup requires template semantic mode");
        llvm::ArrayRef<clang::TemplateArgumentLoc> arguments;
        if (unresolved->hasExplicitTemplateArgs())
            arguments = {unresolved->template_arguments().begin(),
                         unresolved->getNumTemplateArgs()};
        auto name = buildUnresolvedName(
            unresolved->getQualifier(), unresolved->getQualifierLoc(),
            unresolved->getName(), arguments, mode, *origins);
        if (!name)
            return name.takeError();
        return factory::makeGlobalExpression(
            unit->buildingArena(), std::move(*origins), *name, NodeId{}, true);
    }
    if (const auto *reference =
            llvm::dyn_cast<clang::DeclRefExpr>(&expression)) {
        const clang::ValueDecl *declaration = reference->getDecl();
        if (!declaration)
            return expressionError(expression, "null declaration reference");
        if (reference->refersToEnclosingVariableOrCapture()) {
            const auto lambda = enclosingLambda(
                context, expression, activeCaptureInitializerClosures);
            if (lambda) {
                auto generated =
                    sources.synthesizedNode(origins->front(), *origins);
                if (!generated)
                    return generated.takeError();
                if (const clang::FieldDecl *field =
                        captureField(*lambda->closure, *declaration)) {
                    const llvm::StringRef name = declaration->getName();
                    if (name.empty())
                        return expressionError(expression,
                                               "anonymous lambda capture");
                    return buildCaptureMember(*this, *lambda, *field, name,
                                              mode, std::move(*origins),
                                              *generated);
                }
                const llvm::StringRef name = declaration->getName();
                if (name.empty())
                    return expressionError(expression,
                                           "anonymous unevaluated capture");
                auto inherited =
                    inheritedTypeOrigins(expression.getType(), {*generated});
                if (!inherited)
                    return inherited.takeError();
                auto type = buildType(expression.getType(), mode,
                                      std::move(*inherited));
                if (!type)
                    return type.takeError();
                auto referenceType = factory::makeUnaryType(
                    unit->buildingArena(), Constructor::TypeLvalueReference,
                    {*generated}, *type);
                if (!referenceType)
                    return referenceType.takeError();
                return factory::makeUnsupportedExpression(
                    unit->buildingArena(), std::move(*origins),
                    (llvm::Twine("Unevaluated variable: ") + name).str(),
                    *referenceType);
            }
        }
        // Legacy lowers a builtin only at the enclosing
        // CK_BuiltinFnToFnPtr implicit cast. A bare/unevaluated reference is
        // an ordinary declaration reference and must retain its function type.
        if (const auto *constant =
                llvm::dyn_cast<clang::EnumConstantDecl>(declaration)) {
            const auto *enumeration =
                llvm::dyn_cast<clang::EnumDecl>(constant->getDeclContext());
            if (!enumeration)
                return expressionError(expression,
                                       "enum constant without enumeration");
            auto enumName = buildName(*enumeration, mode);
            if (!enumName)
                return enumName.takeError();
            auto enumValue = factory::makeEnumConstantExpression(
                unit->buildingArena(), *origins, *enumName,
                constant->getName().str());
            if (!enumValue)
                return enumValue.takeError();
            if (expression.getType()->isEnumeralType())
                return *enumValue;
            auto resultType = expressionType();
            if (!resultType)
                return resultType.takeError();
            auto synthetic =
                sources.synthesizedNode(origins->front(), *origins);
            if (!synthetic)
                return synthetic.takeError();
            auto cast = factory::makeIntegralCast(unit->buildingArena(),
                                                  {*synthetic}, *resultType);
            if (!cast)
                return cast.takeError();
            return factory::makeCastExpression(
                unit->buildingArena(), std::move(*origins), *cast, *enumValue);
        }
        if (const auto *parameter =
                llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(declaration)) {
            // In an instantiated static AST Clang normally supplies a
            // SubstNonTypeTemplateParmExpr, handled by the forwarding branch
            // above. A direct parameter reference has no static substitution
            // to serialize and must not become template-only Eparam.
            if (mode == SemanticMode::Static)
                return expressionError(
                    expression,
                    "template value parameter lacks static substitution");
            const clang::IdentifierInfo *identifier =
                parameter->getIdentifier();
            const std::string name =
                identifier
                    ? identifier->getName().str()
                    : "__value_" + std::to_string(parameter->getDepth()) + "_" +
                          std::to_string(parameter->getIndex());
            return factory::makeParameterExpression(unit->buildingArena(),
                                                    std::move(*origins), name);
        }
        clang::QualType declarationType = declaration->getType();
        if (const auto *binding =
                llvm::dyn_cast<clang::BindingDecl>(declaration))
            if (const clang::VarDecl *holding = binding->getHoldingVar())
                declarationType = holding->getType();
        const clang::DeclContext *declarationContext =
            declaration->getDeclContext();
        const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration);
        const bool staticLocal = variable && variable->isStaticLocal();
        if (declarationContext && declarationContext->isFunctionOrMethod() &&
            !llvm::isa<clang::FunctionDecl>(declaration) && !staticLocal) {
            auto type = semanticType(declarationType);
            if (!type)
                return type.takeError();
            if (declaration->getIdentifier())
                return factory::makeLocalExpression(
                    unit->buildingArena(), std::move(*origins),
                    localIdentifier(*declaration), *type);
            const auto active = anonymousLocals.find(declaration);
            const std::uint64_t index = active == anonymousLocals.end()
                                            ? anonymousLocalIndex(*declaration)
                                            : active->second;
            return factory::makeAnonymousLocalExpression(
                unit->buildingArena(), std::move(*origins), index, *type);
        }
        if (!declarationContext)
            return expressionError(expression, "declaration without context");
        auto name = buildName(*declaration, mode);
        if (!name)
            return name.takeError();
        auto type = semanticType(declarationType);
        if (!type)
            return type.takeError();
        return factory::makeGlobalExpression(
            unit->buildingArena(), std::move(*origins), *name, *type, false);
    }
    if (const auto *statementExpression =
            llvm::dyn_cast<clang::StmtExpr>(&expression)) {
        auto statement =
            buildSingleStatement(statementExpression->getSubStmt(), mode);
        if (!statement)
            return statement.takeError();
        auto type = buildDeclType(*this, expression, mode, *origins);
        if (!type)
            return type.takeError();
        return factory::makeStatementBlockExpression(
            unit->buildingArena(), std::move(*origins), *statement, *type);
    }
    return buildUnsupportedExpression(*this, expression, mode,
                                      std::move(*origins),
                                      expression.getStmtClassName());
}

} // namespace builder
} // namespace ir
