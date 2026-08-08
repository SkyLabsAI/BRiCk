/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include "IR.hpp"

#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace ir {
namespace factory {

using OriginList = std::vector<source::OriginId>;
using TemplateParameters = std::vector<Value>;

llvm::Expected<TemplateParameters>
packTemplateParameters(const Arena &,
                       const std::vector<TemplateParameterEntry> &);

llvm::Expected<NodeId> makeAtomicIdentifier(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeAtomicAnonymousIndex(Arena &, OriginList,
                                                std::uint64_t);
llvm::Expected<NodeId> makeAtomicAnonymousNamespace(Arena &, OriginList);
llvm::Expected<NodeId> makeAtomicFirstDeclaration(Arena &, OriginList,
                                                  std::string);
llvm::Expected<NodeId> makeAtomicFirstChild(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeAtomicUnsupported(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeAtomicFunction(Arena &, OriginList, ScalarTerm,
                                          std::string, std::vector<NodeId>);
llvm::Expected<NodeId> makeAtomicConstructor(Arena &, OriginList,
                                             std::vector<NodeId>);
llvm::Expected<NodeId> makeAtomicDestructor(Arena &, OriginList);
llvm::Expected<NodeId> makeAtomicOperator(Arena &, OriginList, ScalarTerm,
                                          ScalarTerm, std::vector<NodeId>);
llvm::Expected<NodeId>
makeAtomicAllocationOperator(Arena &, OriginList, ScalarTerm qualifiers,
                             bool isDelete, bool isArray,
                             std::vector<NodeId> parameters);
llvm::Expected<NodeId> makeAtomicConversion(Arena &, OriginList, ScalarTerm,
                                            NodeId);
llvm::Expected<NodeId> makeAtomicLiteralOperator(Arena &, OriginList,
                                                 std::string,
                                                 std::vector<NodeId>);
llvm::Expected<NodeId> makeGlobalName(Arena &, OriginList, NodeId atomic);
llvm::Expected<NodeId> makeScopedName(Arena &, OriginList, NodeId scope,
                                      NodeId atomic);
llvm::Expected<NodeId> makeInstantiatedName(Arena &, OriginList, NodeId,
                                            std::vector<NodeId>);
llvm::Expected<NodeId> makeDependentName(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeUnsupportedName(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeNamedType(Arena &, OriginList, NodeId name);
llvm::Expected<NodeId> makeEnumType(Arena &, OriginList, NodeId name);
llvm::Expected<NodeId> makeTypeParameter(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeResultGlobalType(Arena &, OriginList, NodeId name);
llvm::Expected<NodeId> makeResultCallType(Arena &, OriginList, NodeId name,
                                          std::vector<NodeId> arguments);
llvm::Expected<NodeId> makeResultUnarySyntaxType(Arena &, OriginList,
                                                 ScalarTerm, NodeId type);
llvm::Expected<NodeId> makeResultMemberType(Arena &, OriginList, NodeId type,
                                            NodeId name);
llvm::Expected<NodeId> makeNumberType(Arena &, OriginList, ScalarTerm,
                                      ScalarTerm);
llvm::Expected<NodeId> makeLeafType(Arena &, Constructor, OriginList,
                                    std::optional<ScalarTerm> = std::nullopt);
llvm::Expected<NodeId> makeUnaryType(Arena &, Constructor, OriginList, NodeId);
llvm::Expected<NodeId> makeArrayType(Arena &, OriginList, NodeId,
                                     std::uint64_t);
llvm::Expected<NodeId> makeVariableArrayType(Arena &, OriginList, NodeId,
                                             NodeId);
llvm::Expected<NodeId> makeQualifiedType(Arena &, OriginList, ScalarTerm,
                                         NodeId);
llvm::Expected<NodeId> makeFunctionType(Arena &, OriginList, ScalarTerm,
                                        ScalarTerm, NodeId,
                                        std::vector<NodeId>);
llvm::Expected<NodeId> makeMemberPointerType(Arena &, OriginList, NodeId,
                                             NodeId);
llvm::Expected<NodeId> makeExpressionType(Arena &, Constructor, OriginList,
                                          NodeId);
llvm::Expected<NodeId> makeArchitectureType(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeUnsupportedType(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeIntegerExpression(Arena &, OriginList, std::string,
                                             NodeId type);
llvm::Expected<NodeId> makeBooleanExpression(Arena &, OriginList, bool);
llvm::Expected<NodeId> makeStringExpression(Arena &, OriginList,
                                            std::vector<std::uint64_t>, NodeId);
llvm::Expected<NodeId> makeStringExpression(Arena &, OriginList, std::string,
                                            NodeId);
llvm::Expected<NodeId> makeCharacterExpression(Arena &, OriginList,
                                               std::uint64_t, NodeId);
llvm::Expected<NodeId> makeFloatExpression(Arena &, OriginList, ScalarTerm,
                                           std::string bits);
llvm::Expected<NodeId> makeUnsupportedExpression(Arena &, OriginList,
                                                 std::string, NodeId);
llvm::Expected<NodeId> makeUnresolvedStringExpression(Arena &, OriginList,
                                                      NodeId);
llvm::Expected<NodeId> makeNullExpression(Arena &, OriginList);
llvm::Expected<NodeId> makeParameterExpression(Arena &, OriginList,
                                               std::string);
llvm::Expected<NodeId> makeGlobalExpression(Arena &, OriginList, NodeId, NodeId,
                                            bool unresolved);
llvm::Expected<NodeId> makeGlobalMemberExpression(Arena &, OriginList, NodeId,
                                                  NodeId);
llvm::Expected<NodeId> makeEnumConstantExpression(Arena &, OriginList,
                                                  NodeId enumName,
                                                  std::string constant);
llvm::Expected<NodeId> makeAddressOfExpression(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeLocalExpression(Arena &, OriginList, std::string,
                                           NodeId);
llvm::Expected<NodeId> makeAnonymousLocalExpression(Arena &, OriginList,
                                                    std::uint64_t, NodeId);
llvm::Expected<NodeId> makeUnaryExpression(Arena &, OriginList, ScalarTerm,
                                           NodeId, std::optional<NodeId>);
llvm::Expected<NodeId> makeUnsupportedUnaryExpression(Arena &, OriginList,
                                                      std::string, NodeId,
                                                      std::optional<NodeId>);
llvm::Expected<NodeId>
makeUnresolvedBinaryExpression(Arena &, OriginList, ScalarTerm, NodeId, NodeId);
llvm::Expected<NodeId> makeUnresolvedUnarySyntaxExpression(Arena &, OriginList,
                                                           ScalarTerm, NodeId);
llvm::Expected<NodeId> makeUnresolvedBinarySyntaxExpression(Arena &, OriginList,
                                                            ScalarTerm, NodeId,
                                                            NodeId);
llvm::Expected<NodeId>
makeUnresolvedCompoundAssignmentExpression(Arena &, OriginList, ScalarTerm,
                                           NodeId, NodeId);
llvm::Expected<NodeId> makeNullaryCast(Arena &, Constructor, OriginList);
llvm::Expected<NodeId> makeTypeCast(Arena &, Constructor, OriginList, NodeId);
llvm::Expected<NodeId> makePathCast(Arena &, Constructor, OriginList,
                                    std::vector<NodeId>, NodeId);
llvm::Expected<NodeId> makeUnsupportedCast(Arena &, OriginList, std::string,
                                           NodeId);
llvm::Expected<NodeId> makeBuiltinToFunctionCast(Arena &, OriginList,
                                                 NodeId pointerType);
llvm::Expected<NodeId> makeLvalueToRvalueCast(Arena &, OriginList);
llvm::Expected<NodeId> makeIntegralCast(Arena &, OriginList, NodeId type);
llvm::Expected<NodeId> makeCastExpression(Arena &, OriginList, NodeId cast,
                                          NodeId expression);
llvm::Expected<NodeId> makeExplicitCastExpression(Arena &, OriginList,
                                                  ScalarTerm style,
                                                  NodeId writtenType,
                                                  NodeId castExpression);
llvm::Expected<NodeId> makeBinaryExpression(Arena &, OriginList,
                                            ScalarTerm operation, NodeId lhs,
                                            NodeId rhs, NodeId resultType);
llvm::Expected<NodeId> makeDerefExpression(Arena &, OriginList, NodeId, NodeId);
llvm::Expected<NodeId> makeAssignmentExpression(Arena &, OriginList, NodeId,
                                                NodeId, NodeId);
llvm::Expected<NodeId> makeCompoundAssignmentExpression(Arena &, OriginList,
                                                        ScalarTerm, NodeId,
                                                        NodeId, NodeId);
llvm::Expected<NodeId> makeIncrementExpression(Arena &, OriginList, Constructor,
                                               NodeId, NodeId);
llvm::Expected<NodeId> makeSequencingExpression(Arena &, OriginList,
                                                Constructor, NodeId, NodeId);
llvm::Expected<NodeId> makeSubscriptExpression(Arena &, OriginList, NodeId,
                                               NodeId, NodeId);
llvm::Expected<NodeId> makeTraitExpression(Arena &, OriginList, Constructor,
                                           std::optional<NodeId>, NodeId);
llvm::Expected<NodeId> makeUnresolvedSizeofPackExpression(Arena &, OriginList,
                                                          std::string, NodeId);
llvm::Expected<NodeId> makeCallExpression(Arena &, OriginList, NodeId,
                                          std::vector<NodeId>);
llvm::Expected<NodeId> makeUnresolvedCallExpression(Arena &, OriginList, NodeId,
                                                    std::vector<NodeId>);
llvm::Expected<NodeId> makeMemberExpression(Arena &, OriginList, bool, NodeId,
                                            NodeId, bool, NodeId);
llvm::Expected<NodeId> makeMemberIgnoreExpression(Arena &, OriginList, bool,
                                                  NodeId, NodeId);
llvm::Expected<NodeId> makeUnresolvedMemberExpression(Arena &, OriginList,
                                                      NodeId, NodeId);
llvm::Expected<NodeId> makeDirectMemberCallExpression(Arena &, OriginList, bool,
                                                      NodeId, ScalarTerm,
                                                      NodeId, NodeId,
                                                      std::vector<NodeId>);
llvm::Expected<NodeId> makePointerMemberCallExpression(Arena &, OriginList,
                                                       bool, NodeId, NodeId,
                                                       std::vector<NodeId>);
llvm::Expected<NodeId> makeFunctionOperatorCallExpression(Arena &, OriginList,
                                                          ScalarTerm, NodeId,
                                                          NodeId,
                                                          std::vector<NodeId>);
llvm::Expected<NodeId> makeMethodOperatorCallExpression(Arena &, OriginList,
                                                        ScalarTerm, NodeId,
                                                        ScalarTerm, NodeId,
                                                        std::vector<NodeId>);
llvm::Expected<NodeId> makeThisExpression(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeImplicitExpression(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeConstructorExpression(Arena &, OriginList, NodeId,
                                                 std::vector<NodeId>, NodeId);
llvm::Expected<NodeId> makeInheritedConstructorExpression(Arena &, OriginList,
                                                          NodeId, std::size_t,
                                                          NodeId);
llvm::Expected<NodeId>
makeUnresolvedInitializerListExpression(Arena &, OriginList, Constructor,
                                        std::optional<NodeId>,
                                        std::vector<NodeId>);
llvm::Expected<NodeId> makeInitListExpression(Arena &, OriginList,
                                              std::vector<NodeId>,
                                              std::optional<NodeId>, NodeId);
llvm::Expected<NodeId> makeUnionInitListExpression(Arena &, OriginList, NodeId,
                                                   std::optional<NodeId>,
                                                   NodeId);
llvm::Expected<NodeId> makeAndCleanExpression(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeMaterializeTemporaryExpression(Arena &, OriginList,
                                                          NodeId, ScalarTerm);
llvm::Expected<NodeId> makeImplicitInitExpression(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeArrayLoopInitExpression(Arena &, OriginList,
                                                   std::uint64_t, NodeId,
                                                   std::uint64_t, std::string,
                                                   NodeId, NodeId);
llvm::Expected<NodeId> makeArrayLoopIndexExpression(Arena &, OriginList,
                                                    std::uint64_t, NodeId);
llvm::Expected<NodeId> makeOpaqueReferenceExpression(Arena &, OriginList,
                                                     std::uint64_t, NodeId);
llvm::Expected<NodeId> makeNewExpression(Arena &, OriginList, NodeId, NodeId,
                                         std::vector<NodeId>, bool, bool,
                                         NodeId, std::optional<NodeId>,
                                         std::optional<NodeId>);
llvm::Expected<NodeId> makeDeleteExpression(Arena &, OriginList, bool, NodeId,
                                            NodeId, NodeId);
llvm::Expected<NodeId> makeFunctionAllocationOperatorCallExpression(
    Arena &, OriginList, bool, bool, NodeId, NodeId, std::vector<NodeId>);
llvm::Expected<NodeId>
makeMethodAllocationOperatorCallExpression(Arena &, OriginList, bool, bool,
                                           NodeId, ScalarTerm, NodeId,
                                           std::vector<NodeId>);
llvm::Expected<NodeId> makeAtomicExpression(Arena &, OriginList, std::string,
                                            std::vector<NodeId>, NodeId);
llvm::Expected<NodeId> makeVaArgExpression(Arena &, OriginList, NodeId, NodeId);
llvm::Expected<NodeId> makeLambdaExpression(Arena &, OriginList, NodeId,
                                            std::vector<NodeId>);
llvm::Expected<NodeId> makeConditionalExpression(Arena &, OriginList, NodeId,
                                                 NodeId, NodeId, NodeId);
llvm::Expected<NodeId> makeBinaryConditionalExpression(Arena &, OriginList,
                                                       std::uint64_t, NodeId,
                                                       NodeId, NodeId, NodeId,
                                                       NodeId);
llvm::Expected<NodeId> makeOffsetOfExpression(Arena &, OriginList, NodeId,
                                              std::string, NodeId);
llvm::Expected<NodeId> makeStatementBlockExpression(Arena &, OriginList, NodeId,
                                                    NodeId);
llvm::Expected<NodeId> makePseudoDestructorExpression(Arena &, OriginList, bool,
                                                      NodeId, NodeId);
llvm::Expected<NodeId> makeExpressionStatement(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeReturnStatement(Arena &, OriginList,
                                           std::optional<NodeId> expression);
llvm::Expected<NodeId> makeStatementSequence(Arena &, OriginList,
                                             std::vector<NodeId>);
llvm::Expected<NodeId> makeDeclarationStatement(Arena &, OriginList,
                                                std::vector<NodeId>);
llvm::Expected<NodeId> makeIfStatement(Arena &, OriginList,
                                       std::optional<NodeId>,
                                       std::optional<NodeId>, NodeId, NodeId,
                                       NodeId);
llvm::Expected<NodeId> makeIfConstevalStatement(Arena &, OriginList, NodeId,
                                                NodeId);
llvm::Expected<NodeId>
makeWhileStatement(Arena &, OriginList, std::optional<NodeId>, NodeId, NodeId);
llvm::Expected<NodeId> makeForStatement(Arena &, OriginList,
                                        std::optional<NodeId>,
                                        std::optional<NodeId>,
                                        std::optional<NodeId>, NodeId);
llvm::Expected<NodeId> makeDoStatement(Arena &, OriginList, NodeId, NodeId);
llvm::Expected<NodeId> makeSwitchStatement(Arena &, OriginList,
                                           std::optional<NodeId>,
                                           std::optional<NodeId>, NodeId,
                                           NodeId);
llvm::Expected<NodeId> makeCaseStatement(Arena &, OriginList, ScalarTerm);
llvm::Expected<NodeId> makeLeafStatement(Arena &, Constructor, OriginList);
llvm::Expected<NodeId> makeAttributeStatement(Arena &, OriginList,
                                              std::vector<std::string>, NodeId);
llvm::Expected<NodeId>
makeAsmStatement(Arena &, OriginList, std::string, bool,
                 std::vector<std::pair<std::string, NodeId>>,
                 std::vector<std::pair<std::string, NodeId>>,
                 std::vector<std::string>);
llvm::Expected<NodeId> makeLabeledStatement(Arena &, OriginList, std::string,
                                            NodeId);
llvm::Expected<NodeId> makeGotoStatement(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeUnsupportedStatement(Arena &, OriginList,
                                                std::string);
struct DeclarationParameter {
    ScalarTerm name;
    NodeId type;
};
struct StructBaseValue {
    NodeId name;
    NodeId layout;
};
struct StructVirtualValue {
    NodeId name;
    std::optional<NodeId> implementation;
};
struct StructOverrideValue {
    NodeId overridden;
    NodeId overriding;
};

llvm::Expected<NodeId> makeGlobalInitializer(Arena &, Constructor, OriginList,
                                             std::optional<NodeId> expression);
llvm::Expected<NodeId> makeFunctionBody(Arena &, Constructor, OriginList,
                                        std::optional<NodeId> statement,
                                        std::string builtin = {});
llvm::Expected<NodeId> makeDefaultStatementBody(Arena &, Constructor,
                                                OriginList,
                                                std::optional<NodeId>);
llvm::Expected<NodeId> makeConstructorBody(Arena &, Constructor, OriginList,
                                           std::vector<NodeId>,
                                           std::optional<NodeId>);
llvm::Expected<NodeId> makeFunctionRecord(Arena &, OriginList, NodeId,
                                          std::vector<DeclarationParameter>,
                                          ScalarTerm, ScalarTerm, ScalarTerm,
                                          std::optional<NodeId>);
llvm::Expected<NodeId> makeMethodRecord(Arena &, OriginList, NodeId, NodeId,
                                        ScalarTerm,
                                        std::vector<DeclarationParameter>,
                                        ScalarTerm, ScalarTerm, ScalarTerm,
                                        std::optional<NodeId>);
llvm::Expected<NodeId>
makeInitializerPath(Arena &, Constructor, OriginList,
                    std::optional<NodeId> = std::nullopt);
llvm::Expected<NodeId> makeInitializerRecord(Arena &, OriginList, NodeId,
                                             NodeId);
llvm::Expected<NodeId> makeConstructorRecord(Arena &, OriginList, NodeId,
                                             std::vector<DeclarationParameter>,
                                             ScalarTerm, ScalarTerm, ScalarTerm,
                                             std::optional<NodeId>);
llvm::Expected<NodeId> makeDestructorRecord(Arena &, OriginList, NodeId,
                                            ScalarTerm, ScalarTerm,
                                            std::optional<NodeId>);
llvm::Expected<NodeId> makeLayoutInfo(Arena &, OriginList, std::string);
llvm::Expected<NodeId> makeMemberRecord(Arena &, OriginList, NodeId, NodeId,
                                        bool, std::optional<NodeId>, NodeId);
llvm::Expected<NodeId>
makeStructRecord(Arena &, OriginList, std::vector<StructBaseValue>,
                 std::vector<NodeId>, std::vector<StructVirtualValue>,
                 std::vector<StructOverrideValue>, NodeId, bool,
                 std::optional<NodeId>, ScalarTerm, std::string, std::string);
llvm::Expected<NodeId> makeUnionRecord(Arena &, OriginList, std::vector<NodeId>,
                                       NodeId, bool, std::optional<NodeId>,
                                       std::string, std::string);
llvm::Expected<NodeId> makeObjectValue(Arena &, Constructor, OriginList,
                                       NodeId);
llvm::Expected<NodeId> makeVariableObjectValue(Arena &, OriginList, NodeId,
                                               NodeId);
llvm::Expected<NodeId>
makeGlobalDeclaration(Arena &, Constructor, OriginList,
                      std::optional<NodeId> = std::nullopt);
llvm::Expected<NodeId> makeEnumGlobalDeclaration(Arena &, OriginList, NodeId,
                                                 std::vector<std::string>);
llvm::Expected<NodeId> makeConstantGlobalDeclaration(Arena &, OriginList,
                                                     NodeId,
                                                     std::optional<NodeId>);
llvm::Expected<NodeId> makeUnsupportedGlobalDeclaration(Arena &, OriginList,
                                                        std::string);

llvm::Expected<NodeId> makeVariableDeclaration(Arena &, OriginList, std::string,
                                               NodeId, std::optional<NodeId>);
llvm::Expected<NodeId> makeVariableDecomposition(Arena &, OriginList, NodeId,
                                                 std::uint64_t,
                                                 std::vector<NodeId>);
llvm::Expected<NodeId> makeStaticVariableDeclaration(Arena &, OriginList, bool,
                                                     NodeId, NodeId,
                                                     std::optional<NodeId>);
llvm::Expected<NodeId> makeBindingDeclaration(Arena &, Constructor, OriginList,
                                              std::string, NodeId, NodeId);
llvm::Expected<NodeId> makeTypeTemplateParameter(Arena &, OriginList,
                                                 std::string);
llvm::Expected<NodeId> makeValueTemplateParameter(Arena &, OriginList,
                                                  std::string, NodeId);
llvm::Expected<NodeId> makeTemplateTemplateParameter(Arena &, OriginList,
                                                     std::string,
                                                     std::vector<NodeId>);
llvm::Expected<NodeId> makeUnsupportedTemplateParameter(Arena &, OriginList,
                                                        std::string);
llvm::Expected<NodeId> makeTypeTemplateArgument(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeValueTemplateArgument(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makePackTemplateArgument(Arena &, OriginList,
                                                std::vector<NodeId>);
llvm::Expected<NodeId> makeNamedTemplateArgument(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeTemplateParameterArgument(Arena &, OriginList,
                                                     std::string);
llvm::Expected<NodeId> makeUnsupportedTemplateArgument(Arena &, OriginList,
                                                       std::string);
llvm::Expected<NodeId> makeObjectVariable(Arena &, OriginList, NodeId type,
                                          NodeId initializer);
llvm::Expected<NodeId> makeGlobalTypedef(Arena &, OriginList, NodeId type);
llvm::Expected<NodeId> makeGlobalConstant(Arena &, OriginList, NodeId type,
                                          std::optional<NodeId> initializer);
llvm::Expected<NodeId> makeTemplateObjectRoot(Arena &, OriginList,
                                              TemplateParameters, NodeId);
llvm::Expected<NodeId> makeTemplateGlobalRoot(Arena &, OriginList,
                                              TemplateParameters, NodeId);
llvm::Expected<NodeId> makeTemplateAlias(Arena &, OriginList,
                                         TemplateParameters, NodeId type);
llvm::Expected<NodeId>
makeTemplatePreInstantiation(Arena &, OriginList, NodeId target,
                             std::vector<NodeId> arguments);
llvm::Expected<NodeId> makeInitIndirectPath(Arena &, OriginList,
                                            std::vector<Value> qualifiers,
                                            NodeId finalName);

// Test-only Phase-2 container factories.
llvm::Expected<NodeId> makeOptionalFixture(Arena &, OriginList,
                                           std::optional<NodeId>);
llvm::Expected<NodeId> makeSequenceFixture(Arena &, OriginList,
                                           std::vector<NodeId>);
llvm::Expected<NodeId> makeProductFixture(Arena &, OriginList, ScalarTerm,
                                          NodeId);
llvm::Expected<NodeId> makeSumFixture(Arena &, OriginList, NodeId);
llvm::Expected<NodeId> makeIdentTypeListFixture(Arena &, OriginList,
                                                std::vector<Value>);
llvm::Expected<NodeId> makeNameOptionalNameListFixture(Arena &, OriginList,
                                                       std::vector<Value>);
llvm::Expected<NodeId> makeStructureVirtualsFixture(Arena &, OriginList,
                                                    std::vector<Value>);
llvm::Expected<NodeId> makeStructureOverridesFixture(Arena &, OriginList,
                                                     std::vector<Value>);
llvm::Expected<NodeId> makeOpaqueFixture(Arena &, OriginList, std::string);

/// Create a distinct semantic occurrence. The child is never mutated or
/// reused; added wrapper provenance is appended in stable producer order.
llvm::Expected<NodeId> cloneWithOrigins(Arena &, NodeId child,
                                        const OriginList &addedOrigins);

} // namespace factory
} // namespace ir
