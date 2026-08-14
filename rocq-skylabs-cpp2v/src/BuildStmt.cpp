/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include <clang/AST/Attr.h>
#include <clang/AST/StmtCXX.h>
#include <clang/AST/StmtVisitor.h>
#include <clang/Basic/Version.h>
#include <llvm/ADT/SmallString.h>

namespace ir {
namespace builder {
namespace {

llvm::Error statementError(const clang::Stmt *statement,
                           llvm::StringRef branch) {
    return llvm::createStringError(
        std::errc::not_supported,
        "migration incomplete: %s statement branch (%s)", branch.str().c_str(),
        statement ? statement->getStmtClassName() : "nullptr");
}

BuildNodeGroup oneNode(NodeId node) { return {BuildCardinality::One, {node}}; }

BuildNodeGroup severalNodes(std::vector<NodeId> nodes) {
    return {BuildCardinality::Several, std::move(nodes)};
}

llvm::Expected<factory::OriginList>
statementOrigins(State &state, const clang::Stmt &statement) {
    const auto override = state.statementOriginOverrides.find(&statement);
    if (override != state.statementOriginOverrides.end())
        return factory::OriginList{override->second};
    auto origin = state.sources.explicitNode(statement.getSourceRange());
    if (!origin)
        return origin.takeError();
    return factory::OriginList{*origin};
}

llvm::Expected<NodeId>
buildImplicitStatement(State &state, const clang::Stmt *statement,
                       SemanticMode mode, source::OriginId anchor,
                       llvm::ArrayRef<source::OriginId> derivedFrom) {
    if (!statement)
        return statementError(statement, "implicit null");
    const clang::SourceRange written = statement->getSourceRange();
    auto implicit = state.sources.anchoredImplicitNode(
        clang::CharSourceRange::getTokenRange(written), anchor, derivedFrom);
    if (!implicit)
        return implicit.takeError();
    const auto inserted =
        state.statementOriginOverrides.try_emplace(statement, *implicit);
    if (!inserted.second)
        return llvm::createStringError(
            std::errc::invalid_argument,
            "nested statement origin override for %s",
            statement->getStmtClassName());
    auto built = state.buildSingleStatement(statement, mode);
    state.statementOriginOverrides.erase(statement);
    return built;
}

llvm::Expected<std::optional<NodeId>>
buildOptionalStatement(State &state, const clang::Stmt *statement,
                       SemanticMode mode) {
    if (!statement)
        return std::optional<NodeId>{};
    auto built = state.buildSingleStatement(statement, mode);
    if (!built)
        return built.takeError();
    return std::optional<NodeId>{*built};
}

llvm::Expected<std::optional<NodeId>>
buildOptionalExpression(State &state, const clang::Expr *expression,
                        SemanticMode mode) {
    if (!expression)
        return std::optional<NodeId>{};
    auto built = state.buildExpression(*expression, mode);
    if (!built)
        return built.takeError();
    return std::optional<NodeId>{*built};
}

llvm::Expected<std::optional<NodeId>>
buildOptionalDeclaration(State &state, const clang::VarDecl *declaration,
                         SemanticMode mode) {
    if (!declaration)
        return std::optional<NodeId>{};
    auto built = state.buildLocalDeclaration(*declaration, mode);
    if (!built)
        return built.takeError();
    if (built->cardinality != BuildCardinality::One || built->nodes.size() != 1)
        return llvm::createStringError(
            std::errc::invalid_argument,
            "condition declaration did not build exactly one local node");
    return std::optional<NodeId>{built->nodes.front()};
}

llvm::Expected<NodeId>
syntheticSequence(State &state, source::OriginId anchor,
                  llvm::ArrayRef<source::OriginId> derivedFrom,
                  std::vector<NodeId> statements) {
    auto generated = state.sources.synthesizedNode(anchor, derivedFrom);
    if (!generated)
        return generated.takeError();
    return factory::makeStatementSequence(state.unit->buildingArena(),
                                          {*generated}, std::move(statements));
}

std::vector<source::OriginId> nodeOrigins(State &state,
                                          llvm::ArrayRef<NodeId> nodes) {
    std::vector<source::OriginId> result;
    for (NodeId node : nodes) {
        auto value = state.unit->buildingArena().get(node);
        if (!value) {
            llvm::consumeError(value.takeError());
            continue;
        }
        for (source::OriginId origin : (*value)->origins)
            source::appendOriginStable(result, origin);
    }
    return result;
}

bool constexprEvalInt(const clang::Expr &expression, clang::ASTContext &context,
                      llvm::APSInt &value) {
    if (expression.containsErrors() || expression.isValueDependent() ||
        expression.isTypeDependent())
        return false;
    clang::Expr::EvalResult result;
    if (!expression.EvaluateAsInt(result, context))
        return false;
    value = result.Val.getInt();
    return true;
}

std::string apsIntText(const llvm::APSInt &value) {
    llvm::SmallString<32> text;
    value.toString(text, 10);
    return text.str().str();
}

} // namespace

llvm::Expected<NodeId> State::buildSingleStatement(const clang::Stmt *statement,
                                                   SemanticMode mode) {
    auto built = buildStatement(statement, mode);
    if (!built)
        return built.takeError();
    if (built->cardinality != BuildCardinality::One || built->nodes.size() != 1)
        return statementError(statement, "single-statement cardinality");
    return built->nodes.front();
}

llvm::Expected<BuildNodeGroup>
State::buildStatement(const clang::Stmt *statement, SemanticMode mode) {
    if (!statement) {
        auto unsupported = factory::makeUnsupportedStatement(
            unit->buildingArena(), {}, "empty statement");
        if (!unsupported)
            return unsupported.takeError();
        return oneNode(*unsupported);
    }

    auto origins = statementOrigins(*this, *statement);
    if (!origins)
        return origins.takeError();

    if (const auto *declarations = llvm::dyn_cast<clang::DeclStmt>(statement)) {
        std::vector<NodeId> values;
        for (const clang::Decl *declaration : declarations->decls()) {
            if (!declaration)
                continue;
            auto built = buildLocalDeclaration(*declaration, mode);
            if (!built)
                return built.takeError();
            if (built->cardinality == BuildCardinality::Forwarded ||
                built->cardinality == BuildCardinality::Several)
                return statementError(statement,
                                      "local declaration cardinality");
            values.insert(values.end(), built->nodes.begin(),
                          built->nodes.end());
        }
        auto result = factory::makeDeclarationStatement(
            unit->buildingArena(), std::move(*origins), std::move(values));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *loop = llvm::dyn_cast<clang::WhileStmt>(statement)) {
        auto declaration =
            buildOptionalDeclaration(*this, loop->getConditionVariable(), mode);
        if (!declaration)
            return declaration.takeError();
        auto condition = buildExpression(*loop->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto body = buildSingleStatement(loop->getBody(), mode);
        if (!body)
            return body.takeError();
        auto result = factory::makeWhileStatement(
            unit->buildingArena(), std::move(*origins), *declaration,
            *condition, *body);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *loop = llvm::dyn_cast<clang::ForStmt>(statement)) {
        auto init = buildOptionalStatement(*this, loop->getInit(), mode);
        if (!init)
            return init.takeError();
        auto condition = buildOptionalExpression(*this, loop->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto increment = buildOptionalExpression(*this, loop->getInc(), mode);
        if (!increment)
            return increment.takeError();
        auto body = buildSingleStatement(loop->getBody(), mode);
        if (!body)
            return body.takeError();
        auto result = factory::makeForStatement(unit->buildingArena(),
                                                std::move(*origins), *init,
                                                *condition, *increment, *body);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *loop = llvm::dyn_cast<clang::CXXForRangeStmt>(statement)) {
        if (!loop->getRangeStmt() || !loop->getBeginStmt() ||
            !loop->getEndStmt()) {
            auto result = factory::makeUnsupportedStatement(
                unit->buildingArena(), std::move(*origins),
                "dependent for-each loop");
            if (!result)
                return result.takeError();
            return oneNode(*result);
        }
        auto init = buildOptionalStatement(*this, loop->getInit(), mode);
        if (!init)
            return init.takeError();
        auto range = buildImplicitStatement(*this, loop->getRangeStmt(), mode,
                                            origins->front(), *origins);
        if (!range)
            return range.takeError();
        auto begin = buildImplicitStatement(*this, loop->getBeginStmt(), mode,
                                            origins->front(), *origins);
        if (!begin)
            return begin.takeError();
        auto end = buildImplicitStatement(*this, loop->getEndStmt(), mode,
                                          origins->front(), *origins);
        if (!end)
            return end.takeError();
        generatedExpressionAnchors.push_back(origins->front());
        auto condition = buildOptionalExpression(*this, loop->getCond(), mode);
        if (!condition) {
            generatedExpressionAnchors.pop_back();
            return condition.takeError();
        }
        auto increment = buildOptionalExpression(*this, loop->getInc(), mode);
        generatedExpressionAnchors.pop_back();
        if (!increment)
            return increment.takeError();
        auto declaration = buildImplicitStatement(
            *this, loop->getLoopVarStmt(), mode, origins->front(), *origins);
        if (!declaration)
            return declaration.takeError();
        auto body = buildSingleStatement(loop->getBody(), mode);
        if (!body)
            return body.takeError();

        std::vector<NodeId> innerValues{*declaration, *body};
        auto innerDerived = nodeOrigins(*this, innerValues);
        source::appendOriginStable(innerDerived, origins->front());
        auto inner = syntheticSequence(*this, origins->front(), innerDerived,
                                       std::move(innerValues));
        if (!inner)
            return inner.takeError();
        auto generatedFor = sources.synthesizedNode(origins->front(), *origins);
        if (!generatedFor)
            return generatedFor.takeError();
        auto forStatement = factory::makeForStatement(
            unit->buildingArena(), {*generatedFor}, std::nullopt, *condition,
            *increment, *inner);
        if (!forStatement)
            return forStatement.takeError();
        std::vector<NodeId> values;
        if (*init)
            values.push_back(**init);
        values.push_back(*range);
        values.push_back(*begin);
        values.push_back(*end);
        values.push_back(*forStatement);
        auto generatedOuter =
            sources.synthesizedNode(origins->front(), *origins);
        if (!generatedOuter)
            return generatedOuter.takeError();
        auto outer = factory::makeStatementSequence(
            unit->buildingArena(), {*generatedOuter}, std::move(values));
        if (!outer)
            return outer.takeError();
        return oneNode(*outer);
    }

    if (const auto *loop = llvm::dyn_cast<clang::DoStmt>(statement)) {
        auto body = buildSingleStatement(loop->getBody(), mode);
        if (!body)
            return body.takeError();
        auto condition = buildExpression(*loop->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto result = factory::makeDoStatement(
            unit->buildingArena(), std::move(*origins), *body, *condition);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (llvm::isa<clang::BreakStmt>(statement)) {
        auto result = factory::makeLeafStatement(unit->buildingArena(),
                                                 Constructor::StatementBreak,
                                                 std::move(*origins));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }
    if (llvm::isa<clang::ContinueStmt>(statement)) {
        auto result = factory::makeLeafStatement(unit->buildingArena(),
                                                 Constructor::StatementContinue,
                                                 std::move(*origins));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *ifStatement = llvm::dyn_cast<clang::IfStmt>(statement)) {
        auto whenTrue = buildSingleStatement(ifStatement->getThen(), mode);
        if (!whenTrue)
            return whenTrue.takeError();
        llvm::Expected<NodeId> whenFalse = [&]() -> llvm::Expected<NodeId> {
            if (ifStatement->getElse())
                return buildSingleStatement(ifStatement->getElse(), mode);
            return syntheticSequence(*this, origins->front(), *origins, {});
        }();
        if (!whenFalse)
            return whenFalse.takeError();
        if (ifStatement->isConsteval()) {
            auto result = factory::makeIfConstevalStatement(
                unit->buildingArena(), std::move(*origins), *whenTrue,
                *whenFalse);
            if (!result)
                return result.takeError();
            return oneNode(*result);
        }
        auto init = buildOptionalStatement(*this, ifStatement->getInit(), mode);
        if (!init)
            return init.takeError();
        auto declaration = buildOptionalDeclaration(
            *this, ifStatement->getConditionVariable(), mode);
        if (!declaration)
            return declaration.takeError();
        auto condition = buildExpression(*ifStatement->getCond(), mode);
        if (!condition)
            return condition.takeError();
        auto result = factory::makeIfStatement(
            unit->buildingArena(), std::move(*origins), *init, *declaration,
            *condition, *whenTrue, *whenFalse);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *caseStatement =
            llvm::dyn_cast<clang::CaseStmt>(statement)) {
        llvm::APSInt low, high;
        llvm::Expected<NodeId> marker = [&]() -> llvm::Expected<NodeId> {
            const clang::Expr *right = caseStatement->getRHS();
            if (!constexprEvalInt(*caseStatement->getLHS(), context, low) ||
                (right && !constexprEvalInt(*right, context, high)))
                return factory::makeUnsupportedStatement(
                    unit->buildingArena(), *origins,
                    "unsupported (dependent) case label");
            const ScalarTerm branch =
                right ? ScalarTerm::switchBranchRange(apsIntText(low),
                                                      apsIntText(high))
                      : ScalarTerm::switchBranchExact(apsIntText(low));
            return factory::makeCaseStatement(unit->buildingArena(), *origins,
                                              branch);
        }();
        if (!marker)
            return marker.takeError();
        auto substatement = buildStatement(caseStatement->getSubStmt(), mode);
        if (!substatement)
            return substatement.takeError();
        std::vector<NodeId> values{*marker};
        values.insert(values.end(), substatement->nodes.begin(),
                      substatement->nodes.end());
        return severalNodes(std::move(values));
    }

    if (const auto *defaultStatement =
            llvm::dyn_cast<clang::DefaultStmt>(statement)) {
        auto marker = factory::makeLeafStatement(
            unit->buildingArena(), Constructor::StatementDefault, *origins);
        if (!marker)
            return marker.takeError();
        std::vector<NodeId> values{*marker};
        if (defaultStatement->getSubStmt()) {
            auto substatement =
                buildStatement(defaultStatement->getSubStmt(), mode);
            if (!substatement)
                return substatement.takeError();
            values.insert(values.end(), substatement->nodes.begin(),
                          substatement->nodes.end());
            return severalNodes(std::move(values));
        }
        return oneNode(*marker);
    }

    if (const auto *switchStatement =
            llvm::dyn_cast<clang::SwitchStmt>(statement)) {
        auto init =
            buildOptionalStatement(*this, switchStatement->getInit(), mode);
        if (!init)
            return init.takeError();
        auto declaration = buildOptionalDeclaration(
            *this, switchStatement->getConditionVariable(), mode);
        if (!declaration)
            return declaration.takeError();
        auto condition = buildExpression(*switchStatement->getCond(), mode);
        if (!condition)
            return condition.takeError();
        llvm::Expected<NodeId> body = [&]() -> llvm::Expected<NodeId> {
            if (llvm::isa<clang::CompoundStmt>(switchStatement->getBody()))
                return buildSingleStatement(switchStatement->getBody(), mode);
            auto built = buildStatement(switchStatement->getBody(), mode);
            if (!built)
                return built.takeError();
            auto derived = nodeOrigins(*this, built->nodes);
            source::appendOriginStable(derived, origins->front());
            return syntheticSequence(*this, origins->front(), derived,
                                     std::move(built->nodes));
        }();
        if (!body)
            return body.takeError();
        auto result = factory::makeSwitchStatement(
            unit->buildingArena(), std::move(*origins), *init, *declaration,
            *condition, *body);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *expression = llvm::dyn_cast<clang::Expr>(statement)) {
        auto value = buildExpression(*expression, mode);
        if (!value)
            return value.takeError();
        auto result = factory::makeExpressionStatement(
            unit->buildingArena(), std::move(*origins), *value);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *returnStatement =
            llvm::dyn_cast<clang::ReturnStmt>(statement)) {
        std::optional<NodeId> value;
        if (const clang::Expr *expression = returnStatement->getRetValue()) {
            auto built = buildExpression(*expression, mode);
            if (!built)
                return built.takeError();
            value = *built;
        }
        auto result = factory::makeReturnStatement(unit->buildingArena(),
                                                   std::move(*origins), value);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(statement)) {
        std::vector<NodeId> values;
        for (const clang::Stmt *child : compound->body()) {
            auto built = buildStatement(child, mode);
            if (!built)
                return built.takeError();
            values.insert(values.end(), built->nodes.begin(),
                          built->nodes.end());
        }
        auto result = factory::makeStatementSequence(
            unit->buildingArena(), std::move(*origins), std::move(values));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (llvm::isa<clang::NullStmt>(statement)) {
        auto result = factory::makeStatementSequence(unit->buildingArena(),
                                                     std::move(*origins), {});
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *assembly = llvm::dyn_cast<clang::GCCAsmStmt>(statement)) {
        std::vector<std::pair<std::string, NodeId>> inputs;
        std::vector<std::pair<std::string, NodeId>> outputs;
        std::vector<std::string> clobbers;
        inputs.reserve(assembly->getNumInputs());
        outputs.reserve(assembly->getNumOutputs());
        clobbers.reserve(assembly->getNumClobbers());
        for (unsigned index = 0; index < assembly->getNumInputs(); ++index) {
            auto expression =
                buildExpression(*assembly->getInputExpr(index), mode);
            if (!expression)
                return expression.takeError();
            inputs.emplace_back(assembly->getInputConstraint(index),
                                *expression);
        }
        for (unsigned index = 0; index < assembly->getNumOutputs(); ++index) {
            auto expression =
                buildExpression(*assembly->getOutputExpr(index), mode);
            if (!expression)
                return expression.takeError();
            outputs.emplace_back(assembly->getOutputConstraint(index),
                                 *expression);
        }
        for (unsigned index = 0; index < assembly->getNumClobbers(); ++index) {
            const auto clobber = assembly->getClobber(index);
            clobbers.emplace_back(clobber.data(), clobber.size());
        }
#if CLANG_VERSION_MAJOR > 20
        const std::string assemblyText = assembly->getAsmString();
#else
        const std::string assemblyText =
            assembly->getAsmString()->getString().str();
#endif
        auto result = factory::makeAsmStatement(
            unit->buildingArena(), std::move(*origins), assemblyText,
            assembly->isVolatile(), std::move(inputs), std::move(outputs),
            std::move(clobbers));
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *attributed =
            llvm::dyn_cast<clang::AttributedStmt>(statement)) {
        std::vector<std::string> attributes;
        attributes.reserve(attributed->getAttrs().size());
        for (const clang::Attr *attribute : attributed->getAttrs())
            attributes.push_back(attribute->getSpelling());
        auto child = buildSingleStatement(attributed->getSubStmt(), mode);
        if (!child)
            return child.takeError();
        auto result = factory::makeAttributeStatement(
            unit->buildingArena(), std::move(*origins), std::move(attributes),
            *child);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *label = llvm::dyn_cast<clang::LabelStmt>(statement)) {
        auto child = buildSingleStatement(label->getSubStmt(), mode);
        if (!child)
            return child.takeError();
        auto result = factory::makeLabeledStatement(
            unit->buildingArena(), std::move(*origins),
            label->getDecl()->getNameAsString(), *child);
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (const auto *goTo = llvm::dyn_cast<clang::GotoStmt>(statement)) {
        auto result = factory::makeGotoStatement(
            unit->buildingArena(), std::move(*origins),
            goTo->getLabel()->getNameAsString());
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    if (llvm::isa<clang::CXXTryStmt>(statement)) {
        auto result = factory::makeUnsupportedStatement(
            unit->buildingArena(), std::move(*origins), "try");
        if (!result)
            return result.takeError();
        return oneNode(*result);
    }

    return statementError(statement, "unsupported");
}

} // namespace builder
} // namespace ir
