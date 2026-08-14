/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "../../src/IRBuilderInternal.hpp"
#include "IRBuilder.hpp"
#include "IRFactories.hpp"
#include "RocqEmitter.hpp"

#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Basic/Diagnostic.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/MemoryBuffer.h>

namespace {

class Finder : public clang::RecursiveASTVisitor<Finder> {
public:
    bool shouldVisitImplicitCode() const { return true; }
    bool shouldVisitTemplateInstantiations() const { return true; }

    bool VisitNamedDecl(clang::NamedDecl *declaration) {
        if (const clang::IdentifierInfo *identifier =
                declaration->getIdentifier())
            if (!declaration->isImplicit())
                named.emplace(identifier->getName().str(), declaration);
        if (const auto *function = llvm::dyn_cast_or_null<clang::FunctionDecl>(
                declaration->getLexicalDeclContext())) {
            if (function->getName() == "statement_static_kernel" ||
                function->getName() == "statement_template_kernel")
                statementLocals[declaration->getNameAsString()] = declaration;
            if (declaration->getName() == "values" &&
                function->getName() == "lambda_vla_static_kernel")
                staticVlaLocal = declaration;
            if (declaration->getName() == "values" &&
                function->getName() == "lambda_vla_template_kernel")
                templateVlaLocal = declaration;
        }
        if (const auto *function =
                llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
            if (function->getName() == "statement_static_kernel")
                statementStaticFunction = function;
            if (function->getName() == "statement_template_kernel" &&
                !function->isTemplateInstantiation())
                statementTemplateFunction = function;
        }
        if (const auto *constructor =
                llvm::dyn_cast<clang::CXXConstructorDecl>(declaration))
            if (!constructor->isImplicit() &&
                constructor->getParent()->getName() == "C")
                ctor = constructor;
        if (const auto *destructor =
                llvm::dyn_cast<clang::CXXDestructorDecl>(declaration))
            if (!destructor->isImplicit() &&
                destructor->getParent()->getName() == "C")
                dtor = destructor;
        if (const auto *conversion =
                llvm::dyn_cast<clang::CXXConversionDecl>(declaration))
            if (!conversion->isImplicit() &&
                conversion->getParent()->getName() == "C")
                conversionOperator = conversion;
        if (const auto *method =
                llvm::dyn_cast<clang::CXXMethodDecl>(declaration))
            if (!method->isImplicit() && method->isOverloadedOperator() &&
                method->getOverloadedOperator() == clang::OO_Plus)
                plusOperator = method;
        if (const auto *templ =
                llvm::dyn_cast<clang::ClassTemplateDecl>(declaration)) {
            if (templ->getName() == "Primary")
                primaryTemplate = templ;
            if (templ->getName() == "DefaultBox")
                defaultBoxTemplate = templ;
            if (templ->getName() == "InheritedDefaults") {
                bool inherited = false;
                for (const clang::NamedDecl *parameter :
                     templ->getTemplateParameters()->asArray()) {
                    if (const auto *type =
                            llvm::dyn_cast<clang::TemplateTypeParmDecl>(
                                parameter))
                        inherited |= type->hasDefaultArgument() &&
                                     type->defaultArgumentWasInherited();
                    else if (const auto *value =
                                 llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(
                                     parameter))
                        inherited |= value->hasDefaultArgument() &&
                                     value->defaultArgumentWasInherited();
                    else if (const auto *nested = llvm::dyn_cast<
                                 clang::TemplateTemplateParmDecl>(parameter))
                        inherited |= nested->hasDefaultArgument() &&
                                     nested->defaultArgumentWasInherited();
                }
                if (inherited)
                    inheritedDefaultsTemplate = templ;
            }
        }
        if (const auto *alias =
                llvm::dyn_cast<clang::TypeAliasDecl>(declaration)) {
            aliases.emplace(alias->getName().str(), alias);
            if (alias->getName() == "DependentType")
                dependentType = alias;
            if (alias->getName() == "ReboundType")
                reboundType = alias;
        }
        if (const auto *specialization =
                llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
                    declaration))
            if (specialization->getName() == "Primary") {
                const auto *written =
                    specialization->getTemplateArgsAsWritten();
                if (specialization->getTemplateSpecializationKind() ==
                        clang::TSK_ImplicitInstantiation &&
                    (!written || written->arguments().size() <
                                     specialization->getTemplateArgs().size()))
                    defaultedSpecialization = specialization;
                else if (!specialization->isImplicit())
                    classSpecializations.push_back(specialization);
            }
        if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration))
            if (variable->getName() == "values")
                if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(
                        variable->getDeclContext()))
                    if (function->getName() == "variable_array_kernel")
                        variableArray = variable;
        if (const auto *specialization =
                llvm::dyn_cast<clang::VarTemplateSpecializationDecl>(
                    declaration))
            if (!specialization->isImplicit() &&
                specialization->getName() == "variable_template")
                variableSpecializations.push_back(specialization);
        if (const auto *functionTemplate =
                llvm::dyn_cast<clang::FunctionTemplateDecl>(declaration))
            if (functionTemplate->getName() == "function_template")
                primaryFunctionTemplate = functionTemplate;
        if (const auto *variableTemplate =
                llvm::dyn_cast<clang::VarTemplateDecl>(declaration))
            if (variableTemplate->getName() == "variable_template")
                primaryVariableTemplate = variableTemplate;
        if (const auto *aliasTemplate =
                llvm::dyn_cast<clang::TypeAliasTemplateDecl>(declaration)) {
            if (aliasTemplate->getName() == "AliasTemplate")
                primaryAliasTemplate = aliasTemplate;
            if (aliasTemplate->getName() == "ApplyTemplate")
                applyAliasTemplate = aliasTemplate;
        }
        if (const auto *guide =
                llvm::dyn_cast<clang::CXXDeductionGuideDecl>(declaration))
            if (!guide->isImplicit() && !deductionGuide)
                deductionGuide = guide;
        if (const auto *function =
                llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
            if (!function->isImplicit() &&
                function->getName() == "function_template" &&
                function->getTemplateSpecializationKind() !=
                    clang::TSK_Undeclared)
                functionSpecializations.push_back(function);
            if (!function->isImplicit() && function->isOverloadedOperator() &&
                ((function->getOverloadedOperator() == clang::OO_New &&
                  function->getNumParams() == 1) ||
                 function->getOverloadedOperator() == clang::OO_Array_Delete))
                allocationOperators.push_back(function);
        }
        return true;
    }

    bool VisitDeclRefExpr(clang::DeclRefExpr *expression) {
        if (const clang::IdentifierInfo *identifier =
                expression->getDecl()->getIdentifier()) {
            if (identifier->getName() == "ordinary")
                ordinaryReference = expression;
            if (identifier->getName() == "local_value")
                localReference = expression;
            if (identifier->getName() == "named_local")
                namedLocalReference = expression;
            if (identifier->getName() == "static_local")
                staticLocalReference = expression;
            if (identifier->getName() == "reference_local")
                referenceLocal = expression;
            if (identifier->getName() == "binding_value")
                bindingReference = expression;
            if (identifier->getName() == "KFirst") {
                if (expression->getType()->isEnumeralType())
                    enumReference = expression;
                else
                    enumUnderlyingReference = expression;
            }
        }
        if (expression->refersToEnclosingVariableOrCapture()) {
            const llvm::StringRef name = expression->getDecl()->getName();
            if (name == "local") {
                if (expression->isNonOdrUse() != clang::NOUR_None)
                    lambdaUnevaluatedReference = expression;
                else
                    lambdaCapturedReferences.push_back(expression);
            }
            if (name == "value")
                lambdaTemplateCapturedReference = expression;
            if (name == "captured")
                lambdaInitCapturedReference = expression;
            if (name == "static_copy" || name == "static_reference" ||
                name == "static_copy_this" || name == "template_copy" ||
                name == "template_reference" || name == "template_copy_this")
                nestedCaptureReferences[name.str()] = expression;
        }
        if (llvm::isa<clang::NonTypeTemplateParmDecl>(expression->getDecl()) &&
            !templateParameterReference)
            templateParameterReference = expression;
        return true;
    }

    bool VisitImplicitCastExpr(clang::ImplicitCastExpr *expression) {
        if (expression->getCastKind() == clang::CK_BuiltinFnToFnPtr)
            builtinReference = expression;
        return true;
    }

    bool VisitCastExpr(clang::CastExpr *expression) {
        if (expression->getCastKind() == clang::CK_ToVoid && !toVoidCast)
            toVoidCast = expression;
        if (expression->getCastKind() == clang::CK_Dependent &&
            expression->getType()->isIntegerType() && !dependentCast)
            dependentCast = expression;
        return true;
    }

    bool VisitSourceLocExpr(clang::SourceLocExpr *expression) {
        if (expression->isIntType())
            sourceLine = expression;
        else
            sourceFile = expression;
        return true;
    }

    bool VisitPredefinedExpr(clang::PredefinedExpr *expression) {
        predefined = expression;
        return true;
    }

    bool VisitCXXDefaultInitExpr(clang::CXXDefaultInitExpr *expression) {
        if (!defaultInit)
            defaultInit = expression;
        return true;
    }

    bool VisitInitListExpr(clang::InitListExpr *expression) {
        if (expression->isTransparent() && !transparentInitList)
            transparentInitList = expression;
        return true;
    }

    bool VisitCXXBindTemporaryExpr(clang::CXXBindTemporaryExpr *expression) {
        if (!bindTemporary)
            bindTemporary = expression;
        return true;
    }

    bool
    VisitMaterializeTemporaryExpr(clang::MaterializeTemporaryExpr *expression) {
        if (expression->getExtendingDecl()) {
            if (const auto *named = llvm::dyn_cast<clang::NamedDecl>(
                    expression->getExtendingDecl()))
                if (named->getName() == "construction_extended")
                    extendedTemporary = expression;
        } else if (!materializedTemporary) {
            materializedTemporary = expression;
        }
        return true;
    }

    bool
    VisitCXXInheritedCtorInitExpr(clang::CXXInheritedCtorInitExpr *expression) {
        if (!inheritedConstructor)
            inheritedConstructor = expression;
        return true;
    }

    bool VisitArrayInitLoopExpr(clang::ArrayInitLoopExpr *expression) {
        if (!arrayInitLoop)
            arrayInitLoop = expression;
        return true;
    }

    bool VisitCXXDeleteExpr(clang::CXXDeleteExpr *expression) {
        if (expression->getOperatorDelete())
            staticDeletes.push_back(expression);
        else
            templateDeletes.push_back(expression);
        return true;
    }

    bool VisitUnaryOperator(clang::UnaryOperator *expression) {
        if (expression->getOpcode() == clang::UO_Minus) {
            if (expression->isValueDependent() && !dependentUnary)
                dependentUnary = expression;
            else if (!resolvedUnary &&
                     llvm::isa<clang::IntegerLiteral>(expression->getSubExpr()))
                resolvedUnary = expression;
        }
        return true;
    }

    bool VisitSizeOfPackExpr(clang::SizeOfPackExpr *expression) {
        if (expression->isValueDependent())
            dependentSizeOfPack = expression;
        else
            resolvedSizeOfPack = expression;
        return true;
    }

    bool VisitBinaryOperator(clang::BinaryOperator *expression) {
        if (expression->getOpcode() == clang::BO_Add) {
            const auto *localLhs = llvm::dyn_cast<clang::DeclRefExpr>(
                expression->getLHS()->IgnoreParenImpCasts());
            const auto *localRhs = llvm::dyn_cast<clang::DeclRefExpr>(
                expression->getRHS()->IgnoreParenImpCasts());
            if (localLhs && localRhs &&
                localLhs->getDecl()->getName() == "named_local" &&
                localRhs->getDecl()->getName() == "static_local")
                localBinary = expression;
            if (expression->isValueDependent() && !dependentBinary)
                dependentBinary = expression;
            else if (!resolvedBinary) {
                const clang::Expr *lhs = expression->getLHS();
                const bool literalLhs =
                    llvm::isa<clang::IntegerLiteral>(lhs) ||
                    (llvm::isa<clang::UnaryOperator>(lhs) &&
                     llvm::isa<clang::IntegerLiteral>(
                         llvm::cast<clang::UnaryOperator>(lhs)->getSubExpr()));
                if (literalLhs &&
                    llvm::isa<clang::IntegerLiteral>(expression->getRHS()))
                    resolvedBinary = expression;
            }
        }
        return true;
    }

    bool VisitDependentScopeDeclRefExpr(
        clang::DependentScopeDeclRefExpr *expression) {
        if (!dependentReference)
            dependentReference = expression;
        return true;
    }

    bool VisitCallExpr(clang::CallExpr *expression) {
        if (llvm::isa<clang::CXXPseudoDestructorExpr>(expression->getCallee()))
            pseudoDestructorCalls.push_back(expression);
        return true;
    }

    bool VisitDecompositionDecl(clang::DecompositionDecl *declaration) {
        for (const clang::BindingDecl *binding : declaration->bindings()) {
            if (binding->getName() == "direct_binding")
                directDecomposition = declaration;
            if (binding->getName() == "holding_binding")
                holdingDecomposition = declaration;
        }
        return true;
    }

    bool VisitStaticAssertDecl(clang::StaticAssertDecl *declaration) {
        if (const auto *function = llvm::dyn_cast_or_null<clang::FunctionDecl>(
                declaration->getLexicalDeclContext()))
            if (function->getName() == "statement_static_kernel")
                localStaticAssert = declaration;
        return true;
    }

    bool VisitIfStmt(clang::IfStmt *statement) {
        if (statement->isConsteval())
            constevalIf = statement;
        return true;
    }

    bool VisitCXXCatchStmt(clang::CXXCatchStmt *statement) {
        if (!unsupportedCatch)
            unsupportedCatch = statement;
        return true;
    }

    bool VisitChooseExpr(clang::ChooseExpr *expression) {
        if (!unsupportedChoose)
            unsupportedChoose = expression;
        return true;
    }

    bool VisitCXXThrowExpr(clang::CXXThrowExpr *expression) {
        if (!unsupportedThrow)
            unsupportedThrow = expression;
        return true;
    }

    bool VisitCXXThisExpr(clang::CXXThisExpr *expression) {
        lambdaThisExpressions.push_back(expression);
        return true;
    }

    const clang::NamedDecl *get(llvm::StringRef name) const {
        const auto found = named.find(name.str());
        return found == named.end() ? nullptr : found->second;
    }

    const clang::VarDecl *variable(llvm::StringRef name) const {
        return llvm::dyn_cast_or_null<clang::VarDecl>(get(name));
    }

    const clang::TypeAliasDecl *typeAlias(llvm::StringRef name) const {
        const auto found = aliases.find(name.str());
        return found == aliases.end() ? nullptr : found->second;
    }

    const clang::FunctionDecl *function(llvm::StringRef name) const {
        return llvm::dyn_cast_or_null<clang::FunctionDecl>(get(name));
    }

    std::map<std::string, clang::NamedDecl *> named;
    std::map<std::string, const clang::TypeAliasDecl *> aliases;
    const clang::CXXConstructorDecl *ctor = nullptr;
    const clang::CXXDestructorDecl *dtor = nullptr;
    const clang::CXXConversionDecl *conversionOperator = nullptr;
    const clang::CXXMethodDecl *plusOperator = nullptr;
    const clang::ClassTemplateDecl *primaryTemplate = nullptr;
    const clang::ClassTemplateDecl *defaultBoxTemplate = nullptr;
    const clang::ClassTemplateDecl *inheritedDefaultsTemplate = nullptr;
    const clang::FunctionTemplateDecl *primaryFunctionTemplate = nullptr;
    const clang::VarTemplateDecl *primaryVariableTemplate = nullptr;
    const clang::TypeAliasTemplateDecl *primaryAliasTemplate = nullptr;
    const clang::TypeAliasTemplateDecl *applyAliasTemplate = nullptr;
    const clang::TypeAliasDecl *dependentType = nullptr;
    const clang::TypeAliasDecl *reboundType = nullptr;
    std::vector<const clang::ClassTemplateSpecializationDecl *>
        classSpecializations;
    const clang::ClassTemplateSpecializationDecl *defaultedSpecialization =
        nullptr;
    const clang::VarDecl *variableArray = nullptr;
    std::vector<const clang::VarTemplateSpecializationDecl *>
        variableSpecializations;
    std::vector<const clang::FunctionDecl *> functionSpecializations;
    std::vector<const clang::FunctionDecl *> allocationOperators;
    const clang::DeclRefExpr *ordinaryReference = nullptr;
    const clang::DeclRefExpr *localReference = nullptr;
    const clang::DeclRefExpr *namedLocalReference = nullptr;
    const clang::DeclRefExpr *staticLocalReference = nullptr;
    const clang::DeclRefExpr *referenceLocal = nullptr;
    const clang::DeclRefExpr *bindingReference = nullptr;
    const clang::DeclRefExpr *enumReference = nullptr;
    const clang::DeclRefExpr *enumUnderlyingReference = nullptr;
    const clang::ImplicitCastExpr *builtinReference = nullptr;
    const clang::UnaryOperator *resolvedUnary = nullptr;
    const clang::UnaryOperator *dependentUnary = nullptr;
    const clang::SizeOfPackExpr *resolvedSizeOfPack = nullptr;
    const clang::SizeOfPackExpr *dependentSizeOfPack = nullptr;
    const clang::BinaryOperator *resolvedBinary = nullptr;
    const clang::BinaryOperator *dependentBinary = nullptr;
    const clang::BinaryOperator *localBinary = nullptr;
    const clang::DependentScopeDeclRefExpr *dependentReference = nullptr;
    const clang::DeclRefExpr *templateParameterReference = nullptr;
    std::vector<const clang::DeclRefExpr *> lambdaCapturedReferences;
    const clang::DeclRefExpr *lambdaUnevaluatedReference = nullptr;
    const clang::DeclRefExpr *lambdaTemplateCapturedReference = nullptr;
    const clang::DeclRefExpr *lambdaInitCapturedReference = nullptr;
    std::map<std::string, const clang::DeclRefExpr *> nestedCaptureReferences;
    const clang::CXXDeductionGuideDecl *deductionGuide = nullptr;
    const clang::CastExpr *toVoidCast = nullptr;
    const clang::CastExpr *dependentCast = nullptr;
    const clang::SourceLocExpr *sourceLine = nullptr;
    const clang::SourceLocExpr *sourceFile = nullptr;
    const clang::PredefinedExpr *predefined = nullptr;
    const clang::CXXDefaultInitExpr *defaultInit = nullptr;
    const clang::InitListExpr *transparentInitList = nullptr;
    const clang::CXXBindTemporaryExpr *bindTemporary = nullptr;
    const clang::MaterializeTemporaryExpr *materializedTemporary = nullptr;
    const clang::MaterializeTemporaryExpr *extendedTemporary = nullptr;
    const clang::CXXInheritedCtorInitExpr *inheritedConstructor = nullptr;
    const clang::ArrayInitLoopExpr *arrayInitLoop = nullptr;
    std::vector<const clang::CXXDeleteExpr *> staticDeletes;
    std::vector<const clang::CXXDeleteExpr *> templateDeletes;
    std::vector<const clang::CallExpr *> pseudoDestructorCalls;
    std::vector<const clang::CXXThisExpr *> lambdaThisExpressions;
    std::map<std::string, const clang::Decl *> statementLocals;
    const clang::Decl *staticVlaLocal = nullptr;
    const clang::Decl *templateVlaLocal = nullptr;
    const clang::FunctionDecl *statementStaticFunction = nullptr;
    const clang::FunctionDecl *statementTemplateFunction = nullptr;
    const clang::DecompositionDecl *directDecomposition = nullptr;
    const clang::DecompositionDecl *holdingDecomposition = nullptr;
    const clang::StaticAssertDecl *localStaticAssert = nullptr;
    const clang::IfStmt *constevalIf = nullptr;
    const clang::CXXCatchStmt *unsupportedCatch = nullptr;
    const clang::ChooseExpr *unsupportedChoose = nullptr;
    const clang::CXXThrowExpr *unsupportedThrow = nullptr;
};

class InvalidLocalFinder
    : public clang::RecursiveASTVisitor<InvalidLocalFinder> {
public:
    bool VisitVarDecl(clang::VarDecl *declaration) {
        if (!invalid && declaration->isInvalidDecl())
            invalid = declaration;
        return true;
    }

    const clang::VarDecl *invalid = nullptr;
};

bool fail(const std::string &message) {
    std::cerr << "type-expression builder probe: " << message << '\n';
    return false;
}

template <typename T> const T *initializerAs(const clang::VarDecl *variable) {
    if (!variable || !variable->hasInit())
        return nullptr;
    return llvm::dyn_cast<T>(variable->getInit()->IgnoreParenImpCasts());
}

bool originKind(const ir::BuildArtifact &artifact, ir::NodeId id,
                std::size_t index, source::OriginKind kind) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || (*node)->origins.size() <= index)
        return false;
    return artifact.unit->sources()
               .origins[(*node)->origins[index].value()]
               .kind == kind;
}

bool hasOriginKind(const ir::BuildArtifact &artifact, ir::NodeId id,
                   source::OriginKind kind) {
    auto node = artifact.unit->nodes().get(id);
    if (!node)
        return false;
    for (source::OriginId origin : (*node)->origins)
        if (artifact.unit->sources().origins[origin.value()].kind == kind)
            return true;
    return false;
}

bool originAnchorKind(const ir::BuildArtifact &artifact, ir::NodeId id,
                      std::size_t index, source::OriginKind kind) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || (*node)->origins.size() <= index)
        return false;
    const source::Origin &origin =
        artifact.unit->sources().origins[(*node)->origins[index].value()];
    return origin.anchor &&
           artifact.unit->sources().origins[origin.anchor->value()].kind ==
               kind;
}

bool originDerivedFromKind(const ir::BuildArtifact &artifact, ir::NodeId id,
                           std::size_t index, source::OriginKind kind) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || (*node)->origins.size() <= index)
        return false;
    const source::Origin &origin =
        artifact.unit->sources().origins[(*node)->origins[index].value()];
    for (source::OriginId derived : origin.derivedFrom)
        if (artifact.unit->sources().origins[derived.value()].kind == kind)
            return true;
    return false;
}

bool originKindBeginsAt(const ir::BuildArtifact &artifact, ir::NodeId id,
                        source::OriginKind kind,
                        const clang::SourceManager &sourceManager,
                        clang::SourceLocation location) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || location.isInvalid())
        return false;
    const clang::SourceLocation spelling =
        sourceManager.getSpellingLoc(location);
    if (spelling.isInvalid())
        return false;
    const std::uint64_t offset = sourceManager.getFileOffset(spelling);
    for (source::OriginId id : (*node)->origins) {
        const source::Origin &origin =
            artifact.unit->sources().origins[id.value()];
        if (origin.kind == kind && origin.spelling && origin.spelling->begin &&
            origin.spelling->begin->byteOffset == offset)
            return true;
    }
    return false;
}

bool originAtBeginsAt(const ir::BuildArtifact &artifact, ir::NodeId id,
                      std::size_t index,
                      const clang::SourceManager &sourceManager,
                      clang::SourceLocation location) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || (*node)->origins.size() <= index || location.isInvalid())
        return false;
    const source::Origin &origin =
        artifact.unit->sources().origins[(*node)->origins[index].value()];
    const clang::SourceLocation spelling =
        sourceManager.getSpellingLoc(location);
    return origin.spelling && origin.spelling->begin && spelling.isValid() &&
           origin.spelling->begin->byteOffset ==
               sourceManager.getFileOffset(spelling);
}

bool originBeginsAt(const ir::BuildArtifact &artifact, ir::NodeId id,
                    const clang::SourceManager &sourceManager,
                    clang::SourceLocation location) {
    auto node = artifact.unit->nodes().get(id);
    if (!node || (*node)->origins.empty() || location.isInvalid())
        return false;
    const source::Origin &origin =
        artifact.unit->sources().origins[(*node)->origins.front().value()];
    const clang::SourceLocation spelling =
        sourceManager.getSpellingLoc(location);
    return origin.spelling && origin.spelling->begin && spelling.isValid() &&
           origin.spelling->begin->byteOffset ==
               sourceManager.getFileOffset(spelling);
}

std::optional<std::vector<ir::NodeId>>
explicitChildren(const ir::BuildArtifact &artifact, ir::NodeId parent,
                 std::size_t count) {
    auto children = artifact.unit->nodes().children(parent);
    if (!children || children->size() != count)
        return std::nullopt;
    for (ir::NodeId child : *children)
        if (!originKind(artifact, child, 0, source::OriginKind::Explicit))
            return std::nullopt;
    return *children;
}

} // namespace

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr
            << "usage: cpp2v-type-expr-builder-probe SOURCE [-- ARGS...]\n";
        return 2;
    }
    auto buffer = llvm::MemoryBuffer::getFile(argv[1]);
    if (!buffer) {
        std::cerr << "cannot read " << argv[1] << '\n';
        return 2;
    }
    std::vector<std::string> arguments{"-std=c++17"};
    bool afterDash = false;
    for (int index = 2; index < argc; ++index) {
        if (std::string(argv[index]) == "--")
            afterDash = true;
        else if (afterDash)
            arguments.emplace_back(argv[index]);
        else {
            std::cerr << "unknown argument " << argv[index] << '\n';
            return 2;
        }
    }
    auto ast = clang::tooling::buildASTFromCodeWithArgs((*buffer)->getBuffer(),
                                                        arguments, argv[1]);
    if (!ast)
        return fail("could not build AST") ? 0 : 1;
    Finder finder;
    finder.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    const auto *normalized = finder.function("normalized");
    const auto *taggedUse =
        llvm::dyn_cast_or_null<clang::TypeAliasDecl>(finder.get("TaggedUse"));
    const auto *declarationUse = llvm::dyn_cast_or_null<clang::TypeAliasDecl>(
        finder.get("DeclarationUse"));
    const auto *pointerCv = finder.variable("pointer_cv");
    const auto *fixedArray = finder.variable("fixed_array");
    const auto *functionPointer = finder.variable("function_pointer");
    const auto *memberPointer = finder.variable("member_pointer");
    const auto *alias = finder.variable("alias_value");
    const auto *restrictType = finder.variable("restrict_unported");
    const auto *longDouble = finder.variable("long_double_value");
    const auto *undeduced = finder.function("undeduced_function");
    const auto *dependentType = finder.dependentType;
    const auto *reboundType = finder.reboundType;
    const auto *unaryUnderlying = llvm::dyn_cast_or_null<clang::TypeAliasDecl>(
        finder.get("UnaryUnderlying"));
    const auto *deducedAuto = finder.variable("deduced_auto_value");
    const auto *decltypeId = llvm::dyn_cast_or_null<clang::TypeAliasDecl>(
        finder.get("DecltypeIdStatic"));
    const auto *decltypeParen = llvm::dyn_cast_or_null<clang::TypeAliasDecl>(
        finder.get("DecltypeParenStatic"));
    const auto *elaborated = llvm::dyn_cast_or_null<clang::TypeAliasDecl>(
        finder.get("ElaboratedAudit"));
    const auto *vectorValue = finder.variable("vector_value");
    const auto *blockPointer = finder.variable("block_pointer");
    const auto *decayUse =
        llvm::dyn_cast_or_null<clang::TypeAliasDecl>(finder.get("DecayUse"));
    const auto *packExpansion = finder.typeAlias("PackExpansionAudit");
    const auto *dependentDecltypeId = finder.typeAlias("DependentDecltypeId");
    const auto *dependentDecltypeParen =
        finder.typeAlias("DependentDecltypeParen");
    const auto *injectedSelf = finder.typeAlias("Self");
    const auto *applyTemplate = finder.typeAlias("ApplyTemplate");
    const auto *literalVariable = finder.variable("literal_value");
    const auto *literal =
        literalVariable
            ? llvm::dyn_cast<clang::ParenExpr>(literalVariable->getInit())
            : nullptr;
    const auto *boolean =
        initializerAs<clang::CXXBoolLiteralExpr>(finder.variable("bool_value"));
    const auto *string =
        initializerAs<clang::StringLiteral>(finder.variable("string_value"));
    const auto *null = initializerAs<clang::CXXNullPtrLiteralExpr>(
        finder.variable("null_value"));
    const auto *directBuiltin = finder.builtinReference
                                    ? llvm::dyn_cast<clang::DeclRefExpr>(
                                          finder.builtinReference->getSubExpr())
                                    : nullptr;
    auto initializer = [&](llvm::StringRef name) -> const clang::Expr * {
        const clang::VarDecl *variable = finder.variable(name);
        return variable && variable->hasInit() ? variable->getInit() : nullptr;
    };
    auto literalInitializer = [&](llvm::StringRef name) -> const clang::Expr * {
        const clang::Expr *value = initializer(name);
        return value ? value->IgnoreParenImpCasts() : nullptr;
    };
    const clang::CastExpr *dependentCast = finder.dependentCast;
    const std::vector<const clang::Expr *> castLiteralStatic{
        initializer("cast_implicit_integral"),
        initializer("cast_pointer_bool"),
        initializer("cast_integral_bool"),
        initializer("cast_floating_bool"),
        initializer("cast_integral_float"),
        initializer("cast_floating_integral"),
        initializer("cast_floating"),
        initializer("cast_null_pointer"),
        initializer("cast_null_member"),
        initializer("cast_function_pointer"),
        initializer("cast_array_pointer"),
        initializer("cast_cstyle"),
        initializer("cast_functional"),
        initializer("cast_static"),
        initializer("cast_reinterpret"),
        initializer("cast_const"),
        initializer("cast_bit_pointer"),
        initializer("cast_lvalue_bit"),
        initializer("cast_integral_pointer"),
        initializer("cast_unchecked_base"),
        initializer("cast_dynamic"),
        initializer("cast_derived_to_base"),
        initializer("cast_base_to_derived"),
        initializer("cast_builtin_bit"),
        finder.toVoidCast,
        literalInitializer("literal_char"),
        literalInitializer("literal_wchar"),
        literalInitializer("literal_char16"),
        literalInitializer("literal_char32"),
        literalInitializer("literal_float"),
        literalInitializer("literal_double"),
        literalInitializer("literal_long_double"),
        literalInitializer("literal_wide_string"),
        literalInitializer("literal_u16_string"),
        literalInitializer("literal_u32_string"),
        literalInitializer("literal_gnu_null"),
        finder.sourceLine,
        finder.sourceFile,
        literalInitializer("literal_noexcept"),
        literalInitializer("literal_trait"),
        finder.predefined,
        finder.defaultInit};
    bool castLiteralsComplete = dependentCast != nullptr;
    for (const clang::Expr *value : castLiteralStatic)
        castLiteralsComplete &= value != nullptr;
    std::vector<const clang::Expr *> cxx20Literals;
    const clang::Expr *char8 = literalInitializer("literal_char8");
    const clang::Expr *string8 = literalInitializer("literal_u8_string");
    if (char8 || string8) {
        castLiteralsComplete &= char8 && string8;
        cxx20Literals = {char8, string8};
    }

    auto operatorInitializer =
        [&](llvm::StringRef name) -> const clang::Expr * {
        const clang::VarDecl *variable = finder.variable(name);
        if (!variable || !variable->hasInit())
            return nullptr;
        const clang::Expr *initializer = variable->getInit();
        if (name.ends_with("extension")) {
            const clang::Expr *candidate = initializer;
            while (const auto *paren =
                       llvm::dyn_cast<clang::ParenExpr>(candidate))
                candidate = paren->getSubExpr();
            if (const auto *cast =
                    llvm::dyn_cast<clang::ImplicitCastExpr>(candidate))
                candidate = cast->getSubExpr();
            while (const auto *paren =
                       llvm::dyn_cast<clang::ParenExpr>(candidate))
                candidate = paren->getSubExpr();
            if (const auto *unary =
                    llvm::dyn_cast<clang::UnaryOperator>(candidate))
                if (unary->getOpcode() == clang::UO_Extension)
                    return unary;
        }
        return initializer->IgnoreParenImpCasts();
    };
    const std::vector<const char *> staticOperatorNames{"op_unary_plus",
                                                        "op_unary_minus",
                                                        "op_unary_bitnot",
                                                        "op_unary_lnot",
                                                        "op_preinc",
                                                        "op_postinc",
                                                        "op_predec",
                                                        "op_postdec",
                                                        "op_deref",
                                                        "op_addrof",
                                                        "op_mul",
                                                        "op_div",
                                                        "op_rem",
                                                        "op_add",
                                                        "op_sub",
                                                        "op_shl",
                                                        "op_shr",
                                                        "op_lt",
                                                        "op_gt",
                                                        "op_le",
                                                        "op_ge",
                                                        "op_eq",
                                                        "op_ne",
                                                        "op_bitand",
                                                        "op_bitxor",
                                                        "op_bitor",
                                                        "op_dotp",
                                                        "op_dotip",
                                                        "op_assign",
                                                        "op_mul_assign",
                                                        "op_div_assign",
                                                        "op_rem_assign",
                                                        "op_add_assign",
                                                        "op_sub_assign",
                                                        "op_shl_assign",
                                                        "op_shr_assign",
                                                        "op_and_assign",
                                                        "op_xor_assign",
                                                        "op_or_assign",
                                                        "op_comma",
                                                        "op_logical_and",
                                                        "op_logical_or",
                                                        "op_subscript_array",
                                                        "op_subscript_reversed",
                                                        "op_subscript_pointer",
                                                        "op_sizeof_type",
                                                        "op_sizeof_expr",
                                                        "op_alignof_type",
                                                        "op_alignof_expr",
                                                        "op_preferred_type",
                                                        "op_preferred_expr",
                                                        "op_vec_step",
                                                        "op_real",
                                                        "op_imag",
                                                        "op_extension"};
    const std::vector<const char *> templateOperatorNames{
        "dep_op_unary_plus",
        "dep_op_unary_minus",
        "dep_op_unary_bitnot",
        "dep_op_unary_lnot",
        "dep_op_preinc",
        "dep_op_postinc",
        "dep_op_predec",
        "dep_op_postdec",
        "dep_op_deref",
        "dep_op_addrof",
        "dep_op_mul",
        "dep_op_div",
        "dep_op_rem",
        "dep_op_add",
        "dep_op_sub",
        "dep_op_shl",
        "dep_op_shr",
        "dep_op_lt",
        "dep_op_gt",
        "dep_op_le",
        "dep_op_ge",
        "dep_op_eq",
        "dep_op_ne",
        "dep_op_bitand",
        "dep_op_bitxor",
        "dep_op_bitor",
        "dep_op_assign",
        "dep_op_mul_assign",
        "dep_op_div_assign",
        "dep_op_rem_assign",
        "dep_op_add_assign",
        "dep_op_sub_assign",
        "dep_op_shl_assign",
        "dep_op_shr_assign",
        "dep_op_and_assign",
        "dep_op_xor_assign",
        "dep_op_or_assign",
        "dep_op_comma",
        "dep_op_logical_and",
        "dep_op_logical_or",
        "dep_op_subscript",
        "dep_op_sizeof_type",
        "dep_op_sizeof_expr",
        "dep_op_alignof_type",
        "dep_op_alignof_expr",
        "dep_op_preferred_type",
        "dep_op_preferred_expr",
        "dep_ptr_unary_plus",
        "dep_ptr_preinc",
        "dep_ptr_postinc",
        "dep_ptr_predec",
        "dep_ptr_postdec",
        "dep_ptr_add",
        "dep_ptr_add_reversed",
        "dep_ptr_sub",
        "dep_ptr_diff",
        "dep_ptr_lt",
        "dep_ptr_eq",
        "dep_ptr_assign",
        "dep_ptr_add_assign",
        "dep_ptr_sub_assign",
        "dep_ptr_comma",
        "dep_ptr_logical_and",
        "dep_ptr_logical_or",
        "dep_ptr_subscript",
        "dep_ptr_subscript_reversed",
        "dep_op_real",
        "dep_op_imag",
        "dep_ptr_logical_not",
        "dep_ptr_character_add_reversed",
        "dep_ptr_incompatible_diff",
        "dep_nttp_pointer_plus",
        "dep_nttp_comma",
        "dep_nttp_subscript",
        "dep_global_add",
        "dep_global_comma",
        "dep_op_extension"};
    std::vector<const clang::Expr *> staticOperators;
    std::vector<const clang::Expr *> templateOperators;
    const clang::Expr *deferredMemberAddress =
        operatorInitializer("op_member_address_deferred");
    bool operatorsComplete = finder.resolvedSizeOfPack &&
                             finder.dependentSizeOfPack &&
                             deferredMemberAddress;
    for (const char *name : staticOperatorNames) {
        const clang::Expr *value = operatorInitializer(name);
        operatorsComplete &= value != nullptr;
        staticOperators.push_back(value);
    }
    if (const clang::Expr *comparison = operatorInitializer("op_cmp"))
        staticOperators.push_back(comparison);
    staticOperators.push_back(finder.resolvedSizeOfPack);
    for (const char *name : templateOperatorNames) {
        const clang::Expr *value = operatorInitializer(name);
        operatorsComplete &= value != nullptr;
        templateOperators.push_back(value);
    }
    if (const clang::Expr *comparison = operatorInitializer("dep_op_cmp"))
        templateOperators.push_back(comparison);
    templateOperators.push_back(finder.dependentSizeOfPack);

    const std::vector<const char *> staticCallMemberNames{
        "call_free_zero",
        "call_free_two",
        "call_with_default",
        "member_field_dot",
        "member_field_arrow",
        "member_mutable",
        "member_enum",
        "member_static",
        "member_static_method",
        "member_call_direct",
        "member_call_arrow",
        "member_call_virtual",
        "member_pointer_dot_call",
        "member_pointer_arrow_call",
        "member_address_field",
        "member_address_method",
        "operator_call_member",
        "operator_call_virtual",
        "operator_call_function",
        "operator_call_free",
        "call_this",
        "member_enum_arrow",
        "member_static_arrow",
        "member_call_qualified_virtual",
        "member_call_static",
        "call_nested",
        "member_this_field",
        "member_this_call"};
    const std::vector<const char *> templateCallMemberNames{
        "call_dependent_free",
        "member_dependent_dot",
        "member_dependent_arrow",
        "call_dependent_member",
        "call_dependent_member_arrow",
        "call_dependent_member_template",
        "call_dependent_local",
        "call_dependent_fixed",
        "call_dependent_parenthesized",
        "call_unresolved_overload",
        "call_unresolved_overload_template",
        "call_dependent_cast",
        "call_noop_pointer_cast",
        "call_noop_function_cast"};
    std::vector<const clang::Expr *> staticCallMembers;
    std::vector<const clang::Expr *> templateCallMembers;
    bool callsComplete = finder.pseudoDestructorCalls.size() == 2;
    for (const char *name : staticCallMemberNames) {
        const clang::Expr *value = operatorInitializer(name);
        callsComplete &= value != nullptr;
        staticCallMembers.push_back(value);
    }
    staticCallMembers.insert(staticCallMembers.end(),
                             finder.pseudoDestructorCalls.begin(),
                             finder.pseudoDestructorCalls.end());
    for (const char *name : templateCallMemberNames) {
        const clang::Expr *value = operatorInitializer(name);
        callsComplete &= value != nullptr;
        templateCallMembers.push_back(value);
    }

    const auto *arrayInitializer = llvm::dyn_cast_or_null<clang::InitListExpr>(
        initializer("init_list_array"));
    const clang::Expr *arrayFiller =
        arrayInitializer ? arrayInitializer->getArrayFiller() : nullptr;
    const clang::Expr *dependentParen = initializer("unresolved_paren_list");
    const clang::Expr *dependentInit = initializer("unresolved_init_list");
    const clang::Expr *dependentConstruct = initializer("unresolved_construct");
    const std::vector<const clang::Expr *> staticInitializers{
        initializer("construct_zero"),
        initializer("construct_one"),
        initializer("construct_two"),
        initializer("init_list_aggregate"),
        initializer("init_list_union"),
        arrayInitializer,
        arrayFiller,
        initializer("scalar_value_init"),
        initializer("construction_cleanup"),
        finder.materializedTemporary,
        finder.extendedTemporary,
        finder.transparentInitList,
        finder.inheritedConstructor,
        finder.arrayInitLoop,
        initializer("construct_default"),
        finder.bindTemporary,
        dependentParen};
    const std::vector<const clang::Expr *> templateInitializers{
        dependentParen, dependentInit, dependentConstruct};
    bool initializersComplete = true;
    for (const clang::Expr *value : staticInitializers)
        initializersComplete &= value != nullptr;
    for (const clang::Expr *value : templateInitializers)
        initializersComplete &= value != nullptr;

    std::vector<const clang::Expr *> staticAllocations{
        initializer("allocation_new_scalar"),
        initializer("allocation_new_initialized"),
        initializer("allocation_new_array"),
        initializer("allocation_new_array_initialized"),
        initializer("allocation_new_object"),
        initializer("allocation_new_placement"),
        initializer("allocation_new_aligned")};
    staticAllocations.insert(staticAllocations.end(),
                             finder.staticDeletes.begin(),
                             finder.staticDeletes.end());
    std::vector<const clang::Expr *> templateAllocations{
        initializer("allocation_new_dependent")};
    templateAllocations.insert(templateAllocations.end(),
                               finder.templateDeletes.begin(),
                               finder.templateDeletes.end());
    bool allocationsComplete =
        finder.staticDeletes.size() == 2 && finder.templateDeletes.size() == 2;
    for (const clang::Expr *value : staticAllocations)
        allocationsComplete &= value != nullptr;
    for (const clang::Expr *value : templateAllocations)
        allocationsComplete &= value != nullptr;

    const std::vector<const clang::Expr *> staticLambdaAtomic{
        initializer("atomic_load_value"),
        initializer("atomic_exchange_value"),
        initializer("va_arg_value"),
        initializer("lambda_empty"),
        initializer("lambda"),
        initializer("lambda_reference"),
        initializer("lambda_unevaluated")};
    const std::vector<const clang::Expr *> templateLambdas{
        initializer("lambda_template_capture"),
        initializer("lambda_template_init")};
    auto nestedReference = [&](llvm::StringRef name) -> const clang::Expr * {
        const auto found = finder.nestedCaptureReferences.find(name.str());
        return found == finder.nestedCaptureReferences.end() ? nullptr
                                                             : found->second;
    };
    const std::vector<const clang::Expr *> staticNestedLambdas{
        initializer("nested_inner_static"), nestedReference("static_copy"),
        nestedReference("static_reference"),
        nestedReference("static_copy_this")};
    const std::vector<const clang::Expr *> templateNestedLambdas{
        initializer("nested_inner_template"), nestedReference("template_copy"),
        nestedReference("template_reference"),
        nestedReference("template_copy_this")};
    const clang::Expr *staticVlaLambda = initializer("lambda_vla_static");
    const clang::Expr *templateVlaLambda = initializer("lambda_vla_template");
    auto semanticInitializer = [&](llvm::StringRef name) {
        const clang::Expr *value = initializer(name);
        return value ? value->IgnoreParenImpCasts() : nullptr;
    };
    std::vector<const clang::Expr *> staticConditionals{
        semanticInitializer("conditional_ordinary"),
        semanticInitializer("conditional_binary"),
        semanticInitializer("conditional_binary_nested"),
        semanticInitializer("offset_field"),
        semanticInitializer("offset_nested"),
        finder.unsupportedChoose,
        finder.unsupportedThrow};
    std::vector<const clang::Expr *> templateConditionals{
        semanticInitializer("conditional_dependent"),
        semanticInitializer("conditional_binary_dependent")};
    if (ast->getASTContext().getLangOpts().CPlusPlus20) {
        staticConditionals.push_back(
            semanticInitializer("concept_nondependent"));
        templateConditionals.push_back(
            semanticInitializer("concept_dependent"));
    }
    const clang::Expr *statementExpression =
        initializer("statement_expression");
    auto statementLocal = [&](llvm::StringRef name) -> const clang::Decl * {
        const auto found = finder.statementLocals.find(name.str());
        return found == finder.statementLocals.end() ? nullptr : found->second;
    };
    const clang::FunctionDecl *staticStatementFunction =
        finder.statementStaticFunction;
    const clang::FunctionDecl *templateStatementFunction =
        finder.statementTemplateFunction;
    std::vector<const clang::Decl *> staticLocalDeclarations{
        statementLocal("local_uninitialized"),
        statementLocal("local_initialized"),
        statementLocal("local_static"),
        statementLocal("local_external_target"),
        statementLocal("LocalFilteredAlias"),
        finder.localStaticAssert,
        statementLocal("mixed_first"),
        statementLocal("mixed_function"),
        statementLocal("mixed_last"),
        finder.directDecomposition,
        finder.holdingDecomposition};
    std::vector<const clang::Decl *> templateLocalDeclarations{
        statementLocal("template_local"),
        statementLocal("template_uninitialized")};
    const clang::SourceManager &sourceManager = ast->getSourceManager();
    auto latestBySource = [&](const auto &values) {
        using Pointer = typename std::decay_t<decltype(values)>::value_type;
        Pointer latest = nullptr;
        unsigned latestOffset = 0;
        for (Pointer value : values) {
            const clang::SourceLocation location =
                sourceManager.getExpansionLoc(value->getExprLoc());
            if (!location.isValid() || !location.isFileID())
                continue;
            const unsigned offset = sourceManager.getFileOffset(location);
            if (!latest || offset > latestOffset) {
                latest = value;
                latestOffset = offset;
            }
        }
        return latest;
    };
    std::vector<const clang::CXXThisExpr *> boundaryThisExpressions;
    for (const clang::CXXThisExpr *candidate : finder.lambdaThisExpressions) {
        const clang::CXXRecordDecl *record =
            candidate->getType()->getPointeeCXXRecordDecl();
        if (record && record->getName() == "LambdaThisBoundary")
            boundaryThisExpressions.push_back(candidate);
    }
    const clang::CXXThisExpr *lambdaCapturedThis =
        latestBySource(boundaryThisExpressions);
    std::sort(
        finder.lambdaCapturedReferences.begin(),
        finder.lambdaCapturedReferences.end(),
        [&](const clang::DeclRefExpr *left, const clang::DeclRefExpr *right) {
            return sourceManager.getFileOffset(
                       sourceManager.getExpansionLoc(left->getExprLoc())) <
                   sourceManager.getFileOffset(
                       sourceManager.getExpansionLoc(right->getExprLoc()));
        });
    finder.lambdaCapturedReferences.erase(
        std::unique(finder.lambdaCapturedReferences.begin(),
                    finder.lambdaCapturedReferences.end()),
        finder.lambdaCapturedReferences.end());
    bool lambdaAtomicComplete = lambdaCapturedThis &&
                                finder.lambdaCapturedReferences.size() >= 2 &&
                                finder.lambdaUnevaluatedReference &&
                                finder.lambdaTemplateCapturedReference &&
                                finder.lambdaInitCapturedReference;
    for (const clang::Expr *value : staticLambdaAtomic)
        lambdaAtomicComplete &= value != nullptr;
    for (const clang::Expr *value : templateLambdas)
        lambdaAtomicComplete &= value != nullptr;
    for (const clang::Expr *value : staticNestedLambdas)
        lambdaAtomicComplete &= value != nullptr;
    for (const clang::Expr *value : templateNestedLambdas)
        lambdaAtomicComplete &= value != nullptr;
    lambdaAtomicComplete &=
        staticVlaLambda != nullptr && templateVlaLambda != nullptr &&
        finder.staticVlaLocal != nullptr && finder.templateVlaLocal != nullptr;
    bool conditionalsComplete =
        statementExpression != nullptr && staticStatementFunction &&
        staticStatementFunction->getBody() && templateStatementFunction &&
        templateStatementFunction->getBody();
    for (const clang::Expr *value : staticConditionals)
        conditionalsComplete &= value != nullptr;
    for (const clang::Expr *value : templateConditionals)
        conditionalsComplete &= value != nullptr;
    for (const clang::Decl *value : staticLocalDeclarations)
        conditionalsComplete &= value != nullptr;
    for (const clang::Decl *value : templateLocalDeclarations)
        conditionalsComplete &= value != nullptr;

    if (!normalized || !taggedUse || !declarationUse || !pointerCv ||
        !fixedArray || !functionPointer || !memberPointer || !alias ||
        !restrictType || !literal || !boolean || !string || !null ||
        !directBuiltin || !finder.ctor || !finder.dtor ||
        !finder.conversionOperator || !finder.plusOperator ||
        !finder.ordinaryReference || !finder.builtinReference ||
        !finder.localReference || !finder.namedLocalReference ||
        !finder.staticLocalReference || !finder.referenceLocal ||
        !finder.bindingReference || !finder.enumReference ||
        !finder.enumUnderlyingReference || !finder.variableArray ||
        !castLiteralsComplete || !finder.defaultedSpecialization ||
        !finder.localBinary || !longDouble || !undeduced || !dependentType ||
        !reboundType || !unaryUnderlying || !deducedAuto || !decltypeId ||
        !decltypeParen || !elaborated || !vectorValue || !blockPointer ||
        !decayUse || !packExpansion || !dependentDecltypeId ||
        !dependentDecltypeParen || !injectedSelf || !applyTemplate ||
        !finder.primaryTemplate || !finder.defaultBoxTemplate ||
        !finder.inheritedDefaultsTemplate || !finder.primaryFunctionTemplate ||
        !finder.primaryVariableTemplate || !finder.primaryAliasTemplate ||
        !finder.applyAliasTemplate || finder.classSpecializations.size() < 2 ||
        finder.variableSpecializations.empty() ||
        finder.functionSpecializations.empty() ||
        finder.allocationOperators.size() != 2 || !finder.resolvedUnary ||
        !finder.dependentUnary || !finder.resolvedBinary ||
        !finder.dependentBinary || !finder.dependentReference ||
        !finder.templateParameterReference || !finder.deductionGuide ||
        !operatorsComplete || !callsComplete || !initializersComplete ||
        !allocationsComplete || !lambdaAtomicComplete ||
        !conditionalsComplete || !finder.unsupportedCatch ||
        (ast->getASTContext().getLangOpts().CPlusPlus23 && !finder.constevalIf))
        return fail(
                   "fixture declarations/expressions were not found: class=" +
                   std::to_string(finder.classSpecializations.size()) +
                   " var=" +
                   std::to_string(finder.variableSpecializations.size()) +
                   " fun=" +
                   std::to_string(finder.functionSpecializations.size()) +
                   " unary=" + std::to_string(finder.resolvedUnary != nullptr) +
                   "/" + std::to_string(finder.dependentUnary != nullptr) +
                   " binary=" +
                   std::to_string(finder.resolvedBinary != nullptr) + "/" +
                   std::to_string(finder.dependentBinary != nullptr) +
                   " depref=" +
                   std::to_string(finder.dependentReference != nullptr) +
                   " new=" + std::to_string(finder.referenceLocal != nullptr) +
                   std::to_string(finder.bindingReference != nullptr) +
                   std::to_string(finder.enumReference != nullptr) +
                   std::to_string(finder.enumUnderlyingReference != nullptr) +
                   std::to_string(finder.variableArray != nullptr) +
                   std::to_string(finder.defaultedSpecialization != nullptr) +
                   " audit=" + std::to_string(unaryUnderlying != nullptr) +
                   std::to_string(deducedAuto != nullptr) +
                   std::to_string(decltypeId != nullptr) +
                   std::to_string(decltypeParen != nullptr) +
                   std::to_string(elaborated != nullptr) +
                   std::to_string(vectorValue != nullptr) +
                   std::to_string(blockPointer != nullptr) +
                   std::to_string(decayUse != nullptr) +
                   std::to_string(packExpansion != nullptr) +
                   std::to_string(dependentDecltypeId != nullptr) +
                   std::to_string(dependentDecltypeParen != nullptr) +
                   std::to_string(injectedSelf != nullptr) +
                   std::to_string(applyTemplate != nullptr) +
                   " init=" + std::to_string(arrayInitializer != nullptr) +
                   std::to_string(arrayFiller != nullptr) +
                   std::to_string(dependentParen != nullptr) +
                   std::to_string(dependentInit != nullptr) +
                   std::to_string(dependentConstruct != nullptr) +
                   std::to_string(finder.bindTemporary != nullptr) +
                   std::to_string(finder.materializedTemporary != nullptr) +
                   std::to_string(finder.extendedTemporary != nullptr) +
                   std::to_string(finder.transparentInitList != nullptr) +
                   std::to_string(finder.inheritedConstructor != nullptr) +
                   std::to_string(finder.arrayInitLoop != nullptr) +
                   " alloc=" + std::to_string(finder.staticDeletes.size()) +
                   "/" + std::to_string(finder.templateDeletes.size()) +
                   std::to_string(initializer("allocation_new_scalar") !=
                                  nullptr) +
                   std::to_string(initializer("allocation_new_initialized") !=
                                  nullptr) +
                   std::to_string(initializer("allocation_new_array") !=
                                  nullptr) +
                   std::to_string(
                       initializer("allocation_new_array_initialized") !=
                       nullptr) +
                   std::to_string(initializer("allocation_new_object") !=
                                  nullptr) +
                   std::to_string(initializer("allocation_new_placement") !=
                                  nullptr) +
                   std::to_string(initializer("allocation_new_aligned") !=
                                  nullptr) +
                   std::to_string(initializer("allocation_new_dependent") !=
                                  nullptr))
                   ? 0
                   : 1;

    clang::TypeLoc argumentOwner = taggedUse->getTypeSourceInfo()->getTypeLoc();
    clang::TemplateSpecializationTypeLoc specialization;
    for (clang::TypeLoc current = argumentOwner; !current.isNull();
         current = current.getNextTypeLoc())
        if ((specialization =
                 current.getAs<clang::TemplateSpecializationTypeLoc>()))
            break;
    if (!specialization || specialization.getNumArgs() != 2)
        return fail("written template arguments were not found") ? 0 : 1;
    clang::TypeLoc declarationOwner =
        declarationUse->getTypeSourceInfo()->getTypeLoc();
    clang::TemplateSpecializationTypeLoc declarationSpecialization;
    for (clang::TypeLoc current = declarationOwner; !current.isNull();
         current = current.getNextTypeLoc())
        if ((declarationSpecialization =
                 current.getAs<clang::TemplateSpecializationTypeLoc>()))
            break;
    if (!declarationSpecialization ||
        declarationSpecialization.getNumArgs() != 1)
        return fail("written declaration template argument was not found") ? 0
                                                                           : 1;

    std::vector<clang::TemplateArgumentLoc> writtenArgumentStorage{
        specialization.getArgLoc(0), specialization.getArgLoc(1),
        declarationSpecialization.getArgLoc(0)};
    std::vector<ir::PointerUse<clang::TemplateArgumentLoc>> writtenArguments{
        {&writtenArgumentStorage[0], ir::SemanticMode::Static},
        {&writtenArgumentStorage[1], ir::SemanticMode::Static},
        {&writtenArgumentStorage[2], ir::SemanticMode::Static}};
    std::vector<clang::TemplateArgument> packElements{
        clang::TemplateArgument(ast->getASTContext().IntTy),
        clang::TemplateArgument(ast->getASTContext().LongTy)};
    auto *declarationTarget =
        const_cast<clang::VarDecl *>(finder.variable("declaration_target"));
    if (!declarationTarget)
        return fail("declaration target was not found") ? 0 : 1;
    const clang::TemplateName defaultBoxName(
        const_cast<clang::ClassTemplateDecl *>(finder.defaultBoxTemplate));
    std::vector<clang::TemplateArgument> semanticArgumentStorage{
        writtenArgumentStorage[0].getArgument(),
        clang::TemplateArgument(
            llvm::ArrayRef<clang::TemplateArgument>(packElements)),
        clang::TemplateArgument(declarationTarget,
                                declarationTarget->getType()),
        clang::TemplateArgument(),
        clang::TemplateArgument(defaultBoxName, std::nullopt)};
    std::vector<ir::PointerUse<clang::TemplateArgument>> semanticArguments{
        {&semanticArgumentStorage[0], ir::SemanticMode::Static},
        {&semanticArgumentStorage[1], ir::SemanticMode::Template},
        {&semanticArgumentStorage[2], ir::SemanticMode::Static},
        {&semanticArgumentStorage[3], ir::SemanticMode::Template},
        {&semanticArgumentStorage[4], ir::SemanticMode::Template}};

    std::vector<ir::PointerUse<clang::NamedDecl>> names{
        {normalized, ir::SemanticMode::Static},
        {finder.ctor, ir::SemanticMode::Static},
        {finder.dtor, ir::SemanticMode::Static},
        {finder.conversionOperator, ir::SemanticMode::Static},
        {finder.plusOperator, ir::SemanticMode::Static},
        {finder.primaryTemplate, ir::SemanticMode::Template}};
    for (const auto *specialization : finder.classSpecializations)
        names.push_back({specialization, ir::SemanticMode::Template});
    for (const auto *specialization : finder.functionSpecializations)
        names.push_back({specialization, ir::SemanticMode::Template});
    for (const auto *specialization : finder.variableSpecializations)
        names.push_back({specialization, ir::SemanticMode::Template});
    for (const auto *operation : finder.allocationOperators)
        names.push_back({operation, ir::SemanticMode::Static});
    const std::size_t defaultedSpecializationName = names.size();
    names.push_back(
        {finder.defaultedSpecialization, ir::SemanticMode::Template});
    const std::size_t additionalPrimaryNames = names.size();
    names.push_back(
        {finder.primaryFunctionTemplate, ir::SemanticMode::Template});
    names.push_back(
        {finder.primaryVariableTemplate, ir::SemanticMode::Template});
    names.push_back({finder.primaryAliasTemplate, ir::SemanticMode::Template});
    names.push_back({finder.applyAliasTemplate, ir::SemanticMode::Template});
    std::vector<ir::PointerUse<clang::TypeSourceInfo>> writtenTypes{
        {pointerCv->getTypeSourceInfo(), ir::SemanticMode::Static},
        {fixedArray->getTypeSourceInfo(), ir::SemanticMode::Static},
        {functionPointer->getTypeSourceInfo(), ir::SemanticMode::Static},
        {memberPointer->getTypeSourceInfo(), ir::SemanticMode::Static},
        {alias->getTypeSourceInfo(), ir::SemanticMode::Static},
        {normalized->getTypeSourceInfo(), ir::SemanticMode::Static},
        {longDouble->getTypeSourceInfo(), ir::SemanticMode::Static},
        {undeduced->getTypeSourceInfo(), ir::SemanticMode::Static},
        {undeduced->getTypeSourceInfo(), ir::SemanticMode::Template},
        {dependentType->getTypeSourceInfo(), ir::SemanticMode::Template},
        {reboundType->getTypeSourceInfo(), ir::SemanticMode::Template},
        {unaryUnderlying->getTypeSourceInfo(), ir::SemanticMode::Static},
        {deducedAuto->getTypeSourceInfo(), ir::SemanticMode::Static},
        {decltypeId->getTypeSourceInfo(), ir::SemanticMode::Static},
        {decltypeParen->getTypeSourceInfo(), ir::SemanticMode::Static},
        {elaborated->getTypeSourceInfo(), ir::SemanticMode::Static},
        {vectorValue->getTypeSourceInfo(), ir::SemanticMode::Static},
        {blockPointer->getTypeSourceInfo(), ir::SemanticMode::Static},
        {decayUse->getTypeSourceInfo(), ir::SemanticMode::Static},
        {packExpansion->getTypeSourceInfo(), ir::SemanticMode::Template},
        {dependentDecltypeId->getTypeSourceInfo(), ir::SemanticMode::Template},
        {dependentDecltypeParen->getTypeSourceInfo(),
         ir::SemanticMode::Template},
        {injectedSelf->getTypeSourceInfo(), ir::SemanticMode::Template},
        {applyTemplate->getTypeSourceInfo(), ir::SemanticMode::Template},
        {dependentDecltypeId->getTypeSourceInfo(), ir::SemanticMode::Static},
        {dependentDecltypeParen->getTypeSourceInfo(), ir::SemanticMode::Static},
        {finder.variableArray->getTypeSourceInfo(), ir::SemanticMode::Static},
        {restrictType->getTypeSourceInfo(), ir::SemanticMode::Static}};
    // Exercise the qualifier-preserving semantic QualType boundary separately
    // from every written TypeSourceInfo selection.
    std::vector<ir::QualTypeUse> semanticTypes{
        {pointerCv->getType(), ir::SemanticMode::Static}};
    std::vector<ir::PointerUse<clang::Expr>> expressions{
        {literal, ir::SemanticMode::Static},
        {boolean, ir::SemanticMode::Static},
        {string, ir::SemanticMode::Static},
        {null, ir::SemanticMode::Static},
        {finder.ordinaryReference, ir::SemanticMode::Static},
        {finder.builtinReference, ir::SemanticMode::Static},
        {finder.resolvedUnary, ir::SemanticMode::Static},
        {finder.resolvedBinary, ir::SemanticMode::Static},
        {finder.dependentUnary, ir::SemanticMode::Template},
        {finder.dependentBinary, ir::SemanticMode::Template},
        {finder.dependentReference, ir::SemanticMode::Template},
        {finder.namedLocalReference, ir::SemanticMode::Static},
        {finder.staticLocalReference, ir::SemanticMode::Static},
        {finder.localBinary, ir::SemanticMode::Static},
        {finder.referenceLocal, ir::SemanticMode::Static},
        {finder.bindingReference, ir::SemanticMode::Static},
        {finder.enumReference, ir::SemanticMode::Static},
        {finder.enumUnderlyingReference, ir::SemanticMode::Static},
        {directBuiltin, ir::SemanticMode::Static}};
    const std::size_t castLiteralBegin = expressions.size();
    for (const clang::Expr *value : castLiteralStatic)
        expressions.push_back({value, ir::SemanticMode::Static});
    for (const clang::Expr *value : cxx20Literals)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t dependentCastIndex = expressions.size();
    expressions.push_back({dependentCast, ir::SemanticMode::Template});
    const std::size_t staticOperatorBegin = expressions.size();
    for (const clang::Expr *value : staticOperators)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateOperatorBegin = expressions.size();
    for (const clang::Expr *value : templateOperators)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t operatorEnd = expressions.size();
    const std::size_t staticCallMemberBegin = expressions.size();
    for (const clang::Expr *value : staticCallMembers)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateCallMemberBegin = expressions.size();
    for (const clang::Expr *value : templateCallMembers)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t callMemberEnd = expressions.size();
    const std::size_t staticInitializerBegin = expressions.size();
    for (const clang::Expr *value : staticInitializers)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateInitializerBegin = expressions.size();
    for (const clang::Expr *value : templateInitializers)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t initializerEnd = expressions.size();
    const std::size_t staticAllocationBegin = expressions.size();
    for (const clang::Expr *value : staticAllocations)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateAllocationBegin = expressions.size();
    for (const clang::Expr *value : templateAllocations)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t allocationEnd = expressions.size();
    const std::size_t staticLambdaAtomicBegin = expressions.size();
    for (const clang::Expr *value : staticLambdaAtomic)
        expressions.push_back({value, ir::SemanticMode::Static});
    expressions.push_back(
        {finder.lambdaCapturedReferences[0], ir::SemanticMode::Static});
    expressions.push_back(
        {finder.lambdaCapturedReferences[1], ir::SemanticMode::Static});
    expressions.push_back({lambdaCapturedThis, ir::SemanticMode::Static});
    expressions.push_back(
        {finder.lambdaUnevaluatedReference, ir::SemanticMode::Static});
    const std::size_t templateLambdaBegin = expressions.size();
    for (const clang::Expr *value : templateLambdas)
        expressions.push_back({value, ir::SemanticMode::Template});
    expressions.push_back(
        {finder.lambdaTemplateCapturedReference, ir::SemanticMode::Template});
    expressions.push_back(
        {finder.lambdaInitCapturedReference, ir::SemanticMode::Template});
    const std::size_t lambdaAtomicEnd = expressions.size();
    const std::size_t staticNestedLambdaBegin = expressions.size();
    for (const clang::Expr *value : staticNestedLambdas)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateNestedLambdaBegin = expressions.size();
    for (const clang::Expr *value : templateNestedLambdas)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t nestedLambdaEnd = expressions.size();
    const std::size_t staticConditionalBegin = expressions.size();
    for (const clang::Expr *value : staticConditionals)
        expressions.push_back({value, ir::SemanticMode::Static});
    const std::size_t templateConditionalBegin = expressions.size();
    for (const clang::Expr *value : templateConditionals)
        expressions.push_back({value, ir::SemanticMode::Template});
    const std::size_t conditionalEnd = expressions.size();
    const std::size_t statementExpressionIndex = expressions.size();
    expressions.push_back({statementExpression, ir::SemanticMode::Static});
    std::vector<ir::PointerUse<clang::Decl>> localDeclarations;
    for (const clang::Decl *declaration : staticLocalDeclarations)
        localDeclarations.push_back({declaration, ir::SemanticMode::Static});
    for (const clang::Decl *declaration : templateLocalDeclarations)
        localDeclarations.push_back({declaration, ir::SemanticMode::Template});
    const std::size_t staticVlaLocalGroupIndex = localDeclarations.size();
    localDeclarations.push_back(
        {finder.staticVlaLocal, ir::SemanticMode::Static});
    const std::size_t templateVlaLocalGroupIndex = localDeclarations.size();
    localDeclarations.push_back(
        {finder.templateVlaLocal, ir::SemanticMode::Template});
    std::vector<ir::PointerUse<clang::Stmt>> statements{
        {staticStatementFunction->getBody(), ir::SemanticMode::Static},
        {templateStatementFunction->getBody(), ir::SemanticMode::Template},
        {nullptr, ir::SemanticMode::Static}};
    if (finder.constevalIf)
        statements.push_back({finder.constevalIf, ir::SemanticMode::Template});
    std::vector<ir::PointerUse<clang::NamedDecl>> parameters;
    for (const clang::NamedDecl *parameter :
         finder.primaryTemplate->getTemplateParameters()->asArray())
        parameters.push_back({parameter, ir::SemanticMode::Template});
    for (const clang::NamedDecl *parameter :
         finder.defaultBoxTemplate->getTemplateParameters()->asArray())
        parameters.push_back({parameter, ir::SemanticMode::Template});
    for (const clang::NamedDecl *parameter :
         finder.inheritedDefaultsTemplate->getTemplateParameters()->asArray())
        parameters.push_back({parameter, ir::SemanticMode::Template});
    ir::BuildSelection selection{
        names,      writtenTypes,     semanticTypes,     expressions,
        parameters, writtenArguments, semanticArguments, localDeclarations,
        statements};
    auto artifact = ir::IRBuilder::build(ast->getASTContext(), selection);
    if (!artifact) {
        std::cerr << llvm::toString(artifact.takeError()) << '\n';
        return 1;
    }
    if (!artifact->unit || !artifact->unit->finished() ||
        artifact->names.size() != names.size() ||
        artifact->types.size() != writtenTypes.size() + semanticTypes.size() ||
        artifact->expressions.size() != expressions.size() ||
        artifact->templateParameters.size() != parameters.size() ||
        artifact->templateParameterEntries.size() != parameters.size() ||
        artifact->templateArguments.size() != 8 ||
        artifact->localDeclarationGroups.size() != localDeclarations.size() ||
        artifact->statementGroups.size() != statements.size())
        return fail("builder returned an incomplete artifact") ? 0 : 1;

    ir::SemanticRocqEmitter emitter;
    auto renderAll = [&](llvm::StringRef label,
                         const std::vector<ir::NodeId> &values) -> bool {
        for (ir::NodeId value : values) {
            auto rendered = emitter.renderNode(*artifact->unit, value);
            if (!rendered) {
                std::cerr << llvm::toString(rendered.takeError()) << '\n';
                return false;
            }
            std::cout << label.str() << " " << *rendered << '\n';
        }
        return true;
    };
    const std::vector<ir::NodeId> originalExpressions(
        artifact->expressions.begin(),
        artifact->expressions.begin() + staticOperatorBegin);
    const std::vector<ir::NodeId> staticOperatorNodes(
        artifact->expressions.begin() + staticOperatorBegin,
        artifact->expressions.begin() + templateOperatorBegin);
    const std::vector<ir::NodeId> templateOperatorNodes(
        artifact->expressions.begin() + templateOperatorBegin,
        artifact->expressions.begin() + operatorEnd);
    const std::vector<ir::NodeId> staticCallMemberNodes(
        artifact->expressions.begin() + staticCallMemberBegin,
        artifact->expressions.begin() + templateCallMemberBegin);
    const std::vector<ir::NodeId> templateCallMemberNodes(
        artifact->expressions.begin() + templateCallMemberBegin,
        artifact->expressions.begin() + callMemberEnd);
    const std::vector<ir::NodeId> staticInitializerNodes(
        artifact->expressions.begin() + staticInitializerBegin,
        artifact->expressions.begin() + templateInitializerBegin);
    const std::vector<ir::NodeId> templateInitializerNodes(
        artifact->expressions.begin() + templateInitializerBegin,
        artifact->expressions.begin() + initializerEnd);
    const std::vector<ir::NodeId> staticAllocationNodes(
        artifact->expressions.begin() + staticAllocationBegin,
        artifact->expressions.begin() + templateAllocationBegin);
    const std::vector<ir::NodeId> templateAllocationNodes(
        artifact->expressions.begin() + templateAllocationBegin,
        artifact->expressions.begin() + allocationEnd);
    const std::vector<ir::NodeId> staticLambdaAtomicNodes(
        artifact->expressions.begin() + staticLambdaAtomicBegin,
        artifact->expressions.begin() + templateLambdaBegin);
    const std::vector<ir::NodeId> templateLambdaNodes(
        artifact->expressions.begin() + templateLambdaBegin,
        artifact->expressions.begin() + lambdaAtomicEnd);
    const std::vector<ir::NodeId> staticNestedLambdaNodes(
        artifact->expressions.begin() + staticNestedLambdaBegin,
        artifact->expressions.begin() + templateNestedLambdaBegin);
    const std::vector<ir::NodeId> templateNestedLambdaNodes(
        artifact->expressions.begin() + templateNestedLambdaBegin,
        artifact->expressions.begin() + nestedLambdaEnd);
    const std::vector<ir::NodeId> staticConditionalNodes(
        artifact->expressions.begin() + staticConditionalBegin,
        artifact->expressions.begin() + templateConditionalBegin);
    const std::vector<ir::NodeId> templateConditionalNodes(
        artifact->expressions.begin() + templateConditionalBegin,
        artifact->expressions.begin() + conditionalEnd);
    const std::vector<ir::NodeId> statementExpressionNodes{
        artifact->expressions[statementExpressionIndex]};
    std::vector<ir::NodeId> staticLocalNodes;
    std::vector<ir::NodeId> templateLocalNodes;
    for (std::size_t index = 0; index < staticLocalDeclarations.size(); ++index)
        staticLocalNodes.insert(
            staticLocalNodes.end(),
            artifact->localDeclarationGroups[index].nodes.begin(),
            artifact->localDeclarationGroups[index].nodes.end());
    for (std::size_t index = staticLocalDeclarations.size();
         index <
         staticLocalDeclarations.size() + templateLocalDeclarations.size();
         ++index)
        templateLocalNodes.insert(
            templateLocalNodes.end(),
            artifact->localDeclarationGroups[index].nodes.begin(),
            artifact->localDeclarationGroups[index].nodes.end());
    const std::vector<ir::NodeId> staticVlaLocalNodes =
        artifact->localDeclarationGroups[staticVlaLocalGroupIndex].nodes;
    const std::vector<ir::NodeId> templateVlaLocalNodes =
        artifact->localDeclarationGroups[templateVlaLocalGroupIndex].nodes;
    if (!renderAll("NAME", artifact->names) ||
        !renderAll("TYPE", artifact->types) ||
        !renderAll("EXPR", originalExpressions) ||
        !renderAll("OP_STATIC", staticOperatorNodes) ||
        !renderAll("OP_TEMPLATE", templateOperatorNodes) ||
        !renderAll("CALL_STATIC", staticCallMemberNodes) ||
        !renderAll("CALL_TEMPLATE", templateCallMemberNodes) ||
        !renderAll("INIT_STATIC", staticInitializerNodes) ||
        !renderAll("INIT_TEMPLATE", templateInitializerNodes) ||
        !renderAll("ALLOC_STATIC", staticAllocationNodes) ||
        !renderAll("ALLOC_TEMPLATE", templateAllocationNodes) ||
        !renderAll("LAMBDA_ATOMIC_STATIC", staticLambdaAtomicNodes) ||
        !renderAll("LAMBDA_TEMPLATE", templateLambdaNodes) ||
        !renderAll("LAMBDA_NESTED_STATIC", staticNestedLambdaNodes) ||
        !renderAll("LAMBDA_NESTED_TEMPLATE", templateNestedLambdaNodes) ||
        !renderAll("COND_STATIC", staticConditionalNodes) ||
        !renderAll("COND_TEMPLATE", templateConditionalNodes) ||
        !renderAll("STMT_EXPR", statementExpressionNodes) ||
        !renderAll("LOCAL_STATIC", staticLocalNodes) ||
        !renderAll("LOCAL_TEMPLATE", templateLocalNodes) ||
        !renderAll("LOCAL_VLA_STATIC", staticVlaLocalNodes) ||
        !renderAll("LOCAL_VLA_TEMPLATE", templateVlaLocalNodes) ||
        !renderAll("STMT_STATIC", artifact->statementGroups[0].nodes) ||
        !renderAll("STMT_TEMPLATE", artifact->statementGroups[1].nodes) ||
        !renderAll("STMT_NULL", artifact->statementGroups[2].nodes) ||
        !renderAll("PARAM", artifact->templateParameters) ||
        !renderAll("ARG", artifact->templateArguments))
        return 1;
    if (finder.constevalIf &&
        !renderAll("STMT_CONSTEVAL", artifact->statementGroups[3].nodes))
        return 1;
    for (const ir::TemplateParameterEntry &entry :
         artifact->templateParameterEntries) {
        if (!entry.defaultArgument)
            continue;
        auto rendered =
            emitter.renderNode(*artifact->unit, *entry.defaultArgument);
        if (!rendered) {
            std::cerr << llvm::toString(rendered.takeError()) << '\n';
            return 1;
        }
        std::cout << "DEFAULT " << *rendered << '\n';
    }

    auto constructorIs = [&](ir::NodeId id, ir::Constructor constructor) {
        auto node = artifact->unit->nodes().get(id);
        return node && (*node)->constructor == constructor;
    };

    if (staticOperatorNodes.size() < 53 || templateOperatorNodes.size() < 67)
        return fail("operator selection matrix is incomplete") ? 0 : 1;
    for (ir::NodeId id : staticOperatorNodes)
        if (!originKind(*artifact, id, 0, source::OriginKind::Explicit))
            return fail("static operator root lacks direct provenance") ? 0 : 1;
    for (ir::NodeId id : templateOperatorNodes)
        if (!originKind(*artifact, id, 0, source::OriginKind::Explicit))
            return fail("template operator root lacks direct provenance") ? 0
                                                                          : 1;
    auto childCountIs = [&](ir::NodeId id, std::size_t count) {
        auto children = artifact->unit->nodes().children(id);
        return children && children->size() == count;
    };
    const std::vector<std::tuple<std::size_t, ir::Constructor, std::size_t>>
        staticShapes{{0, ir::Constructor::ExpressionUnary, 2},
                     {9, ir::Constructor::ExpressionAddressOf, 1},
                     {10, ir::Constructor::ExpressionBinary, 3},
                     {28, ir::Constructor::ExpressionAssign, 3},
                     {29, ir::Constructor::ExpressionAssignOp, 3},
                     {39, ir::Constructor::ExpressionComma, 2},
                     {42, ir::Constructor::ExpressionSubscript, 3},
                     {45, ir::Constructor::ExpressionSizeofType, 2},
                     {54, ir::Constructor::ExpressionGlobal, 2}};
    for (const auto &[index, constructor, count] : staticShapes)
        if (!constructorIs(staticOperatorNodes[index], constructor) ||
            !childCountIs(staticOperatorNodes[index], count))
            return fail("static operator constructor or child order mismatch")
                       ? 0
                       : 1;
    const std::vector<std::tuple<std::size_t, ir::Constructor, std::size_t>>
        templateShapes{
            {0, ir::Constructor::ExpressionUnresolvedUnary, 1},
            {10, ir::Constructor::ExpressionUnresolvedBinary, 2},
            {26, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {27, ir::Constructor::ExpressionUnresolvedCompoundAssignment, 2},
            {37, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {40, ir::Constructor::ExpressionSubscript, 3},
            {47, ir::Constructor::ExpressionUnary, 2},
            {48, ir::Constructor::ExpressionPreIncrement, 2},
            {49, ir::Constructor::ExpressionPostIncrement, 2},
            {50, ir::Constructor::ExpressionPreDecrement, 2},
            {51, ir::Constructor::ExpressionPostDecrement, 2},
            {52, ir::Constructor::ExpressionBinary, 3},
            {58, ir::Constructor::ExpressionAssign, 3},
            {59, ir::Constructor::ExpressionAssignOp, 3},
            {61, ir::Constructor::ExpressionComma, 2},
            {64, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {65, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {68, ir::Constructor::ExpressionUnary, 2},
            {69, ir::Constructor::ExpressionBinary, 3},
            {70, ir::Constructor::ExpressionBinary, 3},
            {71, ir::Constructor::ExpressionUnary, 2},
            {72, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {73, ir::Constructor::ExpressionUnresolvedBinarySyntax, 2},
            {74, ir::Constructor::ExpressionBinary, 3},
            {75, ir::Constructor::ExpressionComma, 2},
            {76, ir::Constructor::ExpressionLocalNamed, 1}};
    for (const auto &[index, constructor, count] : templateShapes)
        if (!constructorIs(templateOperatorNodes[index], constructor) ||
            !childCountIs(templateOperatorNodes[index], count))
            return fail("template operator constructor or child order mismatch")
                       ? 0
                       : 1;

    auto inferredSubscriptChildren =
        artifact->unit->nodes().children(templateOperatorNodes[40]);
    if (!inferredSubscriptChildren || inferredSubscriptChildren->size() != 3 ||
        !constructorIs(inferredSubscriptChildren->front(),
                       ir::Constructor::ExpressionCast) ||
        !originKind(*artifact, inferredSubscriptChildren->front(), 0,
                    source::OriginKind::Cpp2vSynthesized))
        return fail("template subscript helper did not synthesize Cl2r") ? 0
                                                                         : 1;
    auto inferredCastChildren =
        artifact->unit->nodes().children(inferredSubscriptChildren->front());
    if (!inferredCastChildren || inferredCastChildren->size() != 2 ||
        !constructorIs(inferredCastChildren->front(),
                       ir::Constructor::CastLvalueToRvalue) ||
        !originKind(*artifact, inferredCastChildren->front(), 0,
                    source::OriginKind::Cpp2vSynthesized))
        return fail("template subscript synthetic cast child order mismatch")
                   ? 0
                   : 1;
    for (std::size_t index : {47U, 69U}) {
        auto children =
            artifact->unit->nodes().children(templateOperatorNodes[index]);
        if (!children || children->empty() ||
            !originKind(*artifact, children->back(), 0,
                        source::OriginKind::Inherited) ||
            !originAnchorKind(*artifact, children->back(), 0,
                              source::OriginKind::Cpp2vSynthesized))
            return fail("mparser-generated semantic type lacks synthetic "
                        "anchor " +
                        std::to_string(index))
                       ? 0
                       : 1;
    }
    for (std::size_t index : {70U, 74U}) {
        auto children =
            artifact->unit->nodes().children(templateOperatorNodes[index]);
        if (!children || children->empty() ||
            !originKind(*artifact, children->back(), 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("mparser-generated structural type lacks synthetic "
                        "origin " +
                        std::to_string(index))
                       ? 0
                       : 1;
    }
    auto globalAddChildren =
        artifact->unit->nodes().children(templateOperatorNodes[74]);
    if (!globalAddChildren || globalAddChildren->size() != 3 ||
        !constructorIs(globalAddChildren->back(),
                       ir::Constructor::TypeResultGlobal))
        return fail("dependent-global binary result did not expand mparser")
                   ? 0
                   : 1;

    if (!hasOriginKind(*artifact, staticOperatorNodes[54],
                       source::OriginKind::ClangTransformed))
        return fail("erased static unary extension lacks transformed "
                    "provenance")
                   ? 0
                   : 1;
    if (!hasOriginKind(*artifact, templateOperatorNodes[76],
                       source::OriginKind::ClangTransformed))
        return fail("erased template unary extension lacks transformed "
                    "provenance")
                   ? 0
                   : 1;

    const std::vector<std::pair<ir::Constructor, std::size_t>> callShapes{
        {ir::Constructor::ExpressionCall, 1},
        {ir::Constructor::ExpressionCall, 3},
        {ir::Constructor::ExpressionCall, 2},
        {ir::Constructor::ExpressionMember, 3},
        {ir::Constructor::ExpressionMember, 3},
        {ir::Constructor::ExpressionMember, 3},
        {ir::Constructor::ExpressionMemberIgnore, 2},
        {ir::Constructor::ExpressionMemberIgnore, 2},
        {ir::Constructor::ExpressionMemberIgnore, 2},
        {ir::Constructor::ExpressionMemberCallDirect, 4},
        {ir::Constructor::ExpressionMemberCallDirect, 4},
        {ir::Constructor::ExpressionMemberCallDirect, 4},
        {ir::Constructor::ExpressionMemberCallPointer, 3},
        {ir::Constructor::ExpressionMemberCallPointer, 3},
        {ir::Constructor::ExpressionGlobalMember, 2},
        {ir::Constructor::ExpressionGlobalMember, 2},
        {ir::Constructor::ExpressionOperatorCallMethod, 4},
        {ir::Constructor::ExpressionOperatorCallMethod, 4},
        {ir::Constructor::ExpressionOperatorCallMethod, 4},
        {ir::Constructor::ExpressionOperatorCallFunction, 4},
        {ir::Constructor::ExpressionThis, 1},
        {ir::Constructor::ExpressionMemberIgnore, 2},
        {ir::Constructor::ExpressionMemberIgnore, 2},
        {ir::Constructor::ExpressionMemberCallDirect, 4},
        {ir::Constructor::ExpressionCall, 2},
        {ir::Constructor::ExpressionCall, 3},
        {ir::Constructor::ExpressionMember, 3},
        {ir::Constructor::ExpressionMemberCallDirect, 4},
        {ir::Constructor::ExpressionPseudoDestructor, 2},
        {ir::Constructor::ExpressionPseudoDestructor, 2}};
    if (staticCallMemberNodes.size() != callShapes.size())
        return fail("static call/member matrix is incomplete") ? 0 : 1;
    for (std::size_t index = 0; index < callShapes.size(); ++index)
        if (!constructorIs(staticCallMemberNodes[index],
                           callShapes[index].first) ||
            !childCountIs(staticCallMemberNodes[index],
                          callShapes[index].second) ||
            !originKind(*artifact, staticCallMemberNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("static call/member constructor, order, or origin "
                        "mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    const std::vector<std::pair<ir::Constructor, std::size_t>>
        templateCallShapes{{ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedMember, 2},
                           {ir::Constructor::ExpressionUnresolvedMember, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2},
                           {ir::Constructor::ExpressionUnresolvedCall, 2}};
    if (templateCallMemberNodes.size() != templateCallShapes.size())
        return fail("template call/member matrix is incomplete") ? 0 : 1;
    for (std::size_t index = 0; index < templateCallShapes.size(); ++index)
        if (!constructorIs(templateCallMemberNodes[index],
                           templateCallShapes[index].first) ||
            !childCountIs(templateCallMemberNodes[index],
                          templateCallShapes[index].second) ||
            !originKind(*artifact, templateCallMemberNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("template call/member constructor, order, or origin "
                        "mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;

    auto defaultCallChildren =
        artifact->unit->nodes().children(staticCallMemberNodes[2]);
    if (!defaultCallChildren || defaultCallChildren->size() != 2 ||
        !constructorIs(defaultCallChildren->back(),
                       ir::Constructor::ExpressionImplicit) ||
        !originKind(*artifact, defaultCallChildren->back(), 0,
                    source::OriginKind::Implicit))
        return fail("default call argument lacks implicit wrapper provenance")
                   ? 0
                   : 1;
    for (std::size_t index : {3U, 4U, 5U}) {
        auto children =
            artifact->unit->nodes().children(staticCallMemberNodes[index]);
        if (!children || children->size() != 3 ||
            !originKind(*artifact, (*children)[1], 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("field member helper lacks synthetic provenance") ? 0
                                                                          : 1;
    }
    for (std::size_t index : {12U, 13U})
        if (!hasOriginKind(*artifact, staticCallMemberNodes[index],
                           source::OriginKind::ClangTransformed))
            return fail("erased parenthesized member-call callee lacks "
                        "transformed provenance")
                       ? 0
                       : 1;
    for (std::size_t index : {6U, 7U, 8U, 21U, 22U}) {
        auto children =
            artifact->unit->nodes().children(staticCallMemberNodes[index]);
        if (!children || children->size() != 2 ||
            !originKind(*artifact, children->back(), 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("ignored member result lacks synthetic provenance") ? 0
                                                                            : 1;
    }
    auto dependentArrowChildren =
        artifact->unit->nodes().children(templateCallMemberNodes[2]);
    if (!dependentArrowChildren || dependentArrowChildren->size() != 2 ||
        !constructorIs(dependentArrowChildren->front(),
                       ir::Constructor::ExpressionUnresolvedUnarySyntax) ||
        !originKind(*artifact, dependentArrowChildren->front(), 0,
                    source::OriginKind::Cpp2vSynthesized))
        return fail("dependent arrow member lacks synthetic Rarrow") ? 0 : 1;
    for (std::size_t index : {3U, 4U, 5U}) {
        auto children =
            artifact->unit->nodes().children(templateCallMemberNodes[index]);
        if (!children || children->size() != 2 ||
            !constructorIs(children->front(), ir::Constructor::NameDependent) ||
            !originKind(*artifact, children->front(), 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("dependent member call name lacks final synthesized "
                        "Tresult_member")
                       ? 0
                       : 1;
    }
    auto localCallChildren =
        artifact->unit->nodes().children(templateCallMemberNodes[6]);
    if (!localCallChildren || localCallChildren->size() != 2 ||
        !constructorIs(localCallChildren->front(),
                       ir::Constructor::NameFromAtomic) ||
        !originKind(*artifact, localCallChildren->front(), 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, localCallChildren->front(), 0,
                          source::OriginKind::Explicit))
        return fail("dependent local call name lacks synthesized Nlocal") ? 0
                                                                          : 1;

    const auto *parenthesizedCall =
        llvm::dyn_cast<clang::CallExpr>(templateCallMembers[8]);
    const auto *outerParen =
        parenthesizedCall
            ? llvm::dyn_cast<clang::ParenExpr>(parenthesizedCall->getCallee())
            : nullptr;
    const auto *innerParen =
        outerParen ? llvm::dyn_cast<clang::ParenExpr>(outerParen->getSubExpr())
                   : nullptr;
    const clang::Expr *parenthesizedLeaf =
        innerParen ? innerParen->getSubExpr() : nullptr;
    auto parenthesizedChildren =
        artifact->unit->nodes().children(templateCallMemberNodes[8]);
    if (!outerParen || !innerParen || !parenthesizedLeaf ||
        !parenthesizedChildren || parenthesizedChildren->size() != 2)
        return fail("parenthesized dependent call fixture shape changed") ? 0
                                                                          : 1;
    const ir::NodeId parenthesizedName = parenthesizedChildren->front();
    if (!originKind(*artifact, parenthesizedName, 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, parenthesizedName, 0,
                          source::OriginKind::Explicit) ||
        !originKind(*artifact, parenthesizedName, 1,
                    source::OriginKind::ClangTransformed) ||
        !originKind(*artifact, parenthesizedName, 2,
                    source::OriginKind::ClangTransformed) ||
        !originKind(*artifact, parenthesizedName, 3,
                    source::OriginKind::ClangTransformed) ||
        !originAtBeginsAt(*artifact, parenthesizedName, 1,
                          ast->getSourceManager(),
                          parenthesizedLeaf->getBeginLoc()) ||
        !originAtBeginsAt(*artifact, parenthesizedName, 2,
                          ast->getSourceManager(), innerParen->getBeginLoc()) ||
        !originAtBeginsAt(*artifact, parenthesizedName, 3,
                          ast->getSourceManager(), outerParen->getBeginLoc()))
        return fail("dependent callee wrapper origins are not nearest-first")
                   ? 0
                   : 1;

    for (std::size_t index : {9U, 10U, 11U, 12U}) {
        auto children =
            artifact->unit->nodes().children(templateCallMemberNodes[index]);
        if (!children || children->size() != 2 ||
            !constructorIs(children->front(),
                           ir::Constructor::NameUnsupported) ||
            !originKind(*artifact, children->front(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !hasOriginKind(*artifact, children->front(),
                           source::OriginKind::ClangTransformed))
            return fail("unsupported dependent callee lost exact final name or "
                        "provenance " +
                        std::to_string(index))
                       ? 0
                       : 1;
    }
    auto noopFunctionChildren =
        artifact->unit->nodes().children(templateCallMemberNodes[13]);
    if (!noopFunctionChildren || noopFunctionChildren->size() != 2 ||
        !constructorIs(noopFunctionChildren->front(),
                       ir::Constructor::NameFromAtomic) ||
        !hasOriginKind(*artifact, noopFunctionChildren->front(),
                       source::OriginKind::ClangTransformed))
        return fail("name-preserving explicit callee cast lost provenance") ? 0
                                                                            : 1;

    const std::vector<std::pair<ir::Constructor, std::size_t>>
        staticInitializerShapes{
            {ir::Constructor::ExpressionConstructor, 2},
            {ir::Constructor::ExpressionConstructor, 3},
            {ir::Constructor::ExpressionConstructor, 4},
            {ir::Constructor::ExpressionInitList, 3},
            {ir::Constructor::ExpressionInitListUnion, 3},
            {ir::Constructor::ExpressionInitList, 4},
            {ir::Constructor::ExpressionImplicitInit, 1},
            {ir::Constructor::ExpressionImplicitInit, 1},
            {ir::Constructor::ExpressionAndClean, 1},
            {ir::Constructor::ExpressionMaterializeTemporary, 1},
            {ir::Constructor::ExpressionUnsupported, 1},
            {ir::Constructor::ExpressionCast, 2},
            {ir::Constructor::ExpressionInheritedConstructor, 2},
            {ir::Constructor::ExpressionArrayLoopInit, 3},
            {ir::Constructor::ExpressionConstructor, 4},
            {ir::Constructor::ExpressionCall, 1},
            {ir::Constructor::ExpressionUnsupported, 1}};
    if (staticInitializerNodes.size() != staticInitializerShapes.size())
        return fail("static construction/initialization matrix is incomplete")
                   ? 0
                   : 1;
    for (std::size_t index = 0; index < staticInitializerShapes.size(); ++index)
        if (!constructorIs(staticInitializerNodes[index],
                           staticInitializerShapes[index].first) ||
            !childCountIs(staticInitializerNodes[index],
                          staticInitializerShapes[index].second))
            return fail("static construction/initialization shape mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    for (std::size_t index : {0U, 1U, 2U, 3U, 4U, 5U, 7U, 14U, 16U})
        if (!originKind(*artifact, staticInitializerNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("written initializer root lacks explicit origin " +
                        std::to_string(index))
                       ? 0
                       : 1;
    for (std::size_t index : {6U, 8U, 9U, 10U, 12U, 13U})
        if (!originKind(*artifact, staticInitializerNodes[index], 0,
                        source::OriginKind::Implicit))
            return fail("compiler-generated initializer root lacks implicit "
                        "origin " +
                        std::to_string(index))
                       ? 0
                       : 1;
    for (std::size_t index : {6U, 8U, 10U, 12U, 13U})
        if (!originDerivedFromKind(*artifact, staticInitializerNodes[index], 0,
                                   source::OriginKind::Explicit))
            return fail(
                       "implicit initializer origin lacks written derivation " +
                       std::to_string(index))
                       ? 0
                       : 1;
    if (!originDerivedFromKind(*artifact, staticInitializerNodes[9], 0,
                               source::OriginKind::Implicit) ||
        !hasOriginKind(*artifact, staticInitializerNodes[11],
                       source::OriginKind::ClangTransformed) ||
        !hasOriginKind(*artifact, staticInitializerNodes[15],
                       source::OriginKind::ClangTransformed) ||
        !originKindBeginsAt(*artifact, staticInitializerNodes[11],
                            source::OriginKind::ClangTransformed,
                            ast->getSourceManager(),
                            finder.transparentInitList->getBeginLoc()))
        return fail("temporary or transparent initializer provenance is "
                    "incomplete")
                   ? 0
                   : 1;
    const std::vector<std::pair<ir::Constructor, std::size_t>>
        templateInitializerShapes{
            {ir::Constructor::ExpressionUnresolvedParenList, 2},
            {ir::Constructor::ExpressionUnresolvedInitList, 2},
            {ir::Constructor::ExpressionUnsupported, 1}};
    if (templateInitializerNodes.size() != templateInitializerShapes.size())
        return fail("template construction/initialization matrix is incomplete")
                   ? 0
                   : 1;
    for (std::size_t index = 0; index < templateInitializerShapes.size();
         ++index)
        if (!constructorIs(templateInitializerNodes[index],
                           templateInitializerShapes[index].first) ||
            !childCountIs(templateInitializerNodes[index],
                          templateInitializerShapes[index].second) ||
            !originKind(*artifact, templateInitializerNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("template construction/initialization shape or origin "
                        "mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;

    auto constructorChildren =
        artifact->unit->nodes().children(staticInitializerNodes[2]);
    auto arrayInitializerChildren =
        artifact->unit->nodes().children(staticInitializerNodes[5]);
    auto inheritedChildren =
        artifact->unit->nodes().children(staticInitializerNodes[12]);
    auto scalarInitChildren =
        artifact->unit->nodes().children(staticInitializerNodes[7]);
    const auto *scalarInit =
        llvm::dyn_cast<clang::CXXScalarValueInitExpr>(staticInitializers[7]);
    auto unresolvedConstructChildren =
        artifact->unit->nodes().children(templateInitializerNodes[2]);
    const auto *unresolvedConstruct =
        llvm::dyn_cast<clang::CXXUnresolvedConstructExpr>(
            templateInitializers[2]);
    auto arrayLoopChildren =
        artifact->unit->nodes().children(staticInitializerNodes[13]);
    auto defaultConstructorChildren =
        artifact->unit->nodes().children(staticInitializerNodes[14]);
    if (!constructorChildren || constructorChildren->size() != 4 ||
        !constructorIs((*constructorChildren)[1],
                       ir::Constructor::ExpressionInteger) ||
        !constructorIs((*constructorChildren)[2],
                       ir::Constructor::ExpressionInteger) ||
        !arrayInitializerChildren || arrayInitializerChildren->size() != 4 ||
        !constructorIs((*arrayInitializerChildren)[2],
                       ir::Constructor::ExpressionImplicitInit) ||
        !originKind(*artifact, (*arrayInitializerChildren)[2], 0,
                    source::OriginKind::Implicit) ||
        !inheritedChildren || inheritedChildren->size() != 2 || !scalarInit ||
        !scalarInit->getTypeSourceInfo() || !scalarInitChildren ||
        scalarInitChildren->size() != 1 ||
        !originBeginsAt(
            *artifact, scalarInitChildren->front(), ast->getSourceManager(),
            scalarInit->getTypeSourceInfo()->getTypeLoc().getBeginLoc()) ||
        !unresolvedConstruct || !unresolvedConstruct->getTypeSourceInfo() ||
        !unresolvedConstructChildren ||
        unresolvedConstructChildren->size() != 1 ||
        !originBeginsAt(*artifact, unresolvedConstructChildren->front(),
                        ast->getSourceManager(),
                        unresolvedConstruct->getTypeSourceInfo()
                            ->getTypeLoc()
                            .getBeginLoc()) ||
        !arrayLoopChildren || arrayLoopChildren->size() != 3 ||
        !originKind(*artifact, (*arrayLoopChildren)[0], 0,
                    source::OriginKind::Implicit) ||
        !originKind(*artifact, (*arrayLoopChildren)[1], 0,
                    source::OriginKind::Implicit) ||
        !defaultConstructorChildren ||
        defaultConstructorChildren->size() != 4 ||
        !constructorIs((*defaultConstructorChildren)[2],
                       ir::Constructor::ExpressionImplicit) ||
        !originKind(*artifact, (*defaultConstructorChildren)[2], 0,
                    source::OriginKind::Implicit))
        return fail("construction/initialization child order or generated "
                    "provenance mismatch")
                   ? 0
                   : 1;

    const std::vector<std::pair<ir::Constructor, std::size_t>>
        staticAllocationShapes{{ir::Constructor::ExpressionNewAllocating, 3},
                               {ir::Constructor::ExpressionNewAllocating, 4},
                               {ir::Constructor::ExpressionNewAllocating, 4},
                               {ir::Constructor::ExpressionNewAllocating, 5},
                               {ir::Constructor::ExpressionNewAllocating, 4},
                               {ir::Constructor::ExpressionNewNonAllocating, 5},
                               {ir::Constructor::ExpressionNewAllocating, 4},
                               {ir::Constructor::ExpressionDelete, 3},
                               {ir::Constructor::ExpressionDelete, 3}};
    if (staticAllocationNodes.size() != staticAllocationShapes.size())
        return fail("static allocation matrix is incomplete") ? 0 : 1;
    for (std::size_t index = 0; index < staticAllocationShapes.size(); ++index)
        if (!constructorIs(staticAllocationNodes[index],
                           staticAllocationShapes[index].first) ||
            !childCountIs(staticAllocationNodes[index],
                          staticAllocationShapes[index].second) ||
            !originKind(*artifact, staticAllocationNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("static allocation shape or root origin mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    const std::vector<std::pair<ir::Constructor, std::size_t>>
        templateAllocationShapes{{ir::Constructor::ExpressionUnsupported, 1},
                                 {ir::Constructor::ExpressionUnsupported, 1},
                                 {ir::Constructor::ExpressionUnsupported, 1}};
    if (templateAllocationNodes.size() != templateAllocationShapes.size())
        return fail("template allocation matrix is incomplete") ? 0 : 1;
    for (std::size_t index = 0; index < templateAllocationShapes.size();
         ++index)
        if (!constructorIs(templateAllocationNodes[index],
                           templateAllocationShapes[index].first) ||
            !childCountIs(templateAllocationNodes[index],
                          templateAllocationShapes[index].second) ||
            !originKind(*artifact, templateAllocationNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("template allocation shape or root origin mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    for (std::size_t index : {1U, 2U}) {
        auto children =
            artifact->unit->nodes().children(templateAllocationNodes[index]);
        if (!children || children->size() != 1 ||
            !constructorIs(children->front(), ir::Constructor::TypeVoid) ||
            !originKind(*artifact, children->front(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !originAnchorKind(*artifact, children->front(), 0,
                              source::OriginKind::Explicit))
            return fail("unresolved delete helper was not eagerly reduced " +
                        std::to_string(index))
                       ? 0
                       : 1;
    }
    const auto *scalarNew =
        llvm::dyn_cast<clang::CXXNewExpr>(staticAllocations[0]);
    auto scalarNewChildren =
        artifact->unit->nodes().children(staticAllocationNodes[0]);
    auto arrayNewChildren =
        artifact->unit->nodes().children(staticAllocationNodes[3]);
    auto placementNewChildren =
        artifact->unit->nodes().children(staticAllocationNodes[5]);
    auto deleteChildren =
        artifact->unit->nodes().children(staticAllocationNodes[7]);
    if (!scalarNew || !scalarNew->getAllocatedTypeSourceInfo() ||
        !scalarNewChildren || scalarNewChildren->size() != 3 ||
        !originBeginsAt(*artifact, (*scalarNewChildren)[2],
                        ast->getSourceManager(),
                        scalarNew->getAllocatedTypeSourceInfo()
                            ->getTypeLoc()
                            .getBeginLoc()) ||
        !arrayNewChildren || arrayNewChildren->size() != 5 ||
        !constructorIs((*arrayNewChildren)[3],
                       ir::Constructor::ExpressionCast) ||
        !constructorIs((*arrayNewChildren)[4],
                       ir::Constructor::ExpressionInitList) ||
        !placementNewChildren || placementNewChildren->size() != 5 ||
        !constructorIs((*placementNewChildren)[2],
                       ir::Constructor::ExpressionCast) ||
        !constructorIs((*placementNewChildren)[4],
                       ir::Constructor::ExpressionInteger) ||
        !deleteChildren || deleteChildren->size() != 3 ||
        !constructorIs((*deleteChildren)[1], ir::Constructor::ExpressionCast))
        return fail("allocation child order or written allocated type mismatch")
                   ? 0
                   : 1;

    const std::vector<std::pair<ir::Constructor, std::size_t>>
        staticLambdaAtomicShapes{{ir::Constructor::ExpressionAtomic, 3},
                                 {ir::Constructor::ExpressionAtomic, 4},
                                 {ir::Constructor::ExpressionVaArg, 2},
                                 {ir::Constructor::ExpressionLambda, 1},
                                 {ir::Constructor::ExpressionLambda, 3},
                                 {ir::Constructor::ExpressionLambda, 2},
                                 {ir::Constructor::ExpressionLambda, 1},
                                 {ir::Constructor::ExpressionMember, 3},
                                 {ir::Constructor::ExpressionMember, 3},
                                 {ir::Constructor::ExpressionCast, 2},
                                 {ir::Constructor::ExpressionUnsupported, 1}};
    if (staticLambdaAtomicNodes.size() != staticLambdaAtomicShapes.size())
        return fail("static lambda/atomic matrix is incomplete") ? 0 : 1;
    for (std::size_t index = 0; index < staticLambdaAtomicShapes.size();
         ++index)
        if (!constructorIs(staticLambdaAtomicNodes[index],
                           staticLambdaAtomicShapes[index].first) ||
            !childCountIs(staticLambdaAtomicNodes[index],
                          staticLambdaAtomicShapes[index].second) ||
            !originKind(*artifact, staticLambdaAtomicNodes[index], 0,
                        source::OriginKind::Explicit))
            return fail("static lambda/atomic shape or provenance mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    if (templateLambdaNodes.size() != 4 ||
        !constructorIs(templateLambdaNodes[0],
                       ir::Constructor::ExpressionLambda) ||
        !constructorIs(templateLambdaNodes[1],
                       ir::Constructor::ExpressionLambda) ||
        !constructorIs(templateLambdaNodes[2],
                       ir::Constructor::ExpressionMember) ||
        !constructorIs(templateLambdaNodes[3],
                       ir::Constructor::ExpressionMember))
        return fail("template lambda matrix is incomplete") ? 0 : 1;
    auto initializingLambdaChildren =
        artifact->unit->nodes().children(templateLambdaNodes[1]);
    auto capturedThisChildren =
        artifact->unit->nodes().children(staticLambdaAtomicNodes[9]);
    if (!initializingLambdaChildren ||
        initializingLambdaChildren->size() != 2 ||
        !constructorIs((*initializingLambdaChildren)[1],
                       ir::Constructor::ExpressionUnresolvedInitList) ||
        !capturedThisChildren || capturedThisChildren->size() != 2 ||
        !constructorIs((*capturedThisChildren)[1],
                       ir::Constructor::ExpressionMember) ||
        !originKind(*artifact, (*capturedThisChildren)[1], 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, (*capturedThisChildren)[1], 0,
                          source::OriginKind::Explicit))
        return fail("lambda helper reduction or capture provenance mismatch")
                   ? 0
                   : 1;

    auto checkNestedLambda = [&](const std::vector<ir::NodeId> &nodes,
                                 bool templates) {
        if (nodes.size() != 4 ||
            !constructorIs(nodes[0], ir::Constructor::ExpressionLambda) ||
            !childCountIs(nodes[0], 4))
            return false;
        for (std::size_t index = 1; index != 4; ++index)
            if (!constructorIs(nodes[index],
                               ir::Constructor::ExpressionMember) ||
                !childCountIs(nodes[index], 3) ||
                !originKind(*artifact, nodes[index], 0,
                            source::OriginKind::Explicit))
                return false;
        auto lambdaChildren = artifact->unit->nodes().children(nodes[0]);
        if (!lambdaChildren || lambdaChildren->size() != 4 ||
            !constructorIs((*lambdaChildren)[1],
                           templates ? ir::Constructor::ExpressionMember
                                     : ir::Constructor::ExpressionCast) ||
            !constructorIs((*lambdaChildren)[2],
                           ir::Constructor::ExpressionMember) ||
            !constructorIs((*lambdaChildren)[3],
                           ir::Constructor::ExpressionCast))
            return false;
        auto outerMemberChildren =
            artifact->unit->nodes().children((*lambdaChildren)[2]);
        if (!outerMemberChildren || outerMemberChildren->size() != 3 ||
            !constructorIs(outerMemberChildren->front(),
                           ir::Constructor::ExpressionThis) ||
            !originKind(*artifact, outerMemberChildren->front(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !originAnchorKind(*artifact, outerMemberChildren->front(), 0,
                              source::OriginKind::Explicit))
            return false;
        auto outerThisChildren =
            artifact->unit->nodes().children(outerMemberChildren->front());
        if (!outerThisChildren || outerThisChildren->size() != 1 ||
            !constructorIs(outerThisChildren->front(),
                           ir::Constructor::TypePointer))
            return false;
        auto outerPointerChildren =
            artifact->unit->nodes().children(outerThisChildren->front());
        if (!outerPointerChildren || outerPointerChildren->size() != 1 ||
            !constructorIs(outerPointerChildren->front(),
                           ir::Constructor::TypeNamed))
            return false;
        auto copyChildren = artifact->unit->nodes().children(nodes[1]);
        auto referenceChildren = artifact->unit->nodes().children(nodes[2]);
        return copyChildren && copyChildren->size() == 3 && referenceChildren &&
               referenceChildren->size() == 3 &&
               constructorIs(referenceChildren->back(),
                             ir::Constructor::TypeLvalueReference) &&
               (!templates ||
                constructorIs(copyChildren->back(), ir::Constructor::TypeAuto));
    };
    if (!checkNestedLambda(staticNestedLambdaNodes, false) ||
        !checkNestedLambda(templateNestedLambdaNodes, true))
        return fail("nested lambda capture context, cv, or field type mismatch")
                   ? 0
                   : 1;

    const std::size_t expectedStaticConditionals =
        ast->getASTContext().getLangOpts().CPlusPlus20 ? 8 : 7;
    const std::size_t expectedTemplateConditionals =
        ast->getASTContext().getLangOpts().CPlusPlus20 ? 3 : 2;
    if (staticConditionalNodes.size() != expectedStaticConditionals ||
        templateConditionalNodes.size() != expectedTemplateConditionals ||
        !constructorIs(staticConditionalNodes[0],
                       ir::Constructor::ExpressionConditional) ||
        !childCountIs(staticConditionalNodes[0], 4) ||
        !constructorIs(staticConditionalNodes[1],
                       ir::Constructor::ExpressionBinaryConditional) ||
        !childCountIs(staticConditionalNodes[1], 5) ||
        !constructorIs(staticConditionalNodes[2],
                       ir::Constructor::ExpressionBinaryConditional) ||
        !childCountIs(staticConditionalNodes[2], 5) ||
        !constructorIs(staticConditionalNodes[3],
                       ir::Constructor::ExpressionOffsetOf) ||
        !childCountIs(staticConditionalNodes[3], 2) ||
        !constructorIs(staticConditionalNodes[4],
                       ir::Constructor::ExpressionUnsupported) ||
        !constructorIs(staticConditionalNodes[5],
                       ir::Constructor::ExpressionUnsupported) ||
        !constructorIs(staticConditionalNodes[6],
                       ir::Constructor::ExpressionUnsupported) ||
        !constructorIs(templateConditionalNodes[0],
                       ir::Constructor::ExpressionConditional) ||
        !constructorIs(templateConditionalNodes[1],
                       ir::Constructor::ExpressionBinaryConditional))
        return fail("conditional/offsetof/unsupported shape mismatch") ? 0 : 1;
    auto binaryConditionalChildren =
        artifact->unit->nodes().children(staticConditionalNodes[1]);
    auto offsetChildren =
        artifact->unit->nodes().children(staticConditionalNodes[3]);
    auto nestedConditionalTerm =
        emitter.renderNode(*artifact->unit, staticConditionalNodes[2]);
    if (!binaryConditionalChildren || binaryConditionalChildren->size() != 5 ||
        !constructorIs((*binaryConditionalChildren)[2],
                       ir::Constructor::ExpressionOpaqueReference) ||
        !originKind(*artifact, (*binaryConditionalChildren)[2], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*binaryConditionalChildren)[2], 0,
                          source::OriginKind::Explicit) ||
        !offsetChildren || offsetChildren->size() != 2 ||
        !constructorIs(offsetChildren->front(), ir::Constructor::TypeNamed) ||
        !nestedConditionalTerm ||
        nestedConditionalTerm->find("(Eif2 0%N (Eif2 1%N") == std::string::npos)
        return fail("conditional opaque binding/order or offsetof child order "
                    "mismatch")
                   ? 0
                   : 1;
    if (ast->getASTContext().getLangOpts().CPlusPlus20) {
        auto conceptChildren =
            artifact->unit->nodes().children(staticConditionalNodes[7]);
        if (!conceptChildren || conceptChildren->size() != 1 ||
            !constructorIs(conceptChildren->front(),
                           ir::Constructor::TypeBoolean) ||
            !originKind(*artifact, conceptChildren->front(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !originAnchorKind(*artifact, conceptChildren->front(), 0,
                              source::OriginKind::Explicit) ||
            !constructorIs(templateConditionalNodes[2],
                           ir::Constructor::ExpressionUnsupported))
            return fail("concept helper reduction or provenance mismatch") ? 0
                                                                           : 1;
    }

    const std::vector<ir::BuildCardinality> expectedLocalCardinalities{
        ir::BuildCardinality::One,  ir::BuildCardinality::One,
        ir::BuildCardinality::One,  ir::BuildCardinality::Zero,
        ir::BuildCardinality::Zero, ir::BuildCardinality::Zero,
        ir::BuildCardinality::One,  ir::BuildCardinality::Zero,
        ir::BuildCardinality::One,  ir::BuildCardinality::One,
        ir::BuildCardinality::One,  ir::BuildCardinality::One,
        ir::BuildCardinality::One,  ir::BuildCardinality::One,
        ir::BuildCardinality::One};
    if (artifact->localDeclarationGroups.size() !=
        expectedLocalCardinalities.size())
        return fail("local cardinality matrix size mismatch") ? 0 : 1;
    for (std::size_t index = 0; index < expectedLocalCardinalities.size();
         ++index)
        if (artifact->localDeclarationGroups[index].cardinality !=
                expectedLocalCardinalities[index] ||
            artifact->localDeclarationGroups[index].nodes.size() !=
                (expectedLocalCardinalities[index] == ir::BuildCardinality::One
                     ? 1U
                     : 0U))
            return fail("local zero/one cardinality mismatch " +
                        std::to_string(index))
                       ? 0
                       : 1;
    if (staticLocalNodes.size() != 7 || templateLocalNodes.size() != 2 ||
        !constructorIs(staticLocalNodes[0],
                       ir::Constructor::VariableDeclaration) ||
        !childCountIs(staticLocalNodes[0], 1) ||
        !constructorIs(staticLocalNodes[2],
                       ir::Constructor::VariableStaticInit) ||
        !childCountIs(staticLocalNodes[2], 3) ||
        !constructorIs(staticLocalNodes[5],
                       ir::Constructor::VariableDecomposition) ||
        !constructorIs(staticLocalNodes[6],
                       ir::Constructor::VariableDecomposition) ||
        !childCountIs(staticLocalNodes[5], 2) ||
        !childCountIs(staticLocalNodes[6], 2) ||
        !constructorIs(templateLocalNodes[0],
                       ir::Constructor::VariableDeclaration) ||
        !childCountIs(templateLocalNodes[0], 2) ||
        !childCountIs(templateLocalNodes[1], 1))
        return fail("local declaration constructor or child order mismatch")
                   ? 0
                   : 1;
    auto directDecompositionChildren =
        artifact->unit->nodes().children(staticLocalNodes[5]);
    auto holdingDecompositionChildren =
        artifact->unit->nodes().children(staticLocalNodes[6]);
    auto templateLocalChildren =
        artifact->unit->nodes().children(templateLocalNodes[0]);
    if (!directDecompositionChildren ||
        directDecompositionChildren->size() != 2 ||
        !constructorIs(directDecompositionChildren->back(),
                       ir::Constructor::BindingReference) ||
        !holdingDecompositionChildren ||
        holdingDecompositionChildren->size() != 2 ||
        !constructorIs(holdingDecompositionChildren->back(),
                       ir::Constructor::BindingVariable) ||
        !templateLocalChildren || templateLocalChildren->size() != 2 ||
        !constructorIs(templateLocalChildren->back(),
                       ir::Constructor::ExpressionUnresolvedParenList) ||
        staticLocalNodes[5] == staticLocalNodes[6])
        return fail("binding kind, anonymous occurrence, or template Dvar "
                    "reduction mismatch")
                   ? 0
                   : 1;
    if (staticVlaLocalNodes.size() != 1 || templateVlaLocalNodes.size() != 1 ||
        !constructorIs(staticVlaLocalNodes.front(),
                       ir::Constructor::VariableDeclaration) ||
        !constructorIs(templateVlaLocalNodes.front(),
                       ir::Constructor::VariableDeclaration) ||
        !childCountIs(staticVlaLocalNodes.front(), 1) ||
        !childCountIs(templateVlaLocalNodes.front(), 1) ||
        !originKind(*artifact, staticVlaLocalNodes.front(), 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, templateVlaLocalNodes.front(), 0,
                    source::OriginKind::Explicit))
        return fail("VLA local declaration root mismatch") ? 0 : 1;
    auto staticVlaLocalChildren =
        artifact->unit->nodes().children(staticVlaLocalNodes.front());
    auto templateVlaLocalChildren =
        artifact->unit->nodes().children(templateVlaLocalNodes.front());
    if (!staticVlaLocalChildren || staticVlaLocalChildren->size() != 1 ||
        !templateVlaLocalChildren || templateVlaLocalChildren->size() != 1 ||
        !constructorIs(staticVlaLocalChildren->front(),
                       ir::Constructor::TypeVariableArray) ||
        !constructorIs(templateVlaLocalChildren->front(),
                       ir::Constructor::TypeVariableArray) ||
        !childCountIs(staticVlaLocalChildren->front(), 2) ||
        !childCountIs(templateVlaLocalChildren->front(), 2))
        return fail("VLA local type/size child order mismatch") ? 0 : 1;

    if (!constructorIs(statementExpressionNodes.front(),
                       ir::Constructor::ExpressionStatementBlock) ||
        !childCountIs(statementExpressionNodes.front(), 2) ||
        artifact->statementGroups[0].cardinality != ir::BuildCardinality::One ||
        artifact->statementGroups[1].cardinality != ir::BuildCardinality::One ||
        artifact->statementGroups[2].cardinality != ir::BuildCardinality::One ||
        artifact->statementGroups[0].nodes.size() != 1 ||
        artifact->statementGroups[1].nodes.size() != 1 ||
        artifact->statementGroups[2].nodes.size() != 1 ||
        !constructorIs(artifact->statementGroups[2].nodes.front(),
                       ir::Constructor::StatementUnsupported))
        return fail("statement group cardinality or StmtExpr shape mismatch")
                   ? 0
                   : 1;
    const ir::NodeId staticBody = artifact->statementGroups[0].nodes.front();
    const ir::NodeId templateBody = artifact->statementGroups[1].nodes.front();
    auto nullStatementNode =
        artifact->unit->nodes().get(artifact->statementGroups[2].nodes.front());
    if (!originKind(*artifact, statementExpressionNodes.front(), 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, staticBody, 0, source::OriginKind::Explicit) ||
        !originKind(*artifact, templateBody, 0, source::OriginKind::Explicit) ||
        !nullStatementNode || !(*nullStatementNode)->origins.empty())
        return fail("written/empty statement provenance policy mismatch") ? 0
                                                                          : 1;
    auto staticBodyChildren = artifact->unit->nodes().children(staticBody);
    auto templateBodyChildren = artifact->unit->nodes().children(templateBody);
    const std::size_t expectedStaticBodyChildren =
        ast->getASTContext().getLangOpts().CPlusPlus20 ? 29 : 28;
    if (!constructorIs(staticBody, ir::Constructor::StatementSequence) ||
        !staticBodyChildren ||
        staticBodyChildren->size() != expectedStaticBodyChildren ||
        !constructorIs(templateBody, ir::Constructor::StatementSequence) ||
        !templateBodyChildren || templateBodyChildren->size() != 6)
        return fail("statement body top-level sequence mismatch") ? 0 : 1;
    auto firstBodyDeclaration =
        artifact->unit->nodes().children((*staticBodyChildren)[0]);
    if (!firstBodyDeclaration || firstBodyDeclaration->size() != 1 ||
        firstBodyDeclaration->front() == staticLocalNodes[0] ||
        !originKind(*artifact, firstBodyDeclaration->front(), 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, staticLocalNodes[0], 0,
                    source::OriginKind::Explicit))
        return fail("repeated local occurrence was shared or lost provenance")
                   ? 0
                   : 1;
    for (std::size_t index : {3U, 4U, 5U}) {
        auto filtered =
            artifact->unit->nodes().children((*staticBodyChildren)[index]);
        if (!constructorIs((*staticBodyChildren)[index],
                           ir::Constructor::StatementDeclaration) ||
            !filtered || !filtered->empty())
            return fail("filtered DeclStmt retained phantom children") ? 0 : 1;
    }
    auto mixedDeclarations =
        artifact->unit->nodes().children((*staticBodyChildren)[6]);
    auto missingElse =
        artifact->unit->nodes().children((*staticBodyChildren)[14]);
    auto fullIf = artifact->unit->nodes().children((*staticBodyChildren)[15]);
    if (!mixedDeclarations || mixedDeclarations->size() != 2 || !missingElse ||
        missingElse->size() != 3 ||
        !constructorIs(missingElse->back(),
                       ir::Constructor::StatementSequence) ||
        !originKind(*artifact, missingElse->back(), 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, missingElse->back(), 0,
                          source::OriginKind::Explicit) ||
        !fullIf || fullIf->size() != 5)
        return fail("mixed filtering or if optional/synthetic shape mismatch")
                   ? 0
                   : 1;

    auto bracedSwitch =
        artifact->unit->nodes().children((*staticBodyChildren)[16]);
    auto unbracedSwitch =
        artifact->unit->nodes().children((*staticBodyChildren)[17]);
    if (!bracedSwitch || bracedSwitch->size() != 2 || !unbracedSwitch ||
        unbracedSwitch->size() != 2 ||
        !constructorIs(bracedSwitch->back(),
                       ir::Constructor::StatementSequence) ||
        !constructorIs(unbracedSwitch->back(),
                       ir::Constructor::StatementSequence) ||
        !originKind(*artifact, bracedSwitch->back(), 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, unbracedSwitch->back(), 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, unbracedSwitch->back(), 0,
                          source::OriginKind::Explicit))
        return fail("switch compound/noncompound normalization mismatch") ? 0
                                                                          : 1;
    auto bracedSwitchBody =
        artifact->unit->nodes().children(bracedSwitch->back());
    if (!bracedSwitchBody || bracedSwitchBody->size() != 8 ||
        !constructorIs((*bracedSwitchBody)[0],
                       ir::Constructor::StatementCase) ||
        !constructorIs((*bracedSwitchBody)[3],
                       ir::Constructor::StatementCase) ||
        !constructorIs((*bracedSwitchBody)[6],
                       ir::Constructor::StatementDefault))
        return fail("case/default sibling splicing mismatch") ? 0 : 1;
    const ir::NodeId rangeFor = (*staticBodyChildren)[19];
    auto rangeChildren = artifact->unit->nodes().children(rangeFor);
    if (!constructorIs(rangeFor, ir::Constructor::StatementSequence) ||
        !originKind(*artifact, rangeFor, 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, rangeFor, 0,
                          source::OriginKind::Explicit) ||
        !rangeChildren || rangeChildren->size() != 4 ||
        !originKind(*artifact, (*rangeChildren)[0], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*rangeChildren)[0], 0,
                          source::OriginKind::Explicit) ||
        !originKind(*artifact, (*rangeChildren)[1], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*rangeChildren)[1], 0,
                          source::OriginKind::Explicit) ||
        !originKind(*artifact, (*rangeChildren)[2], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*rangeChildren)[2], 0,
                          source::OriginKind::Explicit) ||
        !constructorIs(rangeChildren->back(), ir::Constructor::StatementFor) ||
        !originKind(*artifact, rangeChildren->back(), 0,
                    source::OriginKind::Cpp2vSynthesized) ||
        !originAnchorKind(*artifact, rangeChildren->back(), 0,
                          source::OriginKind::Explicit))
        return fail("range-for eager expansion/order mismatch") ? 0 : 1;
    auto rangeForChildren =
        artifact->unit->nodes().children(rangeChildren->back());
    if (!rangeForChildren || rangeForChildren->size() != 3 ||
        !originKind(*artifact, (*rangeForChildren)[0], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*rangeForChildren)[0], 0,
                          source::OriginKind::Explicit) ||
        !originKind(*artifact, (*rangeForChildren)[1], 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, (*rangeForChildren)[1], 0,
                          source::OriginKind::Explicit) ||
        !constructorIs(rangeForChildren->back(),
                       ir::Constructor::StatementSequence) ||
        !originKind(*artifact, rangeForChildren->back(), 0,
                    source::OriginKind::Cpp2vSynthesized))
        return fail("range-for nested Sfor/Sseq shape mismatch") ? 0 : 1;
    auto rangeInnerChildren =
        artifact->unit->nodes().children(rangeForChildren->back());
    if (!rangeInnerChildren || rangeInnerChildren->size() != 2 ||
        !originKind(*artifact, rangeInnerChildren->front(), 0,
                    source::OriginKind::Implicit) ||
        !originAnchorKind(*artifact, rangeInnerChildren->front(), 0,
                          source::OriginKind::Explicit) ||
        !originKind(*artifact, rangeInnerChildren->back(), 0,
                    source::OriginKind::Explicit))
        return fail("range-for generated declaration/body provenance mismatch")
                   ? 0
                   : 1;
    if (!constructorIs((*templateBodyChildren)[4],
                       ir::Constructor::StatementUnsupported))
        return fail("dependent range-for did not retain exact fallback") ? 0
                                                                         : 1;

    if (finder.constevalIf) {
        const ir::BuildNodeGroup &constevalGroup = artifact->statementGroups[3];
        if (constevalGroup.cardinality != ir::BuildCardinality::One ||
            constevalGroup.nodes.size() != 1 ||
            !constructorIs(constevalGroup.nodes.front(),
                           ir::Constructor::StatementIfConsteval))
            return fail("consteval-if cardinality mismatch") ? 0 : 1;
        auto constevalChildren =
            artifact->unit->nodes().children(constevalGroup.nodes.front());
        if (!constevalChildren || constevalChildren->size() != 2 ||
            !constructorIs(constevalChildren->back(),
                           ir::Constructor::StatementSequence) ||
            !originKind(*artifact, constevalChildren->back(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !originAnchorKind(*artifact, constevalChildren->back(), 0,
                              source::OriginKind::Explicit))
            return fail("consteval-if synthetic else mismatch") ? 0 : 1;
    }

    auto nestedCallChildren =
        artifact->unit->nodes().children(staticCallMemberNodes[25]);
    if (!nestedCallChildren || nestedCallChildren->size() != 3 ||
        !constructorIs((*nestedCallChildren)[1],
                       ir::Constructor::ExpressionCall) ||
        !constructorIs((*nestedCallChildren)[2],
                       ir::Constructor::ExpressionCall))
        return fail("nested call child order is not callee then arguments") ? 0
                                                                            : 1;
    auto thisMemberChildren =
        artifact->unit->nodes().children(staticCallMemberNodes[26]);
    auto thisCallChildren =
        artifact->unit->nodes().children(staticCallMemberNodes[27]);
    if (!thisMemberChildren || thisMemberChildren->size() != 3 ||
        !constructorIs(thisMemberChildren->front(),
                       ir::Constructor::ExpressionThis) ||
        !thisCallChildren || thisCallChildren->size() != 4 ||
        !constructorIs((*thisCallChildren)[2], ir::Constructor::ExpressionThis))
        return fail("implicit-object this child order is malformed") ? 0 : 1;
    for (std::size_t index : {28U, 29U})
        if (!hasOriginKind(*artifact, staticCallMemberNodes[index],
                           source::OriginKind::ClangTransformed))
            return fail(
                       "erased pseudo-destructor call lacks transformed origin")
                       ? 0
                       : 1;

    auto staticArrayChildren =
        artifact->unit->nodes().children(staticOperatorNodes[42]);
    if (!staticArrayChildren || staticArrayChildren->size() != 3 ||
        !constructorIs(staticArrayChildren->front(),
                       ir::Constructor::ExpressionGlobal) ||
        !originKind(*artifact, staticArrayChildren->front(), 1,
                    source::OriginKind::ClangTransformed))
        return fail("array-decay erasure provenance or child order mismatch")
                   ? 0
                   : 1;

    for (std::size_t offset = 0; offset <= 10; ++offset) {
        const ir::NodeId id = artifact->expressions[castLiteralBegin + offset];
        if (!constructorIs(id, ir::Constructor::ExpressionCast) ||
            !originKind(*artifact, id, 0, source::OriginKind::Implicit))
            return fail("implicit cast root or origin is malformed") ? 0 : 1;
        auto children = artifact->unit->nodes().children(id);
        if (!children || children->size() != 2)
            return fail("implicit cast child order is not cast then operand")
                       ? 0
                       : 1;
        auto descriptor = artifact->unit->nodes().get((*children)[0]);
        auto operand = artifact->unit->nodes().get((*children)[1]);
        if (!descriptor || !operand ||
            (*descriptor)->category != ir::Category::Cast ||
            (*operand)->category != ir::Category::Expression)
            return fail("implicit cast children have wrong categories") ? 0 : 1;
    }
    for (std::size_t offset = 11; offset <= 24; ++offset) {
        const ir::NodeId id = artifact->expressions[castLiteralBegin + offset];
        if (!constructorIs(id, ir::Constructor::ExpressionExplicitCast) ||
            !originKind(*artifact, id, 0, source::OriginKind::Explicit))
            return fail("explicit cast root or origin is malformed") ? 0 : 1;
        auto children = artifact->unit->nodes().children(id);
        if (!children || children->size() != 2)
            return fail("explicit cast children are not written type then cast")
                       ? 0
                       : 1;
        auto inner = artifact->unit->nodes().get((*children)[1]);
        if (!inner ||
            (*inner)->constructor != ir::Constructor::ExpressionCast ||
            !originKind(*artifact, (*children)[1], 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("explicit helper cast is not synthesized") ? 0 : 1;
        auto castChildren = artifact->unit->nodes().children((*children)[1]);
        if (!castChildren || castChildren->size() != 2)
            return fail("explicit inner child order is not cast then operand")
                       ? 0
                       : 1;
    }
    const std::vector<std::pair<std::size_t, ir::Constructor>> literalKinds{
        {25, ir::Constructor::ExpressionCharacter},
        {26, ir::Constructor::ExpressionCharacter},
        {27, ir::Constructor::ExpressionCharacter},
        {28, ir::Constructor::ExpressionCharacter},
        {29, ir::Constructor::ExpressionFloat},
        {30, ir::Constructor::ExpressionFloat},
        {31, ir::Constructor::ExpressionUnsupported},
        {32, ir::Constructor::ExpressionString},
        {33, ir::Constructor::ExpressionString},
        {34, ir::Constructor::ExpressionString},
        {35, ir::Constructor::ExpressionCast},
        {36, ir::Constructor::ExpressionInteger},
        {37, ir::Constructor::ExpressionString},
        {38, ir::Constructor::ExpressionBoolean},
        {39, ir::Constructor::ExpressionBoolean},
        {40, ir::Constructor::ExpressionString}};
    for (const auto &entry : literalKinds)
        if (!constructorIs(
                artifact->expressions[castLiteralBegin + entry.first],
                entry.second))
            return fail("literal-like branch has the wrong final constructor")
                       ? 0
                       : 1;
    if (!cxx20Literals.empty() &&
        (!constructorIs(artifact->expressions[castLiteralBegin + 42],
                        ir::Constructor::ExpressionCharacter) ||
         !constructorIs(artifact->expressions[castLiteralBegin + 43],
                        ir::Constructor::ExpressionString)))
        return fail("C++20 char8 literal branches did not build") ? 0 : 1;
    if (!constructorIs(artifact->expressions[dependentCastIndex],
                       ir::Constructor::ExpressionExplicitCast))
        return fail("template dependent cast did not build") ? 0 : 1;
    if (!constructorIs(artifact->expressions[castLiteralBegin + 41],
                       ir::Constructor::ExpressionInteger) ||
        !originKind(*artifact, artifact->expressions[castLiteralBegin + 41], 1,
                    source::OriginKind::ClangTransformed))
        return fail("default-init forwarding provenance is malformed") ? 0 : 1;

    auto sourceString = artifact->unit->nodes().get(
        artifact->expressions[castLiteralBegin + 37]);
    if (!sourceString || (*sourceString)->origins.size() != 2)
        return fail("source-location string lacks exact wrapper provenance")
                   ? 0
                   : 1;
    const source::OriginId syntheticId = (*sourceString)->origins[0];
    const source::OriginId transformedId = (*sourceString)->origins[1];
    const source::Origin &synthetic =
        artifact->unit->sources().origins[syntheticId.value()];
    const source::Origin &transformed =
        artifact->unit->sources().origins[transformedId.value()];
    if (synthetic.kind != source::OriginKind::Cpp2vSynthesized ||
        !synthetic.anchor || synthetic.derivedFrom.size() != 1 ||
        synthetic.derivedFrom.front() != *synthetic.anchor ||
        transformed.kind != source::OriginKind::ClangTransformed ||
        transformed.derivedFrom != std::vector<source::OriginId>{syntheticId})
        return fail("source-location string origin order/derivation is wrong")
                   ? 0
                   : 1;

    for (std::size_t index : {std::size_t(9)}) {
        std::vector<ir::NodeId> pending{artifact->types[index]};
        bool writtenQualifier = false;
        while (!pending.empty()) {
            const ir::NodeId current = pending.back();
            pending.pop_back();
            auto node = artifact->unit->nodes().get(current);
            if (!node)
                return fail("dependent qualifier node is absent") ? 0 : 1;
            if ((*node)->constructor == ir::Constructor::TypeParameter &&
                originKind(*artifact, current, 0, source::OriginKind::Explicit))
                writtenQualifier = true;
            auto children = artifact->unit->nodes().children(current);
            if (!children)
                return fail("dependent qualifier children are malformed") ? 0
                                                                          : 1;
            pending.insert(pending.end(), children->begin(), children->end());
        }
        if (!writtenQualifier)
            return fail("dependent NestedNameSpecifierLoc was not preserved")
                       ? 0
                       : 1;
    }
    auto semanticTypeNode = artifact->unit->nodes().get(artifact->types.back());
    if (!semanticTypeNode || !(*semanticTypeNode)->origins.empty())
        return fail("semantic QualType unexpectedly acquired a written origin")
                   ? 0
                   : 1;

    if (!constructorIs(artifact->types[6], ir::Constructor::TypeUnsupported))
        return fail("long double did not preserve legacy Tunsupported") ? 0 : 1;
    const std::vector<std::pair<std::size_t, ir::Constructor>> auditedTypes{
        {10, ir::Constructor::TypeUnsupported},
        {11, ir::Constructor::TypeNumber},
        {12, ir::Constructor::TypeUnsupported},
        {13, ir::Constructor::TypeNumber},
        {14, ir::Constructor::TypeLvalueReference},
        {15, ir::Constructor::TypeNamed},
        {16, ir::Constructor::TypeUnsupported},
        {17, ir::Constructor::TypeUnsupported},
        {18, ir::Constructor::TypePointer},
        {19, ir::Constructor::TypeNamed},
        {20, ir::Constructor::TypeDecltype},
        {21, ir::Constructor::TypeDecltype},
        {22, ir::Constructor::TypeNamed},
        {23, ir::Constructor::TypeNamed},
        {24, ir::Constructor::TypeUnsupported},
        {25, ir::Constructor::TypeUnsupported}};
    for (const auto &[index, constructor] : auditedTypes)
        if (!constructorIs(artifact->types[index], constructor))
            return fail("PrintType audit constructor mismatch at " +
                        std::to_string(index))
                       ? 0
                       : 1;
    if (!constructorIs(artifact->types[26], ir::Constructor::TypeVariableArray))
        return fail("variable-array kernel type was not completed") ? 0 : 1;
    auto variableArrayChildren =
        artifact->unit->nodes().children(artifact->types[26]);
    if (!variableArrayChildren || variableArrayChildren->size() != 2 ||
        !constructorIs(variableArrayChildren->back(),
                       ir::Constructor::ExpressionBinary))
        return fail("variable-array bound tree is incomplete") ? 0 : 1;
    auto staticAutoChildren =
        artifact->unit->nodes().children(artifact->types[7]);
    auto templateAutoChildren =
        artifact->unit->nodes().children(artifact->types[8]);
    if (!staticAutoChildren || staticAutoChildren->empty() ||
        !templateAutoChildren || templateAutoChildren->empty() ||
        !constructorIs(staticAutoChildren->front(),
                       ir::Constructor::TypeUnsupported) ||
        !constructorIs(templateAutoChildren->front(),
                       ir::Constructor::TypeAuto))
        return fail("per-use static/template auto modes diverged incorrectly")
                   ? 0
                   : 1;
    for (std::size_t index = 5; index < 10; ++index) {
        if (!constructorIs(artifact->names[index],
                           ir::Constructor::NameInstantiation))
            return fail("template declaration/specialization lacks Ninst") ? 0
                                                                           : 1;
        auto children =
            artifact->unit->nodes().children(artifact->names[index]);
        if (!children || children->empty() ||
            constructorIs(children->front(),
                          ir::Constructor::NameInstantiation))
            return fail("template name was double-instantiated") ? 0 : 1;
    }
    for (std::size_t index = 6; index <= 9; ++index) {
        auto children =
            artifact->unit->nodes().children(artifact->names[index]);
        if (!children || children->size() < 2)
            return fail("specialization name lost argument children") ? 0 : 1;
        for (std::size_t child = 1; child < children->size(); ++child)
            if (!originKind(*artifact, (*children)[child], 0,
                            source::OriginKind::Explicit))
                return fail("specialization argument lost as-written origin")
                           ? 0
                           : 1;
    }
    bool sawNew = false;
    bool sawDelete = false;
    for (std::size_t index = 10; index < defaultedSpecializationName; ++index) {
        auto children =
            artifact->unit->nodes().children(artifact->names[index]);
        if (!children || children->size() != 1)
            return fail("allocation operator name root is malformed") ? 0 : 1;
        sawNew |= constructorIs(children->front(),
                                ir::Constructor::AtomicNewOperator);
        sawDelete |= constructorIs(children->front(),
                                   ir::Constructor::AtomicDeleteOperator);
    }
    if (!sawNew || !sawDelete)
        return fail("structured allocation operator names are absent") ? 0 : 1;
    auto defaultedChildren = artifact->unit->nodes().children(
        artifact->names[defaultedSpecializationName]);
    if (!defaultedChildren || defaultedChildren->size() != 4)
        return fail("defaulted specialization arguments are incomplete") ? 0
                                                                         : 1;
    for (std::size_t index = 1; index < defaultedChildren->size(); ++index)
        if (!originKind(*artifact, (*defaultedChildren)[index], 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("omitted specialization argument is not synthesized")
                       ? 0
                       : 1;
    for (std::size_t index = additionalPrimaryNames;
         index < artifact->names.size(); ++index)
        if (!constructorIs(artifact->names[index],
                           ir::Constructor::NameInstantiation))
            return fail("primary function/variable/alias name lacks Ninst") ? 0
                                                                            : 1;

    for (std::size_t specializationIndex = 0;
         specializationIndex < finder.classSpecializations.size();
         ++specializationIndex) {
        const clang::ASTTemplateArgumentListInfo *written =
            finder.classSpecializations[specializationIndex]
                ->getTemplateArgsAsWritten();
        auto children = artifact->unit->nodes().children(
            artifact->names[6 + specializationIndex]);
        if (!written || !children ||
            written->arguments().size() + 1 != children->size())
            return fail("class specialization written arguments are absent")
                       ? 0
                       : 1;
        for (std::size_t argument = 0; argument < written->arguments().size();
             ++argument)
            if (!originBeginsAt(
                    *artifact, (*children)[argument + 1],
                    ast->getSourceManager(),
                    written->arguments()[argument].getSourceRange().getBegin()))
                return fail("class specialization argument range is not exact")
                           ? 0
                           : 1;
    }
    const clang::ASTTemplateArgumentListInfo *variableWritten =
        finder.variableSpecializations.front()->getTemplateArgsAsWritten();
    auto variableNameChildren =
        artifact->unit->nodes().children(artifact->names[9]);
    if (!variableWritten || variableWritten->arguments().empty() ||
        !variableNameChildren || variableNameChildren->size() != 2 ||
        !originBeginsAt(
            *artifact, variableNameChildren->back(), ast->getSourceManager(),
            variableWritten->arguments().front().getSourceRange().getBegin()))
        return fail("variable specialization argument range is not exact") ? 0
                                                                           : 1;

    const clang::ASTTemplateArgumentListInfo *functionWritten =
        finder.functionSpecializations.front()
            ->getTemplateSpecializationArgsAsWritten();
    auto functionNameChildren =
        artifact->unit->nodes().children(artifact->names[8]);
    if (!functionWritten || functionWritten->arguments().empty() ||
        !functionNameChildren || functionNameChildren->size() != 2 ||
        !originBeginsAt(
            *artifact, functionNameChildren->back(), ast->getSourceManager(),
            functionWritten->arguments().front().getSourceRange().getBegin()))
        return fail("function specialization argument range is not exact") ? 0
                                                                           : 1;
    auto primaryChildren = artifact->unit->nodes().children(artifact->names[5]);
    if (!primaryChildren || primaryChildren->size() != 4)
        return fail("primary template name child order is incomplete") ? 0 : 1;
    for (std::size_t index = 1; index < primaryChildren->size(); ++index)
        if (!originKind(*artifact, (*primaryChildren)[index], 0,
                        source::OriginKind::Cpp2vSynthesized))
            return fail("fabricated primary argument is not synthesized") ? 0
                                                                          : 1;
    for (std::size_t index : {std::size_t(6), std::size_t(7)})
        if (!constructorIs(artifact->expressions[index],
                           index == 6 ? ir::Constructor::ExpressionUnary
                                      : ir::Constructor::ExpressionBinary))
            return fail("resolved expression kernel constructor mismatch") ? 0
                                                                           : 1;
    if (!constructorIs(artifact->expressions[8],
                       ir::Constructor::ExpressionUnary) ||
        !constructorIs(artifact->expressions[9],
                       ir::Constructor::ExpressionBinary) ||
        !constructorIs(artifact->expressions[10],
                       ir::Constructor::ExpressionUnresolvedGlobal))
        return fail("dependent expression kernel constructor mismatch") ? 0 : 1;
    if (!constructorIs(artifact->expressions[11],
                       ir::Constructor::ExpressionLocalNamed) ||
        !constructorIs(artifact->expressions[12],
                       ir::Constructor::ExpressionGlobal) ||
        !constructorIs(artifact->expressions[13],
                       ir::Constructor::ExpressionBinary) ||
        !constructorIs(artifact->expressions[14],
                       ir::Constructor::ExpressionLocalNamed) ||
        !constructorIs(artifact->expressions[15],
                       ir::Constructor::ExpressionLocalNamed) ||
        !constructorIs(artifact->expressions[16],
                       ir::Constructor::ExpressionEnumConstant) ||
        !constructorIs(artifact->expressions[17],
                       ir::Constructor::ExpressionCast))
        return fail("local/static/binding/enum expression kernel mismatch") ? 0
                                                                            : 1;
    auto referenceChildren =
        artifact->unit->nodes().children(artifact->expressions[14]);
    auto bindingChildren =
        artifact->unit->nodes().children(artifact->expressions[15]);
    if (!referenceChildren || referenceChildren->size() != 1 ||
        !constructorIs(referenceChildren->front(),
                       ir::Constructor::TypeLvalueReference) ||
        !bindingChildren || bindingChildren->size() != 1 ||
        !constructorIs(bindingChildren->front(), ir::Constructor::TypeNumber))
        return fail("declaration-reference type ownership is incorrect") ? 0
                                                                         : 1;
    auto enumCastChildren =
        artifact->unit->nodes().children(artifact->expressions[17]);
    if (!enumCastChildren || enumCastChildren->size() != 2 ||
        !constructorIs(enumCastChildren->front(),
                       ir::Constructor::CastIntegral) ||
        !constructorIs(enumCastChildren->back(),
                       ir::Constructor::ExpressionEnumConstant))
        return fail("enum constant integral cast is malformed") ? 0 : 1;

    auto localBinaryChildren =
        artifact->unit->nodes().children(artifact->expressions[13]);
    if (!localBinaryChildren || localBinaryChildren->size() != 3)
        return fail("local binary child order is malformed") ? 0 : 1;
    for (std::size_t index = 0; index < 2; ++index) {
        const ir::NodeId castExpression = (*localBinaryChildren)[index];
        if (!constructorIs(castExpression, ir::Constructor::ExpressionCast) ||
            !originKind(*artifact, castExpression, 0,
                        source::OriginKind::Implicit))
            return fail("required lvalue conversion lacks implicit origin") ? 0
                                                                            : 1;
        auto castChildren = artifact->unit->nodes().children(castExpression);
        if (!castChildren || castChildren->size() != 2 ||
            !constructorIs(castChildren->front(),
                           ir::Constructor::CastLvalueToRvalue))
            return fail("required lvalue conversion lacks Cl2r") ? 0 : 1;
    }
    for (std::size_t index : {std::size_t(0), std::size_t(1), std::size_t(2),
                              std::size_t(4), std::size_t(5), std::size_t(6)})
        if (!artifact->templateParameterEntries[index].defaultArgument)
            return fail("template default was lost") ? 0 : 1;
    if (artifact->templateParameterEntries[3].defaultArgument)
        return fail("absent template default became present") ? 0 : 1;
    for (std::size_t index = 4; index <= 6; ++index) {
        const ir::TemplateParameterEntry &entry =
            artifact->templateParameterEntries[index];
        auto parameterNode = artifact->unit->nodes().get(entry.parameter);
        auto defaultNode = artifact->unit->nodes().get(*entry.defaultArgument);
        if (!parameterNode || !defaultNode || (*parameterNode)->origins.empty())
            return fail("inherited default nodes are malformed") ? 0 : 1;
        bool exactInherited = false;
        for (source::OriginId originId : (*defaultNode)->origins) {
            const source::Origin &origin =
                artifact->unit->sources().origins[originId.value()];
            exactInherited |=
                origin.kind == source::OriginKind::Inherited &&
                origin.anchor == (*parameterNode)->origins.front() &&
                origin.derivedFrom == (*parameterNode)->origins;
        }
        if (!exactInherited)
            return fail("inherited default lacks current-parameter relation")
                       ? 0
                       : 1;
    }
    auto packed = ir::factory::packTemplateParameters(
        artifact->unit->nodes(), artifact->templateParameterEntries);
    if (!packed || packed->size() != 7)
        return fail("template parameter entries did not pack") ? 0 : 1;
    for (std::size_t index = 0; index < packed->size(); ++index) {
        const auto *product =
            std::get_if<ir::ProductValue>(&(*packed)[index].payload);
        if (!product || product->fields.size() != 2)
            return fail("template parameter pair grouping was lost") ? 0 : 1;
        const auto *optional =
            std::get_if<ir::OptionalValue>(&product->fields[1].payload);
        const bool expected = index < 3 || index >= 4;
        if (!optional || static_cast<bool>(optional->value) != expected)
            return fail("template default option grouping was lost") ? 0 : 1;
    }

    // Assert each recursively written TypeLoc, rather than merely finding one
    // explicit child somewhere below a written root.
    for (std::size_t index : {std::size_t(0), std::size_t(1), std::size_t(2),
                              std::size_t(3), std::size_t(5)})
        if (!originKind(*artifact, artifact->types[index], 0,
                        source::OriginKind::Explicit))
            return fail("written type root lacks an explicit origin") ? 0 : 1;

    auto pointerChildren = explicitChildren(*artifact, artifact->types[0], 1);
    auto pointerQualifier =
        pointerChildren
            ? explicitChildren(*artifact, pointerChildren->front(), 1)
            : std::nullopt;
    if (!pointerQualifier)
        return fail("pointer/cv/element TypeLoc chain is incomplete") ? 0 : 1;

    if (!explicitChildren(*artifact, artifact->types[1], 1))
        return fail("array element TypeLoc is absent") ? 0 : 1;

    auto functionPointerChildren =
        explicitChildren(*artifact, artifact->types[2], 1);
    auto pointedFunctionChildren =
        functionPointerChildren
            ? explicitChildren(*artifact, functionPointerChildren->front(), 2)
            : std::nullopt;
    if (!pointedFunctionChildren)
        return fail("function-pointer return/parameter TypeLocs are incomplete")
                   ? 0
                   : 1;

    auto memberChildren = explicitChildren(*artifact, artifact->types[3], 2);
    if (!memberChildren)
        return fail("member-pointer class/pointee TypeLocs are incomplete") ? 0
                                                                            : 1;

    if (!originKind(*artifact, artifact->types[4], 0,
                    source::OriginKind::ClangTransformed))
        return fail("erased typedef lacks wrapper-specific provenance") ? 0 : 1;

    auto functionChildren = explicitChildren(*artifact, artifact->types[5], 4);
    if (!functionChildren)
        return fail("function return/each parameter TypeLoc is incomplete") ? 0
                                                                            : 1;
    auto firstParameterChildren =
        explicitChildren(*artifact, (*functionChildren)[1], 1);
    auto firstParameterQualifier =
        firstParameterChildren
            ? explicitChildren(*artifact, firstParameterChildren->front(), 1)
            : std::nullopt;
    auto secondParameterChildren =
        explicitChildren(*artifact, (*functionChildren)[2], 1);
    auto nestedFunctionChildren =
        secondParameterChildren
            ? explicitChildren(*artifact, secondParameterChildren->front(), 2)
            : std::nullopt;
    auto thirdParameterChildren =
        explicitChildren(*artifact, (*functionChildren)[3], 1);
    if (!firstParameterQualifier)
        return fail("normalized array parameter TypeLoc chain is incomplete")
                   ? 0
                   : 1;
    if (!nestedFunctionChildren)
        return fail("normalized function parameter TypeLoc chain is incomplete")
                   ? 0
                   : 1;
    if (!thirdParameterChildren)
        return fail("normalized cv-pointer parameter TypeLoc chain is "
                    "incomplete")
                   ? 0
                   : 1;

    if (!originKind(*artifact, artifact->expressions[0], 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, artifact->expressions[0], 1,
                    source::OriginKind::ClangTransformed))
        return fail("forwarded expression origin order is not direct/wrapper")
                   ? 0
                   : 1;

    auto writtenTypeArgument =
        explicitChildren(*artifact, artifact->templateArguments[0], 1);
    auto argumentPointer =
        writtenTypeArgument
            ? explicitChildren(*artifact, writtenTypeArgument->front(), 1)
            : std::nullopt;
    auto argumentQualifier =
        argumentPointer
            ? explicitChildren(*artifact, argumentPointer->front(), 1)
            : std::nullopt;
    auto writtenValueArgument =
        explicitChildren(*artifact, artifact->templateArguments[1], 1);
    if (!originKind(*artifact, artifact->templateArguments[0], 0,
                    source::OriginKind::Explicit) ||
        !originKind(*artifact, artifact->templateArguments[1], 0,
                    source::OriginKind::Explicit) ||
        !argumentQualifier || !writtenValueArgument)
        return fail("written template argument origins/children are incomplete")
                   ? 0
                   : 1;
    auto writtenDeclaration =
        explicitChildren(*artifact, artifact->templateArguments[2], 1);
    if (!writtenDeclaration ||
        !constructorIs(artifact->templateArguments[2],
                       ir::Constructor::TemplateArgumentValue))
        return fail("written declaration argument lost Avalue/origin") ? 0 : 1;
    if (!constructorIs(artifact->templateArguments[4],
                       ir::Constructor::TemplateArgumentPack))
        return fail("semantic pack argument lost Apack") ? 0 : 1;
    auto packChildren =
        artifact->unit->nodes().children(artifact->templateArguments[4]);
    if (!packChildren || packChildren->size() != 2 ||
        !constructorIs((*packChildren)[0],
                       ir::Constructor::TemplateArgumentType) ||
        !constructorIs((*packChildren)[1],
                       ir::Constructor::TemplateArgumentType))
        return fail("semantic pack argument order is malformed") ? 0 : 1;

    auto declarationArgumentChildren =
        artifact->unit->nodes().children(artifact->templateArguments[5]);
    if (!declarationArgumentChildren ||
        declarationArgumentChildren->size() != 1 ||
        !constructorIs(declarationArgumentChildren->front(),
                       ir::Constructor::ExpressionGlobal))
        return fail("canonical declaration argument differs from legacy") ? 0
                                                                          : 1;
    if (!constructorIs(artifact->templateArguments[6],
                       ir::Constructor::TemplateArgumentUnsupported) ||
        !constructorIs(artifact->templateArguments[7],
                       ir::Constructor::TemplateArgumentUnsupported))
        return fail("unsupported template argument kinds are not final") ? 0
                                                                         : 1;

    auto semanticArgument =
        artifact->unit->nodes().get(artifact->templateArguments[3]);
    auto semanticArgumentChildren =
        artifact->unit->nodes().children(artifact->templateArguments[3]);
    if (!semanticArgument || !(*semanticArgument)->origins.empty() ||
        !semanticArgumentChildren || semanticArgumentChildren->size() != 1)
        return fail("semantic template argument fallback is malformed") ? 0 : 1;
    auto semanticArgumentType =
        artifact->unit->nodes().get(semanticArgumentChildren->front());
    if (!semanticArgumentType || !(*semanticArgumentType)->origins.empty())
        return fail("semantic template argument gained a written origin") ? 0
                                                                          : 1;
    auto directBuiltinNode = artifact->unit->nodes().get(
        artifact->expressions[castLiteralBegin - 1]);
    if (!directBuiltinNode ||
        (*directBuiltinNode)->constructor != ir::Constructor::ExpressionGlobal)
        return fail("bare builtin reference was eagerly cast") ? 0 : 1;

    auto builtinChildren =
        artifact->unit->nodes().children(artifact->expressions[5]);
    if (!builtinChildren || builtinChildren->size() != 2) {
        return fail("builtin lowering is not cast then global") ? 0 : 1;
    }
    auto castNode = artifact->unit->nodes().get((*builtinChildren)[0]);
    if (!castNode ||
        (*castNode)->constructor != ir::Constructor::CastBuiltinToFunction)
        return fail("builtin lowering lacks Cbuiltin2fun") ? 0 : 1;

    std::vector<ir::PointerUse<clang::Expr>> localExpressions{
        {finder.localReference, ir::SemanticMode::Static}};
    ir::BuildSelection localSelection{{}, {}, {}, localExpressions, {}, {}, {}};
    auto local = ir::IRBuilder::build(ast->getASTContext(), localSelection);
    if (!local || local->expressions.size() != 1)
        return fail("local reference did not build") ? 0 : 1;
    auto localTerm = emitter.renderNode(*local->unit, local->expressions[0]);
    if (!localTerm ||
        *localTerm != "(Evar \"local_value\" (Tnum int_rank.Iint Signed))")
        return fail("local reference has the wrong final term") ? 0 : 1;

    auto restrictTerm = emitter.renderNode(
        *artifact->unit, artifact->types[writtenTypes.size() - 1]);
    if (!restrictTerm || *restrictTerm != "(Tptr (Tnum int_rank.Iint Signed))")
        return fail("restrict qualifier did not erase to the legacy type") ? 0
                                                                           : 1;

    std::vector<ir::PointerUse<clang::Expr>> staticDependent{
        {finder.dependentReference, ir::SemanticMode::Static}};
    auto rejectedDependent = ir::IRBuilder::build(
        ast->getASTContext(),
        ir::BuildSelection{{}, {}, {}, staticDependent, {}, {}, {}});
    if (rejectedDependent ||
        llvm::toString(rejectedDependent.takeError())
                .find("requires template semantic mode") == std::string::npos)
        return fail("static dependent reference crossed the mode boundary") ? 0
                                                                            : 1;

    std::vector<ir::PointerUse<clang::Expr>> staticDependentMember{
        {templateCallMembers[1], ir::SemanticMode::Static}};
    auto rejectedDependentMember = ir::IRBuilder::build(
        ast->getASTContext(),
        ir::BuildSelection{{}, {}, {}, staticDependentMember, {}, {}, {}});
    if (rejectedDependentMember ||
        llvm::toString(rejectedDependentMember.takeError())
                .find("requires template semantic mode") == std::string::npos)
        return fail("static dependent member crossed the mode boundary") ? 0
                                                                         : 1;

    std::vector<ir::PointerUse<clang::Expr>> staticUnresolvedDelete{
        {finder.templateDeletes.front(), ir::SemanticMode::Static}};
    auto rejectedUnresolvedDelete = ir::IRBuilder::build(
        ast->getASTContext(),
        ir::BuildSelection{{}, {}, {}, staticUnresolvedDelete, {}, {}, {}});
    if (rejectedUnresolvedDelete ||
        llvm::toString(rejectedUnresolvedDelete.takeError())
                .find("unresolved delete in static mode") == std::string::npos)
        return fail("unresolved delete crossed the static mode boundary") ? 0
                                                                          : 1;

    for (const auto &[value, semanticMode, label, expectedChildren, message] :
         {std::tuple<const clang::Expr *, ir::SemanticMode, const char *,
                     std::size_t, const char *>{
              staticVlaLambda, ir::SemanticMode::Static, "VLA_STATIC", 3,
              "empty expression (nullptr)"},
          std::tuple<const clang::Expr *, ir::SemanticMode, const char *,
                     std::size_t, const char *>{
              templateVlaLambda, ir::SemanticMode::Template, "VLA_TEMPLATE", 4,
              "variable length array capture"}}) {
        std::vector<ir::PointerUse<clang::Expr>> vlaLambda{
            {value, semanticMode}};
        auto builtVla = ir::IRBuilder::build(
            ast->getASTContext(),
            ir::BuildSelection{{}, {}, {}, vlaLambda, {}, {}, {}});
        if (!builtVla || builtVla->expressions.size() != 1)
            return fail("VLA lambda capture did not build") ? 0 : 1;
        auto vlaConstructorIs = [&](ir::NodeId id, ir::Constructor expected) {
            auto node = builtVla->unit->nodes().get(id);
            return node && (*node)->constructor == expected;
        };
        auto children =
            builtVla->unit->nodes().children(builtVla->expressions.front());
        if (!children || children->size() != expectedChildren ||
            !vlaConstructorIs((*children)[1],
                              ir::Constructor::ExpressionUnsupported) ||
            !originKind(*builtVla, (*children)[1], 0,
                        source::OriginKind::Implicit) ||
            !originAnchorKind(*builtVla, (*children)[1], 0,
                              source::OriginKind::Explicit)) {
            std::cerr << label << " child count "
                      << (children ? children->size() : 0) << " expected "
                      << expectedChildren << '\n';
            if (children)
                for (ir::NodeId child : *children) {
                    auto node = builtVla->unit->nodes().get(child);
                    if (node)
                        std::cerr << "  "
                                  << ir::constructorSpec((*node)->constructor)
                                         .rocqSpelling
                                  << " origins " << (*node)->origins.size();
                    for (source::OriginId originId : (*node)->origins) {
                        const source::Origin &origin =
                            builtVla->unit->sources().origins[originId.value()];
                        std::cerr << " kind " << static_cast<int>(origin.kind);
                        if (origin.anchor)
                            std::cerr
                                << " anchor-kind "
                                << static_cast<int>(
                                       builtVla->unit->sources()
                                           .origins[origin.anchor->value()]
                                           .kind);
                    }
                    std::cerr << '\n';
                }
            return fail("VLA lambda capture shape or provenance mismatch") ? 0
                                                                           : 1;
        }
        auto unsupportedChildren =
            builtVla->unit->nodes().children((*children)[1]);
        if (!unsupportedChildren || unsupportedChildren->size() != 1 ||
            !vlaConstructorIs(unsupportedChildren->front(),
                              ir::Constructor::TypeAuto) ||
            !originKind(*builtVla, unsupportedChildren->front(), 0,
                        source::OriginKind::Cpp2vSynthesized) ||
            !originAnchorKind(*builtVla, unsupportedChildren->front(), 0,
                              source::OriginKind::Implicit))
            return fail("VLA unsupported type provenance mismatch") ? 0 : 1;
        auto rendered =
            emitter.renderNode(*builtVla->unit, builtVla->expressions.front());
        if (!rendered || rendered->find(message) == std::string::npos)
            return fail("VLA lambda fallback payload mismatch") ? 0 : 1;
        std::cout << label << " " << *rendered << '\n';
    }

    std::vector<ir::PointerUse<clang::Expr>> staticParameter{
        {finder.templateParameterReference, ir::SemanticMode::Static}};
    auto rejectedParameter = ir::IRBuilder::build(
        ast->getASTContext(),
        ir::BuildSelection{{}, {}, {}, staticParameter, {}, {}, {}});
    if (rejectedParameter ||
        llvm::toString(rejectedParameter.takeError())
                .find("lacks static substitution") == std::string::npos)
        return fail("static template parameter became Eparam") ? 0 : 1;

    clang::IgnoringDiagConsumer ignoredInvalidLocalDiagnostics;
    auto invalidAst = clang::tooling::buildASTFromCodeWithArgs(
        "void invalid_local_kernel() { void broken; }", {"-std=c++17"},
        "invalid-local.cpp", "type-expression-builder-probe",
        std::make_shared<clang::PCHContainerOperations>(),
        clang::tooling::getClangStripDependencyFileAdjuster(), {},
        &ignoredInvalidLocalDiagnostics);
    InvalidLocalFinder invalidLocalFinder;
    if (invalidAst)
        invalidLocalFinder.TraverseDecl(
            invalidAst->getASTContext().getTranslationUnitDecl());
    std::vector<ir::PointerUse<clang::Decl>> invalidLocals{
        {invalidLocalFinder.invalid, ir::SemanticMode::Static}};
    ir::BuildSelection invalidLocalSelection;
    invalidLocalSelection.localDeclarations = invalidLocals;
    auto rejectedInvalidLocal =
        invalidAst ? ir::IRBuilder::build(invalidAst->getASTContext(),
                                          invalidLocalSelection)
                   : llvm::Expected<ir::BuildArtifact>(llvm::createStringError(
                         std::errc::invalid_argument,
                         "failed to parse invalid local"));
    if (rejectedInvalidLocal ||
        llvm::toString(rejectedInvalidLocal.takeError())
                .find("invalid local declaration (Derror)") ==
            std::string::npos)
        return fail("invalid local did not retain the Derror boundary") ? 0 : 1;

    std::vector<ir::PointerUse<clang::Stmt>> unsupportedStatements{
        {finder.unsupportedCatch, ir::SemanticMode::Static}};
    ir::BuildSelection unsupportedStatementSelection;
    unsupportedStatementSelection.statements = unsupportedStatements;
    auto rejectedStatement = ir::IRBuilder::build(
        ast->getASTContext(), unsupportedStatementSelection);
    if (rejectedStatement ||
        llvm::toString(rejectedStatement.takeError()).find("unsupported") ==
            std::string::npos)
        return fail("unknown statement did not retain the fatal boundary") ? 0
                                                                           : 1;

    std::vector<ir::PointerUse<clang::NamedDecl>> guideName{
        {finder.deductionGuide, ir::SemanticMode::Static}};
    auto guide = ir::IRBuilder::build(
        ast->getASTContext(),
        ir::BuildSelection{guideName, {}, {}, {}, {}, {}, {}});
    if (!guide || guide->names.size() != 1)
        return fail("deduction guide name did not build") ? 0 : 1;
    auto guideTerm = emitter.renderNode(*guide->unit, guide->names.front());
    if (!guideTerm || *guideTerm !=
                          "(Nglobal (Nunsupported_atomic \"atomic name of kind "
                          "CXXDeductionGuide\"))")
        return fail("deduction guide did not use legacy unsupported atomic")
                   ? 0
                   : 1;

    if (std::string(ir::builder::templateArgumentKindNameForTest(
            clang::TemplateArgument::StructuralValue)) != "<unknown>")
        return fail("structural argument did not use legacy unknown kind") ? 0
                                                                           : 1;
    return 0;
}
