/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include <clang/AST/ASTContext.h>
#include <clang/AST/Attr.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/RecordLayout.h>
#include <clang/Basic/Builtins.h>
#include <clang/Basic/Version.inc>
#include <clang/Sema/Sema.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/Support/Casting.h>

#include <system_error>

namespace ir {
namespace builder {
namespace {

llvm::Error declarationError(const clang::Decl &declaration,
                             llvm::StringRef message) {
    return llvm::createStringError(
        std::errc::invalid_argument, "declaration builder rejected %s: %s",
        declaration.getDeclKindName(), message.str().c_str());
}

bool isUntemplatedNode(Arena &arena, NodeId node) {
    auto value = arena.get(node);
    if (!value)
        return false;
    switch ((*value)->constructor) {
    case Constructor::TypeParameter:
    case Constructor::TypeResultGlobal:
    case Constructor::TypeResultCall:
    case Constructor::TypeResultUnarySyntax:
    case Constructor::TypeResultMember:
    case Constructor::ExpressionParameter:
    case Constructor::ExpressionUnresolvedGlobal:
    case Constructor::ExpressionUnresolvedSizeofPack:
    case Constructor::ExpressionUnresolvedUnary:
    case Constructor::ExpressionUnresolvedUnsupportedUnary:
    case Constructor::ExpressionUnresolvedUnarySyntax:
    case Constructor::ExpressionUnresolvedBinary:
    case Constructor::ExpressionUnresolvedBinarySyntax:
    case Constructor::ExpressionUnresolvedCompoundAssignment:
    case Constructor::ExpressionUnresolvedCall:
    case Constructor::ExpressionUnresolvedMember:
    case Constructor::ExpressionUnresolvedParenList:
    case Constructor::ExpressionUnresolvedInitList:
        return false;
    default:
        break;
    }
    auto children = arena.children(node);
    if (!children)
        return false;
    for (NodeId child : *children)
        if (!isUntemplatedNode(arena, child))
            return false;
    return true;
}

struct SpecializationParts {
    const clang::TemplateDecl *templ = nullptr;
    const clang::TemplateArgumentList *arguments = nullptr;
};

std::optional<SpecializationParts>
recoverSpecialization(const clang::NamedDecl &declaration) {
    using namespace clang;
    if (const auto *value =
            dyn_cast<ClassTemplateSpecializationDecl>(&declaration))
        return SpecializationParts{&*value->getSpecializedTemplate(),
                                   &value->getTemplateArgs()};
    if (const auto *value = dyn_cast<FunctionDecl>(&declaration))
        if (const FunctionTemplateDecl *templ = value->getPrimaryTemplate())
            if (const TemplateArgumentList *arguments =
                    value->getTemplateSpecializationArgs())
                return SpecializationParts{templ, arguments};
    if (const auto *value =
            dyn_cast<VarTemplateSpecializationDecl>(&declaration))
        return SpecializationParts{&*value->getSpecializedTemplate(),
                                   &value->getTemplateArgs()};
    return std::nullopt;
}

const clang::NamedDecl *recoverPattern(const clang::NamedDecl &declaration) {
    using namespace clang;
    if (const auto *value = dyn_cast<CXXRecordDecl>(&declaration)) {
        if (const CXXRecordDecl *pattern =
                value->getInstantiatedFromMemberClass())
            return pattern;
        return value->getTemplateInstantiationPattern();
    }
    if (const auto *value = dyn_cast<FunctionDecl>(&declaration)) {
        if (const FunctionDecl *pattern =
                value->getInstantiatedFromMemberFunction())
            return pattern;
        if (const FunctionDecl *pattern = value->getInstantiatedFromDecl())
            return pattern;
        return value->getTemplateInstantiationPattern();
    }
    if (const auto *value = dyn_cast<EnumDecl>(&declaration)) {
        if (const EnumDecl *pattern = value->getInstantiatedFromMemberEnum())
            return pattern;
        return value->getTemplateInstantiationPattern();
    }
    if (const auto *value = dyn_cast<VarDecl>(&declaration)) {
        if (const VarDecl *pattern =
                value->getInstantiatedFromStaticDataMember())
            return pattern;
        return value->getTemplateInstantiationPattern();
    }
    return nullptr;
}

void collectSpecializationArgumentLists(
    const clang::Decl &declaration,
    llvm::SmallVectorImpl<const clang::TemplateArgumentList *> &result) {
    if (const clang::DeclContext *context = declaration.getDeclContext())
        collectSpecializationArgumentLists(clang::cast<clang::Decl>(*context),
                                           result);
    if (const auto *named = llvm::dyn_cast<clang::NamedDecl>(&declaration))
        if (const auto specialization = recoverSpecialization(*named))
            result.push_back(specialization->arguments);
}

const clang::TemplateDecl *recoverTemplate(const clang::Decl &declaration) {
    using namespace clang;
    if (const auto *value = dyn_cast<TemplateDecl>(&declaration))
        return value;
    if (const auto *value = dyn_cast<CXXRecordDecl>(&declaration))
        return value->getDescribedClassTemplate();
    if (const auto *value = dyn_cast<FunctionDecl>(&declaration))
        return value->getDescribedFunctionTemplate();
    if (const auto *value = dyn_cast<TypeAliasDecl>(&declaration))
        return value->getDescribedAliasTemplate();
    if (const auto *value = dyn_cast<VarDecl>(&declaration))
        return value->getDescribedVarTemplate();
    return nullptr;
}

void collectTemplateParameterLists(
    const clang::Decl &declaration,
    llvm::SmallVectorImpl<const clang::TemplateParameterList *> &result) {
    if (const clang::DeclContext *context = declaration.getDeclContext()) {
        const auto &contextDeclaration = clang::cast<clang::Decl>(*context);
        collectTemplateParameterLists(contextDeclaration, result);
        if (const clang::TemplateDecl *templ = recoverTemplate(declaration))
            if (const clang::TemplateParameterList *parameters =
                    templ->getTemplateParameters())
                result.push_back(parameters);
    }
}

bool isImplicitSpecialMethod(const clang::Decl &declaration) {
    using namespace clang;
    if (!declaration.isImplicit())
        return false;
    if (const auto *constructor = dyn_cast<CXXConstructorDecl>(&declaration))
        return constructor->isDefaultConstructor() ||
               constructor->isCopyConstructor() ||
               constructor->isMoveConstructor();
    if (isa<CXXDestructorDecl>(&declaration))
        return true;
    if (const auto *method = dyn_cast<CXXMethodDecl>(&declaration))
        return method->isCopyAssignmentOperator() ||
               method->isMoveAssignmentOperator();
    return false;
}

llvm::Expected<ScalarTerm>
callingConvention(const clang::FunctionDecl &function) {
    using clang::CallingConv;
    const auto *functionType = function.getType()->getAs<clang::FunctionType>();
    switch (functionType ? functionType->getCallConv() : CallingConv::CC_C) {
    case CallingConv::CC_C:
        return ScalarTerm::symbol("CC_C");
    case CallingConv::CC_X86RegCall:
        return ScalarTerm::symbol("CC_RegCall");
    case CallingConv::CC_Win64:
        return ScalarTerm::symbol("CC_MsAbi");
    default:
        return declarationError(function, "unsupported calling convention");
    }
}

bool defaultsToNoexcept(const clang::FunctionDecl &function) {
    if (llvm::isa<clang::CXXDestructorDecl>(function))
        return true;
    if (const auto *constructor =
            llvm::dyn_cast<clang::CXXConstructorDecl>(&function))
        return constructor->isDefaultConstructor() ||
               constructor->isCopyConstructor() ||
               constructor->isMoveConstructor();
    if (const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(&function))
        return method->isCopyAssignmentOperator() ||
               method->isMoveAssignmentOperator();
    return false;
}

llvm::Expected<ScalarTerm>
exceptionSpecification(State &state, const clang::FunctionDecl &function) {
    using clang::ExceptionSpecificationType;
    const auto *functionType =
        function.getFunctionType()->getAs<clang::FunctionProtoType>();
    int retries = 0;
    while (functionType && retries++ <= 1) {
        switch (functionType->getExceptionSpecType()) {
        case ExceptionSpecificationType::EST_None:
            if (function.isDependentContext() && defaultsToNoexcept(function))
                return ScalarTerm::symbol("exception_spec.Unknown");
            return ScalarTerm::symbol("exception_spec.MayThrow");
        case ExceptionSpecificationType::EST_NoThrow:
        case ExceptionSpecificationType::EST_BasicNoexcept:
        case ExceptionSpecificationType::EST_NoexceptTrue:
        case ExceptionSpecificationType::EST_DynamicNone:
            return ScalarTerm::symbol("exception_spec.NoThrow");
        case ExceptionSpecificationType::EST_NoexceptFalse:
        case ExceptionSpecificationType::EST_MSAny:
            return ScalarTerm::symbol("exception_spec.MayThrow");
        case ExceptionSpecificationType::EST_DependentNoexcept:
        case ExceptionSpecificationType::EST_Unevaluated:
            if (!state.sema)
                return declarationError(
                    function,
                    "a live Sema is required to resolve the exception "
                    "specification");
            functionType = state.sema->ResolveExceptionSpec(
                function.getLocation(), functionType);
            break;
        case ExceptionSpecificationType::EST_Uninstantiated:
            break;
        case ExceptionSpecificationType::EST_Unparsed:
        case ExceptionSpecificationType::EST_Dynamic:
            return ScalarTerm::symbol("exception_spec.Unknown");
        }
    }
    return ScalarTerm::symbol("exception_spec.Unknown");
}

ScalarTerm methodQualifier(const clang::CXXMethodDecl &method) {
    if (method.isConst())
        return ScalarTerm::symbol(method.isVolatile() ? "QCV" : "QC");
    return ScalarTerm::symbol(method.isVolatile() ? "QV" : "QM");
}

llvm::Expected<factory::OriginList>
generatedOrigins(State &state, const clang::Decl &declaration,
                 bool implicit = false) {
    auto owner = state.declarationOrigins(declaration);
    if (!owner)
        return owner.takeError();
    if (owner->empty())
        return factory::OriginList{};
    llvm::Expected<source::OriginId> generated =
        implicit ? state.sources.anchoredImplicitNode(
                       clang::CharSourceRange::getTokenRange(
                           declaration.getSourceRange()),
                       owner->front())
                 : state.sources.synthesizedNode(owner->front());
    if (!generated)
        return generated.takeError();
    return factory::OriginList{*generated};
}

llvm::Expected<std::vector<factory::DeclarationParameter>>
buildParameters(State &state, const clang::FunctionDecl &function,
                SemanticMode mode) {
    std::vector<factory::DeclarationParameter> result;
    result.reserve(function.getNumParams());
    const clang::IdentifierInfo *previous = nullptr;
    unsigned duplicateOffset = 0;
    unsigned index = 0;
    for (const clang::ParmVarDecl *parameter : function.parameters()) {
        if (!parameter)
            return declarationError(function, "null function parameter");
        if (parameter->getIdentifier() == previous)
            ++duplicateOffset;
        else
            duplicateOffset = 0;
        auto origins = state.declarationOrigins(*parameter);
        if (!origins)
            return origins.takeError();
        ScalarTerm name = [&]() {
            if (parameter->getIdentifier()) {
                std::string spelling = parameter->getNameAsString();
                if (duplicateOffset)
                    spelling += "..." + std::to_string(duplicateOffset);
                return ScalarTerm::localIdentifier(std::move(spelling));
            }
            return ScalarTerm::anonymousLocal(index);
        }();
        llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
            if (const clang::TypeSourceInfo *written =
                    parameter->getTypeSourceInfo()) {
                if (state.context.hasSameType(written->getType(),
                                              parameter->getType()))
                    return state.buildWrittenType(*written, mode);
                auto origin = state.sources.typeSourceInfoNode(written);
                if (!origin)
                    return origin.takeError();
                return state.buildType(parameter->getType(), mode, {*origin});
            }
            return state.buildType(parameter->getType(), mode, *origins);
        }();
        if (!type)
            return type.takeError();
        result.push_back({std::move(name), *type});
        previous = parameter->getIdentifier();
        ++index;
    }
    return result;
}

llvm::Expected<std::optional<NodeId>>
buildFunctionBody(State &state, const clang::FunctionDecl &function,
                  SemanticMode mode) {
    if (const clang::Stmt *statement = function.getBody()) {
        auto body = state.buildSingleStatement(statement, mode);
        if (!body)
            return body.takeError();
        auto origins = generatedOrigins(state, function);
        if (!origins)
            return origins.takeError();
        auto wrapper =
            factory::makeFunctionBody(state.unit->buildingArena(),
                                      Constructor::FunctionBodyImplementation,
                                      std::move(*origins), *body);
        if (!wrapper)
            return wrapper.takeError();
        return std::optional<NodeId>(*wrapper);
    }
    if (function.getBuiltinID() != clang::Builtin::ID::NotBuiltin) {
        auto origins = generatedOrigins(state, function);
        if (!origins)
            return origins.takeError();
        auto wrapper = factory::makeFunctionBody(
            state.unit->buildingArena(), Constructor::FunctionBodyBuiltin,
            std::move(*origins), std::nullopt,
            state.context.BuiltinInfo.getName(function.getBuiltinID()));
        if (!wrapper)
            return wrapper.takeError();
        return std::optional<NodeId>(*wrapper);
    }
    return std::optional<NodeId>{};
}

llvm::Expected<std::optional<NodeId>>
buildDefaultStatementBody(State &state, const clang::FunctionDecl &function,
                          SemanticMode mode) {
    if (const clang::Stmt *statement = function.getBody()) {
        auto body = state.buildSingleStatement(statement, mode);
        if (!body)
            return body.takeError();
        auto origins = generatedOrigins(state, function, function.isImplicit());
        if (!origins)
            return origins.takeError();
        const Constructor constructor =
            function.isImplicit() || function.isDefaulted()
                ? Constructor::DefaultStatementBodyCompilerProvided
                : Constructor::DefaultStatementBodyUserDefined;
        auto wrapper = factory::makeDefaultStatementBody(
            state.unit->buildingArena(), constructor, std::move(*origins),
            *body);
        if (!wrapper)
            return wrapper.takeError();
        return std::optional<NodeId>(*wrapper);
    }
    if (function.isDefaulted() || isImplicitSpecialMethod(function)) {
        auto origins = generatedOrigins(state, function, function.isImplicit());
        if (!origins)
            return origins.takeError();
        auto wrapper = factory::makeDefaultStatementBody(
            state.unit->buildingArena(),
            Constructor::DefaultStatementBodyDefaulted, std::move(*origins),
            std::nullopt);
        if (!wrapper)
            return wrapper.takeError();
        return std::optional<NodeId>(*wrapper);
    }
    return std::optional<NodeId>{};
}

llvm::Expected<NodeId> buildReturnType(State &state,
                                       const clang::FunctionDecl &function,
                                       SemanticMode mode,
                                       const factory::OriginList &origins) {
    if (const clang::TypeSourceInfo *written = function.getTypeSourceInfo())
        if (clang::FunctionTypeLoc functionLocation =
                written->getTypeLoc().getAs<clang::FunctionTypeLoc>()) {
            clang::TypeLoc returnLocation = functionLocation.getReturnLoc();
            if (!returnLocation.getType()->getContainedAutoType())
                return state.buildTypeLoc(returnLocation, mode);
            auto origin = state.sources.typeLocNode(returnLocation);
            if (!origin)
                return origin.takeError();
            return state.buildType(function.getReturnType(), mode, {*origin});
        }
    return state.buildType(function.getReturnType(), mode, origins);
}

llvm::Expected<NodeId> buildFunctionRecord(State &state,
                                           const clang::FunctionDecl &function,
                                           SemanticMode mode) {
    auto origins = state.declarationOrigins(function);
    if (!origins)
        return origins.takeError();
    auto resultType = buildReturnType(state, function, mode, *origins);
    if (!resultType)
        return resultType.takeError();
    auto parameters = buildParameters(state, function, mode);
    if (!parameters)
        return parameters.takeError();
    auto convention = callingConvention(function);
    if (!convention)
        return convention.takeError();
    auto exception = exceptionSpecification(state, function);
    if (!exception)
        return exception.takeError();
    auto body = buildFunctionBody(state, function, mode);
    if (!body)
        return body.takeError();
    return factory::makeFunctionRecord(
        state.unit->buildingArena(), std::move(*origins), *resultType,
        std::move(*parameters), std::move(*convention),
        ScalarTerm::symbol(function.isVariadic() ? "Ar_Variadic"
                                                 : "Ar_Definite"),
        std::move(*exception), *body);
}

llvm::Expected<NodeId> buildMethodRecord(State &state,
                                         const clang::CXXMethodDecl &method,
                                         SemanticMode mode) {
    auto origins = state.declarationOrigins(method);
    if (!origins)
        return origins.takeError();
    auto resultType = buildReturnType(state, method, mode, *origins);
    if (!resultType)
        return resultType.takeError();
    auto className = state.buildName(*method.getParent(), mode);
    if (!className)
        return className.takeError();
    auto parameters = buildParameters(state, method, mode);
    if (!parameters)
        return parameters.takeError();
    auto convention = callingConvention(method);
    if (!convention)
        return convention.takeError();
    auto exception = exceptionSpecification(state, method);
    if (!exception)
        return exception.takeError();
    auto body = buildDefaultStatementBody(state, method, mode);
    if (!body)
        return body.takeError();
    return factory::makeMethodRecord(
        state.unit->buildingArena(), std::move(*origins), *resultType,
        *className, methodQualifier(method), std::move(*parameters),
        std::move(*convention),
        ScalarTerm::symbol(method.isVariadic() ? "Ar_Variadic" : "Ar_Definite"),
        std::move(*exception), *body);
}

llvm::Expected<NodeId>
buildStaticMethodAsFunction(State &state, const clang::CXXMethodDecl &method,
                            SemanticMode mode) {
    auto origins = state.declarationOrigins(method);
    if (!origins)
        return origins.takeError();
    if (!origins->empty()) {
        auto transformed =
            state.transformedDeclarationOrigin(method, origins->front());
        if (!transformed)
            return transformed.takeError();
        origins->push_back(*transformed);
    }
    auto resultType = buildReturnType(state, method, mode, *origins);
    if (!resultType)
        return resultType.takeError();
    auto parameters = buildParameters(state, method, mode);
    if (!parameters)
        return parameters.takeError();
    auto convention = callingConvention(method);
    if (!convention)
        return convention.takeError();
    auto exception = exceptionSpecification(state, method);
    if (!exception)
        return exception.takeError();
    std::optional<NodeId> functionBody;
    if (const clang::Stmt *statement = method.getBody()) {
        auto body = state.buildSingleStatement(statement, mode);
        if (!body)
            return body.takeError();
        auto wrapperOrigins = generatedOrigins(state, method);
        if (!wrapperOrigins)
            return wrapperOrigins.takeError();
        auto wrapper =
            factory::makeFunctionBody(state.unit->buildingArena(),
                                      Constructor::FunctionBodyImplementation,
                                      std::move(*wrapperOrigins), *body);
        if (!wrapper)
            return wrapper.takeError();
        functionBody = *wrapper;
    }
    return factory::makeFunctionRecord(
        state.unit->buildingArena(), std::move(*origins), *resultType,
        std::move(*parameters), std::move(*convention),
        ScalarTerm::symbol(method.isVariadic() ? "Ar_Variadic" : "Ar_Definite"),
        std::move(*exception), functionBody);
}

llvm::Expected<NodeId>
buildVariable(State &state, const clang::VarDecl &variable, SemanticMode mode) {
    auto origins = state.declarationOrigins(variable);
    if (!origins)
        return origins.takeError();
    llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
        if (const clang::TypeSourceInfo *written =
                variable.getTypeSourceInfo()) {
            if (!written->getType()->getContainedAutoType() &&
                state.context.hasSameType(written->getType(),
                                          variable.getType()))
                return state.buildWrittenType(*written, mode);
            auto origin = state.sources.typeSourceInfoNode(written);
            if (!origin)
                return origin.takeError();
            return state.buildType(variable.getType(), mode, {*origin});
        }
        return state.buildType(variable.getType(), mode, *origins);
    }();
    if (!type)
        return type.takeError();
    Constructor constructor = Constructor::GlobalInitNone;
    std::optional<NodeId> expression;
    if (variable.hasExternalStorage()) {
        if (variable.getInit())
            return declarationError(variable,
                                    "external variable has an initializer");
        constructor = Constructor::GlobalInitExtern;
    } else if (llvm::isa<clang::FunctionDecl>(variable.getDeclContext())) {
        constructor = Constructor::GlobalInitDelayed;
    } else if (const clang::Expr *initializer = variable.getInit()) {
        auto built = state.buildExpression(*initializer, mode);
        if (!built)
            return built.takeError();
        constructor = Constructor::GlobalInitExpression;
        expression = *built;
    } else if (variable.getTemplateSpecializationKind() ==
               clang::TemplateSpecializationKind::TSK_ImplicitInstantiation) {
        constructor = Constructor::GlobalInitImplicit;
    }
    auto initOrigins = generatedOrigins(state, variable, variable.isImplicit());
    if (!initOrigins)
        return initOrigins.takeError();
    auto initializer =
        factory::makeGlobalInitializer(state.unit->buildingArena(), constructor,
                                       std::move(*initOrigins), expression);
    if (!initializer)
        return initializer.takeError();
    return factory::makeVariableObjectValue(
        state.unit->buildingArena(), std::move(*origins), *type, *initializer);
}

bool isBRiCkCharacterType(const clang::BuiltinType &type) {
    using Kind = clang::BuiltinType::Kind;
    switch (type.getKind()) {
    case Kind::Char_S:
    case Kind::Char_U:
    case Kind::WChar_S:
    case Kind::WChar_U:
    case Kind::Char16:
    case Kind::Char8:
    case Kind::Char32:
        return true;
    default:
        return false;
    }
}

std::string integerText(const llvm::APSInt &value) {
    llvm::SmallString<32> result;
    value.toString(result, 10);
    return std::string(result);
}

llvm::Expected<NodeId>
buildEnumConstant(State &state, const clang::EnumConstantDecl &constant,
                  SemanticMode mode) {
    const clang::EnumDecl *enumeration =
        llvm::dyn_cast<clang::EnumDecl>(constant.getDeclContext());
    if (!enumeration)
        return declarationError(constant, "constant has no enum parent");
    clang::QualType underlying = enumeration->getIntegerType();
    const auto *builtin = underlying->getAs<clang::BuiltinType>();
    if (!builtin || underlying->isDependentType())
        return declarationError(constant,
                                "unsupported enum constant underlying type");
    auto origins = state.declarationOrigins(constant);
    if (!origins)
        return origins.takeError();
    llvm::Expected<NodeId> underlyingType =
        enumeration->getIntegerTypeSourceInfo()
            ? state.buildWrittenType(*enumeration->getIntegerTypeSourceInfo(),
                                     mode)
            : state.buildType(underlying, mode, *origins);
    if (!underlyingType)
        return underlyingType.takeError();
    auto globalEnumName = state.buildName(*enumeration, mode);
    if (!globalEnumName)
        return globalEnumName.takeError();
    auto globalEnumType = factory::makeEnumType(state.unit->buildingArena(),
                                                *origins, *globalEnumName);
    if (!globalEnumType)
        return globalEnumType.takeError();
    auto castEnumName = state.buildName(*enumeration, mode);
    if (!castEnumName)
        return castEnumName.takeError();
    auto castEnumType = factory::makeEnumType(state.unit->buildingArena(),
                                              *origins, *castEnumName);
    if (!castEnumType)
        return castEnumType.takeError();
    auto helperOrigins =
        generatedOrigins(state, constant, constant.isImplicit());
    if (!helperOrigins)
        return helperOrigins.takeError();
    llvm::Expected<NodeId> literal = [&]() -> llvm::Expected<NodeId> {
        const llvm::APSInt value = constant.getInitVal();
        if (isBRiCkCharacterType(*builtin)) {
            const unsigned bits = state.context.getTypeSize(builtin);
            const std::uint64_t mask =
                bits >= 64 ? ~std::uint64_t{0} : (std::uint64_t{1} << bits) - 1;
            return factory::makeCharacterExpression(
                state.unit->buildingArena(), *helperOrigins,
                static_cast<std::uint64_t>(value.getExtValue()) & mask,
                *underlyingType);
        }
        return factory::makeIntegerExpression(
            state.unit->buildingArena(), *helperOrigins, integerText(value),
            *underlyingType);
    }();
    if (!literal)
        return literal.takeError();
    auto cast = factory::makeIntegralCast(state.unit->buildingArena(),
                                          *helperOrigins, *castEnumType);
    if (!cast)
        return cast.takeError();
    auto castExpression = factory::makeCastExpression(
        state.unit->buildingArena(), *helperOrigins, *cast, *literal);
    if (!castExpression)
        return castExpression.takeError();
    return factory::makeConstantGlobalDeclaration(
        state.unit->buildingArena(), std::move(*origins), *globalEnumType,
        std::optional<NodeId>(*castExpression));
}

llvm::Expected<NodeId>
buildEnum(State &state, const clang::EnumDecl &enumeration, SemanticMode mode) {
    auto origins = state.declarationOrigins(enumeration);
    if (!origins)
        return origins.takeError();
    llvm::Expected<NodeId> type =
        enumeration.getIntegerTypeSourceInfo()
            ? state.buildWrittenType(*enumeration.getIntegerTypeSourceInfo(),
                                     mode)
            : state.buildType(enumeration.getIntegerType(), mode, *origins);
    if (!type)
        return type.takeError();
    std::vector<std::string> constants;
    constants.reserve(std::distance(enumeration.enumerator_begin(),
                                    enumeration.enumerator_end()));
    for (const clang::EnumConstantDecl *constant : enumeration.enumerators()) {
        if (!constant)
            return declarationError(enumeration, "null enumerator");
        constants.push_back(constant->getNameAsString());
    }
    return factory::makeEnumGlobalDeclaration(state.unit->buildingArena(),
                                              std::move(*origins), *type,
                                              std::move(constants));
}

llvm::Expected<NodeId> buildTypedef(State &state,
                                    const clang::TypedefNameDecl &declaration,
                                    SemanticMode mode) {
    auto origins = state.declarationOrigins(declaration);
    if (!origins)
        return origins.takeError();
    llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
        if (const clang::TypeSourceInfo *written =
                declaration.getTypeSourceInfo()) {
            if (state.context.hasSameType(written->getType(),
                                          declaration.getUnderlyingType()))
                return state.buildWrittenType(*written, mode);
            auto origin = state.sources.typeSourceInfoNode(written);
            if (!origin)
                return origin.takeError();
            return state.buildType(declaration.getUnderlyingType(), mode,
                                   {*origin});
        }
        return state.buildType(declaration.getUnderlyingType(), mode, *origins);
    }();
    if (!type)
        return type.takeError();
    return factory::makeGlobalTypedef(state.unit->buildingArena(),
                                      std::move(*origins), *type);
}

llvm::Expected<factory::OriginList>
initializerOrigins(State &state, const clang::CXXConstructorDecl &constructor,
                   const clang::CXXCtorInitializer &initializer) {
    auto owner = state.declarationOrigins(constructor);
    if (!owner)
        return owner.takeError();
    if (initializer.isWritten()) {
        auto origin = state.sources.explicitNode(initializer.getSourceRange());
        if (!origin)
            return origin.takeError();
        return factory::OriginList{*origin};
    }
    if (owner->empty())
        return factory::OriginList{};
    auto origin = state.sources.anchoredImplicitNode(
        clang::CharSourceRange::getTokenRange(initializer.getSourceRange()),
        owner->front());
    if (!origin)
        return origin.takeError();
    return factory::OriginList{*origin};
}

llvm::Expected<NodeId> dependentClassName(State &state, clang::QualType type,
                                          SemanticMode mode,
                                          factory::OriginList origins) {
    if (const clang::CXXRecordDecl *record = type->getAsCXXRecordDecl()) {
        auto name = state.buildName(*record, mode);
        if (!name)
            return name.takeError();
        return factory::cloneWithOrigins(state.unit->buildingArena(), *name,
                                         origins);
    }
    auto builtType = state.buildType(type, mode, origins);
    if (!builtType)
        return builtType.takeError();
    auto node = state.unit->buildingArena().get(*builtType);
    if (!node)
        return node.takeError();
    if ((*node)->constructor == Constructor::TypeNamed &&
        (*node)->arguments.size() == 1)
        if (const auto *name =
                std::get_if<NodeRef>(&(*node)->arguments[0].payload))
            return factory::cloneWithOrigins(state.unit->buildingArena(),
                                             name->value, std::move(origins));
    return factory::makeDependentName(state.unit->buildingArena(),
                                      std::move(origins), *builtType);
}

llvm::Expected<NodeId> printedClassName(State &state, clang::QualType type,
                                        SemanticMode mode,
                                        factory::OriginList origins) {
    if (const clang::CXXRecordDecl *record = type->getAsCXXRecordDecl()) {
        auto name = state.buildName(*record, mode);
        if (!name)
            return name.takeError();
        return factory::cloneWithOrigins(state.unit->buildingArena(), *name,
                                         origins);
    }
    return factory::makeUnsupportedName(
        state.unit->buildingArena(), std::move(origins),
        "printClassName: " + std::string(type->getTypeClassName()));
}

llvm::Expected<NodeId>
buildInitializerPath(State &state, const clang::CXXConstructorDecl &constructor,
                     const clang::CXXCtorInitializer &initializer,
                     SemanticMode mode, factory::OriginList origins) {
    if (initializer.isMemberInitializer()) {
        const clang::FieldDecl *field = initializer.getMember();
        if (!field)
            return declarationError(constructor,
                                    "member initializer has no field");
        auto name = state.buildFieldName(*field, mode, origins);
        if (!name)
            return name.takeError();
        return factory::makeInitializerPath(state.unit->buildingArena(),
                                            Constructor::InitializerFieldPath,
                                            std::move(origins), *name);
    }
    if (initializer.isBaseInitializer()) {
        const clang::Type *base = initializer.getBaseClass();
        if (!base)
            return declarationError(constructor,
                                    "base initializer has no base type");
        auto name =
            printedClassName(state, clang::QualType(base, 0), mode, origins);
        if (!name)
            return name.takeError();
        return factory::makeInitializerPath(state.unit->buildingArena(),
                                            Constructor::InitializerBasePath,
                                            std::move(origins), *name);
    }
    if (initializer.isIndirectMemberInitializer()) {
        const clang::IndirectFieldDecl *indirect =
            initializer.getIndirectMember();
        if (!indirect)
            return declarationError(
                constructor, "indirect initializer has no indirect field");
        std::vector<Value> qualifiers;
        std::optional<std::string> finalIdentifier;
        for (const clang::NamedDecl *part : indirect->chain()) {
            if (!part)
                return declarationError(constructor,
                                        "null indirect field chain part");
            if (part->getIdentifier()) {
                finalIdentifier = part->getNameAsString();
                break;
            }
            const auto *field = llvm::dyn_cast<clang::FieldDecl>(part);
            if (!field)
                return declarationError(constructor,
                                        "non-field indirect chain part");
            auto fieldName = state.buildFieldName(*field, mode, origins);
            if (!fieldName)
                return fieldName.takeError();
            auto className =
                printedClassName(state, field->getType(), mode, origins);
            if (!className)
                return className.takeError();
            qualifiers.push_back(Value::product(
                {Value::node(*fieldName), Value::node(*className)}));
        }
        if (!finalIdentifier)
            return declarationError(constructor,
                                    "indirect chain has no named field");
        auto finalName = factory::makeAtomicIdentifier(
            state.unit->buildingArena(), origins, *finalIdentifier);
        if (!finalName)
            return finalName.takeError();
        return factory::makeInitIndirectPath(state.unit->buildingArena(),
                                             std::move(origins),
                                             std::move(qualifiers), *finalName);
    }
    if (initializer.isDelegatingInitializer())
        return factory::makeInitializerPath(state.unit->buildingArena(),
                                            Constructor::InitializerThisPath,
                                            std::move(origins));
    return declarationError(constructor, "unknown constructor initializer");
}

llvm::Expected<NodeId> buildConstructorInitializer(
    State &state, const clang::CXXConstructorDecl &constructor,
    const clang::CXXCtorInitializer &initializer, SemanticMode mode) {
    const clang::Expr *expression = initializer.getInit();
    if (!expression)
        return declarationError(constructor, "initializer has no expression");
    auto origins = initializerOrigins(state, constructor, initializer);
    if (!origins)
        return origins.takeError();
    auto path =
        buildInitializerPath(state, constructor, initializer, mode, *origins);
    if (!path)
        return path.takeError();
    auto builtExpression = state.buildExpression(*expression, mode);
    if (!builtExpression)
        return builtExpression.takeError();
    if (mode == SemanticMode::Template) {
        clang::QualType target;
        if (const clang::FieldDecl *field = initializer.getAnyMember())
            target = field->getType();
        else if (const clang::Type *base = initializer.getBaseClass())
            target = clang::QualType(base, 0);
        if (target.isNull())
            return declarationError(
                constructor, "template initializer has no initializing type");
        auto generated = state.sources.synthesizedNode(
            origins->empty() ? std::optional<source::OriginId>{}
                             : origins->front());
        if (!generated)
            return generated.takeError();
        builtExpression = state.applyInitializingType(*builtExpression, target,
                                                      mode, *generated);
        if (!builtExpression)
            return builtExpression.takeError();
    }
    return factory::makeInitializerRecord(state.unit->buildingArena(),
                                          std::move(*origins), *path,
                                          *builtExpression);
}

llvm::Expected<NodeId>
buildConstructorRecord(State &state,
                       const clang::CXXConstructorDecl &constructor,
                       SemanticMode mode) {
    auto origins = state.declarationOrigins(constructor);
    if (!origins)
        return origins.takeError();
    auto className = state.buildName(*constructor.getParent(), mode);
    if (!className)
        return className.takeError();
    auto parameters = buildParameters(state, constructor, mode);
    if (!parameters)
        return parameters.takeError();
    auto convention = callingConvention(constructor);
    if (!convention)
        return convention.takeError();
    auto exception = exceptionSpecification(state, constructor);
    if (!exception)
        return exception.takeError();
    std::optional<NodeId> body;
    if (const clang::Stmt *statement = constructor.getBody()) {
        std::vector<NodeId> initializers;
        initializers.reserve(constructor.getNumCtorInitializers());
        for (const clang::CXXCtorInitializer *initializer :
             constructor.inits()) {
            if (!initializer)
                return declarationError(constructor,
                                        "null constructor initializer");
            auto value = buildConstructorInitializer(state, constructor,
                                                     *initializer, mode);
            if (!value)
                return value.takeError();
            initializers.push_back(*value);
        }
        auto builtStatement = state.buildSingleStatement(statement, mode);
        if (!builtStatement)
            return builtStatement.takeError();
        auto bodyOrigins =
            generatedOrigins(state, constructor, constructor.isImplicit());
        if (!bodyOrigins)
            return bodyOrigins.takeError();
        const Constructor bodyConstructor =
            constructor.isImplicit() || constructor.isDefaulted()
                ? Constructor::ConstructorBodyCompilerProvided
                : Constructor::ConstructorBodyUserDefined;
        auto wrapper = factory::makeConstructorBody(
            state.unit->buildingArena(), bodyConstructor,
            std::move(*bodyOrigins), std::move(initializers), *builtStatement);
        if (!wrapper)
            return wrapper.takeError();
        body = *wrapper;
    } else if (constructor.isDefaulted() ||
               isImplicitSpecialMethod(constructor)) {
        auto bodyOrigins =
            generatedOrigins(state, constructor, constructor.isImplicit());
        if (!bodyOrigins)
            return bodyOrigins.takeError();
        auto wrapper = factory::makeConstructorBody(
            state.unit->buildingArena(), Constructor::ConstructorBodyDefaulted,
            std::move(*bodyOrigins), {}, std::nullopt);
        if (!wrapper)
            return wrapper.takeError();
        body = *wrapper;
    }
    return factory::makeConstructorRecord(
        state.unit->buildingArena(), std::move(*origins), *className,
        std::move(*parameters), std::move(*convention),
        ScalarTerm::symbol(constructor.isVariadic() ? "Ar_Variadic"
                                                    : "Ar_Definite"),
        std::move(*exception), body);
}

llvm::Expected<NodeId>
buildDestructorRecord(State &state, const clang::CXXDestructorDecl &destructor,
                      SemanticMode mode) {
    auto origins = state.declarationOrigins(destructor);
    if (!origins)
        return origins.takeError();
    auto className = state.buildName(*destructor.getParent(), mode);
    if (!className)
        return className.takeError();
    auto convention = callingConvention(destructor);
    if (!convention)
        return convention.takeError();
    auto exception = exceptionSpecification(state, destructor);
    if (!exception)
        return exception.takeError();
    auto body = buildDefaultStatementBody(state, destructor, mode);
    if (!body)
        return body.takeError();
    return factory::makeDestructorRecord(
        state.unit->buildingArena(), std::move(*origins), *className,
        std::move(*convention), std::move(*exception), *body);
}

llvm::Expected<std::vector<NodeId>>
buildMembers(State &state, const clang::RecordDecl &record,
             const clang::ASTRecordLayout *layout, SemanticMode mode) {
    std::vector<NodeId> result;
    result.reserve(std::distance(record.field_begin(), record.field_end()));
    unsigned index = 0;
    for (const clang::FieldDecl *field : record.fields()) {
        if (!field)
            return declarationError(record, "null field");
        if (field->isBitField())
            return declarationError(*field, "bit fields are not supported");
        if (field->isInvalidDecl())
            return declarationError(*field, "invalid field");
        auto origins = state.declarationOrigins(*field);
        if (!origins)
            return origins.takeError();
        auto name = state.buildFieldName(*field, mode, *origins);
        if (!name)
            return name.takeError();
        llvm::Expected<NodeId> type =
            field->getTypeSourceInfo()
                ? state.buildWrittenType(*field->getTypeSourceInfo(), mode)
                : state.buildType(field->getType(), mode, *origins);
        if (!type)
            return type.takeError();
        std::optional<NodeId> initializer;
        if (const clang::Expr *expression = field->getInClassInitializer()) {
            auto value = state.buildExpression(*expression, mode);
            if (!value)
                return value.takeError();
            initializer = *value;
        }
        const std::uint64_t offset = layout ? layout->getFieldOffset(index) : 0;
        auto layoutOrigins =
            generatedOrigins(state, *field, field->isImplicit());
        if (!layoutOrigins)
            return layoutOrigins.takeError();
        auto layoutInfo = factory::makeLayoutInfo(state.unit->buildingArena(),
                                                  std::move(*layoutOrigins),
                                                  std::to_string(offset));
        if (!layoutInfo)
            return layoutInfo.takeError();
        auto member = factory::makeMemberRecord(
            state.unit->buildingArena(), std::move(*origins), *name, *type,
            field->isMutable(), initializer, *layoutInfo);
        if (!member)
            return member.takeError();
        result.push_back(*member);
        ++index;
    }
    return result;
}

llvm::Expected<NodeId>
recordDestructorName(State &state, const clang::RecordDecl &record,
                     SemanticMode mode, const factory::OriginList &origins) {
    const auto *cxx = llvm::dyn_cast<clang::CXXRecordDecl>(&record);
    if (!cxx)
        return declarationError(
            record, "C record definitions have no final destructor name");
    auto scope = state.buildName(*cxx, mode);
    if (!scope)
        return scope.takeError();
    auto generated = state.sources.synthesizedNode(
        origins.empty() ? std::optional<source::OriginId>{} : origins.front());
    if (!generated)
        return generated.takeError();
    factory::OriginList generatedOrigins{*generated};
    auto atom = factory::makeAtomicDestructor(state.unit->buildingArena(),
                                              generatedOrigins);
    if (!atom)
        return atom.takeError();
    return factory::makeScopedName(state.unit->buildingArena(),
                                   std::move(generatedOrigins), *scope, *atom);
}

llvm::Expected<NodeId>
buildRecord(State &state, const clang::RecordDecl &record, SemanticMode mode) {
    auto origins = state.declarationOrigins(record);
    if (!origins)
        return origins.takeError();
    if (!record.isCompleteDefinition())
        return factory::makeGlobalDeclaration(state.unit->buildingArena(),
                                              Constructor::GlobalType,
                                              std::move(*origins));
    if (!llvm::isa<clang::CXXRecordDecl>(record))
        return declarationError(
            record, "C record definitions are outside the C++17 IR scope");
    if (const auto *cxx = llvm::dyn_cast<clang::CXXRecordDecl>(&record))
        for (const clang::CXXBaseSpecifier &base : cxx->bases())
            if (base.isVirtual())
                return factory::makeUnsupportedGlobalDeclaration(
                    state.unit->buildingArena(), std::move(*origins),
                    "virtual base classes are not supported");
    for (const clang::FieldDecl *field : record.fields()) {
        if (field->isBitField())
            return factory::makeUnsupportedGlobalDeclaration(
                state.unit->buildingArena(), std::move(*origins),
                "bitfields are not supported");
        if (field->isInvalidDecl())
            return factory::makeUnsupportedGlobalDeclaration(
                state.unit->buildingArena(), std::move(*origins),
                "invalid field");
    }
    const clang::ASTRecordLayout *layout =
        record.isDependentContext()
            ? nullptr
            : &state.context.getASTRecordLayout(&record);
    auto members = buildMembers(state, record, layout, mode);
    if (!members)
        return members.takeError();
    auto destructorName = recordDestructorName(state, record, mode, *origins);
    if (!destructorName)
        return destructorName.takeError();
    const std::string size =
        std::to_string(layout ? layout->getSize().getQuantity() : 0);
    const std::string alignment =
        std::to_string(layout ? layout->getAlignment().getQuantity() : 0);
    const auto *cxx = llvm::dyn_cast<clang::CXXRecordDecl>(&record);
    std::optional<NodeId> deleteName;
    bool trivial = true;
    if (cxx) {
        trivial = cxx->hasTrivialDestructor();
        if (const clang::CXXDestructorDecl *destructor = cxx->getDestructor())
            if (const clang::FunctionDecl *operatorDelete =
                    destructor->getOperatorDelete()) {
                auto name = state.buildName(*operatorDelete, mode);
                if (!name)
                    return name.takeError();
                deleteName = *name;
            }
    }
    if (record.isUnion()) {
        auto value = factory::makeUnionRecord(
            state.unit->buildingArena(), *origins, std::move(*members),
            *destructorName, trivial, deleteName, size, alignment);
        if (!value)
            return value.takeError();
        return factory::makeGlobalDeclaration(state.unit->buildingArena(),
                                              Constructor::GlobalUnion,
                                              std::move(*origins), *value);
    }
    std::vector<factory::StructBaseValue> bases;
    std::vector<factory::StructVirtualValue> virtuals;
    std::vector<factory::StructOverrideValue> overrides;
    ScalarTerm layoutKind = ScalarTerm::symbol("POD");
    if (cxx) {
        for (const clang::CXXBaseSpecifier &base : cxx->bases()) {
            if (base.isVirtual())
                return declarationError(
                    record, "virtual base classes are not supported");
            llvm::Expected<source::OriginId> baseOrigin =
                base.getTypeSourceInfo()
                    ? state.sources.typeSourceInfoNode(base.getTypeSourceInfo())
                    : state.sources.explicitNode(base.getSourceRange());
            if (!baseOrigin)
                return baseOrigin.takeError();
            factory::OriginList baseOrigins{*baseOrigin};
            auto name =
                dependentClassName(state, base.getType(), mode, baseOrigins);
            if (!name)
                return name.takeError();
            std::uint64_t offset = 0;
            if (layout)
                if (const clang::CXXRecordDecl *baseRecord =
                        base.getType()->getAsCXXRecordDecl())
                    offset =
                        layout->getBaseClassOffset(baseRecord).getQuantity();
            auto layoutOrigin =
                state.sources.synthesizedNode(baseOrigins.front());
            if (!layoutOrigin)
                return layoutOrigin.takeError();
            auto layoutInfo = factory::makeLayoutInfo(
                state.unit->buildingArena(), {*layoutOrigin},
                std::to_string(offset));
            if (!layoutInfo)
                return layoutInfo.takeError();
            bases.push_back({*name, *layoutInfo});
        }
        for (const clang::CXXMethodDecl *method : cxx->methods()) {
            if (!method)
                return declarationError(record, "null record method");
            if (method->isVirtual()) {
                auto name = state.buildName(*method, mode);
                if (!name)
                    return name.takeError();
                std::optional<NodeId> implementation;
                if (!method->isPureVirtual()) {
                    auto duplicate = state.buildName(*method, mode);
                    if (!duplicate)
                        return duplicate.takeError();
                    implementation = *duplicate;
                }
                virtuals.push_back({*name, implementation});
            }
            if (method->isVirtual() && !method->isPureVirtual())
                for (const clang::CXXMethodDecl *overridden :
                     method->overridden_methods()) {
                    auto oldName = state.buildName(*overridden, mode);
                    if (!oldName)
                        return oldName.takeError();
                    auto newName = state.buildName(*method, mode);
                    if (!newName)
                        return newName.takeError();
                    overrides.push_back({*oldName, *newName});
                }
        }
        layoutKind = ScalarTerm::symbol(
            cxx->isPOD()
                ? "POD"
                : (cxx->isStandardLayout() ? "Standard" : "Unspecified"));
    }
    auto value = factory::makeStructRecord(
        state.unit->buildingArena(), *origins, std::move(bases),
        std::move(*members), std::move(virtuals), std::move(overrides),
        *destructorName, trivial, deleteName, std::move(layoutKind), size,
        alignment);
    if (!value)
        return value.takeError();
    return factory::makeGlobalDeclaration(state.unit->buildingArena(),
                                          Constructor::GlobalStruct,
                                          std::move(*origins), *value);
}

} // namespace

llvm::Expected<factory::TemplateParameters>
State::buildDeclarationTemplateParameters(const clang::Decl &declaration,
                                          SemanticMode mode) {
    llvm::SmallVector<const clang::TemplateParameterList *, 4> lists;
    collectTemplateParameterLists(declaration, lists);
    std::vector<TemplateParameterEntry> entries;
    for (const clang::TemplateParameterList *list : lists) {
        for (const clang::NamedDecl *parameter : list->asArray()) {
            if (!parameter)
                return declarationError(declaration, "null template parameter");
            auto value = buildTemplateParameter(*parameter, mode);
            if (!value)
                return value.takeError();
            auto defaultArgument =
                buildTemplateParameterDefault(*parameter, *value, mode);
            if (!defaultArgument)
                return defaultArgument.takeError();
            entries.push_back({*value, std::move(*defaultArgument)});
        }
    }
    return factory::packTemplateParameters(unit->buildingArena(), entries);
}

llvm::Expected<NodeId>
State::buildObjectValue(const clang::NamedDecl &declaration,
                        SemanticMode mode) {
    using namespace clang;
    if (const auto *variable = dyn_cast<VarDecl>(&declaration))
        return buildVariable(*this, *variable, mode);
    if (const auto *constructor = dyn_cast<CXXConstructorDecl>(&declaration)) {
        auto value = buildConstructorRecord(*this, *constructor, mode);
        if (!value)
            return value.takeError();
        auto origins = declarationOrigins(*constructor);
        if (!origins)
            return origins.takeError();
        return factory::makeObjectValue(unit->buildingArena(),
                                        Constructor::ObjectConstructor,
                                        std::move(*origins), *value);
    }
    if (const auto *destructor = dyn_cast<CXXDestructorDecl>(&declaration)) {
        auto value = buildDestructorRecord(*this, *destructor, mode);
        if (!value)
            return value.takeError();
        auto origins = declarationOrigins(*destructor);
        if (!origins)
            return origins.takeError();
        return factory::makeObjectValue(unit->buildingArena(),
                                        Constructor::ObjectDestructor,
                                        std::move(*origins), *value);
    }
    if (const auto *method = dyn_cast<CXXMethodDecl>(&declaration)) {
        if (method->isStatic()) {
            auto value = buildStaticMethodAsFunction(*this, *method, mode);
            if (!value)
                return value.takeError();
            auto origins = declarationOrigins(*method);
            if (!origins)
                return origins.takeError();
            if (!origins->empty()) {
                auto transformed =
                    transformedDeclarationOrigin(*method, origins->front());
                if (!transformed)
                    return transformed.takeError();
                origins->push_back(*transformed);
            }
            return factory::makeObjectValue(unit->buildingArena(),
                                            Constructor::ObjectFunction,
                                            std::move(*origins), *value);
        }
        auto value = buildMethodRecord(*this, *method, mode);
        if (!value)
            return value.takeError();
        auto origins = declarationOrigins(*method);
        if (!origins)
            return origins.takeError();
        return factory::makeObjectValue(unit->buildingArena(),
                                        Constructor::ObjectMethod,
                                        std::move(*origins), *value);
    }
    if (const auto *function = dyn_cast<FunctionDecl>(&declaration)) {
        auto value = buildFunctionRecord(*this, *function, mode);
        if (!value)
            return value.takeError();
        auto origins = declarationOrigins(*function);
        if (!origins)
            return origins.takeError();
        return factory::makeObjectValue(unit->buildingArena(),
                                        Constructor::ObjectFunction,
                                        std::move(*origins), *value);
    }
    return declarationError(declaration,
                            "declaration is not an object-value family");
}

llvm::Expected<NodeId>
State::buildGlobalDeclaration(const clang::NamedDecl &declaration,
                              SemanticMode mode) {
    using namespace clang;
    if (const auto *constant = dyn_cast<EnumConstantDecl>(&declaration))
        return buildEnumConstant(*this, *constant, mode);
    if (const auto *enumeration = dyn_cast<EnumDecl>(&declaration))
        return buildEnum(*this, *enumeration, mode);
    if (const auto *alias = dyn_cast<TypedefNameDecl>(&declaration))
        return buildTypedef(*this, *alias, mode);
    if (const auto *record = dyn_cast<RecordDecl>(&declaration))
        return buildRecord(*this, *record, mode);
    return declarationError(declaration,
                            "declaration is not a global-declaration family");
}

llvm::Error State::addImplicitMemberRoots(const clang::NamedDecl &declaration,
                                          SemanticMode mode) {
    const auto *record = llvm::dyn_cast<clang::CXXRecordDecl>(&declaration);
    if (!record || !record->isCompleteDefinition())
        return declarationError(declaration,
                                "implicit member owner is not a complete C++ "
                                "record");
    if (record->isDependentContext())
        return llvm::Error::success();

    auto findConstructor = [&](auto predicate) {
        for (const clang::CXXConstructorDecl *constructor : record->ctors())
            if (constructor && constructor->isImplicit() &&
                predicate(*constructor))
                return constructor;
        return static_cast<const clang::CXXConstructorDecl *>(nullptr);
    };
    auto findMethod = [&](auto predicate) {
        for (const clang::CXXMethodDecl *method : record->methods())
            if (method && method->isImplicit() && predicate(*method))
                return method;
        return static_cast<const clang::CXXMethodDecl *>(nullptr);
    };
    const auto *defaultConstructor =
        findConstructor([](const clang::CXXConstructorDecl &value) {
            return value.isDefaultConstructor();
        });
    const auto *copyConstructor =
        findConstructor([](const clang::CXXConstructorDecl &value) {
            return value.isCopyConstructor();
        });
    const auto *moveConstructor =
        findConstructor([](const clang::CXXConstructorDecl &value) {
            return value.isMoveConstructor();
        });
    const auto *copyAssignment =
        findMethod([](const clang::CXXMethodDecl &value) {
            return value.isCopyAssignmentOperator();
        });
    const auto *moveAssignment =
        findMethod([](const clang::CXXMethodDecl &value) {
            return value.isMoveAssignmentOperator();
        });

    auto origins = [&]() { return generatedOrigins(*this, *record, true); };
    auto className = [&]() { return buildName(*record, mode); };
    auto namedClassType = [&]() -> llvm::Expected<NodeId> {
        auto name = className();
        if (!name)
            return name.takeError();
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        return factory::makeNamedType(unit->buildingArena(),
                                      std::move(*generated), *name);
    };
    auto argumentType = [&](bool rvalue,
                            bool isConst) -> llvm::Expected<NodeId> {
        auto type = namedClassType();
        if (!type)
            return type.takeError();
        if (isConst) {
            auto generated = origins();
            if (!generated)
                return generated.takeError();
            type = factory::makeQualifiedType(unit->buildingArena(),
                                              std::move(*generated),
                                              ScalarTerm::symbol("QC"), *type);
            if (!type)
                return type.takeError();
        }
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        return factory::makeUnaryType(unit->buildingArena(),
                                      rvalue ? Constructor::TypeRvalueReference
                                             : Constructor::TypeLvalueReference,
                                      std::move(*generated), *type);
    };
    auto defaultConstructorBody = [&]() -> llvm::Expected<NodeId> {
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        return factory::makeConstructorBody(
            unit->buildingArena(), Constructor::ConstructorBodyDefaulted,
            std::move(*generated), {}, std::nullopt);
    };
    auto defaultStatementBody = [&]() -> llvm::Expected<NodeId> {
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        return factory::makeDefaultStatementBody(
            unit->buildingArena(), Constructor::DefaultStatementBodyDefaulted,
            std::move(*generated), std::nullopt);
    };
    auto addRoot = [&](NodeId name, NodeId value) {
        return unit->addRoot({RootKind::Symbol, name, value, false, false});
    };

    auto addConstructor = [&](std::optional<bool> move,
                              bool isConst) -> llvm::Error {
        std::vector<factory::DeclarationParameter> parameters;
        std::vector<NodeId> keyTypes;
        if (move) {
            auto valueType = argumentType(*move, isConst);
            if (!valueType)
                return valueType.takeError();
            parameters.push_back({ScalarTerm::anonymousLocal(0), *valueType});
            auto keyType = argumentType(*move, isConst);
            if (!keyType)
                return keyType.takeError();
            keyTypes.push_back(*keyType);
        }
        auto valueClass = className();
        if (!valueClass)
            return valueClass.takeError();
        auto body = defaultConstructorBody();
        if (!body)
            return body.takeError();
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        auto constructor = factory::makeConstructorRecord(
            unit->buildingArena(), std::move(*generated), *valueClass,
            std::move(parameters), ScalarTerm::symbol("CC_C"),
            ScalarTerm::symbol("Ar_Definite"),
            ScalarTerm::symbol("exception_spec.Unknown"), *body);
        if (!constructor)
            return constructor.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto object = factory::makeObjectValue(
            unit->buildingArena(), Constructor::ObjectConstructor,
            std::move(*generated), *constructor);
        if (!object)
            return object.takeError();
        auto keyClass = className();
        if (!keyClass)
            return keyClass.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto atom = factory::makeAtomicConstructor(
            unit->buildingArena(), *generated, std::move(keyTypes));
        if (!atom)
            return atom.takeError();
        auto key = factory::makeScopedName(
            unit->buildingArena(), std::move(*generated), *keyClass, *atom);
        if (!key)
            return key.takeError();
        return addRoot(*key, *object);
    };

    auto addAssignment = [&](bool move, bool isConst) -> llvm::Error {
        auto parameterType = argumentType(move, isConst);
        if (!parameterType)
            return parameterType.takeError();
        llvm::Expected<NodeId> returnType = [&]() -> llvm::Expected<NodeId> {
            if (!move)
                return argumentType(false, isConst);
            auto named = namedClassType();
            if (!named)
                return named.takeError();
            auto generated = origins();
            if (!generated)
                return generated.takeError();
            return factory::makeUnaryType(unit->buildingArena(),
                                          Constructor::TypeLvalueReference,
                                          std::move(*generated), *named);
        }();
        if (!returnType)
            return returnType.takeError();
        auto valueClass = className();
        if (!valueClass)
            return valueClass.takeError();
        auto body = defaultStatementBody();
        if (!body)
            return body.takeError();
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        auto method = factory::makeMethodRecord(
            unit->buildingArena(), std::move(*generated), *returnType,
            *valueClass, ScalarTerm::symbol("QM"),
            {{ScalarTerm::anonymousLocal(0), *parameterType}},
            ScalarTerm::symbol("CC_C"), ScalarTerm::symbol("Ar_Definite"),
            ScalarTerm::symbol("exception_spec.Unknown"), *body);
        if (!method)
            return method.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto object = factory::makeObjectValue(unit->buildingArena(),
                                               Constructor::ObjectMethod,
                                               std::move(*generated), *method);
        if (!object)
            return object.takeError();
        auto keyType = argumentType(move, isConst);
        if (!keyType)
            return keyType.takeError();
        auto keyClass = className();
        if (!keyClass)
            return keyClass.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto atom = factory::makeAtomicOperator(
            unit->buildingArena(), *generated,
            ScalarTerm::symbol("function_qualifiers.N"),
            ScalarTerm::symbol("OOEqual"), {*keyType});
        if (!atom)
            return atom.takeError();
        auto key = factory::makeScopedName(
            unit->buildingArena(), std::move(*generated), *keyClass, *atom);
        if (!key)
            return key.takeError();
        return addRoot(*key, *object);
    };

    auto addDestructor = [&]() -> llvm::Error {
        auto valueClass = className();
        if (!valueClass)
            return valueClass.takeError();
        auto body = defaultStatementBody();
        if (!body)
            return body.takeError();
        auto generated = origins();
        if (!generated)
            return generated.takeError();
        auto destructor = factory::makeDestructorRecord(
            unit->buildingArena(), std::move(*generated), *valueClass,
            ScalarTerm::symbol("CC_C"),
            ScalarTerm::symbol("exception_spec.Unknown"), *body);
        if (!destructor)
            return destructor.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto object = factory::makeObjectValue(
            unit->buildingArena(), Constructor::ObjectDestructor,
            std::move(*generated), *destructor);
        if (!object)
            return object.takeError();
        auto keyClass = className();
        if (!keyClass)
            return keyClass.takeError();
        generated = origins();
        if (!generated)
            return generated.takeError();
        auto atom =
            factory::makeAtomicDestructor(unit->buildingArena(), *generated);
        if (!atom)
            return atom.takeError();
        auto key = factory::makeScopedName(
            unit->buildingArena(), std::move(*generated), *keyClass, *atom);
        if (!key)
            return key.takeError();
        return addRoot(*key, *object);
    };

    if (!defaultConstructor && record->needsImplicitDefaultConstructor())
        if (auto failure = addConstructor(std::nullopt, false))
            return failure;
    if (!copyConstructor && record->needsImplicitCopyConstructor() &&
        !record->hasUserDeclaredCopyAssignment())
        if (auto failure = addConstructor(
                false, record->hasCopyConstructorWithConstParam()))
            return failure;
    if (!moveConstructor && record->needsImplicitMoveConstructor())
        if (auto failure = addConstructor(true, false))
            return failure;
    if (!copyAssignment && record->needsImplicitCopyAssignment() &&
        !record->hasUserDeclaredCopyConstructor())
        if (auto failure =
                addAssignment(false, record->hasCopyAssignmentWithConstParam()))
            return failure;
    if (!moveAssignment && record->needsImplicitMoveAssignment())
        if (auto failure = addAssignment(true, false))
            return failure;
    if (!record->getDestructor() && record->needsImplicitDestructor())
        if (auto failure = addDestructor())
            return failure;
    return llvm::Error::success();
}

llvm::Error State::addNamespaceAlias(const clang::Decl &owner,
                                     const clang::NamedDecl *from,
                                     const clang::NamedDecl &to,
                                     SemanticMode mode) {
    std::optional<NodeId> builtFrom;
    if (from) {
        auto value = buildName(*from, mode);
        if (!value)
            return value.takeError();
        builtFrom = *value;
    }
    auto builtTo = buildName(to, mode);
    if (!builtTo)
        return builtTo.takeError();
    auto origins = declarationOrigins(owner);
    if (!origins)
        return origins.takeError();
    return unit->addNonRoot(
        NamespaceAliasEvent{builtFrom, *builtTo, std::move(*origins)});
}

llvm::Error State::addStaticAssertion(const clang::Decl &declaration,
                                      SemanticMode mode) {
    const auto *assertion =
        llvm::dyn_cast<clang::StaticAssertDecl>(&declaration);
    if (!assertion)
        return declarationError(declaration, "event is not a static assertion");
    if (assertion->getDeclContext()->isDependentContext())
        return declarationError(declaration,
                                "dependent static assertion event");
    const clang::Expr *condition = assertion->getAssertExpr();
    if (!condition)
        return declarationError(declaration,
                                "static assertion has no expression");
    auto builtCondition = buildExpression(*condition, mode);
    if (!builtCondition)
        return builtCondition.takeError();
    std::optional<ScalarTerm> message;
#if CLANG_VERSION_MAJOR <= 16
    const clang::StringLiteral *literal = assertion->getMessage();
#else
    const clang::StringLiteral *literal =
        llvm::dyn_cast_or_null<clang::StringLiteral>(assertion->getMessage());
#endif
    if (literal)
        message = ScalarTerm::string(literal->getString().str());
    auto origins = declarationOrigins(declaration);
    if (!origins)
        return origins.takeError();
    return unit->addNonRoot(StaticAssertEvent{
        std::move(message), *builtCondition, std::move(*origins)});
}

llvm::Error State::addTemplateAlias(const clang::NamedDecl &declaration,
                                    SemanticMode mode, bool includeComment) {
    const auto *alias = llvm::dyn_cast<clang::TypedefNameDecl>(&declaration);
    if (!alias)
        return declarationError(declaration, "event is not a template alias");
    auto name = buildName(*alias, mode);
    if (!name)
        return name.takeError();
    auto parameters = buildDeclarationTemplateParameters(*alias, mode);
    if (!parameters)
        return parameters.takeError();
    auto origins = declarationOrigins(*alias);
    if (!origins)
        return origins.takeError();
    llvm::Expected<NodeId> type =
        alias->getTypeSourceInfo()
            ? buildWrittenType(*alias->getTypeSourceInfo(), mode)
            : buildType(alias->getUnderlyingType(), mode, *origins);
    if (!type)
        return type.takeError();
    auto value = factory::makeTemplateAlias(unit->buildingArena(), *origins,
                                            std::move(*parameters), *type);
    if (!value)
        return value.takeError();
    std::optional<std::string> comment;
    if (includeComment)
        comment = diagnosticName(*alias);
    return unit->addNonRoot(TemplateAliasEvent{
        *name, *value, std::move(*origins), std::move(comment)});
}

llvm::Error State::addTemplateInstance(const clang::NamedDecl &declaration,
                                       SemanticMode mode,
                                       bool includeComments) {
    const clang::NamedDecl *pattern = recoverPattern(declaration);
    if (!pattern)
        return declarationError(declaration,
                                "event has no specialization pattern");
    auto key = buildName(declaration, mode);
    if (!key)
        return key.takeError();
    // mparser.Dinstantiation first runs untempN on the concrete key and skips
    // entries that still contain template-only types or expressions.
    if (!isUntemplatedNode(unit->buildingArena(), *key))
        return llvm::Error::success();
    auto target = buildPatternName(*pattern, mode);
    if (!target)
        return target.takeError();
    auto origins = declarationOrigins(declaration);
    if (!origins)
        return origins.takeError();
    llvm::SmallVector<const clang::TemplateArgumentList *, 4> lists;
    collectSpecializationArgumentLists(declaration, lists);
    std::vector<NodeId> arguments;
    for (const clang::TemplateArgumentList *list : lists) {
        arguments.reserve(arguments.size() + list->size());
        for (const clang::TemplateArgument &argument : list->asArray()) {
            auto value = buildTemplateArgument(argument, mode, *origins);
            if (!value)
                return value.takeError();
            arguments.push_back(*value);
        }
    }
    auto value = factory::makeTemplatePreInstantiation(
        unit->buildingArena(), *origins, *target, std::move(arguments));
    if (!value)
        return value.takeError();
    std::optional<std::string> keyComment;
    std::optional<std::string> targetComment;
    if (includeComments) {
        keyComment = diagnosticName(declaration);
        targetComment = diagnosticName(*pattern);
    }
    return unit->addNonRoot(
        TemplateInstanceEvent{*key, *value, std::move(*origins),
                              std::move(keyComment), std::move(targetComment)});
}

} // namespace builder
} // namespace ir
