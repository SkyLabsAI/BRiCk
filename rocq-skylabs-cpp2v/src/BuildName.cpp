/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/NestedNameSpecifier.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/AST/Type.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallString.h>

namespace ir {
namespace builder {
namespace {

template <typename Function> auto makeScopeExit(Function &&function) {
#if CLANG_VERSION_MAJOR >= 22
    return llvm::scope_exit(std::forward<Function>(function));
#else
    return llvm::make_scope_exit(std::forward<Function>(function));
#endif
}

bool isEmptyOrGlobalQualifier(NestedNameSpecifierArg qualifier) {
#if CLANG_VERSION_MAJOR >= 22
    return !qualifier ||
           qualifier.getKind() == clang::NestedNameSpecifier::Kind::Null ||
           qualifier.getKind() == clang::NestedNameSpecifier::Kind::Global;
#else
    return !qualifier ||
           qualifier->getKind() == clang::NestedNameSpecifier::Global;
#endif
}

const clang::NamedDecl *qualifierNamespace(NestedNameSpecifierArg qualifier) {
#if CLANG_VERSION_MAJOR >= 22
    if (!qualifier ||
        qualifier.getKind() != clang::NestedNameSpecifier::Kind::Namespace)
        return nullptr;
    return qualifier.getAsNamespaceAndPrefix().Namespace;
#else
    if (!qualifier)
        return nullptr;
    if (const clang::NamespaceDecl *space = qualifier->getAsNamespace())
        return space;
    return qualifier->getAsNamespaceAlias();
#endif
}

const clang::Type *qualifierType(NestedNameSpecifierArg qualifier) {
#if CLANG_VERSION_MAJOR >= 22
    return qualifier &&
                   qualifier.getKind() == clang::NestedNameSpecifier::Kind::Type
               ? qualifier.getAsType()
               : nullptr;
#else
    return qualifier ? qualifier->getAsType() : nullptr;
#endif
}

clang::TypeLoc
qualifierTypeLocation(clang::NestedNameSpecifierLoc qualifierLocation) {
    if (!qualifierLocation)
        return {};
#if CLANG_VERSION_MAJOR >= 22
    return qualifierLocation.getAsTypeLoc();
#else
    return qualifierLocation.getTypeLoc();
#endif
}

const char *templateArgumentKindName(clang::TemplateArgument::ArgKind kind) {
    using K = clang::TemplateArgument;
    switch (kind) {
    case K::Null:
        return "Null";
    case K::Type:
        return "Type";
    case K::Declaration:
        return "Declaration";
    case K::NullPtr:
        return "NullPtr";
    case K::Integral:
        return "Integral";
    // Legacy PrintName predates this Clang argument kind and reaches its
    // default branch.
    case K::StructuralValue:
        return "<unknown>";
    case K::Template:
        return "Template";
    case K::TemplateExpansion:
        return "TemplateExpansion";
    case K::Expression:
        return "Expression";
    case K::Pack:
        return "Pack";
    }
    return "<unknown>";
}

std::string templateParameterName(const clang::NamedDecl &declaration) {
    if (const auto *identifier = declaration.getIdentifier())
        return identifier->getName().str();
    if (const auto *parameter =
            llvm::dyn_cast<clang::TemplateTypeParmDecl>(&declaration))
        return "__type_" + std::to_string(parameter->getDepth()) + "_" +
               std::to_string(parameter->getIndex());
    if (const auto *parameter =
            llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(&declaration))
        return "__value_" + std::to_string(parameter->getDepth()) + "_" +
               std::to_string(parameter->getIndex());
    if (const auto *parameter =
            llvm::dyn_cast<clang::TemplateTemplateParmDecl>(&declaration))
        return "__template_" + std::to_string(parameter->getDepth()) + "_" +
               std::to_string(parameter->getIndex());
    return "__template_param";
}

llvm::Expected<NodeId> identifier(State &state, factory::OriginList origins,
                                  const clang::NamedDecl &declaration) {
    const clang::IdentifierInfo *identifier = declaration.getIdentifier();
    if (!identifier)
        return migrationIncomplete(declaration, "unnamed identifier");

    std::string name = identifier->getName().str();
    if (const clang::DeclContext *function =
            declaration.getParentFunctionOrMethod()) {
        const auto *functionDecl =
            llvm::dyn_cast<clang::FunctionDecl>(function);
        const clang::Stmt *body =
            functionDecl ? functionDecl->getBody() : nullptr;
        if (body) {
            class DuplicateFinder
                : public clang::RecursiveASTVisitor<DuplicateFinder> {
            public:
                explicit DuplicateFinder(const clang::NamedDecl &wanted)
                    : target(wanted), targetName(wanted.getNameAsString()) {}
                bool shouldVisitLambdaBody() const { return false; }
                bool VisitDecl(clang::Decl *candidate) {
                    if (candidate == &target) {
                        result = static_cast<int>(count);
                        return false;
                    }
                    if (const auto *named =
                            llvm::dyn_cast<clang::NamedDecl>(candidate))
                        if (named->getNameAsString() == targetName)
                            ++count;
                    return true;
                }
                const clang::NamedDecl &target;
                const std::string targetName;
                unsigned count = 0;
                int result = -1;
            } finder(declaration);
            finder.TraverseStmt(const_cast<clang::Stmt *>(body));
            if (finder.result < 0)
                return factory::makeAtomicUnsupported(
                    state.unit->buildingArena(), std::move(origins),
                    "failed to find identifier");
            if (finder.result > 0)
                name += "'" + std::to_string(finder.result - 1);
        }
    }
    return factory::makeAtomicIdentifier(state.unit->buildingArena(),
                                         std::move(origins), std::move(name));
}

const char *functionQualifiers(const clang::FunctionDecl &declaration) {
    static const char *const table[2][2][3] = {
        {{"function_qualifiers.N", "function_qualifiers.Nl",
          "function_qualifiers.Nr"},
         {"function_qualifiers.Nv", "function_qualifiers.Nvl",
          "function_qualifiers.Nvr"}},
        {{"function_qualifiers.Nc", "function_qualifiers.Ncl",
          "function_qualifiers.Ncr"},
         {"function_qualifiers.Ncv", "function_qualifiers.Ncvl",
          "function_qualifiers.Ncvr"}}};
    if (const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(&declaration))
        return table[method->isConst()][method->isVolatile()]
                    [static_cast<unsigned>(method->getRefQualifier())];
    return "function_qualifiers.N";
}

llvm::Expected<ScalarTerm>
operatorTerm(clang::OverloadedOperatorKind operation) {
    switch (operation) {
#define OVERLOADED_OPERATOR(Name, Spelling, Token, Unary, Binary, MemberOnly)  \
    case clang::OO_##Name:                                                     \
        return ScalarTerm::symbol("OO" #Name);
#include <clang/Basic/OperatorKinds.def>
#undef OVERLOADED_OPERATOR
#undef OVERLOADED_OPERATOR_MULTI
    default:
        return llvm::createStringError(
            std::errc::not_supported, "migration incomplete: unknown operator");
    }
}

llvm::Expected<NodeId> unresolvedAtomicName(State &state,
                                            clang::DeclarationName name,
                                            SemanticMode mode,
                                            factory::OriginList origins) {
    using Kind = clang::DeclarationName::NameKind;
    switch (name.getNameKind()) {
    case Kind::Identifier:
        if (const clang::IdentifierInfo *identifier =
                name.getAsIdentifierInfo())
            return factory::makeAtomicIdentifier(state.unit->buildingArena(),
                                                 std::move(origins),
                                                 identifier->getName().str());
        break;
    case Kind::CXXConstructorName:
        return factory::makeAtomicConstructor(state.unit->buildingArena(),
                                              std::move(origins), {});
    case Kind::CXXDestructorName:
        return factory::makeAtomicDestructor(state.unit->buildingArena(),
                                             std::move(origins));
    case Kind::CXXOperatorName: {
        const clang::OverloadedOperatorKind operationKind =
            name.getCXXOverloadedOperator();
        if (operationKind == clang::OO_New ||
            operationKind == clang::OO_Array_New ||
            operationKind == clang::OO_Delete ||
            operationKind == clang::OO_Array_Delete)
            return factory::makeAtomicAllocationOperator(
                state.unit->buildingArena(), std::move(origins),
                ScalarTerm::symbol("function_qualifiers.N"),
                operationKind == clang::OO_Delete ||
                    operationKind == clang::OO_Array_Delete,
                operationKind == clang::OO_Array_New ||
                    operationKind == clang::OO_Array_Delete,
                {});
        auto operation = operatorTerm(operationKind);
        if (!operation)
            return operation.takeError();
        return factory::makeAtomicOperator(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol("function_qualifiers.N"), std::move(*operation),
            {});
    }
    case Kind::CXXConversionFunctionName: {
        auto inherited =
            state.inheritedTypeOrigins(name.getCXXNameType(), origins);
        if (!inherited)
            return inherited.takeError();
        auto type =
            state.buildType(name.getCXXNameType(), mode, std::move(*inherited));
        if (!type)
            return type.takeError();
        return factory::makeAtomicConversion(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol("function_qualifiers.N"), *type);
    }
    case Kind::CXXLiteralOperatorName:
        if (const clang::IdentifierInfo *identifier =
                name.getCXXLiteralIdentifier())
            return factory::makeAtomicLiteralOperator(
                state.unit->buildingArena(), std::move(origins),
                identifier->getName().str(), {});
        break;
    default:
        break;
    }
    return factory::makeAtomicUnsupported(
        state.unit->buildingArena(), std::move(origins),
        "printDeclarationName(" +
            std::to_string(static_cast<unsigned>(name.getNameKind())) + ")");
}

llvm::Expected<std::vector<NodeId>>
functionParameterTypes(State &state, const clang::FunctionDecl &declaration,
                       SemanticMode mode, const factory::OriginList &origins) {
    std::vector<NodeId> result;
    result.reserve(declaration.getNumParams());
    for (const clang::ParmVarDecl *parameter : declaration.parameters()) {
        // ParmVarDecl::getType is Clang's adjusted argument type (arrays and
        // functions have decayed and top-level cv is absent).  Pair it with
        // the written TypeSourceInfo so the already-final normalized IR keeps
        // the source ranges of the original spelling.
        auto built = state.buildNormalizedArgumentType(
            parameter->getType(), parameter->getTypeSourceInfo(), mode,
            origins);
        if (!built)
            return built.takeError();
        result.push_back(*built);
    }
    return result;
}

llvm::Expected<NodeId>
functionAtomicName(State &state, const clang::FunctionDecl &declaration,
                   SemanticMode mode, factory::OriginList origins) {
    if (declaration.isExternC())
        return identifier(state, std::move(origins), declaration);
    auto parameters = functionParameterTypes(state, declaration, mode, origins);
    if (!parameters)
        return parameters.takeError();
    const clang::DeclarationName name = declaration.getDeclName();
    switch (name.getNameKind()) {
    case clang::DeclarationName::Identifier:
        if (!name.getAsIdentifierInfo())
            return migrationIncomplete(declaration, "function identifier");
        return factory::makeAtomicFunction(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol(functionQualifiers(declaration)),
            name.getAsIdentifierInfo()->getName().str(),
            std::move(*parameters));
    case clang::DeclarationName::CXXConstructorName:
        return factory::makeAtomicConstructor(state.unit->buildingArena(),
                                              std::move(origins),
                                              std::move(*parameters));
    case clang::DeclarationName::CXXDestructorName:
        return factory::makeAtomicDestructor(state.unit->buildingArena(),
                                             std::move(origins));
    case clang::DeclarationName::CXXOperatorName: {
        const clang::OverloadedOperatorKind operationKind =
            name.getCXXOverloadedOperator();
        if (operationKind == clang::OO_New ||
            operationKind == clang::OO_Array_New ||
            operationKind == clang::OO_Delete ||
            operationKind == clang::OO_Array_Delete)
            return factory::makeAtomicAllocationOperator(
                state.unit->buildingArena(), std::move(origins),
                ScalarTerm::symbol(functionQualifiers(declaration)),
                operationKind == clang::OO_Delete ||
                    operationKind == clang::OO_Array_Delete,
                operationKind == clang::OO_Array_New ||
                    operationKind == clang::OO_Array_Delete,
                std::move(*parameters));
        auto operation = operatorTerm(operationKind);
        if (!operation)
            return operation.takeError();
        return factory::makeAtomicOperator(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol(functionQualifiers(declaration)),
            std::move(*operation), std::move(*parameters));
    }
    case clang::DeclarationName::CXXConversionFunctionName: {
        llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
            if (const auto *conversion =
                    llvm::dyn_cast<clang::CXXConversionDecl>(&declaration))
                if (const clang::TypeSourceInfo *written =
                        conversion->getNameInfo().getNamedTypeInfo()) {
                    auto origin = state.sources.typeSourceInfoNode(written);
                    if (!origin)
                        return origin.takeError();
                    return state.buildType(name.getCXXNameType(), mode,
                                           {*origin});
                }
            auto inherited =
                state.inheritedTypeOrigins(name.getCXXNameType(), origins);
            if (!inherited)
                return inherited.takeError();
            return state.buildType(name.getCXXNameType(), mode,
                                   std::move(*inherited));
        }();
        if (!type)
            return type.takeError();
        return factory::makeAtomicConversion(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol(functionQualifiers(declaration)), *type);
    }
    case clang::DeclarationName::CXXLiteralOperatorName:
        if (const clang::IdentifierInfo *identifier =
                name.getCXXLiteralIdentifier())
            return factory::makeAtomicLiteralOperator(
                state.unit->buildingArena(), std::move(origins),
                identifier->getName().str(), std::move(*parameters));
        return migrationIncomplete(declaration, "literal operator identifier");
    default:
        return migrationIncomplete(declaration, "function name kind");
    }
}

llvm::Expected<NodeId> atomicName(State &state,
                                  const clang::DeclContext &context,
                                  const clang::NamedDecl &declaration,
                                  SemanticMode mode,
                                  factory::OriginList origins) {
    const source::OriginId direct = origins.front();
    auto appendDerived = [&](const clang::Decl &sourceDecl)
        -> llvm::Expected<factory::OriginList> {
        auto transformed =
            state.transformedDeclarationOrigin(sourceDecl, direct);
        if (!transformed)
            return transformed.takeError();
        source::appendOriginStable(origins, *transformed);
        return origins;
    };

    if (const auto *function =
            llvm::dyn_cast<clang::FunctionDecl>(&declaration)) {
        using K = clang::Decl::Kind;
        switch (declaration.getKind()) {
        case K::Function:
        case K::CXXMethod:
        case K::CXXConstructor:
        case K::CXXDestructor:
        case K::CXXConversion:
            return functionAtomicName(state, *function, mode,
                                      std::move(origins));
        default:
            return factory::makeAtomicUnsupported(
                state.unit->buildingArena(), std::move(origins),
                "atomic name of kind " +
                    std::string(declaration.getDeclKindName()));
        }
    }
    if (const auto *space =
            llvm::dyn_cast<clang::NamespaceDecl>(&declaration)) {
        if (space->isAnonymousNamespace())
            return factory::makeAtomicAnonymousNamespace(
                state.unit->buildingArena(), std::move(origins));
        return identifier(state, std::move(origins), declaration);
    }
    if (const auto *tag = llvm::dyn_cast<clang::TagDecl>(&declaration)) {
        if (isSemanticallyNamed(*tag))
            return identifier(state, std::move(origins), declaration);
        if (const auto *typeName = tag->getTypedefNameForAnonDecl()) {
            auto derived = appendDerived(*typeName);
            if (!derived)
                return derived.takeError();
            return factory::makeAtomicIdentifier(state.unit->buildingArena(),
                                                 std::move(*derived),
                                                 typeName->getName().str());
        }
        for (const clang::Decl *candidate = tag->getNextDeclInContext();
             candidate; candidate = candidate->getNextDeclInContext()) {
            if (const auto *value =
                    llvm::dyn_cast<clang::ValueDecl>(candidate)) {
                const clang::TagDecl *candidateTag =
                    value->getType().getTypePtr()->getAsTagDecl();
                if (candidateTag == tag && value->getIdentifier()) {
                    auto derived = appendDerived(*value);
                    if (!derived)
                        return derived.takeError();
                    return factory::makeAtomicFirstDeclaration(
                        state.unit->buildingArena(), std::move(*derived),
                        value->getIdentifier()->getName().str());
                }
                break;
            }
            bool lexicalChild = true;
            for (const clang::DeclContext *lexical =
                     candidate->getLexicalDeclContext();
                 lexical; lexical = lexical->getParent())
                if (lexical->isTranslationUnit()) {
                    lexicalChild = false;
                    break;
                }
            if (!lexicalChild)
                break;
        }
        if (const auto *record = llvm::dyn_cast<clang::RecordDecl>(tag)) {
            if (context.isTranslationUnit())
                return factory::makeAtomicUnsupported(
                    state.unit->buildingArena(), std::move(origins), "record");
            for (const clang::FieldDecl *field : record->fields())
                if (field->getIdentifier()) {
                    auto derived = appendDerived(*field);
                    if (!derived)
                        return derived.takeError();
                    return factory::makeAtomicFirstChild(
                        state.unit->buildingArena(), std::move(*derived),
                        field->getIdentifier()->getName().str());
                }
        }
        if (const auto *enumeration = llvm::dyn_cast<clang::EnumDecl>(tag)) {
            for (const clang::EnumConstantDecl *constant :
                 enumeration->enumerators())
                if (constant->getIdentifier()) {
                    auto derived = appendDerived(*constant);
                    if (!derived)
                        return derived.takeError();
                    return factory::makeAtomicFirstChild(
                        state.unit->buildingArena(), std::move(*derived),
                        constant->getIdentifier()->getName().str());
                }
            if (context.isTranslationUnit())
                return factory::makeAtomicUnsupported(
                    state.unit->buildingArena(), std::move(origins), "enum");
        }
        auto index = anonymousIndex(context, declaration);
        if (!index)
            return index.takeError();
        return factory::makeAtomicAnonymousIndex(state.unit->buildingArena(),
                                                 std::move(origins), *index);
    }
    auto anonymous = [&]() -> llvm::Expected<NodeId> {
        if (declaration.getIdentifier())
            return identifier(state, std::move(origins), declaration);
        auto index = anonymousIndex(context, declaration);
        if (!index)
            return index.takeError();
        return factory::makeAtomicAnonymousIndex(state.unit->buildingArena(),
                                                 std::move(origins), *index);
    };
    auto namedOrUnsupported =
        [&](llvm::StringRef diagnostic) -> llvm::Expected<NodeId> {
        if (declaration.getIdentifier())
            return identifier(state, std::move(origins), declaration);
        return factory::makeAtomicUnsupported(
            state.unit->buildingArena(), std::move(origins), diagnostic.str());
    };
    using K = clang::Decl::Kind;
    switch (declaration.getKind()) {
    case K::TypeAlias:
    case K::Typedef:
    case K::Field:
    case K::ClassTemplate:
        return anonymous();
    case K::TypeAliasTemplate:
    case K::VarTemplate:
    case K::VarTemplateSpecialization:
    case K::VarTemplatePartialSpecialization:
        return namedOrUnsupported("anonymous template");
    case K::Var:
        return namedOrUnsupported("anonymous variable");
    case K::EnumConstant:
        return namedOrUnsupported("anonymous enum constant");
    case K::Binding:
        return namedOrUnsupported("anonymous binding");
    default:
        return factory::makeAtomicUnsupported(
            state.unit->buildingArena(), std::move(origins),
            "atomic name of kind " +
                std::string(declaration.getDeclKindName()));
    }
}

const clang::TemplateParameterList *
describedParameters(const clang::NamedDecl &declaration) {
    if (const auto *record = llvm::dyn_cast<clang::CXXRecordDecl>(&declaration))
        if (const auto *templ = record->getDescribedClassTemplate())
            return templ->getTemplateParameters();
    if (const auto *function =
            llvm::dyn_cast<clang::FunctionDecl>(&declaration))
        if (const auto *templ = function->getDescribedFunctionTemplate())
            return templ->getTemplateParameters();
    if (const auto *alias = llvm::dyn_cast<clang::TypeAliasDecl>(&declaration))
        if (const auto *templ = alias->getDescribedAliasTemplate())
            return templ->getTemplateParameters();
    if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(&declaration))
        if (const auto *templ = variable->getDescribedVarTemplate())
            return templ->getTemplateParameters();
    return nullptr;
}

const clang::TemplateTypeParmType *templateTypeParameter(clang::QualType type) {
    if (type.isNull())
        return nullptr;
    if (const auto *expansion = type->getAs<clang::PackExpansionType>())
        type = expansion->getPattern();
    return type->getAs<clang::TemplateTypeParmType>();
}

std::optional<std::string>
firstTemplateTypeParameterName(const clang::TemplateArgument &argument) {
    if (argument.getKind() == clang::TemplateArgument::Pack) {
        for (const clang::TemplateArgument &entry : argument.pack_elements())
            if (auto name = firstTemplateTypeParameterName(entry))
                return name;
        return std::nullopt;
    }
    if (argument.getKind() != clang::TemplateArgument::Type)
        return std::nullopt;
    clang::QualType type = argument.getAsType();
    if (const auto *parameter = templateTypeParameter(type))
        if (parameter->getDecl() && parameter->getDecl()->getIdentifier())
            return parameter->getDecl()->getName().str();
    if (const auto *specialization =
            llvm::dyn_cast<clang::TemplateSpecializationType>(type))
        for (const clang::TemplateArgument &entry :
             specialization->template_arguments())
            if (auto name = firstTemplateTypeParameterName(entry))
                return name;
    return std::nullopt;
}

void preferTemplateTypeParameterName(
    clang::QualType type, llvm::StringRef name,
    llvm::DenseMap<std::pair<unsigned, unsigned>, std::string> &result);

void preferTemplateTypeParameterName(
    const clang::TemplateArgument &argument, llvm::StringRef name,
    llvm::DenseMap<std::pair<unsigned, unsigned>, std::string> &result) {
    if (argument.getKind() == clang::TemplateArgument::Pack) {
        for (const clang::TemplateArgument &entry : argument.pack_elements())
            preferTemplateTypeParameterName(entry, name, result);
    } else if (argument.getKind() == clang::TemplateArgument::Type) {
        preferTemplateTypeParameterName(argument.getAsType(), name, result);
    }
}

void preferTemplateTypeParameterName(
    clang::QualType type, llvm::StringRef name,
    llvm::DenseMap<std::pair<unsigned, unsigned>, std::string> &result) {
    if (type.isNull())
        return;
    if (const auto *parameter = templateTypeParameter(type))
        result[{parameter->getDepth(), parameter->getIndex()}] = name.str();
    if (const auto *substitution =
            llvm::dyn_cast<clang::SubstTemplateTypeParmType>(type)) {
        preferTemplateTypeParameterName(substitution->getReplacementType(),
                                        name, result);
    } else if (const auto *specialization =
                   llvm::dyn_cast<clang::TemplateSpecializationType>(type)) {
        for (const clang::TemplateArgument &entry :
             specialization->template_arguments())
            preferTemplateTypeParameterName(entry, name, result);
    } else if (const auto *expansion =
                   llvm::dyn_cast<clang::PackExpansionType>(type)) {
        preferTemplateTypeParameterName(expansion->getPattern(), name, result);
    }
}

void registerTemplateParameters(State &state,
                                const clang::TemplateParameterList &parameters,
                                bool partialSpecialization) {
    const bool firstIsNonType =
        partialSpecialization && !parameters.asArray().empty() &&
        llvm::isa<clang::NonTypeTemplateParmDecl>(parameters.asArray().front());
    for (const clang::NamedDecl *parameter : parameters.asArray()) {
        unsigned depth = 0;
        unsigned index = 0;
        if (const auto *type =
                llvm::dyn_cast<clang::TemplateTypeParmDecl>(parameter)) {
            depth = type->getDepth();
            index = type->getIndex();
        } else if (const auto *value =
                       llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(
                           parameter)) {
            depth = value->getDepth();
            index = value->getIndex();
        } else if (const auto *templ =
                       llvm::dyn_cast<clang::TemplateTemplateParmDecl>(
                           parameter)) {
            depth = templ->getDepth();
            index = templ->getIndex();
        } else {
            continue;
        }
        const auto key = std::make_pair(depth, index);
        if (state.preferredTemplateTypeNames.count(key) ||
            state.preferredTemplateTypeErrors.count(key))
            continue;
        if (llvm::isa<clang::TemplateTypeParmDecl>(parameter)) {
            state.preferredTemplateTypeNames.insert(
                {key, templateParameterName(*parameter)});
        } else {
            const char *kind =
                llvm::isa<clang::NonTypeTemplateParmDecl>(parameter)
                    ? "non-type template parameter "
                    : "template-template parameter ";
            std::string diagnostic = kind + templateParameterName(*parameter);
            state.preferredTemplateTypeErrors.insert({key, diagnostic});
            if (firstIsNonType && parameter == parameters.asArray().front() &&
                !state.preferredTemplateTypeFallbackError)
                state.preferredTemplateTypeFallbackError =
                    std::move(diagnostic);
        }
    }
}

void registerTemplateParameterContext(State &state,
                                      const clang::NamedDecl &declaration) {
    for (const clang::Decl *current = &declaration; current;) {
        const clang::TemplateParameterList *parameters = nullptr;
        bool partialSpecialization = false;
        if (const auto *partial =
                llvm::dyn_cast<clang::ClassTemplatePartialSpecializationDecl>(
                    current)) {
            parameters = partial->getTemplateParameters();
            partialSpecialization = true;
        } else if (const auto *named =
                       llvm::dyn_cast<clang::NamedDecl>(current)) {
            parameters = describedParameters(*named);
        }
        if (parameters)
            registerTemplateParameters(state, *parameters,
                                       partialSpecialization);
        const clang::DeclContext *context = current->getDeclContext();
        current = context ? clang::Decl::castFromDeclContext(context) : nullptr;
    }
}

llvm::Expected<NodeId> buildNameImplRaw(State &state,
                                        const clang::NamedDecl &declaration,
                                        SemanticMode mode,
                                        bool decorateTemplate,
                                        bool detectSpecialization);

llvm::Expected<NodeId> buildNameImpl(State &state,
                                     const clang::NamedDecl &declaration,
                                     SemanticMode mode, bool decorateTemplate,
                                     bool detectSpecialization = true) {
    auto value = buildNameImplRaw(state, declaration, mode, decorateTemplate,
                                  detectSpecialization);
    if (!value)
        return value.takeError();
    // Undecorated bases are transient components of a final Ninst and are not
    // the canonical semantic occurrence keyed by the declaration.
    if (decorateTemplate)
        if (auto failure = state.attachNameShare(*value, declaration, mode))
            return std::move(failure);
    return *value;
}

llvm::Expected<NodeId> buildNameImplRaw(State &state,
                                        const clang::NamedDecl &declaration,
                                        SemanticMode mode,
                                        bool decorateTemplate,
                                        bool detectSpecialization) {
    if (const auto *templ = llvm::dyn_cast<clang::TemplateDecl>(&declaration))
        if (const clang::NamedDecl *templated = templ->getTemplatedDecl())
            return buildNameImpl(state, *templated, mode, decorateTemplate,
                                 detectSpecialization);

    auto buildSpecialization =
        [&](const clang::NamedDecl &base,
            llvm::ArrayRef<clang::TemplateArgument> arguments,
            const clang::ASTTemplateArgumentListInfo *writtenArguments,
            bool useSpecializationAtomic) -> llvm::Expected<NodeId> {
        auto origins = state.declarationOrigins(declaration);
        if (!origins)
            return origins.takeError();
        const llvm::ArrayRef<clang::TemplateArgumentLoc> written =
            writtenArguments ? writtenArguments->arguments()
                             : llvm::ArrayRef<clang::TemplateArgumentLoc>{};
        auto previousNames = state.preferredTemplateTypeNames;
        auto restoreNames = makeScopeExit([&] {
            state.preferredTemplateTypeNames = std::move(previousNames);
        });
        (void)restoreNames;
        if (state.buildingPatternName) {
            std::optional<std::string> firstName;
            for (const clang::TemplateArgumentLoc &argument : written)
                if ((firstName = firstTemplateTypeParameterName(
                         argument.getArgument())))
                    break;
            if (firstName)
                for (const clang::TemplateArgument &argument : arguments)
                    preferTemplateTypeParameterName(
                        argument, *firstName, state.preferredTemplateTypeNames);
        }
        // Function specializations retain the primary template's scope/base
        // identity, but their atomic overload key uses the specialization's
        // substituted parameter types. Other specialization bases are the
        // undecorated primary declaration name.
        auto baseName =
            buildNameImpl(state, useSpecializationAtomic ? declaration : base,
                          mode, false, false);
        if (!baseName)
            return baseName.takeError();
        std::vector<NodeId> built;
        built.reserve(arguments.size());
        for (std::size_t index = 0; index < arguments.size(); ++index) {
            llvm::Expected<NodeId> value = [&]() -> llvm::Expected<NodeId> {
                if (index < written.size()) {
                    // Legacy specialization names serialize Clang's canonical
                    // TemplateArgumentList. The written argument owns the
                    // final canonical value's provenance.
                    auto direct = state.sources.explicitNode(
                        written[index].getSourceRange());
                    if (!direct)
                        return direct.takeError();
                    return state.buildTemplateArgument(arguments[index], mode,
                                                       {*direct});
                }
                auto synthesized =
                    state.sources.synthesizedNode(origins->front(), *origins);
                if (!synthesized)
                    return synthesized.takeError();
                return state.buildTemplateArgument(arguments[index], mode,
                                                   {*synthesized});
            }();
            if (!value)
                return value.takeError();
            built.push_back(*value);
        }
        return factory::makeInstantiatedName(state.unit->buildingArena(),
                                             std::move(*origins), *baseName,
                                             std::move(built));
    };
    if (detectSpecialization)
        if (const auto *specialization =
                llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(
                    &declaration))
            return buildSpecialization(
                *specialization->getSpecializedTemplate()->getTemplatedDecl(),
                specialization->getTemplateArgs().asArray(),
                specialization->getTemplateArgsAsWritten(), false);
    if (detectSpecialization)
        if (const auto *specialization =
                llvm::dyn_cast<clang::VarTemplateSpecializationDecl>(
                    &declaration))
            return buildSpecialization(
                *specialization->getSpecializedTemplate()->getTemplatedDecl(),
                specialization->getTemplateArgs().asArray(),
                specialization->getTemplateArgsAsWritten(), false);
    if (detectSpecialization)
        if (const auto *function =
                llvm::dyn_cast<clang::FunctionDecl>(&declaration))
            if (const clang::TemplateArgumentList *arguments =
                    function->getTemplateSpecializationArgs())
                if (const clang::FunctionTemplateDecl *primary =
                        function->getPrimaryTemplate())
                    return buildSpecialization(
                        *primary->getTemplatedDecl(), arguments->asArray(),
                        function->getTemplateSpecializationArgsAsWritten(),
                        true);

    auto contextResult = nonIgnorableContext(declaration);
    if (!contextResult)
        return contextResult.takeError();
    const clang::DeclContext &declarationContext = **contextResult;
    auto origins = state.declarationOrigins(declaration);
    if (!origins)
        return origins.takeError();
    factory::OriginList nameOrigins = *origins;
    auto atomic = atomicName(state, declarationContext, declaration, mode,
                             std::move(*origins));
    if (!atomic)
        return atomic.takeError();

    llvm::Expected<NodeId> base = [&]() -> llvm::Expected<NodeId> {
        if (declarationContext.isTranslationUnit())
            return factory::makeGlobalName(state.unit->buildingArena(),
                                           nameOrigins, *atomic);
        const auto *parentDecl = llvm::dyn_cast<clang::NamedDecl>(
            llvm::dyn_cast<clang::Decl>(&declarationContext));
        if (!parentDecl)
            return migrationIncomplete(declaration, "non-declaration scope");
        auto scope = buildNameImpl(state, *parentDecl, mode, true);
        if (!scope)
            return scope.takeError();
        return factory::makeScopedName(state.unit->buildingArena(), nameOrigins,
                                       *scope, *atomic);
    }();
    if (!base)
        return base.takeError();
    if (!decorateTemplate)
        return *base;
    const clang::TemplateParameterList *parameters =
        describedParameters(declaration);
    if (!parameters)
        return *base;
    std::vector<NodeId> arguments;
    for (const clang::NamedDecl *parameter : parameters->asArray()) {
        auto argument = [&]() -> llvm::Expected<NodeId> {
            auto writtenOrigins = state.declarationOrigins(*parameter);
            if (!writtenOrigins)
                return writtenOrigins.takeError();
            auto synthesized = state.sources.synthesizedNode(
                writtenOrigins->front(), *writtenOrigins);
            if (!synthesized)
                return synthesized.takeError();
            factory::OriginList parameterOrigins{*synthesized};
            if (parameter->isParameterPack())
                return factory::makeUnsupportedTemplateArgument(
                    state.unit->buildingArena(), std::move(parameterOrigins),
                    "template parameter pack");
            if (llvm::isa<clang::TemplateTypeParmDecl>(parameter)) {
                auto type = factory::makeTypeParameter(
                    state.unit->buildingArena(), parameterOrigins,
                    templateParameterName(*parameter));
                if (!type)
                    return type.takeError();
                return factory::makeTypeTemplateArgument(
                    state.unit->buildingArena(), parameterOrigins, *type);
            }
            if (llvm::isa<clang::NonTypeTemplateParmDecl>(parameter)) {
                auto expression = factory::makeParameterExpression(
                    state.unit->buildingArena(), parameterOrigins,
                    templateParameterName(*parameter));
                if (!expression)
                    return expression.takeError();
                return factory::makeValueTemplateArgument(
                    state.unit->buildingArena(), parameterOrigins, *expression);
            }
            if (llvm::isa<clang::TemplateTemplateParmDecl>(parameter))
                return factory::makeTemplateParameterArgument(
                    state.unit->buildingArena(), parameterOrigins,
                    templateParameterName(*parameter));
            return factory::makeUnsupportedTemplateArgument(
                state.unit->buildingArena(), std::move(parameterOrigins),
                "template parameter kind");
        }();
        if (!argument)
            return argument.takeError();
        arguments.push_back(*argument);
    }
    return factory::makeInstantiatedName(state.unit->buildingArena(),
                                         std::move(nameOrigins), *base,
                                         std::move(arguments));
}

} // namespace

const char *
templateArgumentKindNameForTest(clang::TemplateArgument::ArgKind kind) {
    return templateArgumentKindName(kind);
}

llvm::Expected<NodeId> State::buildName(const clang::NamedDecl &declaration,
                                        SemanticMode mode) {
    if (llvm::isa<clang::ClassTemplatePartialSpecializationDecl>(declaration))
        return buildPatternName(declaration, mode);
    return buildNameImpl(*this, declaration, mode, true);
}

llvm::Expected<NodeId>
State::buildUndecoratedName(const clang::NamedDecl &declaration,
                            SemanticMode mode) {
    return buildNameImpl(*this, declaration, mode, false);
}

llvm::Expected<NodeId>
State::buildPatternName(const clang::NamedDecl &declaration,
                        SemanticMode mode) {
    auto previousNames = preferredTemplateTypeNames;
    auto previousErrors = preferredTemplateTypeErrors;
    auto previousFallback = preferredTemplateTypeFallbackError;
    const bool previousPattern = buildingPatternName;
    auto restore = makeScopeExit([&] {
        preferredTemplateTypeNames = std::move(previousNames);
        preferredTemplateTypeErrors = std::move(previousErrors);
        preferredTemplateTypeFallbackError = std::move(previousFallback);
        buildingPatternName = previousPattern;
    });
    (void)restore;
    buildingPatternName = true;
    registerTemplateParameterContext(*this, declaration);
    return buildNameImpl(*this, declaration, mode, true);
}

llvm::Expected<NodeId> State::buildFieldName(const clang::FieldDecl &field,
                                             SemanticMode mode,
                                             factory::OriginList origins) {
    if (const clang::IdentifierInfo *identifier = field.getIdentifier())
        return factory::makeAtomicIdentifier(unit->buildingArena(),
                                             std::move(origins),
                                             identifier->getName().str());
    if (const auto *parent =
            llvm::dyn_cast<clang::CXXRecordDecl>(field.getParent()))
        if (parent->isLambda()) {
            llvm::DenseMap<const clang::ValueDecl *, clang::FieldDecl *>
                captures;
            clang::FieldDecl *thisCapture = nullptr;
            parent->getCaptureFields(captures, thisCapture);
            if (thisCapture == &field)
                return factory::makeAtomicIdentifier(
                    unit->buildingArena(), std::move(origins), "this");
            for (const auto &capture : captures)
                if (capture.second == &field)
                    return factory::makeAtomicIdentifier(
                        unit->buildingArena(), std::move(origins),
                        capture.first->getName().str());
        }
    if (!field.getType().isNull())
        if (const auto *record = llvm::dyn_cast_or_null<clang::RecordDecl>(
                field.getType()->getAsTagDecl()))
            return atomicName(*this, *record->getDeclContext(), *record, mode,
                              std::move(origins));
    return factory::makeAtomicIdentifier(
        unit->buildingArena(), std::move(origins),
        "<anonymous field not of record type>");
}

llvm::Expected<NodeId>
State::buildUnresolvedName(NestedNameSpecifierArg qualifier,
                           clang::NestedNameSpecifierLoc qualifierLocation,
                           llvm::StringRef identifier,
                           llvm::ArrayRef<clang::TemplateArgumentLoc> arguments,
                           SemanticMode mode, factory::OriginList origins) {
    clang::IdentifierInfo &spelling = context.Idents.get(identifier);
    return buildUnresolvedName(qualifier, qualifierLocation,
                               clang::DeclarationName(&spelling), arguments,
                               mode, std::move(origins));
}

llvm::Expected<NodeId>
State::buildUnresolvedName(NestedNameSpecifierArg qualifier,
                           clang::NestedNameSpecifierLoc qualifierLocation,
                           clang::DeclarationName name,
                           llvm::ArrayRef<clang::TemplateArgumentLoc> arguments,
                           SemanticMode mode, factory::OriginList origins) {
    auto atomic = unresolvedAtomicName(*this, name, mode, origins);
    if (!atomic)
        return atomic.takeError();

    llvm::Expected<NodeId> base = [&]() -> llvm::Expected<NodeId> {
        if (isEmptyOrGlobalQualifier(qualifier))
            return factory::makeGlobalName(unit->buildingArena(), origins,
                                           *atomic);
        if (const clang::NamedDecl *space = qualifierNamespace(qualifier)) {
            auto scope = buildName(*space, mode);
            if (!scope)
                return scope.takeError();
            return factory::makeScopedName(unit->buildingArena(), origins,
                                           *scope, *atomic);
        }
        if (const clang::Type *qualifiedType = qualifierType(qualifier)) {
            clang::QualType qualifierType(qualifiedType, 0);
            llvm::Expected<NodeId> type = [&]() -> llvm::Expected<NodeId> {
                if (clang::TypeLoc written =
                        qualifierTypeLocation(qualifierLocation))
                    return buildTypeLoc(written, mode, origins);
                auto inherited = inheritedTypeOrigins(qualifierType, origins);
                if (!inherited)
                    return inherited.takeError();
                return buildType(qualifierType, mode, std::move(*inherited));
            }();
            if (!type)
                return type.takeError();
            llvm::Expected<NodeId> scope = [&]() -> llvm::Expected<NodeId> {
                auto typeNode = unit->buildingArena().get(*type);
                if (!typeNode)
                    return typeNode.takeError();
                if ((*typeNode)->constructor == Constructor::TypeNamed &&
                    (*typeNode)->arguments.size() == 1)
                    if (const auto *reference = std::get_if<NodeRef>(
                            &(*typeNode)->arguments[0].payload))
                        return factory::cloneWithOrigins(
                            unit->buildingArena(), reference->value, origins);
                return factory::makeDependentName(unit->buildingArena(),
                                                  origins, *type);
            }();
            if (!scope)
                return scope.takeError();
            return factory::makeScopedName(unit->buildingArena(), origins,
                                           *scope, *atomic);
        }
        return factory::makeUnsupportedName(
            unit->buildingArena(), origins,
            "unsupported MicrosoftSuper nested qualifier");
    }();
    if (!base)
        return base.takeError();
    if (arguments.empty())
        return *base;
    std::vector<NodeId> builtArguments;
    builtArguments.reserve(arguments.size());
    for (const clang::TemplateArgumentLoc &argument : arguments) {
        auto built = buildTemplateArgumentLoc(argument, mode);
        if (!built)
            return built.takeError();
        builtArguments.push_back(*built);
    }
    return factory::makeInstantiatedName(unit->buildingArena(),
                                         std::move(origins), *base,
                                         std::move(builtArguments));
}

llvm::Expected<NodeId>
State::buildTemplateParameter(const clang::NamedDecl &parameter,
                              SemanticMode mode) {
    if (!parameter.isTemplateParameter())
        return migrationIncomplete(parameter, "non-template parameter");
    auto origins = declarationOrigins(parameter);
    if (parameter.isParameterPack()) {
        if (!origins)
            return origins.takeError();
        return factory::makeUnsupportedTemplateParameter(
            unit->buildingArena(), std::move(*origins),
            "template parameter pack");
    }
    if (!origins)
        return origins.takeError();
    const std::string name = templateParameterName(parameter);
    if (llvm::isa<clang::TemplateTypeParmDecl>(parameter))
        return factory::makeTypeTemplateParameter(unit->buildingArena(),
                                                  std::move(*origins), name);
    if (const auto *value =
            llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(&parameter)) {
        auto typeOrigins = inheritedTypeOrigins(value->getType(), *origins);
        if (!typeOrigins)
            return typeOrigins.takeError();
        auto type = buildType(value->getType(), mode, std::move(*typeOrigins));
        if (!type)
            return type.takeError();
        return factory::makeValueTemplateParameter(
            unit->buildingArena(), std::move(*origins), name, *type);
    }
    if (const auto *templ =
            llvm::dyn_cast<clang::TemplateTemplateParmDecl>(&parameter)) {
        std::vector<NodeId> nested;
        for (const clang::NamedDecl *entry :
             templ->getTemplateParameters()->asArray()) {
            auto built = buildTemplateParameter(*entry, mode);
            if (!built)
                return built.takeError();
            nested.push_back(*built);
        }
        return factory::makeTemplateTemplateParameter(unit->buildingArena(),
                                                      std::move(*origins), name,
                                                      std::move(nested));
    }
    return factory::makeUnsupportedTemplateParameter(
        unit->buildingArena(), std::move(*origins), "template parameter kind");
}

llvm::Expected<std::optional<NodeId>>
State::buildTemplateParameterDefault(const clang::NamedDecl &parameter,
                                     NodeId builtParameter, SemanticMode mode) {
    const clang::TemplateArgumentLoc *argument = nullptr;
    bool inherited = false;
    if (const auto *type =
            llvm::dyn_cast<clang::TemplateTypeParmDecl>(&parameter)) {
        if (type->hasDefaultArgument()) {
            argument = &type->getDefaultArgument();
            inherited = type->defaultArgumentWasInherited();
        }
    } else if (const auto *value =
                   llvm::dyn_cast<clang::NonTypeTemplateParmDecl>(&parameter)) {
        if (value->hasDefaultArgument()) {
            argument = &value->getDefaultArgument();
            inherited = value->defaultArgumentWasInherited();
        }
    } else if (const auto *templ =
                   llvm::dyn_cast<clang::TemplateTemplateParmDecl>(
                       &parameter)) {
        if (templ->hasDefaultArgument()) {
            argument = &templ->getDefaultArgument();
            inherited = templ->defaultArgumentWasInherited();
        }
    }
    if (!argument)
        return std::optional<NodeId>{};
    auto value = buildTemplateArgumentLoc(*argument, mode);
    if (!value)
        return value.takeError();
    if (!inherited)
        return std::optional<NodeId>{*value};
    auto parameterNode = unit->buildingArena().get(builtParameter);
    if (!parameterNode)
        return parameterNode.takeError();
    std::optional<source::OriginId> anchor;
    if (!(*parameterNode)->origins.empty())
        anchor = (*parameterNode)->origins.front();
    auto inheritedOrigin =
        sources.inheritedNode(anchor, (*parameterNode)->origins);
    if (!inheritedOrigin)
        return inheritedOrigin.takeError();
    auto cloned = factory::cloneWithOrigins(unit->buildingArena(), *value,
                                            {*inheritedOrigin});
    if (!cloned)
        return cloned.takeError();
    return std::optional<NodeId>{*cloned};
}

llvm::Expected<NodeId>
State::buildTemplateArgumentLoc(const clang::TemplateArgumentLoc &argument,
                                SemanticMode mode) {
    auto direct = sources.explicitNode(argument.getSourceRange());
    if (!direct)
        return direct.takeError();
    factory::OriginList origins{*direct};
    if (argument.getArgument().getKind() == clang::TemplateArgument::Type)
        if (const clang::TypeSourceInfo *written =
                argument.getTypeSourceInfo()) {
            auto type = buildTypeLoc(written->getTypeLoc(), mode, origins);
            if (!type)
                return type.takeError();
            return factory::makeTypeTemplateArgument(unit->buildingArena(),
                                                     std::move(origins), *type);
        }
    return buildTemplateArgument(argument.getArgument(), mode,
                                 std::move(origins));
}

llvm::Expected<NodeId>
State::buildTemplateArgument(const clang::TemplateArgument &argument,
                             SemanticMode mode, factory::OriginList origins) {
    switch (argument.getKind()) {
    case clang::TemplateArgument::Type: {
        auto typeOrigins = inheritedTypeOrigins(argument.getAsType(), origins);
        if (!typeOrigins)
            return typeOrigins.takeError();
        auto type =
            buildType(argument.getAsType(), mode, std::move(*typeOrigins));
        if (!type)
            return type.takeError();
        return factory::makeTypeTemplateArgument(unit->buildingArena(),
                                                 std::move(origins), *type);
    }
    case clang::TemplateArgument::Expression: {
        auto expression = buildExpression(*argument.getAsExpr(), mode);
        if (!expression)
            return expression.takeError();
        return factory::makeValueTemplateArgument(
            unit->buildingArena(), std::move(origins), *expression);
    }
    case clang::TemplateArgument::Integral: {
        llvm::SmallString<32> text;
        argument.getAsIntegral().toString(text, 10);
        auto typeOrigins =
            inheritedTypeOrigins(argument.getIntegralType(), origins);
        if (!typeOrigins)
            return typeOrigins.takeError();
        auto type = buildType(argument.getIntegralType(), mode,
                              std::move(*typeOrigins));
        if (!type)
            return type.takeError();
        auto expression = factory::makeIntegerExpression(
            unit->buildingArena(), origins, text.str().str(), *type);
        if (!expression)
            return expression.takeError();
        return factory::makeValueTemplateArgument(
            unit->buildingArena(), std::move(origins), *expression);
    }
    case clang::TemplateArgument::NullPtr: {
        auto expression =
            factory::makeNullExpression(unit->buildingArena(), origins);
        if (!expression)
            return expression.takeError();
        return factory::makeValueTemplateArgument(
            unit->buildingArena(), std::move(origins), *expression);
    }
    case clang::TemplateArgument::Declaration: {
        const clang::ValueDecl *declaration = argument.getAsDecl();
        if (!declaration)
            return factory::makeUnsupportedTemplateArgument(
                unit->buildingArena(), std::move(origins),
                "null declaration template argument");
        auto name = buildName(*declaration, mode);
        if (!name)
            return name.takeError();
        auto typeOrigins =
            inheritedTypeOrigins(declaration->getType(), origins);
        if (!typeOrigins)
            return typeOrigins.takeError();
        auto type =
            buildType(declaration->getType(), mode, std::move(*typeOrigins));
        if (!type)
            return type.takeError();
        auto expression = factory::makeGlobalExpression(
            unit->buildingArena(), origins, *name, *type, false);
        if (!expression)
            return expression.takeError();
        return factory::makeValueTemplateArgument(
            unit->buildingArena(), std::move(origins), *expression);
    }
    case clang::TemplateArgument::Pack: {
        std::vector<NodeId> values;
        for (const clang::TemplateArgument &entry : argument.pack_elements()) {
            auto built = buildTemplateArgument(entry, mode, origins);
            if (!built)
                return built.takeError();
            values.push_back(*built);
        }
        return factory::makePackTemplateArgument(
            unit->buildingArena(), std::move(origins), std::move(values));
    }
    case clang::TemplateArgument::Template: {
        const clang::TemplateDecl *templ =
            argument.getAsTemplate().getAsTemplateDecl();
        if (!templ)
            return factory::makeUnsupportedTemplateArgument(
                unit->buildingArena(), std::move(origins), "Template");
        if (const auto *parameter =
                llvm::dyn_cast<clang::TemplateTemplateParmDecl>(templ))
            return factory::makeTemplateParameterArgument(
                unit->buildingArena(), std::move(origins),
                templateParameterName(*parameter));
        auto name = buildUndecoratedName(*templ->getTemplatedDecl(), mode);
        if (!name)
            return name.takeError();
        return factory::makeNamedTemplateArgument(unit->buildingArena(),
                                                  std::move(origins), *name);
    }
    default:
        return factory::makeUnsupportedTemplateArgument(
            unit->buildingArena(), std::move(origins),
            templateArgumentKindName(argument.getKind()));
    }
}

} // namespace builder
} // namespace ir
