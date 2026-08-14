/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"

#include <clang/AST/DeclTemplate.h>
#include <clang/AST/NestedNameSpecifier.h>
#include <clang/AST/Type.h>
#include <clang/AST/TypeLoc.h>
#include <clang/Basic/Specifiers.h>
#include <clang/Basic/Version.inc>
#include <llvm/Support/raw_ostream.h>

namespace ir {
namespace builder {
namespace {

std::string templateParameterName(const clang::NamedDecl &declaration) {
    if (const auto *identifier = declaration.getIdentifier())
        return identifier->getName().str();
    if (const auto *parameter =
            llvm::dyn_cast<clang::TemplateTypeParmDecl>(&declaration))
        return "__type_" + std::to_string(parameter->getDepth()) + "_" +
               std::to_string(parameter->getIndex());
    return "__type_param";
}

std::string templateParameterName(State &state,
                                  const clang::TemplateTypeParmType &type) {
    if (const clang::TemplateTypeParmDecl *declaration = type.getDecl())
        return templateParameterName(*declaration);
    // ClangPrinter's declaration-based overload historically resolves a null
    // TemplateTypeParmDecl as depth 0, index 0, regardless of the depth/index
    // carried by the type node.  Preserve that frozen semantic behavior.
    const auto preferred = state.preferredTemplateTypeNames.find({0, 0});
    if (preferred != state.preferredTemplateTypeNames.end())
        return preferred->second;
    return "__type_0_0";
}

std::string describeType(State &state, const clang::Type &type) {
    std::string result;
    llvm::raw_string_ostream output(result);
    output << type.getTypeClassName() << ' ';
    state.context.getQualifiedType(&type, clang::Qualifiers())
        .print(output, state.context.getPrintingPolicy());
    return result;
}

llvm::Expected<NodeId> unsupportedType(State &state, const clang::Type &type,
                                       factory::OriginList origins) {
    return factory::makeUnsupportedType(state.unit->buildingArena(),
                                        std::move(origins),
                                        describeType(state, type));
}

llvm::Expected<NodeId> buildBuiltin(State &state,
                                    const clang::BuiltinType &type,
                                    SemanticMode mode,
                                    factory::OriginList origins) {
    using K = clang::BuiltinType::Kind;
    auto number = [&](const char *rank, const char *sign) {
        return factory::makeNumberType(
            state.unit->buildingArena(), std::move(origins),
            ScalarTerm::symbol(rank), ScalarTerm::symbol(sign));
    };
    auto leaf = [&](Constructor constructor) {
        return factory::makeLeafType(state.unit->buildingArena(), constructor,
                                     std::move(origins));
    };
    auto symbolicLeaf = [&](Constructor constructor, const char *symbol) {
        return factory::makeLeafType(state.unit->buildingArena(), constructor,
                                     std::move(origins),
                                     ScalarTerm::symbol(symbol));
    };
    switch (type.getKind()) {
    case K::Bool:
        return leaf(Constructor::TypeBoolean);
    case K::Void:
        return leaf(Constructor::TypeVoid);
    case K::NullPtr:
        return leaf(Constructor::TypeNullPointer);
    case K::SChar:
        return number("int_rank.Ichar", "Signed");
    case K::UChar:
        return number("int_rank.Ichar", "Unsigned");
    case K::Char_S:
    case K::Char_U:
        return symbolicLeaf(Constructor::TypeCharacter, "char_type.Cchar");
    case K::WChar_S:
    case K::WChar_U:
        return symbolicLeaf(Constructor::TypeCharacter, "char_type.Cwchar");
    case K::Char8:
        return symbolicLeaf(Constructor::TypeCharacter, "char_type.C8");
    case K::Char16:
        return symbolicLeaf(Constructor::TypeCharacter, "char_type.C16");
    case K::Char32:
        return symbolicLeaf(Constructor::TypeCharacter, "char_type.C32");
    case K::Short:
        return number("int_rank.Ishort", "Signed");
    case K::UShort:
        return number("int_rank.Ishort", "Unsigned");
    case K::Int:
        return number("int_rank.Iint", "Signed");
    case K::UInt:
        return number("int_rank.Iint", "Unsigned");
    case K::Long:
        return number("int_rank.Ilong", "Signed");
    case K::ULong:
        return number("int_rank.Ilong", "Unsigned");
    case K::LongLong:
        return number("int_rank.Ilonglong", "Signed");
    case K::ULongLong:
        return number("int_rank.Ilonglong", "Unsigned");
    case K::Int128:
        return number("int_rank.I128", "Signed");
    case K::UInt128:
        return number("int_rank.I128", "Unsigned");
    case K::Float16:
        return symbolicLeaf(Constructor::TypeFloat, "float_type.Ffloat16");
    case K::Float:
        return symbolicLeaf(Constructor::TypeFloat, "float_type.Ffloat");
    case K::Double:
        return symbolicLeaf(Constructor::TypeFloat, "float_type.Fdouble");
    case K::LongDouble:
        return unsupportedType(state, type, std::move(origins));
    case K::Float128:
        return symbolicLeaf(Constructor::TypeFloat, "float_type.Ffloat128");
    case K::Dependent:
        if (mode == SemanticMode::Template)
            return leaf(Constructor::TypeAuto);
        return unsupportedType(state, type, std::move(origins));
    default: {
        const std::string name =
            type.getName(state.context.getPrintingPolicy()).str();
        if (type.isSizelessBuiltinType())
            return factory::makeArchitectureType(state.unit->buildingArena(),
                                                 std::move(origins), name);
        return unsupportedType(state, type, std::move(origins));
    }
    }
}

llvm::Expected<NodeId> smartDependentName(State &state, NodeId type,
                                          factory::OriginList origins) {
    auto node = state.unit->buildingArena().get(type);
    if (!node)
        return node.takeError();
    if ((*node)->constructor == Constructor::TypeNamed &&
        (*node)->arguments.size() == 1)
        if (const auto *reference =
                std::get_if<NodeRef>(&(*node)->arguments[0].payload))
            return factory::cloneWithOrigins(state.unit->buildingArena(),
                                             reference->value, origins);
    return factory::makeDependentName(state.unit->buildingArena(),
                                      std::move(origins), type);
}

llvm::Expected<std::vector<NodeId>>
buildSpecializationArguments(State &state,
                             const clang::TemplateSpecializationType &type,
                             clang::TypeLoc location, SemanticMode mode,
                             const factory::OriginList &origins) {
    clang::TemplateSpecializationTypeLoc written;
    if (!location.isNull())
        written = location.getAs<clang::TemplateSpecializationTypeLoc>();
    const llvm::ArrayRef<clang::TemplateArgument> semanticArguments =
        type.template_arguments();
    std::vector<NodeId> result;
    result.reserve(semanticArguments.size());
    for (unsigned index = 0; index < semanticArguments.size(); ++index) {
        llvm::Expected<NodeId> argument =
            written && index < written.getNumArgs()
                ? state.buildTemplateArgumentLoc(written.getArgLoc(index), mode)
                : state.buildTemplateArgument(semanticArguments[index], mode,
                                              origins);
        if (!argument)
            return argument.takeError();
        result.push_back(*argument);
    }
    return result;
}

bool hasUnsupportedQualifiers(clang::QualType type) {
    const clang::Qualifiers qualifiers = type.getLocalQualifiers();
    return qualifiers.hasRestrict() || qualifiers.hasAddressSpace() ||
           qualifiers.hasObjCGCAttr() || qualifiers.hasObjCLifetime() ||
           qualifiers.hasUnaligned();
}

clang::TypeLoc nextLoc(clang::TypeLoc location) {
    return location.isNull() ? clang::TypeLoc() : location.getNextTypeLoc();
}

llvm::Expected<factory::OriginList>
originsFor(State &state, clang::QualType type, clang::TypeLoc location,
           const factory::OriginList &inherited) {
    factory::OriginList result;
    if (!location.isNull()) {
        auto direct = state.sources.typeLocNode(location);
        if (!direct)
            return direct.takeError();
        result.push_back(*direct);
    }
    auto inheritedOrigins = state.inheritedTypeOrigins(type, inherited);
    if (!inheritedOrigins)
        return inheritedOrigins.takeError();
    source::appendOriginsStable(result, *inheritedOrigins);
    return result;
}

llvm::Expected<NodeId> buildTypeUseRaw(State &state, clang::QualType qualified,
                                       clang::TypeLoc location,
                                       SemanticMode mode,
                                       factory::OriginList inherited);

llvm::Expected<NodeId> buildTypeUse(State &state, clang::QualType qualified,
                                    clang::TypeLoc location, SemanticMode mode,
                                    factory::OriginList inherited) {
    auto value =
        buildTypeUseRaw(state, qualified, location, mode, std::move(inherited));
    if (!value)
        return value.takeError();
    if (!qualified.hasLocalQualifiers())
        if (auto failure = state.attachTypeShare(*value, qualified, mode))
            return std::move(failure);
    return *value;
}

llvm::Expected<NodeId>
forwardType(State &state, clang::QualType outer, clang::TypeLoc outerLocation,
            clang::QualType child, clang::TypeLoc childLocation,
            SemanticMode mode, factory::OriginList inherited) {
    auto value = buildTypeUse(state, child, childLocation, mode, {});
    if (!value)
        return value.takeError();
    factory::OriginList additions;
    auto childNode = state.unit->buildingArena().get(*value);
    if (!childNode)
        return childNode.takeError();
    if (!outerLocation.isNull()) {
        auto transformed =
            state.sources.transformedNode(clang::CharSourceRange::getTokenRange(
                                              outerLocation.getSourceRange()),
                                          (*childNode)->origins);
        if (!transformed)
            return transformed.takeError();
        source::appendOriginStable(additions, *transformed);
    }
    auto inheritedOrigins = state.inheritedTypeOrigins(outer, inherited);
    if (!inheritedOrigins)
        return inheritedOrigins.takeError();
    source::appendOriginsStable(additions, *inheritedOrigins);
    return factory::cloneWithOrigins(state.unit->buildingArena(), *value,
                                     additions);
}

llvm::Expected<NodeId>
buildAdjustedArgument(State &state, clang::QualType adjusted,
                      const clang::TypeSourceInfo *written, SemanticMode mode,
                      factory::OriginList inherited) {
    // [normalize_arg_type] discards top-level qualifiers before applying the
    // array/function parameter adjustment already represented by Clang's
    // adjusted ParmVarDecl/FunctionProtoType type.
    adjusted = adjusted.getUnqualifiedType();
    if (!written)
        return buildTypeUse(state, adjusted, {}, mode, std::move(inherited));
    clang::TypeLoc originalLoc = written->getTypeLoc();
    clang::QualType original = originalLoc.getType();
    auto rootOrigins = originsFor(state, adjusted, originalLoc, inherited);
    if (!rootOrigins)
        return rootOrigins.takeError();

    if (const auto *pointer = adjusted->getAs<clang::PointerType>()) {
        if (state.context.getAsArrayType(original)) {
            clang::TypeLoc elementLoc = nextLoc(originalLoc);
            if (auto arrayLoc = originalLoc.getAs<clang::ArrayTypeLoc>())
                elementLoc = arrayLoc.getElementLoc();
            auto element = buildTypeUse(state, pointer->getPointeeType(),
                                        elementLoc, mode, *rootOrigins);
            if (!element)
                return element.takeError();
            auto result = factory::makeUnaryType(
                state.unit->buildingArena(), Constructor::TypePointer,
                std::move(*rootOrigins), *element);
            if (!result)
                return result.takeError();
            if (auto failure = state.attachTypeShare(*result, adjusted, mode))
                return std::move(failure);
            return *result;
        }
        if (original->isFunctionType()) {
            auto function = buildTypeUse(state, pointer->getPointeeType(),
                                         originalLoc, mode, *rootOrigins);
            if (!function)
                return function.takeError();
            auto result = factory::makeUnaryType(
                state.unit->buildingArena(), Constructor::TypePointer,
                std::move(*rootOrigins), *function);
            if (!result)
                return result.takeError();
            if (auto failure = state.attachTypeShare(*result, adjusted, mode))
                return std::move(failure);
            return *result;
        }
    }
    // The parser's [normalize_arg_type] erases top-level cv. Match the
    // adjusted semantic pointer/function with the corresponding unqualified
    // written TypeLoc rather than attaching the discarded qualifier wrapper.
    clang::TypeLoc adjustedLoc = originalLoc;
    if (original.hasLocalQualifiers())
        adjustedLoc = originalLoc.getUnqualifiedLoc();
    return buildTypeUse(state, adjusted, adjustedLoc, mode,
                        std::move(inherited));
}

llvm::Expected<NodeId> buildTypeUseRaw(State &state, clang::QualType qualified,
                                       clang::TypeLoc location,
                                       SemanticMode mode,
                                       factory::OriginList inherited) {
    if (qualified.isNull())
        return llvm::createStringError(std::errc::invalid_argument,
                                       "migration incomplete: null type");
    if (hasUnsupportedQualifiers(qualified) &&
        !qualified.isLocalConstQualified() &&
        !qualified.isLocalVolatileQualified()) {
        clang::TypeLoc childLocation =
            location.isNull() ? clang::TypeLoc() : location.getUnqualifiedLoc();
        return forwardType(state, qualified, location,
                           qualified.getLocalUnqualifiedType(), childLocation,
                           mode, std::move(inherited));
    }

    if (qualified.hasLocalQualifiers()) {
        clang::QualType unqualified = qualified.getLocalUnqualifiedType();
        clang::TypeLoc childLocation = location;
        if (!location.isNull())
            childLocation = location.getUnqualifiedLoc();
        auto origins = originsFor(state, qualified, location, inherited);
        if (!origins)
            return origins.takeError();
        auto nested =
            buildTypeUse(state, unqualified, childLocation, mode, *origins);
        if (!nested)
            return nested.takeError();
        const char *qualifier =
            qualified.isLocalConstQualified()
                ? (qualified.isLocalVolatileQualified() ? "QCV" : "QC")
                : "QV";
        auto nestedNode = state.unit->buildingArena().get(*nested);
        if (!nestedNode)
            return nestedNode.takeError();
        if ((*nestedNode)->constructor == Constructor::TypeQualified &&
            (*nestedNode)->arguments.size() == 2) {
            const auto *nestedQualifier =
                std::get_if<ScalarTerm>(&(*nestedNode)->arguments[0].payload);
            const auto *nestedType =
                std::get_if<NodeRef>(&(*nestedNode)->arguments[1].payload);
            if (nestedQualifier && nestedType) {
                auto mask = [](llvm::StringRef value) {
                    return value == "QC" ? 1U : value == "QV" ? 2U : 3U;
                };
                const unsigned combined =
                    mask(qualifier) | mask(nestedQualifier->text);
                source::appendOriginsStable(*origins, (*nestedNode)->origins);
                if (combined == mask(nestedQualifier->text))
                    return factory::cloneWithOrigins(
                        state.unit->buildingArena(), *nested,
                        std::move(*origins));
                const char *combinedQualifier = combined == 1   ? "QC"
                                                : combined == 2 ? "QV"
                                                                : "QCV";
                return factory::makeQualifiedType(
                    state.unit->buildingArena(), std::move(*origins),
                    ScalarTerm::symbol(combinedQualifier), nestedType->value);
            }
        }
        return factory::makeQualifiedType(
            state.unit->buildingArena(), std::move(*origins),
            ScalarTerm::symbol(qualifier), *nested);
    }

    const clang::Type &type = *qualified.getTypePtr();
    auto origins = originsFor(state, qualified, location, inherited);
    if (!origins)
        return origins.takeError();
    auto recurse =
        [&](clang::QualType child,
            clang::TypeLoc childLocation = {}) -> llvm::Expected<NodeId> {
        return buildTypeUse(state, child, childLocation, mode, *origins);
    };
    auto unary =
        [&](Constructor constructor, clang::QualType child,
            clang::TypeLoc childLocation = {}) -> llvm::Expected<NodeId> {
        auto value = recurse(child, childLocation);
        if (!value)
            return value.takeError();
        return factory::makeUnaryType(state.unit->buildingArena(), constructor,
                                      std::move(*origins), *value);
    };

    if (const auto *builtin = llvm::dyn_cast<clang::BuiltinType>(&type))
        return buildBuiltin(state, *builtin, mode, std::move(*origins));
    if (llvm::isa<clang::BlockPointerType, clang::PackExpansionType,
                  clang::VectorType>(&type))
        return unsupportedType(state, type, std::move(*origins));
    if (const auto *pointer = llvm::dyn_cast<clang::PointerType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::PointerTypeLoc>())
                child = typed.getPointeeLoc();
        return unary(Constructor::TypePointer, pointer->getPointeeType(),
                     child);
    }
    if (const auto *reference =
            llvm::dyn_cast<clang::LValueReferenceType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::LValueReferenceTypeLoc>())
                child = typed.getPointeeLoc();
        return unary(Constructor::TypeLvalueReference,
                     reference->getPointeeType(), child);
    }
    if (const auto *reference =
            llvm::dyn_cast<clang::RValueReferenceType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::RValueReferenceTypeLoc>())
                child = typed.getPointeeLoc();
        return unary(Constructor::TypeRvalueReference,
                     reference->getPointeeType(), child);
    }
    if (const auto *array = llvm::dyn_cast<clang::ConstantArrayType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::ConstantArrayTypeLoc>())
                child = typed.getElementLoc();
        auto element = recurse(array->getElementType(), child);
        if (!element)
            return element.takeError();
        return factory::makeArrayType(state.unit->buildingArena(),
                                      std::move(*origins), *element,
                                      array->getSize().getLimitedValue());
    }
    if (const auto *array = llvm::dyn_cast<clang::IncompleteArrayType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::IncompleteArrayTypeLoc>())
                child = typed.getElementLoc();
        return unary(Constructor::TypeIncompleteArray, array->getElementType(),
                     child);
    }
    if (const auto *array = llvm::dyn_cast<clang::VariableArrayType>(&type)) {
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::VariableArrayTypeLoc>())
                child = typed.getElementLoc();
        auto element = recurse(array->getElementType(), child);
        if (!element)
            return element.takeError();
        const clang::Expr *size = array->getSizeExpr();
        if (!size)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "migration incomplete: variable array without size");
        auto bound = state.buildExpression(*size, mode);
        if (!bound)
            return bound.takeError();
        return factory::makeVariableArrayType(
            state.unit->buildingArena(), std::move(*origins), *element, *bound);
    }
    if (const auto *array =
            llvm::dyn_cast<clang::DependentSizedArrayType>(&type)) {
        // Clang documents a null size for a dependent array whose bound is
        // deduced from its initializer. BRiCk has no final-core dependent
        // deduced-array constructor, so preserve an explicit typed boundary.
        const clang::Expr *size = array->getSizeExpr();
        if (!size)
            return unsupportedType(state, type, std::move(*origins));
        clang::TypeLoc child;
        if (!location.isNull())
            if (auto typed =
                    location.getAs<clang::DependentSizedArrayTypeLoc>())
                child = typed.getElementLoc();
        auto element = recurse(array->getElementType(), child);
        if (!element)
            return element.takeError();
        auto bound = state.buildExpression(*size, mode);
        if (!bound)
            return bound.takeError();
        return factory::makeVariableArrayType(
            state.unit->buildingArena(), std::move(*origins), *element, *bound);
    }
    if (const auto *dependent =
            llvm::dyn_cast<clang::DependentNameType>(&type)) {
        if (dependent->isSugared())
            return forwardType(state, qualified, location, dependent->desugar(),
                               nextLoc(location), mode, std::move(inherited));
        clang::NestedNameSpecifierLoc qualifierLocation;
        if (!location.isNull())
            if (auto written = location.getAs<clang::DependentNameTypeLoc>())
                qualifierLocation = written.getQualifierLoc();
        auto name = state.buildUnresolvedName(
            dependent->getQualifier(), qualifierLocation,
            dependent->getIdentifier()->getName(), {}, mode, *origins);
        if (!name)
            return name.takeError();
        return factory::makeNamedType(state.unit->buildingArena(),
                                      std::move(*origins), *name);
    }
    if (const auto *injected =
            llvm::dyn_cast<clang::InjectedClassNameType>(&type)) {
        if (const clang::CXXRecordDecl *declaration = injected->getDecl()) {
            auto name = state.buildName(*declaration, mode);
            if (!name)
                return name.takeError();
            return factory::makeNamedType(state.unit->buildingArena(),
                                          std::move(*origins), *name);
        }
        return unsupportedType(state, type, std::move(*origins));
    }
    if (const auto *record = llvm::dyn_cast<clang::RecordType>(&type)) {
        auto name = state.buildName(*record->getDecl(), mode);
        if (!name)
            return name.takeError();
        return factory::makeNamedType(state.unit->buildingArena(),
                                      std::move(*origins), *name);
    }
    if (const auto *enumeration = llvm::dyn_cast<clang::EnumType>(&type)) {
        auto name =
            state.buildName(*enumeration->getDecl()->getCanonicalDecl(), mode);
        if (!name)
            return name.takeError();
        return factory::makeEnumType(state.unit->buildingArena(),
                                     std::move(*origins), *name);
    }
    if (const auto *parameter =
            llvm::dyn_cast<clang::TemplateTypeParmType>(&type)) {
        if (!parameter->getDecl()) {
            const auto failure = state.preferredTemplateTypeErrors.find({0, 0});
            if (failure != state.preferredTemplateTypeErrors.end())
                return factory::makeUnsupportedType(state.unit->buildingArena(),
                                                    std::move(*origins),
                                                    failure->second);
            if (state.preferredTemplateTypeFallbackError)
                return factory::makeUnsupportedType(
                    state.unit->buildingArena(), std::move(*origins),
                    *state.preferredTemplateTypeFallbackError);
            if (!state.preferredTemplateTypeNames.count({0, 0}))
                return factory::makeUnsupportedType(state.unit->buildingArena(),
                                                    std::move(*origins),
                                                    "type template parameter");
        }
        return factory::makeTypeParameter(
            state.unit->buildingArena(), std::move(*origins),
            templateParameterName(state, *parameter));
    }
    if (const auto *function =
            llvm::dyn_cast<clang::FunctionProtoType>(&type)) {
        clang::FunctionProtoTypeLoc functionLoc;
        if (!location.isNull())
            functionLoc = location.getAs<clang::FunctionProtoTypeLoc>();
        clang::TypeLoc resultLoc;
        if (functionLoc)
            resultLoc = functionLoc.getReturnLoc();
        auto result = recurse(function->getReturnType(), resultLoc);
        if (!result)
            return result.takeError();
        std::vector<NodeId> parameters;
        for (unsigned index = 0; index < function->getNumParams(); ++index) {
            const clang::TypeSourceInfo *written = nullptr;
            if (functionLoc && index < functionLoc.getNumParams())
                if (const clang::ParmVarDecl *parameter =
                        functionLoc.getParam(index))
                    written = parameter->getTypeSourceInfo();
            auto built = buildAdjustedArgument(
                state, function->getParamType(index), written, mode, *origins);
            if (!built)
                return built.takeError();
            parameters.push_back(*built);
        }
        const char *callingConvention = nullptr;
        switch (function->getCallConv()) {
        case clang::CC_C:
            callingConvention = "CC_C";
            break;
        case clang::CC_X86RegCall:
            callingConvention = "CC_RegCall";
            break;
        case clang::CC_Win64:
            callingConvention = "CC_MsAbi";
            break;
        default:
            return unsupportedType(state, type, std::move(*origins));
        }
        return factory::makeFunctionType(
            state.unit->buildingArena(), std::move(*origins),
            ScalarTerm::symbol(callingConvention),
            ScalarTerm::symbol(function->isVariadic() ? "Ar_Variadic"
                                                      : "Ar_Definite"),
            *result, std::move(parameters));
    }
    if (const auto *member = llvm::dyn_cast<clang::MemberPointerType>(&type)) {
        clang::NestedNameSpecifier qualifier = member->getQualifier();
        clang::TypeLoc classLoc;
        clang::TypeLoc pointeeLoc;
        if (!location.isNull())
            if (auto typed = location.getAs<clang::MemberPointerTypeLoc>()) {
                classLoc = typed.getQualifierLoc().getAsTypeLoc();
                pointeeLoc = typed.getPointeeLoc();
            }
        llvm::Expected<NodeId> classType = [&]() -> llvm::Expected<NodeId> {
            if (qualifier &&
                qualifier.getKind() == clang::NestedNameSpecifier::Kind::Type)
                return recurse(clang::QualType(qualifier.getAsType(), 0),
                               classLoc);
            // Legacy retains the Tmember_pointer node and places the
            // diagnostic Tunsupported only in its class-type child.
            auto childOrigins = state.inheritedTypeOrigins(qualified, *origins);
            if (!childOrigins)
                return childOrigins.takeError();
            return factory::makeUnsupportedType(state.unit->buildingArena(),
                                                std::move(*childOrigins),
                                                describeType(state, type));
        }();
        if (!classType)
            return classType.takeError();
        auto pointee = recurse(member->getPointeeType(), pointeeLoc);
        if (!pointee)
            return pointee.takeError();
        return factory::makeMemberPointerType(state.unit->buildingArena(),
                                              std::move(*origins), *classType,
                                              *pointee);
    }
    if (const auto *transform =
            llvm::dyn_cast<clang::UnaryTransformType>(&type)) {
        if (transform->isDependentType())
            return unsupportedType(state, type, std::move(*origins));
        return forwardType(state, qualified, location,
                           transform->getUnderlyingType(), nextLoc(location),
                           mode, std::move(inherited));
    }
    if (const auto *parenthesized = llvm::dyn_cast<clang::ParenType>(&type)) {
        clang::TypeLoc child = nextLoc(location);
        if (!location.isNull())
            if (auto typed = location.getAs<clang::ParenTypeLoc>())
                child = typed.getInnerLoc();
        return forwardType(state, qualified, location,
                           parenthesized->getInnerType(), child, mode,
                           std::move(inherited));
    }
    if (const auto *attributed = llvm::dyn_cast<clang::AttributedType>(&type))
        return forwardType(state, qualified, location,
                           attributed->getModifiedType(), nextLoc(location),
                           mode, std::move(inherited));
    if (const auto *alias = llvm::dyn_cast<clang::TypedefType>(&type))
        return forwardType(
            state, qualified, location,
            alias->getDecl()->getCanonicalDecl()->getUnderlyingType(), {}, mode,
            std::move(inherited));
    if (const auto *substitution =
            llvm::dyn_cast<clang::SubstTemplateTypeParmType>(&type))
        return forwardType(state, qualified, location,
                           substitution->getReplacementType(),
                           nextLoc(location), mode, std::move(inherited));
    if (const auto *decayed = llvm::dyn_cast<clang::DecayedType>(&type))
        return forwardType(state, qualified, location,
                           decayed->getAdjustedType(), nextLoc(location), mode,
                           std::move(inherited));
    if (const auto *automatic = llvm::dyn_cast<clang::AutoType>(&type)) {
        if (automatic->isDeduced() && !automatic->isDependentType() &&
            !automatic->getDeducedType().isNull())
            return forwardType(state, qualified, location,
                               automatic->getDeducedType(), nextLoc(location),
                               mode, std::move(inherited));
        if (mode == SemanticMode::Template)
            return factory::makeLeafType(state.unit->buildingArena(),
                                         Constructor::TypeAuto,
                                         std::move(*origins));
        return unsupportedType(state, type, std::move(*origins));
    }
    if (const auto *deduced = llvm::dyn_cast<clang::DeducedType>(&type)) {
        if (!deduced->getDeducedType().isNull())
            return forwardType(state, qualified, location,
                               deduced->getDeducedType(), nextLoc(location),
                               mode, std::move(inherited));
        return factory::makeLeafType(state.unit->buildingArena(),
                                     Constructor::TypeAuto,
                                     std::move(*origins));
    }
    if (const auto *macro = llvm::dyn_cast<clang::MacroQualifiedType>(&type))
        return forwardType(state, qualified, location, macro->getModifiedType(),
                           nextLoc(location), mode, std::move(inherited));
    if (const auto *usingType = llvm::dyn_cast<clang::UsingType>(&type))
        return forwardType(state, qualified, location, usingType->desugar(),
                           nextLoc(location), mode, std::move(inherited));
    if (const auto *predefined =
            llvm::dyn_cast<clang::PredefinedSugarType>(&type))
        return forwardType(state, qualified, location, predefined->desugar(),
                           nextLoc(location), mode, std::move(inherited));
    if (const auto *specialization =
            llvm::dyn_cast<clang::TemplateSpecializationType>(&type)) {
        if (specialization->isTypeAlias())
            return forwardType(state, qualified, location,
                               specialization->getAliasedType(),
                               nextLoc(location), mode, std::move(inherited));
        if (specialization->isSugared())
            return forwardType(state, qualified, location,
                               specialization->desugar(), nextLoc(location),
                               mode, std::move(inherited));
        const clang::TemplateName templateName =
            specialization->getTemplateName();
        const clang::TemplateDecl *templ = templateName.getAsTemplateDecl();
        // Legacy decides this outer unsupported branch before traversing any
        // arguments, so an unported argument cannot mask the final type.
        if (!templ)
            return unsupportedType(state, type, std::move(*origins));
        auto arguments = buildSpecializationArguments(state, *specialization,
                                                      location, mode, *origins);
        if (!arguments)
            return arguments.takeError();
        llvm::Expected<NodeId> base = [&]() -> llvm::Expected<NodeId> {
            if (const auto *parameter =
                    llvm::dyn_cast<clang::TemplateTemplateParmDecl>(templ)) {
                auto parameterType = factory::makeTypeParameter(
                    state.unit->buildingArena(), *origins,
                    templateParameterName(*parameter));
                if (!parameterType)
                    return parameterType.takeError();
                return smartDependentName(state, *parameterType, *origins);
            }
            if (const clang::NamedDecl *templated = templ->getTemplatedDecl())
                return state.buildUndecoratedName(*templated, mode);
            return state.buildUndecoratedName(*templ, mode);
        }();
        if (!base)
            return base.takeError();
        auto instantiated =
            factory::makeInstantiatedName(state.unit->buildingArena(), *origins,
                                          *base, std::move(*arguments));
        if (!instantiated)
            return instantiated.takeError();
        return factory::makeNamedType(state.unit->buildingArena(),
                                      std::move(*origins), *instantiated);
    }
    if (const auto *declType = llvm::dyn_cast<clang::DecltypeType>(&type)) {
        if (declType->isSugared())
            return forwardType(state, qualified, location, declType->desugar(),
                               nextLoc(location), mode, std::move(inherited));
        if (mode == SemanticMode::Static)
            return unsupportedType(state, type, std::move(*origins));
        auto expression =
            state.buildExpression(*declType->getUnderlyingExpr(), mode);
        if (!expression)
            return expression.takeError();
        return factory::makeExpressionType(
            state.unit->buildingArena(),
            llvm::isa<clang::DeclRefExpr>(declType->getUnderlyingExpr())
                ? Constructor::TypeExpressionType
                : Constructor::TypeDecltype,
            std::move(*origins), *expression);
    }
    if (const auto *typeOf = llvm::dyn_cast<clang::TypeOfExprType>(&type)) {
        if (typeOf->isSugared())
            return forwardType(state, qualified, location, typeOf->desugar(),
                               nextLoc(location), mode, std::move(inherited));
        if (mode == SemanticMode::Static)
            return unsupportedType(state, type, std::move(*origins));
        return buildTypeUse(state, typeOf->getUnderlyingExpr()->getType(), {},
                            mode, std::move(*origins));
    }
#if CLANG_VERSION_MAJOR < 22
    if (const auto *elaborated = llvm::dyn_cast<clang::ElaboratedType>(&type)) {
        if (elaborated->getNamedType().isNull())
            return factory::makeUnsupportedType(state.unit->buildingArena(),
                                                std::move(*origins),
                                                "elaborated type w/ null");
        return forwardType(state, qualified, location,
                           elaborated->getNamedType(), nextLoc(location), mode,
                           std::move(inherited));
    }
#endif
    return unsupportedType(state, type, std::move(*origins));
}

} // namespace

llvm::Expected<NodeId>
State::buildWrittenType(const clang::TypeSourceInfo &typeSourceInfo,
                        SemanticMode mode) {
    return buildTypeLoc(typeSourceInfo.getTypeLoc(), mode);
}

llvm::Expected<NodeId> State::buildTypeLoc(clang::TypeLoc typeLoc,
                                           SemanticMode mode,
                                           factory::OriginList inherited) {
    if (typeLoc.isNull())
        return llvm::createStringError(std::errc::invalid_argument,
                                       "migration incomplete: null TypeLoc");
    return buildTypeUse(*this, typeLoc.getType(), typeLoc, mode,
                        std::move(inherited));
}

llvm::Expected<NodeId> State::buildType(clang::QualType type, SemanticMode mode,
                                        factory::OriginList origins) {
    return buildTypeUse(*this, type, {}, mode, std::move(origins));
}

llvm::Expected<NodeId> State::buildNormalizedArgumentType(
    clang::QualType adjusted, const clang::TypeSourceInfo *written,
    SemanticMode mode, factory::OriginList inherited) {
    return buildAdjustedArgument(*this, adjusted, written, mode,
                                 std::move(inherited));
}

} // namespace builder
} // namespace ir
