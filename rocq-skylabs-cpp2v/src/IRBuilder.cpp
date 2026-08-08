/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IRBuilderInternal.hpp"
#include "ModuleBuilder.hpp"

#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <llvm/Support/Casting.h>

namespace {

bool introducesTemplate(const clang::Decl &declaration) {
    using namespace clang;
    if (llvm::isa<TemplateDecl>(declaration))
        return true;
    if (const auto *record = llvm::dyn_cast<CXXRecordDecl>(&declaration))
        return record->getDescribedClassTemplate();
    if (const auto *function = llvm::dyn_cast<FunctionDecl>(&declaration))
        return function->getDescribedFunctionTemplate();
    if (const auto *alias = llvm::dyn_cast<TypeAliasDecl>(&declaration))
        return alias->getDescribedAliasTemplate();
    if (const auto *variable = llvm::dyn_cast<VarDecl>(&declaration))
        return variable->getDescribedVarTemplate();
    return false;
}

bool isInTemplateScope(const clang::Decl &declaration) {
    if (introducesTemplate(declaration))
        return true;
    for (const clang::DeclContext *context = declaration.getDeclContext();
         context; context = context->getParent())
        if (introducesTemplate(clang::cast<clang::Decl>(*context)))
            return true;
    return false;
}

bool suppressTemplateEnumConstant(const clang::NamedDecl &declaration) {
    const auto *constant =
        llvm::dyn_cast<clang::EnumConstantDecl>(&declaration);
    const auto *enumeration =
        constant ? llvm::dyn_cast<clang::EnumDecl>(constant->getDeclContext())
                 : nullptr;
    return enumeration && isInTemplateScope(*enumeration);
}

bool isImplicitSpecialMethod(const clang::Decl &declaration) {
    using namespace clang;
    if (!declaration.isImplicit())
        return false;
    if (const auto *constructor = dyn_cast<CXXConstructorDecl>(&declaration))
        return constructor->isDefaultConstructor() ||
               constructor->isCopyConstructor() ||
               constructor->isMoveConstructor();
    if (isa<CXXDestructorDecl>(declaration))
        return true;
    if (const auto *method = dyn_cast<CXXMethodDecl>(&declaration))
        return method->isCopyAssignmentOperator() ||
               method->isMoveAssignmentOperator();
    return false;
}

bool hasDirectSpecialization(const clang::Decl &declaration) {
    using namespace clang;
    if (isa<ClassTemplateSpecializationDecl>(declaration) ||
        isa<VarTemplateSpecializationDecl>(declaration))
        return true;
    if (const auto *function = dyn_cast<FunctionDecl>(&declaration))
        return function->getPrimaryTemplate() &&
               function->getTemplateSpecializationArgs();
    return false;
}

bool isSpecialized(const clang::Decl &declaration) {
    if (isImplicitSpecialMethod(declaration) ||
        llvm::isa<clang::EnumConstantDecl>(declaration))
        return false;
    if (hasDirectSpecialization(declaration))
        return true;
    for (const clang::DeclContext *context = declaration.getDeclContext();
         context; context = context->getParent())
        if (hasDirectSpecialization(clang::cast<clang::Decl>(*context)))
            return true;
    return false;
}

bool isLegacyUnsupportedRecord(const clang::NamedDecl &declaration) {
    const auto *record = llvm::dyn_cast<clang::RecordDecl>(&declaration);
    if (!record || !record->isCompleteDefinition())
        return false;
    if (const auto *cxx = llvm::dyn_cast<clang::CXXRecordDecl>(record))
        for (const clang::CXXBaseSpecifier &base : cxx->bases())
            if (base.isVirtual())
                return true;
    for (const clang::FieldDecl *field : record->fields())
        if (field->isBitField() || field->isInvalidDecl())
            return true;
    return false;
}

} // namespace

namespace ir {

llvm::Expected<BuildArtifact> IRBuilder::build(clang::ASTContext &context,
                                               const BuildSelection &selection,
                                               clang::Sema *sema) {
    builder::State state(context, sema);
    BuildArtifact artifact;
    auto null = [](const char *kind) {
        return llvm::createStringError(
            std::errc::invalid_argument,
            "migration incomplete: null %s in selection", kind);
    };
    for (const auto &use : selection.names) {
        if (!use.value)
            return null("name declaration");
        auto value = state.buildName(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.names.push_back(*value);
    }
    for (const auto &use : selection.writtenTypes) {
        if (!use.value)
            return null("written type");
        auto value = state.buildWrittenType(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.types.push_back(*value);
    }
    for (const auto &use : selection.semanticTypes) {
        if (use.value.isNull())
            return null("semantic type");
        auto value = state.buildType(use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.types.push_back(*value);
    }
    for (const auto &use : selection.expressions) {
        if (!use.value)
            return null("expression");
        auto value = state.buildExpression(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.expressions.push_back(*value);
    }
    for (const auto &use : selection.templateParameters) {
        if (!use.value)
            return null("template parameter");
        auto value = state.buildTemplateParameter(*use.value, use.mode);
        if (!value)
            return value.takeError();
        auto defaultArgument =
            state.buildTemplateParameterDefault(*use.value, *value, use.mode);
        if (!defaultArgument)
            return defaultArgument.takeError();
        artifact.templateParameters.push_back(*value);
        artifact.templateParameterEntries.push_back(
            {*value, std::move(*defaultArgument)});
    }
    for (const auto &use : selection.writtenTemplateArguments) {
        if (!use.value)
            return null("written template argument");
        auto value = state.buildTemplateArgumentLoc(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.templateArguments.push_back(*value);
    }
    for (const auto &use : selection.semanticTemplateArguments) {
        if (!use.value)
            return null("semantic template argument");
        auto value = state.buildTemplateArgument(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.templateArguments.push_back(*value);
    }
    for (const auto &use : selection.objectDeclarations) {
        if (!use.value)
            return null("object declaration");
        auto value = state.buildObjectValue(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.objectValues.push_back(*value);
    }
    for (const auto &use : selection.globalDeclarations) {
        if (!use.value)
            return null("global declaration");
        auto value = state.buildGlobalDeclaration(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.globalDeclarations.push_back(*value);
    }
    for (const auto &use : selection.declarationTemplateParameters) {
        if (!use.value)
            return null("declaration template parameter source");
        auto value =
            state.buildDeclarationTemplateParameters(*use.value, use.mode);
        if (!value)
            return value.takeError();
        artifact.declarationTemplateParameters.push_back(std::move(*value));
    }
    for (const RootDeclarationUse &use : selection.rootDeclarations) {
        if (!use.value)
            return null("root declaration");
        if (suppressTemplateEnumConstant(*use.value))
            continue;
        if (use.includeImplicitMembers) {
            if (use.family != DeclarationFamily::Global || use.templateRoot)
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "implicit member expansion requires an ordinary global "
                    "record root");
            if (auto failure =
                    state.addImplicitMemberRoots(*use.value, use.mode))
                return std::move(failure);
        }
        auto name = state.buildName(*use.value, use.mode);
        if (!name)
            return name.takeError();
        llvm::Expected<NodeId> value =
            use.family == DeclarationFamily::Object
                ? state.buildObjectValue(*use.value, use.mode)
                : state.buildGlobalDeclaration(*use.value, use.mode);
        if (!value)
            return value.takeError();
        RootKind kind;
        if (use.templateRoot) {
            auto parameters =
                state.buildDeclarationTemplateParameters(*use.value, use.mode);
            if (!parameters)
                return parameters.takeError();
            auto origins = state.declarationOrigins(*use.value);
            if (!origins)
                return origins.takeError();
            if (use.family == DeclarationFamily::Object) {
                value = factory::makeTemplateObjectRoot(
                    state.unit->buildingArena(), std::move(*origins),
                    std::move(*parameters), *value);
                kind = RootKind::TemplateSymbol;
            } else {
                value = factory::makeTemplateGlobalRoot(
                    state.unit->buildingArena(), std::move(*origins),
                    std::move(*parameters), *value);
                kind = RootKind::TemplateType;
            }
            if (!value)
                return value.takeError();
        } else {
            kind = use.family == DeclarationFamily::Object ? RootKind::Symbol
                                                           : RootKind::Type;
        }
        if (auto failure =
                state.unit->addRoot({kind, *name, *value, use.seedName}))
            return std::move(failure);
    }
    for (const NamespaceAliasUse &use : selection.namespaceAliases) {
        if (!use.owner || !use.to)
            return null("namespace alias");
        if (auto failure = state.addNamespaceAlias(*use.owner, use.from,
                                                   *use.to, use.mode))
            return std::move(failure);
    }
    for (const auto &use : selection.staticAssertions) {
        if (!use.value)
            return null("static assertion");
        if (auto failure = state.addStaticAssertion(*use.value, use.mode))
            return std::move(failure);
    }
    for (const auto &use : selection.templateAliases) {
        if (!use.value)
            return null("template alias");
        if (auto failure = state.addTemplateAlias(*use.value, use.mode))
            return std::move(failure);
    }
    for (const auto &use : selection.templateInstances) {
        if (!use.value)
            return null("template instance");
        if (auto failure = state.addTemplateInstance(*use.value, use.mode))
            return std::move(failure);
    }
    auto validateGroup = [](const BuildNodeGroup &group) -> llvm::Error {
        const bool valid = (group.cardinality == BuildCardinality::Zero &&
                            group.nodes.empty()) ||
                           (group.cardinality == BuildCardinality::One &&
                            group.nodes.size() == 1) ||
                           (group.cardinality == BuildCardinality::Forwarded &&
                            group.nodes.size() == 1) ||
                           (group.cardinality == BuildCardinality::Several &&
                            group.nodes.size() > 1);
        if (valid)
            return llvm::Error::success();
        return llvm::createStringError(
            std::errc::invalid_argument,
            "builder returned an inconsistent cardinality group");
    };
    for (const auto &use : selection.localDeclarations) {
        if (!use.value)
            return null("local declaration");
        auto value = state.buildLocalDeclaration(*use.value, use.mode);
        if (!value)
            return value.takeError();
        if (auto failure = validateGroup(*value))
            return std::move(failure);
        artifact.localDeclarationGroups.push_back(std::move(*value));
    }
    for (const auto &use : selection.statements) {
        // A null statement is a meaningful focused selection and lowers to
        // Sunsupported "empty statement", matching the legacy visitor.
        auto value = state.buildStatement(use.value, use.mode);
        if (!value)
            return value.takeError();
        if (auto failure = validateGroup(*value))
            return std::move(failure);
        artifact.statementGroups.push_back(std::move(*value));
    }
    return state.finish(std::move(artifact));
}

llvm::Expected<BuildArtifact>
IRBuilder::buildNames(clang::ASTContext &context,
                      llvm::ArrayRef<const clang::NamedDecl *> declarations) {
    std::vector<PointerUse<clang::NamedDecl>> uses;
    uses.reserve(declarations.size());
    for (const clang::NamedDecl *declaration : declarations)
        uses.push_back({declaration, SemanticMode::Static});
    BuildSelection selection{uses, {}, {}, {}, {}, {}, {}};
    return build(context, selection);
}

llvm::Expected<BuildArtifact> IRBuilder::buildModule(clang::ASTContext &context,
                                                     const ::Module &module,
                                                     clang::Sema *sema,
                                                     bool includeTypedefs,
                                                     bool includeComments) {
    builder::State state(context, sema);
    BuildArtifact artifact;
    auto error = [](const clang::NamedDecl &declaration,
                    llvm::StringRef message) {
        return llvm::createStringError(
            std::errc::invalid_argument, "module IR builder rejected %s: %s",
            declaration.getDeclKindName(), message.str().c_str());
    };
    auto family = [&](const clang::NamedDecl &declaration)
        -> llvm::Expected<DeclarationFamily> {
        if (llvm::isa<clang::VarDecl>(declaration) ||
            llvm::isa<clang::FunctionDecl>(declaration))
            return DeclarationFamily::Object;
        if (llvm::isa<clang::RecordDecl>(declaration) ||
            llvm::isa<clang::EnumDecl>(declaration) ||
            llvm::isa<clang::EnumConstantDecl>(declaration) ||
            llvm::isa<clang::TypedefNameDecl>(declaration))
            return DeclarationFamily::Global;
        return error(declaration, "unsupported declaration family");
    };
    auto specializationPattern =
        [](const clang::NamedDecl &declaration) -> const clang::NamedDecl * {
        if (const auto *value =
                llvm::dyn_cast<clang::CXXRecordDecl>(&declaration)) {
            if (const auto *pattern = value->getInstantiatedFromMemberClass())
                return pattern;
            return value->getTemplateInstantiationPattern();
        }
        if (const auto *value =
                llvm::dyn_cast<clang::FunctionDecl>(&declaration)) {
            if (const auto *pattern =
                    value->getInstantiatedFromMemberFunction())
                return pattern;
            if (const auto *pattern = value->getInstantiatedFromDecl())
                return pattern;
            return value->getTemplateInstantiationPattern();
        }
        if (const auto *value = llvm::dyn_cast<clang::EnumDecl>(&declaration)) {
            if (const auto *pattern = value->getInstantiatedFromMemberEnum())
                return pattern;
            return value->getTemplateInstantiationPattern();
        }
        if (const auto *value = llvm::dyn_cast<clang::VarDecl>(&declaration)) {
            if (const auto *pattern =
                    value->getInstantiatedFromStaticDataMember())
                return pattern;
            return value->getTemplateInstantiationPattern();
        }
        return nullptr;
    };
    auto addRoot = [&](const clang::NamedDecl &declaration, SemanticMode mode,
                       bool templateRoot) -> llvm::Error {
        if (suppressTemplateEnumConstant(declaration))
            return llvm::Error::success();
        auto declarationFamily = family(declaration);
        if (!declarationFamily)
            return declarationFamily.takeError();
        if (!templateRoot)
            if (const auto *record =
                    llvm::dyn_cast<clang::CXXRecordDecl>(&declaration))
                if (record->isCompleteDefinition())
                    if (auto failure =
                            state.addImplicitMemberRoots(declaration, mode))
                        return failure;
        auto name = templateRoot ? state.buildPatternName(declaration, mode)
                                 : state.buildName(declaration, mode);
        if (!name)
            return name.takeError();
        llvm::Expected<NodeId> value =
            *declarationFamily == DeclarationFamily::Object
                ? state.buildObjectValue(declaration, mode)
                : state.buildGlobalDeclaration(declaration, mode);
        if (!value)
            return value.takeError();
        bool includeDiagnostic = includeComments;
        auto initialValueNode = state.unit->buildingArena().get(*value);
        if (!initialValueNode)
            return initialValueNode.takeError();
        if ((*initialValueNode)->constructor == Constructor::GlobalUnsupported)
            includeDiagnostic = false;
        RootKind kind;
        if (templateRoot) {
            std::vector<Value> parameters;
            auto valueNode = state.unit->buildingArena().get(*value);
            if (!valueNode)
                return valueNode.takeError();
            if ((*valueNode)->constructor != Constructor::GlobalUnsupported) {
                auto built =
                    state.buildDeclarationTemplateParameters(declaration, mode);
                if (!built)
                    return built.takeError();
                parameters = std::move(*built);
            }
            auto origins = state.declarationOrigins(declaration);
            if (!origins)
                return origins.takeError();
            if (*declarationFamily == DeclarationFamily::Object) {
                value = factory::makeTemplateObjectRoot(
                    state.unit->buildingArena(), std::move(*origins),
                    std::move(parameters), *value);
                kind = RootKind::TemplateSymbol;
            } else {
                value = factory::makeTemplateGlobalRoot(
                    state.unit->buildingArena(), std::move(*origins),
                    std::move(parameters), *value);
                kind = RootKind::TemplateType;
            }
            if (!value)
                return value.takeError();
        } else {
            kind = *declarationFamily == DeclarationFamily::Object
                       ? RootKind::Symbol
                       : RootKind::Type;
        }
        const bool seedName =
            !llvm::isa<clang::VarDecl>(declaration) || templateRoot;
        std::optional<std::string> comment;
        if (includeDiagnostic)
            comment = state.diagnosticName(declaration);
        return state.unit->addRoot(
            {kind, *name, *value, seedName, true, std::move(comment)});
    };
    auto addOrdinaryList =
        [&](const ::Module::DeclList &declarations) -> llvm::Error {
        for (const clang::NamedDecl *declaration : declarations) {
            if (!declaration)
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "module IR builder received a null declaration");
            if (!includeTypedefs &&
                llvm::isa<clang::TypedefNameDecl>(declaration))
                continue;
            if (auto failure =
                    addRoot(*declaration, SemanticMode::Static, false))
                return failure;
        }
        return llvm::Error::success();
    };
    if (auto failure = addOrdinaryList(module.declarations()))
        return std::move(failure);
    if (auto failure = addOrdinaryList(module.definitions()))
        return std::move(failure);

    for (const ::Module::AliasEntry &alias : module.ordered_aliases()) {
        const clang::Decl *owner = module.alias_origin(alias);
        if (!owner || !alias.second)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "module namespace alias lost its declaration origin");
        if (auto failure = state.addNamespaceAlias(
                *owner, alias.first, *alias.second, SemanticMode::Static))
            return std::move(failure);
    }
    for (const clang::StaticAssertDecl *assertion : module.asserts()) {
        if (!assertion)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "module IR builder received a null static assertion");
        if (auto failure =
                state.addStaticAssertion(*assertion, SemanticMode::Static))
            return std::move(failure);
    }

    auto addTemplateList =
        [&](const ::Module::DeclList &declarations) -> llvm::Error {
        for (const clang::NamedDecl *declaration : declarations) {
            if (!declaration)
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "module IR builder received a null template "
                    "declaration");
            if (isSpecialized(*declaration)) {
                if (isLegacyUnsupportedRecord(*declaration)) {
                    if (auto failure =
                            addRoot(*declaration, SemanticMode::Template, true))
                        return failure;
                } else if (specializationPattern(*declaration)) {
                    if (auto failure = state.addTemplateInstance(
                            *declaration, SemanticMode::Template,
                            includeComments))
                        return failure;
                }
                continue;
            }
            if (!declaration->isTemplated())
                continue;
            if (const auto *alias =
                    llvm::dyn_cast<clang::TypedefNameDecl>(declaration)) {
                if (!includeTypedefs)
                    continue;
                if (auto failure = state.addTemplateAlias(
                        *alias, SemanticMode::Template, includeComments))
                    return failure;
                continue;
            }
            if (auto failure =
                    addRoot(*declaration, SemanticMode::Template, true))
                return failure;
        }
        return llvm::Error::success();
    };
    if (auto failure = addTemplateList(module.template_declarations()))
        return std::move(failure);
    if (auto failure = addTemplateList(module.template_definitions()))
        return std::move(failure);
    return state.finish(std::move(artifact));
}

} // namespace ir
