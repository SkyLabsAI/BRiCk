/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *
 * AST-evolution warning: every new or changed BRiCk recursive field must update
 * the IR constructor registry and the grouping/flatten-order cases below. The
 * location path ABI is mechanically derived from those cases.
 */
#include "IR.hpp"
#include "IRFactories.hpp"
#include "LocationDAGEncoding.hpp"
#include "LocationEmitter.hpp"
#include "RocqEmitter.hpp"
#include "RootEventEncoding.hpp"
#include "Sharing.hpp"
#include "SourceInfo.hpp"
#include "SourceInfoEncoding.hpp"

#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <set>
#include <string>
#include <type_traits>
#include <vector>

#include <llvm/Support/Error.h>

using namespace ir;

namespace {

static_assert(!std::is_copy_assignable_v<Arena>);
static_assert(!std::is_move_assignable_v<Arena>);

struct Built {
    NodeId atomic;
    NodeId name;
    NodeId type;
    NodeId expression0;
    NodeId expression1;
    NodeId tempParam;
    NodeId tempArgType;
    NodeId tempArgValue;
    NodeId globalInit;
    NodeId object;
    NodeId global;
    NodeId templateObject;
    NodeId templateGlobal;
};

bool failed(llvm::Error value) {
    if (!value)
        return false;
    llvm::consumeError(std::move(value));
    return true;
}

template <typename T> bool failed(llvm::Expected<T> value) {
    if (value)
        return false;
    llvm::consumeError(value.takeError());
    return true;
}

NodeId add(TranslationUnitIR &unit, Category category, Constructor constructor,
           std::vector<Value> arguments,
           std::vector<source::OriginId> origins = {}) {
    auto result = unit.buildingArena().add(
        Node{category, constructor, std::move(origins), std::move(arguments)});
    if (!result) {
        llvm::consumeError(result.takeError());
        return NodeId();
    }
    return *result;
}

source::Tables tables(unsigned origins = 3) {
    source::Tables result;
    result.files.push_back(source::File{"fixture.cpp", std::nullopt,
                                        source::FileKind::User, true,
                                        std::nullopt});
    for (unsigned i = 0; i < origins; ++i) {
        source::Origin origin;
        origin.kind = i == 0 ? source::OriginKind::Explicit
                             : source::OriginKind::Cpp2vSynthesized;
        source::PhysicalPoint begin{source::FileId(0), i * 10, 1, i + 1};
        source::PhysicalPoint end{source::FileId(0), i * 10 + 1, 1, i + 2};
        origin.spelling = source::Range{begin, end, source::RangeKind::Token,
                                        std::make_pair(begin, end)};
        if (i)
            origin.anchor = source::OriginId(0);
        if (i == 1)
            origin.pointOfInstantiation =
                source::PhysicalPoint{source::FileId(0), 99, 5, 4};
        if (i == 2)
            origin.derivedFrom = {source::OriginId(1)};
        result.origins.push_back(std::move(origin));
    }
    return result;
}

std::vector<Value> templateParameters(const Built &built) {
    std::vector<Value> parameters;
    parameters.push_back(
        Value::product({Value::node(built.tempParam),
                        Value::optional(Value::node(built.tempArgType))}));
    parameters.push_back(Value::product(
        {Value::node(built.tempParam), Value::optional(std::nullopt)}));
    return parameters;
}

Built buildCore(TranslationUnitIR &unit, bool roots = true) {
    (void)unit.setSources(tables());
    Built built;
    built.atomic =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string("name"))}, {source::OriginId(0)});
    built.name = add(unit, Category::Name, Constructor::NameFromAtomic,
                     {Value::node(built.atomic)}, {source::OriginId(0)});
    built.type = add(unit, Category::Type, Constructor::TypeNamed,
                     {Value::node(built.name)}, {});
    built.expression0 =
        add(unit, Category::Expression, Constructor::ExpressionInteger,
            {Value::scalar(ScalarTerm::numeral("7")), Value::node(built.type)},
            {source::OriginId(0)});
    built.expression1 =
        add(unit, Category::Expression, Constructor::ExpressionInteger,
            {Value::scalar(ScalarTerm::numeral("7")), Value::node(built.type)},
            {source::OriginId(1), source::OriginId(2)});
    built.tempParam = add(unit, Category::TemplateParameter,
                          Constructor::TemplateParameterType,
                          {Value::scalar(ScalarTerm::string("T"))});
    built.tempArgType =
        add(unit, Category::TemplateArgument, Constructor::TemplateArgumentType,
            {Value::node(built.type)});
    built.tempArgValue = add(unit, Category::TemplateArgument,
                             Constructor::TemplateArgumentValue,
                             {Value::node(built.expression0)});
    built.globalInit =
        add(unit, Category::GlobalInitializer, Constructor::GlobalInitNone, {},
            {source::OriginId(0)});
    built.object = add(unit, Category::ObjectValue, Constructor::ObjectVariable,
                       {Value::node(built.type), Value::node(built.globalInit)},
                       {source::OriginId(0)});
    built.global =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
            {Value::node(built.type)}, {source::OriginId(1)});
    built.templateObject = add(
        unit, Category::Template, Constructor::TemplateObjectRoot,
        {Value::sequence(templateParameters(built)), Value::node(built.object)},
        {source::OriginId(1)});
    built.templateGlobal = add(
        unit, Category::Template, Constructor::TemplateGlobalRoot,
        {Value::sequence(templateParameters(built)), Value::node(built.global)},
        {source::OriginId(2)});
    if (roots) {
        (void)unit.addRoot({RootKind::Symbol, built.name, built.object});
        (void)unit.addRoot({RootKind::Type, built.name, built.global});
        (void)unit.addRoot(
            {RootKind::TemplateSymbol, built.name, built.templateObject});
        (void)unit.addRoot(
            {RootKind::TemplateType, built.name, built.templateGlobal});
    }
    return built;
}

bool contains(const std::string &text, const std::string &needle) {
    return text.find(needle) != std::string::npos;
}

bool registryComplete() {
    const auto &registry = constructorRegistry();
    const auto count = static_cast<std::size_t>(Constructor::Count);
    if (registry.size() != count)
        return false;
    std::set<Constructor> constructors;
    for (std::size_t i = 0; i < count; ++i) {
        auto constructor = static_cast<Constructor>(i);
        const auto *spec = findConstructorSpec(constructor);
        if (!spec || !spec->rocqSpelling || !*spec->rocqSpelling ||
            spec->constructor != constructor ||
            (spec->testOnly && (spec->category != Category::Auxiliary ||
                                spec->allowedRoots != 0)) ||
            !constructors.insert(spec->constructor).second)
            return false;
    }
    if (findConstructorSpec(Constructor::Count))
        return false;
    return true;
}

bool allValueShapesAndFlattening() {
    TranslationUnitIR unit;
    Built built = buildCore(unit, false);

    NodeId absent = add(unit, Category::Auxiliary, Constructor::OptionalFixture,
                        {Value::optional(std::nullopt)});
    NodeId present =
        add(unit, Category::Auxiliary, Constructor::OptionalFixture,
            {Value::optional(Value::node(built.expression0))});
    NodeId empty = add(unit, Category::Auxiliary, Constructor::SequenceFixture,
                       {Value::sequence({})});
    NodeId sequence =
        add(unit, Category::Auxiliary, Constructor::SequenceFixture,
            {Value::sequence({Value::node(built.expression0),
                              Value::node(built.expression1)})});
    NodeId product =
        add(unit, Category::Auxiliary, Constructor::ProductFixture,
            {Value::product({Value::scalar(ScalarTerm::symbol("field")),
                             Value::node(built.expression1)})});
    NodeId sum = add(unit, Category::Auxiliary, Constructor::SumFixture,
                     {Value::sum(ScalarTerm::symbol("inl"),
                                 Value::node(built.expression0))});

    NodeId nestedIdentType =
        add(unit, Category::Auxiliary, Constructor::IdentTypeList,
            {Value::sequence(
                {Value::product({Value::scalar(ScalarTerm::string("x")),
                                 Value::node(built.type)}),
                 Value::product({Value::scalar(ScalarTerm::string("y")),
                                 Value::node(built.type)})})});
    NodeId nestedNameOption =
        add(unit, Category::Auxiliary, Constructor::NameOptionalNameList,
            {Value::sequence(
                {Value::product(
                     {Value::node(built.name), Value::optional(std::nullopt)}),
                 Value::product({Value::node(built.name),
                                 Value::optional(Value::node(built.name))})})});

    NodeId indirect =
        add(unit, Category::InitializerPath, Constructor::InitIndirectPath,
            {Value::sequence({Value::product({Value::node(built.atomic),
                                              Value::node(built.name)}),
                              Value::product({Value::node(built.atomic),
                                              Value::node(built.name)})}),
             Value::node(built.atomic)});
    NodeId structureVirtuals =
        add(unit, Category::Auxiliary, Constructor::StructureVirtuals,
            {Value::sequence(
                {Value::product(
                     {Value::node(built.name), Value::optional(std::nullopt)}),
                 Value::product({Value::node(built.name),
                                 Value::optional(Value::node(built.name))})})});
    NodeId structureOverrides =
        add(unit, Category::Auxiliary, Constructor::StructureOverrides,
            {Value::sequence({Value::product(
                {Value::node(built.name), Value::node(built.name)})})});

    NodeId binary =
        add(unit, Category::Expression, Constructor::ExpressionBinary,
            {Value::scalar(ScalarTerm::symbol("Badd")),
             Value::node(built.expression0), Value::node(built.expression1),
             Value::node(built.type)});
    NodeId statementExpression =
        add(unit, Category::Statement, Constructor::StatementExpression,
            {Value::node(built.expression0)});
    NodeId returnNone =
        add(unit, Category::Statement, Constructor::StatementReturn,
            {Value::optional(std::nullopt)});
    NodeId returnSome =
        add(unit, Category::Statement, Constructor::StatementReturn,
            {Value::optional(Value::node(built.expression1))});
    NodeId statementSequence =
        add(unit, Category::Statement, Constructor::StatementSequence,
            {Value::sequence(
                {Value::node(statementExpression), Value::node(returnNone)})});

    if (failed(unit.finish()))
        return false;
    auto check = [&](NodeId node, std::vector<NodeId> wanted) {
        auto actual = unit.nodes().children(node);
        return actual && *actual == wanted;
    };
    if (!check(absent, {}) || !check(present, {built.expression0}) ||
        !check(empty, {}) ||
        !check(sequence, {built.expression0, built.expression1}) ||
        !check(product, {built.expression1}) ||
        !check(sum, {built.expression0}) ||
        !check(nestedIdentType, {built.type, built.type}) ||
        !check(nestedNameOption, {built.name, built.name, built.name}) ||
        !check(indirect, {built.atomic, built.name, built.atomic, built.name,
                          built.atomic}) ||
        !check(structureVirtuals, {built.name, built.name, built.name}) ||
        !check(structureOverrides, {built.name, built.name}) ||
        !check(binary, {built.expression0, built.expression1, built.type}) ||
        !check(statementExpression, {built.expression0}) ||
        !check(returnNone, {}) || !check(returnSome, {built.expression1}) ||
        !check(statementSequence, {statementExpression, returnNone}))
        return false;

    SemanticRocqEmitter semantic;
    auto expression0 = semantic.renderNode(unit, built.expression0);
    auto expression1 = semantic.renderNode(unit, built.expression1);
    auto emptyText = semantic.renderNode(unit, empty);
    auto sequenceText = semantic.renderNode(unit, sequence);
    auto productText = semantic.renderNode(unit, product);
    auto absentText = semantic.renderNode(unit, absent);
    auto presentText = semantic.renderNode(unit, present);
    auto sumText = semantic.renderNode(unit, sum);
    auto indirectText = semantic.renderNode(unit, indirect);
    auto typeText = semantic.renderNode(unit, built.type);
    auto binaryText = semantic.renderNode(unit, binary);
    auto statementExpressionText =
        semantic.renderNode(unit, statementExpression);
    auto returnNoneText = semantic.renderNode(unit, returnNone);
    auto returnSomeText = semantic.renderNode(unit, returnSome);
    auto statementSequenceText = semantic.renderNode(unit, statementSequence);
    if (!expression0 || !expression1 || !emptyText || !sequenceText ||
        !productText || !absentText || !presentText || !sumText ||
        !indirectText || !typeText || !binaryText || !statementExpressionText ||
        !returnNoneText || !returnSomeText || !statementSequenceText)
        return false;
    if (*emptyText != "(IR_sequence nil)" ||
        *sequenceText != "(IR_sequence (" + *expression0 +
                             " :: " + *expression1 + " :: nil))" ||
        *productText != "(IR_product (field, " + *expression1 + "))" ||
        *absentText != "(IR_optional None)" ||
        *presentText != "(IR_optional (Some " + *expression0 + "))" ||
        *sumText != "(IR_sum (inl " + *expression0 + "))" ||
        *binaryText != "(core.Ebinop Badd " + *expression0 + " " +
                           *expression1 + " " + *typeText + ")" ||
        *statementExpressionText != "(Sexpr " + *expression0 + ")" ||
        *returnNoneText != "(Sreturn None)" ||
        *returnSomeText != "(Sreturn (Some " + *expression1 + "))" ||
        *statementSequenceText != "(Sseq (" + *statementExpressionText +
                                      " :: " + *returnNoneText + " :: nil))")
        return false;
    if (!contains(*indirectText, ":: nil) (Nid"))
        return false;

    LocationRocqEmitter location;
    auto expression0Tree = location.renderTree(unit, built.expression0);
    auto expression1Tree = location.renderTree(unit, built.expression1);
    auto absentTree = location.renderTree(unit, absent);
    auto presentTree = location.renderTree(unit, present);
    auto sequenceTree = location.renderTree(unit, sequence);
    auto productTree = location.renderTree(unit, product);
    auto sumTree = location.renderTree(unit, sum);
    auto identTypeTree = location.renderTree(unit, nestedIdentType);
    auto nameOptionTree = location.renderTree(unit, nestedNameOption);
    auto typeTree = location.renderTree(unit, built.type);
    auto nameTree = location.renderTree(unit, built.name);
    if (!expression0Tree || !expression1Tree || !absentTree || !presentTree ||
        !sequenceTree || !productTree || !sumTree || !identTypeTree ||
        !nameOptionTree || !typeTree || !nameTree)
        return false;
    return *absentTree == "(LocNode nil nil)" &&
           *presentTree == "(LocNode nil (" + *expression0Tree + " :: nil))" &&
           *sequenceTree == "(LocNode nil (" + *expression0Tree +
                                " :: " + *expression1Tree + " :: nil))" &&
           *productTree == "(LocNode nil (" + *expression1Tree + " :: nil))" &&
           *sumTree == "(LocNode nil (" + *expression0Tree + " :: nil))" &&
           *identTypeTree == "(LocNode nil (" + *typeTree + " :: " + *typeTree +
                                 " :: nil))" &&
           *nameOptionTree == "(LocNode nil (" + *nameTree +
                                  " :: " + *nameTree + " :: " + *nameTree +
                                  " :: nil))";
}

bool originsOccurrencesAndTrees() {
    TranslationUnitIR unit;
    Built built = buildCore(unit);
    if (failed(unit.finish()))
        return false;
    SemanticRocqEmitter semantic;
    auto first = semantic.renderNode(unit, built.expression0);
    auto second = semantic.renderNode(unit, built.expression1);
    LocationRocqEmitter location;
    auto firstTree = location.renderTree(unit, built.expression0);
    auto secondTree = location.renderTree(unit, built.expression1);
    auto typeTree = location.renderTree(unit, built.type);
    return first && second && *first == *second && firstTree && secondTree &&
           typeTree &&
           contains(*firstTree, "LocNode ((Build_origin_id 0) :: nil)") &&
           contains(*secondTree,
                    "LocNode ((Build_origin_id 1) :: (Build_origin_id 2) :: "
                    "nil)") &&
           contains(*typeTree, "LocNode nil") && *firstTree != *secondTree;
}

bool directRootsAndDeterminism() {
    TranslationUnitIR unit;
    Built built = buildCore(unit);
    if (failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    auto first = emitter.emit(unit);
    auto second = emitter.emit(unit);
    auto ordinary = emitter.emitOrdinary(unit);
    auto templates = emitter.emitTemplates(unit);
    SemanticRocqEmitter noSharing({false});
    auto unshared = noSharing.emit(unit);
    LocationRocqEmitter locations;
    auto locationFirst = locations.emit(unit);
    auto locationSecond = locations.emit(unit);
    LocationRocqEmitter ordinaryLocations({false});
    auto locationOrdinaryOnly = ordinaryLocations.emit(unit);
    auto templateObject = emitter.renderNode(unit, built.templateObject);
    if (!first || !second || !ordinary || !templates || !unshared ||
        !locationFirst || !locationSecond || !locationOrdinaryOnly ||
        !templateObject || *first != *second || *first != *unshared ||
        *locationFirst != *locationSecond)
        return false;
    const std::size_t locationEvents =
        locationFirst->find("(* compact root events:");
    if (locationEvents == std::string::npos)
        return false;
    const std::string eventSection = locationFirst->substr(locationEvents);
    auto ordered = [](const std::string &text,
                      std::initializer_list<const char *> needles) {
        std::size_t position = 0;
        for (const char *needle : needles) {
            auto found = text.find(needle, position);
            if (found == std::string::npos)
                return false;
            position = found + std::char_traits<char>::length(needle);
        }
        return true;
    };
    return ordered(*first,
                   {"(Dobj_value ", "(Dglob_decl ", "(Dtemplated_obj_value ",
                    "(Dtemplated_glob_decl "}) &&
           contains(*ordinary, "(Dobj_value ") &&
           contains(*ordinary, "(Dglob_decl ") &&
           !contains(*ordinary, "Dtemplated_") &&
           contains(*templates, "(Dtemplated_obj_value ") &&
           contains(*templates, "(Dtemplated_glob_decl ") &&
           !contains(*templates, "(Dobj_value ") &&
           !contains(*templates, "(Dglob_decl ") &&
           contains(
               *locationOrdinaryOnly,
               "compact root events: 2 selected; 1 singleton; 1 residual") &&
           contains(*locationOrdinaryOnly, "(CIL(") &&
           contains(*locationOrdinaryOnly, "(CRT(") &&
           contains(
               eventSection,
               "compact root events: 4 selected; 3 singleton; 1 residual") &&
           !contains(eventSection, "(Ovar ") &&
           !contains(eventSection, "(Template ") &&
           contains(*first, "(Ovar ") && contains(*first, "Gtypedef") &&
           !contains(*first, "Eliteral") && !contains(*first, "Ebinary") &&
           !contains(*first, "Oexpression") &&
           contains(*templateObject, "(Ptype \"T\"), (Some (Atype ") &&
           contains(*templateObject, "(Ptype \"T\"), None)") &&
           contains(*templateObject, ":: nil) (Ovar ") &&
           contains(*locationFirst, "source_files") &&
           contains(*locationFirst, "presumed_filenames") &&
           contains(*locationFirst, "physical_points") &&
           contains(*locationFirst, "encoded_origins") &&
           contains(*locationFirst, "source_provenance") &&
           contains(*locationFirst, "location_shapes") &&
           contains(*locationFirst, "location_nodes") &&
           contains(*locationFirst, "source_location_dag") &&
           contains(*locationFirst, "Build_source_file") &&
           contains(*locationFirst, "Encoded.Build_encoded_origin") &&
           contains(*locationFirst, "Encoded.Build_indexed_table") &&
           contains(*locationFirst, "Encoded.Build_encoded_origin") &&
           !contains(*locationFirst, "source_origins : list source_origin") &&
           !contains(*locationFirst, "Build_source_origin");
}

bool completeNonRootEvents() {
    TranslationUnitIR unit;
    Built built = buildCore(unit, false);
    NodeId aliasValue = add(
        unit, Category::Template, Constructor::TemplateAliasValue,
        {Value::sequence(templateParameters(built)), Value::node(built.type)});
    NodeId preinst = add(unit, Category::TemplatePreInstantiation,
                         Constructor::TemplatePreInstantiationValue,
                         {Value::node(built.name),
                          Value::sequence({Value::node(built.tempArgType),
                                           Value::node(built.tempArgValue)})});
    (void)unit.addNonRoot(NamespaceAliasEvent{
        std::optional<NodeId>(built.name), built.name, {source::OriginId(0)}});
    (void)unit.addNonRoot(
        NamespaceAliasEvent{std::nullopt, built.name, {source::OriginId(0)}});
    (void)unit.addNonRoot(StaticAssertEvent{
        ScalarTerm::string("ok"), built.expression0, {source::OriginId(1)}});
    (void)unit.addNonRoot(TemplateAliasEvent{built.name, aliasValue});
    (void)unit.addNonRoot(TemplateInstanceEvent{built.name, preinst});
    if (failed(unit.finish()))
        return false;
    auto output = SemanticRocqEmitter().emit(unit);
    auto ordinary = SemanticRocqEmitter().emitOrdinary(unit);
    auto templates = SemanticRocqEmitter().emitTemplates(unit);
    auto alias = SemanticRocqEmitter().renderNode(unit, aliasValue);
    auto instance = SemanticRocqEmitter().renderNode(unit, preinst);
    return output && ordinary && templates && alias && instance &&
           contains(*output, "Dusing_namespace") &&
           contains(*output, "Dglobal_using_namespace") &&
           !contains(*output, "Dnamespace_alias") &&
           contains(*output, "Dstatic_assert (Some \"ok\")") &&
           contains(*output, "Dtemplated_type_alias") &&
           contains(*output, "Dtemplate_preinst") &&
           contains(*ordinary, "Dusing_namespace") &&
           contains(*ordinary, "Dglobal_using_namespace") &&
           contains(*ordinary, "Dstatic_assert") &&
           !contains(*ordinary, "Dtemplated_type_alias") &&
           !contains(*ordinary, "Dtemplate_preinst") &&
           contains(*templates, "Dtemplated_type_alias") &&
           contains(*templates, "Dtemplate_preinst") &&
           !contains(*templates, "Dusing_namespace") &&
           !contains(*templates, "Dstatic_assert") &&
           contains(*alias, "(Ptype \"T\"), (Some (Atype ") &&
           contains(*alias, "(Ptype \"T\"), None)") &&
           contains(*alias, ":: nil) (Tnamed ") &&
           contains(*instance, "(TPreInst (Nglobal ") &&
           contains(*instance, "(Atype ") &&
           contains(*instance, " :: (Avalue ") &&
           !contains(*instance, "TPreInst ((");
}

bool escaping() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables(0));
    NodeId atomic =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string(
                std::string("quote\" slash\\ (* *) ") + "\xCF\x83"))});
    NodeId boolean =
        add(unit, Category::Expression, Constructor::ExpressionBoolean,
            {Value::scalar(ScalarTerm::boolean(true))});
    add(unit, Category::Name, Constructor::NameFromAtomic,
        {Value::node(atomic)});
    if (failed(unit.finish()))
        return false;
    auto text = SemanticRocqEmitter().renderNode(unit, atomic);
    auto booleanText = SemanticRocqEmitter().renderNode(unit, boolean);
    return text && booleanText && contains(*text, "quote\"\"") &&
           contains(*text, "slash\\") && contains(*text, "(* *)") &&
           contains(*text, "\xCF\x83") && contains(*booleanText, " true)");
}

bool emptyTablesAndEvents() {
    TranslationUnitIR unit;
    if (failed(unit.finish()))
        return false;
    auto semantic = SemanticRocqEmitter().emit(unit);
    auto location = LocationRocqEmitter().emit(unit);
    return semantic && semantic->empty() && location &&
           contains(*location,
                    "Require Import skylabs.lang.cpp.syntax.source_location") &&
           contains(*location, "source_files : list source_file := nil") &&
           contains(*location, "presumed_filenames : Encoded.indexed_table") &&
           contains(*location, "encoded_origins : Encoded.indexed_table") &&
           contains(
               *location,
               "compact root events: 0 selected; 0 singleton; 0 residual") &&
           contains(*location,
                    "singleton_root_events : singleton_root_locations") &&
           contains(*location,
                    "residual_root_events : list "
                    "Construction.indexed_located_root_event := nil") &&
           !contains(*location, "source_origins : list source_origin") &&
           contains(*location, "Definition source_locations : source_map") &&
           !contains(*location, "source_location_result");
}

bool rootEventEncoding() {
    namespace root_event_encoding = ir::root_event::encoding;
    TranslationUnitIR unfinished;
    if (!failed(root_event_encoding::encode(unfinished, true)))
        return false;

    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    const NodeId duplicateAtomic0 =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string("duplicate"))},
            {source::OriginId(0)});
    const NodeId duplicateName0 =
        add(unit, Category::Name, Constructor::NameFromAtomic,
            {Value::node(duplicateAtomic0)}, {source::OriginId(0)});
    const NodeId duplicateAtomic1 =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string("duplicate"))},
            {source::OriginId(1)});
    const NodeId duplicateName1 =
        add(unit, Category::Name, Constructor::NameFromAtomic,
            {Value::node(duplicateAtomic1)}, {source::OriginId(1)});
    const NodeId nearAtomic =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string("near"))}, {source::OriginId(2)});
    const NodeId nearName =
        add(unit, Category::Name, Constructor::NameFromAtomic,
            {Value::node(nearAtomic)}, {source::OriginId(2)});
    const NodeId typedefAtomic = add(
        unit, Category::AtomicName, Constructor::AtomicIdentifier,
        {Value::scalar(ScalarTerm::string("typedef"))}, {source::OriginId(0)});
    const NodeId typedefName =
        add(unit, Category::Name, Constructor::NameFromAtomic,
            {Value::node(typedefAtomic)}, {source::OriginId(0)});
    const NodeId boolean = add(unit, Category::Type, Constructor::TypeBoolean,
                               {}, {source::OriginId(0)});
    const NodeId initializer =
        add(unit, Category::GlobalInitializer, Constructor::GlobalInitNone, {},
            {source::OriginId(0)});
    const NodeId object =
        add(unit, Category::ObjectValue, Constructor::ObjectVariable,
            {Value::node(boolean), Value::node(initializer)},
            {source::OriginId(0)});
    const NodeId globalType =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalType, {},
            {source::OriginId(0)});
    const NodeId typedefType =
        add(unit, Category::Type, Constructor::TypeNamed,
            {Value::node(typedefName)}, {source::OriginId(0)});
    const NodeId globalTypedef =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
            {Value::node(typedefType)}, {source::OriginId(0)});
    const NodeId templateObject =
        add(unit, Category::Template, Constructor::TemplateObjectRoot,
            {Value::sequence({}), Value::node(object)}, {source::OriginId(0)});
    const NodeId templateType = add(
        unit, Category::Template, Constructor::TemplateGlobalRoot,
        {Value::sequence({}), Value::node(globalType)}, {source::OriginId(0)});
    auto share = unit.addShareClass(ShareClassKind::Name);
    if (!duplicateAtomic0.valid() || !duplicateName0.valid() ||
        !duplicateAtomic1.valid() || !duplicateName1.valid() ||
        !nearAtomic.valid() || !nearName.valid() || !typedefAtomic.valid() ||
        !typedefName.valid() || !boolean.valid() || !initializer.valid() ||
        !object.valid() || !globalType.valid() || !typedefType.valid() ||
        !globalTypedef.valid() || !templateObject.valid() ||
        !templateType.valid() || !share ||
        failed(arena.setShareClass(duplicateName0, *share)) ||
        failed(unit.addRoot({RootKind::Symbol, duplicateName0, object})) ||
        failed(unit.addRoot({RootKind::Symbol, duplicateName1, object})) ||
        failed(unit.addRoot({RootKind::Symbol, nearName, object})) ||
        failed(unit.addRoot({RootKind::Type, duplicateName0, globalType})) ||
        failed(unit.addRoot({RootKind::Type, typedefName, globalTypedef})) ||
        failed(unit.addRoot(
            {RootKind::TemplateSymbol, nearName, templateObject})) ||
        failed(
            unit.addRoot({RootKind::TemplateType, nearName, templateType})) ||
        failed(unit.finish()))
        return false;

    auto all = root_event_encoding::encode(unit, true);
    auto ordinary = root_event_encoding::encode(unit, false);
    auto collided = root_event_encoding::encode(
        unit, true, root_event_encoding::EncodeOptions{true});
    if (!all || !ordinary || !collided)
        return false;
    using EventClass = root_event_encoding::EventClass;
    const std::vector<EventClass> expectedAll{
        EventClass::Residual,  EventClass::Residual, EventClass::Singleton,
        EventClass::Singleton, EventClass::Residual, EventClass::Singleton,
        EventClass::Singleton};
    const std::vector<EventClass> expectedOrdinary{
        EventClass::Residual,  EventClass::Residual, EventClass::Singleton,
        EventClass::Singleton, EventClass::Residual, EventClass::Excluded,
        EventClass::Excluded};
    const auto exactStats =
        [](const root_event_encoding::EncodingStats &stats,
           std::size_t selected, std::size_t singleton, std::size_t residual,
           std::size_t duplicateGroups, std::size_t duplicateEvents,
           std::size_t typedefResiduals) {
            return stats.selectedEvents == selected &&
                   stats.selectedEvents ==
                       stats.singletonEvents + stats.residualEvents &&
                   stats.singletonEvents == singleton &&
                   stats.residualEvents == residual &&
                   stats.duplicateGroups == duplicateGroups &&
                   stats.duplicateEvents == duplicateEvents &&
                   stats.conservativeTypedefResiduals == typedefResiduals;
        };
    auto emitted = LocationRocqEmitter().emit(unit);
    if (!emitted)
        return false;
    const std::size_t eventStart = emitted->find("(* compact root events:");
    if (eventStart == std::string::npos)
        return false;
    const std::string events = emitted->substr(eventStart);
    const auto count = [&](const std::string &needle) {
        std::size_t result = 0;
        for (std::size_t position = 0;
             (position = events.find(needle, position)) != std::string::npos;
             position += needle.size())
            ++result;
        return result;
    };
    return all->eventClasses == expectedAll &&
           collided->eventClasses == expectedAll &&
           ordinary->eventClasses == expectedOrdinary &&
           exactStats(all->stats, 7, 4, 3, 1, 2, 1) &&
           exactStats(collided->stats, 7, 4, 3, 1, 2, 1) &&
           exactStats(ordinary->stats, 5, 2, 3, 1, 2, 1) &&
           contains(
               events,
               "7 selected; 4 singleton; 3 residual; 1 duplicate groups") &&
           count("(CRS(") == 2 && count("(CRT(") == 1 && count("(CIL(") == 4 &&
           count("(Ovar ") == 2;
}

bool sourceInterningAndRendering() {
    {
        source::TableBuilder distinct;
        source::File equal{"same-name.hpp", std::nullopt,
                           source::FileKind::User, false, std::nullopt};
        auto first = distinct.appendDistinctFile(equal);
        auto second = distinct.appendDistinctFile(equal);
        auto finished = std::move(distinct).finish();
        if (!first || !second || *first == *second || !finished ||
            finished->files.size() != 2 ||
            !(finished->files[first->value()] ==
              finished->files[second->value()]))
            return false;
    }

    {
        source::TableBuilder indexed;
        auto fileId =
            indexed.internFile({"many.cpp", std::nullopt,
                                source::FileKind::User, true, std::nullopt});
        if (!fileId)
            return false;
        auto originAt = [file = *fileId](std::uint32_t index) {
            source::Origin origin;
            const source::PhysicalPoint begin{file, index * 2ULL, index + 1, 1};
            const source::PhysicalPoint end{file, index * 2ULL + 1, index + 1,
                                            2};
            origin.spelling =
                source::Range{begin, end, source::RangeKind::Token,
                              std::make_pair(begin, end)};
            return origin;
        };
        constexpr std::uint32_t originCount = 8192;
        for (std::uint32_t index = 0; index < originCount; ++index) {
            auto id = indexed.internOrigin(originAt(index));
            if (!id || id->value() != index)
                return false;
        }
        for (std::uint32_t index = originCount; index-- > 0;) {
            auto id = indexed.internOrigin(originAt(index));
            if (!id || id->value() != index)
                return false;
        }
        auto finished = std::move(indexed).finish();
        if (!finished || finished->origins.size() != originCount)
            return false;
    }

    source::TableBuilder builder;
    source::File file{"a\"\\.cpp", std::string("requested(*.cpp"),
                      source::FileKind::User, true, std::nullopt};
    auto file0 = builder.internFile(file);
    auto file0Again = builder.internFile(file);
    if (!file0 || !file0Again || *file0 != *file0Again || file0->value() != 0)
        return false;
    source::Origin origin;
    origin.kind = source::OriginKind::Explicit;
    origin.spelling = source::Range{
        source::PhysicalPoint{*file0, 0, 1, 2},
        source::PhysicalPoint{*file0, 1, 3, 4}, source::RangeKind::Character,
        std::make_pair(source::PhysicalPoint{*file0, 2, 5, 6},
                       source::PhysicalPoint{*file0, 3, 7, 8})};
    origin.expansion = source::Range{
        source::PhysicalPoint{*file0, 10, 11, 12},
        source::PhysicalPoint{*file0, 13, 14, 15}, source::RangeKind::Token,
        std::make_pair(source::PhysicalPoint{*file0, 16, 17, 18},
                       source::PhysicalPoint{*file0, 19, 20, 21})};
    origin.presumedBegin = source::PresumedPoint{"logical-begin.cpp", 22, 23};
    origin.presumedEnd = source::PresumedPoint{"logical-end.cpp", 24, 25};
    const source::Range macroSpelling{source::PhysicalPoint{*file0, 30, 31, 32},
                                      source::PhysicalPoint{*file0, 33, 34, 35},
                                      source::RangeKind::Character,
                                      std::nullopt};
    const source::Range macroExpansion{
        source::PhysicalPoint{*file0, 40, 41, 42},
        source::PhysicalPoint{*file0, 43, 44, 45}, source::RangeKind::Token,
        std::make_pair(source::PhysicalPoint{*file0, 46, 47, 48},
                       source::PhysicalPoint{*file0, 49, 50, 51})};
    origin.macroStack.push_back({std::string("MACRO"),
                                 source::MacroOriginKind::Argument,
                                 macroSpelling, macroExpansion});
    origin.pointOfInstantiation = source::PhysicalPoint{*file0, 60, 61, 62};
    auto origin0 = builder.internOrigin(origin);
    auto origin0Again = builder.internOrigin(origin);
    if (!origin0 || !origin0Again || *origin0 != *origin0Again)
        return false;
    std::vector<source::OriginId> ordered{source::OriginId(7)};
    source::appendOriginStable(ordered, *origin0);
    source::appendOriginStable(ordered, source::OriginId(7));
    source::appendOriginsStable(
        ordered, {*origin0, source::OriginId(9), source::OriginId(7)});
    if (ordered != std::vector<source::OriginId>(
                       {source::OriginId(7), *origin0, source::OriginId(9)}))
        return false;
    auto finished = std::move(builder).finish();
    if (!finished || finished->files.size() != 1 ||
        finished->origins.size() != 1)
        return false;

    TranslationUnitIR unit;
    (void)unit.setSources(std::move(*finished));
    NodeId atomic =
        add(unit, Category::AtomicName, Constructor::AtomicIdentifier,
            {Value::scalar(ScalarTerm::string("n"))}, {*origin0});
    NodeId name = add(unit, Category::Name, Constructor::NameFromAtomic,
                      {Value::node(atomic)}, {*origin0});
    NodeId type = add(unit, Category::Type, Constructor::TypeNamed,
                      {Value::node(name)}, {*origin0});
    NodeId global =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
            {Value::node(type)}, {*origin0});
    (void)unit.addRoot({RootKind::Type, name, global});
    if (failed(unit.finish()))
        return false;
    auto text = LocationRocqEmitter().emit(unit);
    const std::string expectedFile =
        "(Build_source_file \"a\"\"\\.cpp\" (Some \"requested(*.cpp\") "
        "FKUser true None)";
    const std::string expectedRange0 =
        "(Encoded.EncodedGeneralRange 0 1 CharacterRange 2 3)";
    const std::string expectedRange1 =
        "(Encoded.EncodedGeneralRange 4 5 TokenRange 6 7)";
    const std::string expectedFrame =
        "(Encoded.Build_encoded_macro_frame (Some \"MACRO\") "
        "MacroArgument (Some 2) (Some 3))";
    const std::string expectedOrigin =
        "(Encoded.Build_encoded_origin ExplicitOrigin (Some 0) (Some 1) "
        "(Some 0) (Some 1) ((Encoded.InlineMacroFrame " +
        expectedFrame + ") :: nil) (Some 14) None nil)";
    return text && contains(*text, expectedFile) &&
           contains(*text, expectedRange0) && contains(*text, expectedRange1) &&
           contains(*text, expectedFrame) && contains(*text, expectedOrigin) &&
           contains(*text, "Encoded.Build_indexed_provenance "
                           "presumed_filenames physical_points presumed_points "
                           "source_ranges macro_frames encoded_origins") &&
           contains(*text, "#[local] Close Scope array_scope") &&
           text->find("Require Import skylabs.lang.cpp.parser.") >
               text->find("#[local] Close Scope array_scope") &&
           !contains(*text, "source_origins : list source_origin") &&
           !contains(*text, "Build_source_origin") &&
           !contains(*text, "source_file_physical_name :=") &&
           !contains(*text, "point_file :=") &&
           !contains(*text, "presumed_file :=") &&
           !contains(*text, "range_begin :=") &&
           !contains(*text, "macro_name :=") &&
           !contains(*text, "origin_class :=") &&
           contains(*text, "Encoded.Build_encoded_location_node") &&
           contains(*text, "Encoded.Build_indexed_location_dag") &&
           contains(*text, "Construction.build_lazy_compact_indexed_dag_source_"
                           "map_or_fail") &&
           !contains(*text, "Build_origin_id") && !contains(*text, "LocNode");
}

bool locationDagEncoding() {
    namespace location_encoding = ir::location::encoding;

    TranslationUnitIR unit;
    Built built = buildCore(unit);
    NodeId differentlyLocatedGlobal =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
            {Value::node(built.type)}, {source::OriginId(2)});
    NodeId exactDuplicateGlobal =
        add(unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
            {Value::node(built.type)}, {source::OriginId(1)});
    (void)unit.addRoot({RootKind::Type, built.name, differentlyLocatedGlobal});
    (void)unit.addRoot({RootKind::Type, built.name, exactDuplicateGlobal});

    NodeId expressionAB =
        add(unit, Category::Expression, Constructor::ExpressionComma,
            {Value::node(built.expression0), Value::node(built.expression1)});
    NodeId expressionBA =
        add(unit, Category::Expression, Constructor::ExpressionComma,
            {Value::node(built.expression1), Value::node(built.expression0)});
    NodeId initializerAB =
        add(unit, Category::GlobalInitializer,
            Constructor::GlobalInitExpression, {Value::node(expressionAB)});
    NodeId initializerBA =
        add(unit, Category::GlobalInitializer,
            Constructor::GlobalInitExpression, {Value::node(expressionBA)});
    NodeId objectAB =
        add(unit, Category::ObjectValue, Constructor::ObjectVariable,
            {Value::node(built.type), Value::node(initializerAB)});
    NodeId objectBA =
        add(unit, Category::ObjectValue, Constructor::ObjectVariable,
            {Value::node(built.type), Value::node(initializerBA)});
    (void)unit.addRoot({RootKind::Symbol, built.name, objectAB});
    (void)unit.addRoot({RootKind::Symbol, built.name, objectBA});

    NodeId orderedOrigins = add(
        unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
        {Value::node(built.type)}, {source::OriginId(0), source::OriginId(1)});
    NodeId reversedOrigins = add(
        unit, Category::GlobalDeclaration, Constructor::GlobalTypedef,
        {Value::node(built.type)}, {source::OriginId(1), source::OriginId(0)});
    (void)unit.addRoot({RootKind::Type, built.name, orderedOrigins});
    (void)unit.addRoot({RootKind::Type, built.name, reversedOrigins});
    if (failed(unit.finish()))
        return false;

    auto encoded = location_encoding::encode(unit, true);
    auto collisionEncoded = location_encoding::encode(
        unit, true, location_encoding::EncodeOptions{true});
    auto ordinaryOnly = location_encoding::encode(unit, false);
    if (!encoded || !collisionEncoded || !ordinaryOnly ||
        encoded->eventRoots.size() != 10 ||
        collisionEncoded->eventRoots != encoded->eventRoots ||
        collisionEncoded->shapes != encoded->shapes ||
        collisionEncoded->nodes != encoded->nodes ||
        encoded->stats.selectedRootEvents != 10 ||
        encoded->stats.visitedSemanticNodes <=
            encoded->stats.locationNodeRows ||
        ordinaryOnly->stats.selectedRootEvents != 8 ||
        ordinaryOnly->eventRoots[2] || ordinaryOnly->eventRoots[3])
        return false;

    auto root = [&](std::size_t index)
        -> const std::optional<location_encoding::EncodedRoot> & {
        return encoded->eventRoots[index];
    };
    if (!root(1) || !root(4) || !root(5) || !root(6) || !root(7) || !root(8) ||
        !root(9) || root(1)->shape != root(4)->shape ||
        root(1)->node == root(4)->node || root(1)->node != root(5)->node ||
        root(6)->shape != root(7)->shape || root(6)->node == root(7)->node ||
        root(8)->shape != root(9)->shape || root(8)->node == root(9)->node)
        return false;

    const auto &ordered = encoded->nodes[root(8)->node.value()].origins;
    const auto &reversed = encoded->nodes[root(9)->node.value()].origins;
    if (ordered != std::vector<source::OriginId>(
                       {source::OriginId(0), source::OriginId(1)}) ||
        reversed != std::vector<source::OriginId>(
                        {source::OriginId(1), source::OriginId(0)}))
        return false;

    for (std::size_t index = 0; index < encoded->shapes.size(); ++index)
        for (location_encoding::ShapeId child : encoded->shapes[index].children)
            if (child.value() >= index)
                return false;
    for (std::size_t index = 0; index < encoded->nodes.size(); ++index)
        for (location_encoding::LocationNodeId child :
             encoded->nodes[index].children)
            if (child.value() >= index)
                return false;

    auto badNodeEdge = *encoded;
    auto nodeWithChildren =
        std::find_if(badNodeEdge.nodes.rbegin(), badNodeEdge.nodes.rend(),
                     [](const auto &node) { return !node.children.empty(); });
    if (nodeWithChildren == badNodeEdge.nodes.rend())
        return false;
    const std::size_t nodeIndex = static_cast<std::size_t>(
        std::distance(nodeWithChildren, badNodeEdge.nodes.rend()) - 1);
    nodeWithChildren->children[0] = location_encoding::LocationNodeId(
        static_cast<std::uint32_t>(nodeIndex));
    if (!failed(location_encoding::validate(badNodeEdge)))
        return false;

    auto badShapeEdge = *encoded;
    auto shapeWithChildren =
        std::find_if(badShapeEdge.shapes.rbegin(), badShapeEdge.shapes.rend(),
                     [](const auto &shape) { return !shape.children.empty(); });
    if (shapeWithChildren == badShapeEdge.shapes.rend())
        return false;
    const std::size_t shapeIndex = static_cast<std::size_t>(
        std::distance(shapeWithChildren, badShapeEdge.shapes.rend()) - 1);
    shapeWithChildren->children[0] =
        location_encoding::ShapeId(static_cast<std::uint32_t>(shapeIndex));
    if (!failed(location_encoding::validate(badShapeEdge)))
        return false;

    auto badOrigin = *encoded;
    badOrigin.nodes[root(1)->node.value()].origins = {source::OriginId(99)};
    if (!failed(location_encoding::validate(badOrigin)))
        return false;

    auto badRootShape = *encoded;
    badRootShape.eventRoots[1]->shape = root(4)->shape;
    if (badRootShape.eventRoots[1]->shape ==
        badRootShape.nodes[badRootShape.eventRoots[1]->node.value()].shape) {
        badRootShape.eventRoots[1]->shape = location_encoding::ShapeId(
            static_cast<std::uint32_t>(badRootShape.shapes.size()));
    }
    return failed(location_encoding::validate(badRootShape));
}

bool sourceEncoding() {
    using namespace source::encoding;

    source::Tables source;
    source.files.push_back({"fixture.cpp", std::nullopt, source::FileKind::User,
                            true, std::nullopt});
    const source::FileId file(0);
    const source::PhysicalPoint a{file, 1, 2, 3};
    const source::PhysicalPoint b{file, 4, 5, 6};
    const source::PhysicalPoint c{file, 7, 8, 9};
    const source::PhysicalPoint d{file, 10, 11, 12};
    const source::Range raw{a, std::nullopt, source::RangeKind::Character,
                            std::nullopt};
    const source::Range sameBegin{a, b, source::RangeKind::Token,
                                  std::make_pair(a, b)};
    const source::Range general{a, b, source::RangeKind::Character,
                                std::make_pair(c, d)};
    const source::MacroFrame shared{"MACRO", source::MacroOriginKind::Argument,
                                    sameBegin, general};
    const source::MacroFrame distinct{"OTHER", source::MacroOriginKind::Body,
                                      raw, sameBegin};

    source::Origin first;
    first.kind = source::OriginKind::Explicit;
    first.spelling = raw;
    first.expansion = sameBegin;
    first.presumedBegin = source::PresumedPoint{"logical.cpp", 20, 21};
    source::Origin second;
    second.kind = source::OriginKind::Implicit;
    second.spelling = general;
    second.presumedEnd = source::PresumedPoint{"other.cpp", 22, 23};
    second.macroStack = {shared, distinct};
    second.pointOfInstantiation = a;
    second.anchor = source::OriginId(0);
    second.derivedFrom = {source::OriginId(0)};
    source::Origin third;
    third.kind = source::OriginKind::Inherited;
    third.expansion = sameBegin;
    third.presumedBegin = source::PresumedPoint{"logical.cpp", 24, 25};
    third.macroStack = {shared};
    third.anchor = source::OriginId(1);
    third.derivedFrom = {source::OriginId(1), source::OriginId(0)};
    source.origins = {first, second, third};

    const std::vector<std::string> expectedFilenames{"logical.cpp",
                                                     "other.cpp"};
    const std::vector<source::PhysicalPoint> expectedPoints{a, b, c, d};
    const std::vector<EncodedPresumedPoint> expectedPresumed{
        {FilenameId(0), 20, 21},
        {FilenameId(1), 22, 23},
        {FilenameId(0), 24, 25},
    };
    const std::vector<EncodedRange> expectedRanges{
        RawRange{PhysicalPointId(0), std::nullopt,
                 source::RangeKind::Character},
        SameBeginNormalizedRange{PhysicalPointId(0), PhysicalPointId(1),
                                 source::RangeKind::Token, PhysicalPointId(1)},
        GeneralNormalizedRange{PhysicalPointId(0), PhysicalPointId(1),
                               source::RangeKind::Character, PhysicalPointId(2),
                               PhysicalPointId(3)},
    };
    const std::vector<EncodedMacroFrame> expectedFrames{
        {std::string("MACRO"), source::MacroOriginKind::Argument, RangeId(1),
         RangeId(2)},
        {std::string("OTHER"), source::MacroOriginKind::Body, RangeId(0),
         RangeId(1)},
    };
    std::vector<EncodedOrigin> expectedOrigins(3);
    expectedOrigins[0].kind = source::OriginKind::Explicit;
    expectedOrigins[0].spelling = RangeId(0);
    expectedOrigins[0].expansion = RangeId(1);
    expectedOrigins[0].presumedBegin = PresumedPointId(0);
    expectedOrigins[1].kind = source::OriginKind::Implicit;
    expectedOrigins[1].spelling = RangeId(2);
    expectedOrigins[1].presumedEnd = PresumedPointId(1);
    expectedOrigins[1].macroStack = {MacroFrameId(0), MacroFrameId(1)};
    expectedOrigins[1].pointOfInstantiation = PhysicalPointId(0);
    expectedOrigins[1].anchor = source::OriginId(0);
    expectedOrigins[1].derivedFrom = {source::OriginId(0)};
    expectedOrigins[2].kind = source::OriginKind::Inherited;
    expectedOrigins[2].expansion = RangeId(1);
    expectedOrigins[2].presumedBegin = PresumedPointId(2);
    expectedOrigins[2].macroStack = {MacroFrameId(0)};
    expectedOrigins[2].anchor = source::OriginId(1);
    expectedOrigins[2].derivedFrom = {source::OriginId(1), source::OriginId(0)};

    auto encoded = encode(source);
    auto repeated = encode(source);
    if (!encoded || !repeated ||
        encoded->presumedFilenames != expectedFilenames ||
        encoded->physicalPoints != expectedPoints ||
        encoded->presumedPoints != expectedPresumed ||
        encoded->ranges != expectedRanges ||
        encoded->macroFrames != expectedFrames ||
        encoded->origins != expectedOrigins ||
        repeated->presumedFilenames != expectedFilenames ||
        repeated->physicalPoints != expectedPoints ||
        repeated->presumedPoints != expectedPresumed ||
        repeated->ranges != expectedRanges ||
        repeated->macroFrames != expectedFrames ||
        repeated->origins != expectedOrigins ||
        encoded->stats.sourceOrigins != 3 ||
        encoded->stats.presumedFilenameRows != 2 ||
        encoded->stats.physicalPointRows != 4 ||
        encoded->stats.presumedPointRows != 3 ||
        encoded->stats.rangeRows != 3 || encoded->stats.rawRanges != 1 ||
        encoded->stats.sameBeginNormalizedRanges != 1 ||
        encoded->stats.generalNormalizedRanges != 1 ||
        encoded->stats.macroFrameRows != 2 ||
        encoded->stats.macroFrameOccurrences != 3)
        return false;
    for (std::uint32_t index = 0; index != source.origins.size(); ++index) {
        auto decoded = decodeOrigin(*encoded, source::OriginId(index));
        if (!decoded || !(*decoded == source.origins[index]))
            return false;
    }

    auto collisions = encode(source, EncodeOptions{true});
    if (!collisions || collisions->presumedFilenames != expectedFilenames ||
        collisions->physicalPoints != expectedPoints ||
        collisions->presumedPoints != expectedPresumed ||
        collisions->ranges != expectedRanges ||
        collisions->macroFrames != expectedFrames ||
        collisions->origins != expectedOrigins)
        return false;
    for (std::uint32_t index = 0; index != source.origins.size(); ++index) {
        auto decoded = decodeOrigin(*collisions, source::OriginId(index));
        if (!decoded || !(*decoded == source.origins[index]))
            return false;
    }

    source::Tables malformedSource = source;
    malformedSource.origins[0].spelling->begin->file = source::FileId(9);
    if (!failed(encode(malformedSource)) ||
        !failed(decodeOrigin(*encoded, source::OriginId(999))))
        return false;
    {
        auto malformed = *encoded;
        malformed.origins[0].spelling = RangeId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(0))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.origins[0].presumedBegin = PresumedPointId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(0))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.presumedPoints[0].file = FilenameId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(0))))
            return false;
    }
    {
        auto malformed = *encoded;
        std::get<RawRange>(malformed.ranges[0]).begin = PhysicalPointId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(0))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.origins[1].macroStack[0] = MacroFrameId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(1))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.macroFrames[0].spelling = RangeId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(1))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.origins[1].anchor = source::OriginId(999);
        if (!failed(decodeOrigin(malformed, source::OriginId(1))))
            return false;
    }
    {
        auto malformed = *encoded;
        malformed.origins[1].derivedFrom = {source::OriginId(999)};
        if (!failed(decodeOrigin(malformed, source::OriginId(1))))
            return false;
    }
    return true;
}

bool invalidCategoryAndShape() {
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Name, Constructor::NameFromAtomic,
            {Value::node(built.type)});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Expression, Constructor::TypeNamed,
            {Value::node(built.name)});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        buildCore(unit, false);
        add(unit, Category::Type, Constructor::TypeNamed, {});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        buildCore(unit, false);
        add(unit, Category::Auxiliary, Constructor::ProductFixture,
            {Value::product({Value::scalar(ScalarTerm::symbol("only"))})});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        buildCore(unit, false);
        add(unit, Category::Auxiliary, Constructor::SequenceFixture,
            {Value::sequence({Value::node(
                NodeId(std::numeric_limits<std::uint32_t>::max() - 1))})});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        buildCore(unit, false);
        add(unit, Category::Auxiliary, static_cast<Constructor>(999), {});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Auxiliary, Constructor::SumFixture,
            {Value::sum(ScalarTerm::symbol("inr"),
                        Value::node(built.expression0))});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Expression, Constructor::ExpressionInteger,
            {Value::scalar(ScalarTerm::string("7")), Value::node(built.type)});
        if (!failed(unit.finish()))
            return false;
    }
    for (const char *unsafe :
         {"Badd bad", "(Badd)", "Badd(*x*)", "//Badd", "bad..atom", "bad."}) {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Expression, Constructor::ExpressionBinary,
            {Value::scalar(ScalarTerm::symbol(unsafe)),
             Value::node(built.expression0), Value::node(built.expression1),
             Value::node(built.type)});
        if (!failed(unit.finish()))
            return false;
    }
    return true;
}

bool invalidRootsAndNonRoots() {
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        NodeId constant =
            add(unit, Category::GlobalDeclaration, Constructor::GlobalConstant,
                {Value::node(built.type), Value::optional(std::nullopt)});
        (void)unit.addRoot({RootKind::Type, built.name, constant});
        if (failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addRoot({RootKind::Symbol, built.type, built.object});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addRoot({RootKind::Type, built.name, built.object});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addRoot(
            {RootKind::TemplateType, built.name, built.templateObject});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addRoot(
            {static_cast<RootKind>(99), built.name, built.object});
        if (!failed(IRValidator::validate(unit, false)) ||
            !failed(SemanticRocqEmitter().emit(unit)) ||
            !failed(LocationRocqEmitter().emit(unit)))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addNonRoot(NamespaceAliasEvent{
            std::optional<NodeId>(built.type), built.name, {}});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addNonRoot(StaticAssertEvent{std::nullopt, built.type, {}});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addNonRoot(StaticAssertEvent{
            ScalarTerm::symbol("message"), built.expression0, {}});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addNonRoot(
            TemplateAliasEvent{built.name, built.templateObject});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        (void)unit.addNonRoot(
            TemplateInstanceEvent{built.name, built.templateObject});
        if (!failed(unit.finish()))
            return false;
    }
    return true;
}

bool semanticCycle() {
    TranslationUnitIR unit;
    Built built = buildCore(unit, false);
    std::uint32_t firstRaw =
        static_cast<std::uint32_t>(unit.buildingArena().size());
    NodeId first(firstRaw);
    NodeId second(firstRaw + 1);
    add(unit, Category::Expression, Constructor::ExpressionBinary,
        {Value::scalar(ScalarTerm::symbol("Badd")), Value::node(second),
         Value::node(built.expression0), Value::node(built.type)});
    add(unit, Category::Expression, Constructor::ExpressionBinary,
        {Value::scalar(ScalarTerm::symbol("Badd")), Value::node(first),
         Value::node(built.expression1), Value::node(built.type)});
    return failed(unit.finish());
}

bool invalidSourcesAndProvenance() {
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        add(unit, Category::Statement, Constructor::StatementExpression,
            {Value::node(built.expression0)}, {source::OriginId(99)});
        if (!failed(unit.finish()))
            return false;
    }
    {
        auto valid = tables(1);
        valid.files.push_back(source::File{"header.hpp", std::nullopt,
                                           source::FileKind::System, false,
                                           std::nullopt});
        auto &range = *valid.origins[0].spelling;
        range.end->file = source::FileId(1);
        range.normalizedHalfOpen = std::nullopt;
        if (failed(source::validate(valid)))
            return false;
    }
    {
        auto partial = tables(1);
        partial.origins[0].spelling->end = std::nullopt;
        partial.origins[0].spelling->normalizedHalfOpen = std::nullopt;
        if (failed(source::validate(partial)))
            return false;
    }
    {
        auto partial = tables(1);
        partial.origins[0].spelling->begin = std::nullopt;
        partial.origins[0].spelling->normalizedHalfOpen = std::nullopt;
        if (failed(source::validate(partial)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].spelling->begin = std::nullopt;
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].spelling->end = std::nullopt;
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.files.push_back(source::File{"other.cpp", std::nullopt,
                                               source::FileKind::User, false,
                                               std::nullopt});
        auto normalized = *malformed.origins[0].spelling->normalizedHalfOpen;
        normalized.first.file = source::FileId(1);
        normalized.second.file = source::FileId(1);
        malformed.origins[0].spelling->normalizedHalfOpen = normalized;
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        auto normalized = *malformed.origins[0].spelling->normalizedHalfOpen;
        normalized.first.byteOffset = 4;
        normalized.second.byteOffset = 3;
        malformed.origins[0].spelling->normalizedHalfOpen = normalized;
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].spelling->begin->file = source::FileId(9);
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].spelling->end->file = source::FileId(9);
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto noncontiguous = tables(1);
        auto &range = *noncontiguous.origins[0].spelling;
        range.begin->byteOffset = 9;
        range.end->byteOffset = 2;
        range.normalizedHalfOpen = std::nullopt;
        // Macro spelling projections may honestly reverse in one file; they
        // are valid only while no contiguous normalization is claimed.
        if (failed(source::validate(noncontiguous)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].anchor = source::OriginId(7);
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.origins[0].derivedFrom = {source::OriginId(7)};
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(2);
        malformed.origins[0].anchor = source::OriginId(1);
        malformed.origins[1].derivedFrom = {source::OriginId(0)};
        if (!failed(source::validate(malformed)))
            return false;
    }
    {
        auto malformed = tables(1);
        malformed.files[0].includeParent =
            std::make_pair(source::FileId(4), std::uint64_t(0));
        if (!failed(source::validate(malformed)))
            return false;
    }
    return true;
}

bool opaqueReachabilityAndFinishBoundary() {
    {
        TranslationUnitIR unit;
        buildCore(unit, false);
        add(unit, Category::Auxiliary, Constructor::OpaqueFixture,
            {Value::opaque("migration")});
        if (failed(unit.finish()))
            return false; // Explicit temporary form is permitted while
                          // unreachable.
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit, false);
        NodeId global =
            add(unit, Category::GlobalDeclaration, Constructor::GlobalConstant,
                {Value::node(built.type),
                 Value::optional(Value::opaque("migration"))});
        (void)unit.addRoot({RootKind::Type, built.name, global});
        if (!failed(unit.finish()))
            return false;
    }
    {
        TranslationUnitIR unit;
        Built built = buildCore(unit);
        if (failed(unit.finish()))
            return false;
        if (!failed(unit.buildingArena().add(
                Node{Category::Expression,
                     Constructor::ExpressionInteger,
                     {},
                     {Value::scalar(ScalarTerm::numeral("0")),
                      Value::node(built.type)}})))
            return false;
        if (!failed(unit.addRoot({RootKind::Symbol, built.name, built.object})))
            return false;
    }
    return true;
}

bool selectedValidationBoundary() {
    TranslationUnitIR unit;
    Built built = buildCore(unit, false);
    NodeId opaque = add(unit, Category::Auxiliary, Constructor::OpaqueFixture,
                        {Value::opaque("selected migration value")});
    if (failed(IRValidator::validateSelected(unit.nodes(), {built.expression0},
                                             Category::Expression,
                                             "expression")))
        return false;
    if (!failed(IRValidator::validateSelected(
            unit.nodes(), {NodeId(999)}, Category::Expression, "expression")))
        return false;
    if (!failed(IRValidator::validateSelected(unit.nodes(), {built.expression0},
                                              Category::Type, "type")))
        return false;
    if (!failed(IRValidator::validateSelected(
            unit.nodes(), {opaque}, Category::Auxiliary, "auxiliary")))
        return false;
    return true;
}

bool factoriesAndCloning() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto identifier = makeAtomicIdentifier(
        arena, {source::OriginId(0), source::OriginId(0)}, "x");
    auto anonymous = makeAtomicAnonymousIndex(arena, {source::OriginId(0)}, 2);
    auto anonymousNamespace =
        makeAtomicAnonymousNamespace(arena, {source::OriginId(0)});
    auto firstDecl =
        makeAtomicFirstDeclaration(arena, {source::OriginId(0)}, "object");
    auto firstChild =
        makeAtomicFirstChild(arena, {source::OriginId(0)}, "field");
    auto unsupported =
        makeAtomicUnsupported(arena, {source::OriginId(0)}, "diagnostic");
    if (!identifier || !anonymous || !anonymousNamespace || !firstDecl ||
        !firstChild || !unsupported)
        return false;
    auto global = makeGlobalName(arena, {source::OriginId(0)}, *identifier);
    auto scoped = global ? makeScopedName(arena, {source::OriginId(1)}, *global,
                                          *firstChild)
                         : llvm::Expected<NodeId>(llvm::createStringError(
                               std::errc::invalid_argument, "missing"));
    if (!global || !scoped)
        return false;
    auto clone = cloneWithOrigins(
        arena, *scoped,
        {source::OriginId(2), source::OriginId(1), source::OriginId(2)});
    if (!clone || *clone == *scoped)
        return false;
    auto original = arena.get(*scoped);
    auto copied = arena.get(*clone);
    if (!original || !copied ||
        (*original)->origins !=
            std::vector<source::OriginId>({source::OriginId(1)}) ||
        (*copied)->origins != std::vector<source::OriginId>(
                                  {source::OriginId(1), source::OriginId(2)}))
        return false;
    auto wrong = makeGlobalName(arena, {}, *global);
    if (!failed(std::move(wrong)) || failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*identifier, "(Nid \"x\")"},
        {*anonymous, "(Nanon 2)"},
        {*anonymousNamespace, "(Nanonymous)"},
        {*firstDecl, "(Nfirst_decl \"object\")"},
        {*firstChild, "(Nfirst_child \"field\")"},
        {*unsupported, "(Nunsupported_atomic \"diagnostic\")"},
        {*scoped, "(Nscoped (Nglobal (Nid \"x\")) (Nfirst_child \"field\"))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    return true;
}

bool functionAndBuiltinFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "builtin");
    auto name = atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
                       : llvm::Expected<NodeId>(atomic.takeError());
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto function = integer
                        ? makeFunctionType(arena, {source::OriginId(0)},
                                           ScalarTerm::symbol("CC_C"),
                                           ScalarTerm::symbol("Ar_Definite"),
                                           *integer, {*integer})
                        : llvm::Expected<NodeId>(integer.takeError());
    auto global = name && function
                      ? makeGlobalExpression(arena, {source::OriginId(0)},
                                             *name, *function, false)
                      : llvm::Expected<NodeId>(llvm::createStringError(
                            std::errc::invalid_argument, "missing"));
    auto pointer = function ? makeUnaryType(arena, Constructor::TypePointer,
                                            {source::OriginId(1)}, *function)
                            : llvm::Expected<NodeId>(llvm::createStringError(
                                  std::errc::invalid_argument, "missing"));
    auto cast =
        pointer
            ? makeBuiltinToFunctionCast(arena, {source::OriginId(1)}, *pointer)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto expression =
        cast && global
            ? makeCastExpression(arena, {source::OriginId(0)}, *cast, *global)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto local = integer ? makeLocalExpression(arena, {source::OriginId(0)},
                                               "local", *integer)
                         : llvm::Expected<NodeId>(integer.takeError());
    auto anonymous = integer ? makeAnonymousLocalExpression(
                                   arena, {source::OriginId(0)}, 3, *integer)
                             : llvm::Expected<NodeId>(llvm::createStringError(
                                   std::errc::invalid_argument, "missing"));
    auto address =
        global ? makeAddressOfExpression(arena, {source::OriginId(0)}, *global)
               : llvm::Expected<NodeId>(llvm::createStringError(
                     std::errc::invalid_argument, "missing"));
    auto lvalueCast = makeLvalueToRvalueCast(arena, {source::OriginId(1)});
    auto read = lvalueCast && local
                    ? makeCastExpression(arena, {source::OriginId(1)},
                                         *lvalueCast, *local)
                    : llvm::Expected<NodeId>(llvm::createStringError(
                          std::errc::invalid_argument, "missing"));
    if (!name || !integer || !function || !global || !pointer || !cast ||
        !expression || !local || !anonymous || !address || !lvalueCast ||
        !read || failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    auto renderedFunction = emitter.renderNode(unit, *function);
    auto renderedExpression = emitter.renderNode(unit, *expression);
    auto renderedLocal = emitter.renderNode(unit, *local);
    auto renderedAnonymous = emitter.renderNode(unit, *anonymous);
    auto renderedAddress = emitter.renderNode(unit, *address);
    auto renderedRead = emitter.renderNode(unit, *read);
    if (!renderedFunction ||
        *renderedFunction !=
            "(core.Tfunction (@FunctionType _ CC_C Ar_Definite "
            "(Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: "
            "nil)))" ||
        !renderedExpression ||
        *renderedExpression !=
            "(Ecast (Cbuiltin2fun (Tptr (core.Tfunction (@FunctionType _ CC_C "
            "Ar_Definite (Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint "
            "Signed) :: nil))))) (Eglobal (Nglobal (Nid \"builtin\")) "
            "(core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum "
            "int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil)))))" ||
        !renderedLocal ||
        *renderedLocal != "(Evar \"local\" (Tnum int_rank.Iint Signed))" ||
        !renderedAnonymous ||
        *renderedAnonymous !=
            "(Evar (localname.anon 3) (Tnum int_rank.Iint Signed))" ||
        !renderedAddress ||
        *renderedAddress !=
            "(Eaddrof (Eglobal (Nglobal (Nid \"builtin\")) "
            "(core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum "
            "int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil)))))" ||
        !renderedRead ||
        *renderedRead != "(Ecast (Cl2r) (Evar \"local\" "
                         "(Tnum int_rank.Iint Signed)))")
        return false;
    auto functionChildren = unit.nodes().children(*function);
    auto expressionChildren = unit.nodes().children(*expression);
    return functionChildren && functionChildren->size() == 2 &&
           (*functionChildren)[0] == *integer &&
           (*functionChildren)[1] == *integer && expressionChildren &&
           *expressionChildren == std::vector<NodeId>({*cast, *global});
}

bool castAndLiteralFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto literal = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                                   "1", *integer)
                           : llvm::Expected<NodeId>(integer.takeError());
    auto character = integer ? makeCharacterExpression(
                                   arena, {source::OriginId(0)}, 65, *integer)
                             : llvm::Expected<NodeId>(integer.takeError());
    auto string = integer ? makeStringExpression(
                                arena, {source::OriginId(0)},
                                std::vector<std::uint64_t>{65, 0x3bb}, *integer)
                          : llvm::Expected<NodeId>(integer.takeError());
    auto floating = makeFloatExpression(arena, {source::OriginId(0)},
                                        ScalarTerm::symbol("float_type.Ffloat"),
                                        "1065353216");
    auto descriptor = integer ? makeTypeCast(arena, Constructor::CastIntegral,
                                             {source::OriginId(1)}, *integer)
                              : llvm::Expected<NodeId>(integer.takeError());
    auto cast = descriptor && literal
                    ? makeCastExpression(arena, {source::OriginId(1)},
                                         *descriptor, *literal)
                    : llvm::Expected<NodeId>(llvm::createStringError(
                          std::errc::invalid_argument, "missing"));
    auto explicitCast =
        cast && integer
            ? makeExplicitCastExpression(
                  arena, {source::OriginId(0)},
                  ScalarTerm::symbol("cast_style.static"), *integer, *cast)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto path = integer
                    ? makePathCast(arena, Constructor::CastDerivedToBase,
                                   {source::OriginId(1)}, {*integer}, *integer)
                    : llvm::Expected<NodeId>(integer.takeError());
    auto unsupported = integer
                           ? makeUnsupportedCast(arena, {source::OriginId(1)},
                                                 "kind", *integer)
                           : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !literal || !character || !string || !floating ||
        !descriptor || !cast || !explicitCast || !path || !unsupported)
        return false;
    if (!failed(makeNullaryCast(arena, Constructor::TypeVoid, {})) ||
        !failed(makeNullaryCast(arena, Constructor::CastIntegral, {})) ||
        !failed(makeTypeCast(arena, Constructor::CastLvalueToRvalue, {},
                             *integer)) ||
        !failed(makeTypeCast(arena, Constructor::CastIntegral, {}, *literal)) ||
        !failed(
            makePathCast(arena, Constructor::CastIntegral, {}, {}, *integer)) ||
        !failed(makeExplicitCastExpression(arena, {}, ScalarTerm::string("bad"),
                                           *integer, *cast)) ||
        !failed(makeExplicitCastExpression(
            arena, {}, ScalarTerm::symbol("cast_style.invalid"), *integer,
            *cast)) ||
        !failed(makeExplicitCastExpression(
            arena, {}, ScalarTerm::symbol("cast_style.c"), *literal, *cast)) ||
        failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*character, "(Echar 65%N (Tnum int_rank.Iint Signed))"},
        {*string,
         "(core.Estring (literal_string.of_list_N (65%N :: 955%N :: nil)) "
         "(Tnum int_rank.Iint Signed))"},
        {*floating,
         "(Efloat float_type.Ffloat (float_value.of_bits float_type.Ffloat "
         "1065353216))"},
        {*explicitCast,
         "(Eexplicit_cast cast_style.static (Tnum int_rank.Iint Signed) "
         "(Ecast (Cintegral (Tnum int_rank.Iint Signed)) (Eint 1 (Tnum "
         "int_rank.Iint Signed))))"},
        {*path, "(Cderived2base ((Tnum int_rank.Iint Signed) :: nil) (Tnum "
                "int_rank.Iint Signed))"},
        {*unsupported, "(Cunsupported \"kind\" (Tnum int_rank.Iint Signed))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    auto children = unit.nodes().children(*explicitCast);
    return children && *children == std::vector<NodeId>({*integer, *cast});
}

bool operatorFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto lhs = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                               "1", *integer)
                       : llvm::Expected<NodeId>(integer.takeError());
    auto rhs = integer ? makeIntegerExpression(arena, {source::OriginId(1)},
                                               "2", *integer)
                       : llvm::Expected<NodeId>(integer.takeError());
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "value");
    auto unresolvedName =
        atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
               : llvm::Expected<NodeId>(atomic.takeError());
    auto resultGlobal =
        unresolvedName ? makeResultGlobalType(arena, {source::OriginId(2)},
                                              *unresolvedName)
                       : llvm::Expected<NodeId>(unresolvedName.takeError());
    if (!integer || !lhs || !rhs || !resultGlobal)
        return false;

    auto unary =
        makeUnaryExpression(arena, {source::OriginId(0)},
                            ScalarTerm::symbol("Uminus"), *lhs, *integer);
    auto unresolvedUnary =
        makeUnaryExpression(arena, {source::OriginId(1)},
                            ScalarTerm::symbol("Uminus"), *lhs, std::nullopt);
    auto unsupportedUnary = makeUnsupportedUnaryExpression(
        arena, {source::OriginId(0)}, "__real", *lhs, *integer);
    auto unresolvedUnsupportedUnary = makeUnsupportedUnaryExpression(
        arena, {source::OriginId(1)}, "__imag", *lhs, std::nullopt);
    auto unresolvedDeref = makeUnresolvedUnarySyntaxExpression(
        arena, {source::OriginId(1)}, ScalarTerm::symbol("Rstar"), *lhs);
    auto binary =
        makeBinaryExpression(arena, {source::OriginId(0)},
                             ScalarTerm::symbol("Badd"), *lhs, *rhs, *integer);
    auto unresolvedBinary = makeUnresolvedBinaryExpression(
        arena, {source::OriginId(1)}, ScalarTerm::symbol("Badd"), *lhs, *rhs);
    auto assignment = makeAssignmentExpression(arena, {source::OriginId(0)},
                                               *lhs, *rhs, *integer);
    auto unresolvedAssignment = makeUnresolvedBinarySyntaxExpression(
        arena, {source::OriginId(1)}, ScalarTerm::symbol("Rassign"), *lhs,
        *rhs);
    auto compound = makeCompoundAssignmentExpression(
        arena, {source::OriginId(0)}, ScalarTerm::symbol("Badd"), *lhs, *rhs,
        *integer);
    auto unresolvedCompound = makeUnresolvedCompoundAssignmentExpression(
        arena, {source::OriginId(1)}, ScalarTerm::symbol("Badd"), *lhs, *rhs);
    auto increment = makeIncrementExpression(
        arena, {source::OriginId(0)}, Constructor::ExpressionPreIncrement, *lhs,
        *integer);
    auto comma = makeSequencingExpression(
        arena, {source::OriginId(0)}, Constructor::ExpressionComma, *lhs, *rhs);
    auto subscript = makeSubscriptExpression(arena, {source::OriginId(0)}, *lhs,
                                             *rhs, *integer);
    auto sizeofType = makeTraitExpression(arena, {source::OriginId(0)},
                                          Constructor::ExpressionSizeofType,
                                          *integer, *integer);
    auto alignofExpression = makeTraitExpression(
        arena, {source::OriginId(0)}, Constructor::ExpressionAlignofExpression,
        *lhs, *integer);
    auto sizeofPack = makeUnresolvedSizeofPackExpression(
        arena, {source::OriginId(1)}, "Ts", *integer);
    if (!unary || !unresolvedUnary || !unsupportedUnary ||
        !unresolvedUnsupportedUnary || !unresolvedDeref || !binary ||
        !unresolvedBinary || !assignment || !unresolvedAssignment ||
        !compound || !unresolvedCompound || !increment || !comma ||
        !subscript || !sizeofType || !alignofExpression || !sizeofPack)
        return false;

    for (llvm::StringRef operation :
         {"Badd", "Band", "Bcmp", "Bdiv", "Beq", "Bge", "Bgt", "Ble", "Blt",
          "Bmul", "Bneq", "Bor", "Bmod", "Bshl", "Bshr", "Bsub", "Bxor",
          "Bdotp", "Bdotip"})
        if (failed(makeBinaryExpression(arena, {},
                                        ScalarTerm::symbol(operation.str()),
                                        *lhs, *rhs, *integer)))
            return false;
    for (llvm::StringRef operation : {"Badd", "Band", "Bdiv", "Bmul", "Bor",
                                      "Bmod", "Bshl", "Bshr", "Bsub", "Bxor"})
        if (failed(makeCompoundAssignmentExpression(
                arena, {}, ScalarTerm::symbol(operation.str()), *lhs, *rhs,
                *integer)))
            return false;

    if (!failed(makeUnaryExpression(arena, {}, ScalarTerm::string("Uminus"),
                                    *lhs, *integer)) ||
        !failed(makeUnaryExpression(arena, {}, ScalarTerm::symbol("Ubad"), *lhs,
                                    *integer)) ||
        !failed(makeUnaryExpression(arena, {}, ScalarTerm::symbol("Uminus"),
                                    *integer, *integer)) ||
        !failed(makeUnsupportedUnaryExpression(arena, {}, "__real", *integer,
                                               *integer)) ||
        !failed(
            makeUnsupportedUnaryExpression(arena, {}, "__real", *lhs, *lhs)) ||
        !failed(makeResultGlobalType(arena, {}, *integer)) ||
        !failed(makeUnresolvedUnarySyntaxExpression(
            arena, {}, ScalarTerm::symbol("Rbad"), *lhs)) ||
        !failed(makeBinaryExpression(arena, {}, ScalarTerm::symbol("Bbad"),
                                     *lhs, *rhs, *integer)) ||
        !failed(makeBinaryExpression(arena, {}, ScalarTerm::symbol("Badd"),
                                     *integer, *rhs, *integer)) ||
        !failed(makeUnresolvedBinarySyntaxExpression(
            arena, {}, ScalarTerm::symbol("Rbad"), *lhs, *rhs)) ||
        !failed(makeUnresolvedCompoundAssignmentExpression(
            arena, {}, ScalarTerm::symbol("Bcmp"), *lhs, *rhs)) ||
        !failed(makeIncrementExpression(arena, {}, Constructor::ExpressionDeref,
                                        *lhs, *integer)) ||
        !failed(makeSequencingExpression(
            arena, {}, Constructor::ExpressionBinary, *lhs, *rhs)) ||
        !failed(makeSubscriptExpression(arena, {}, *integer, *rhs, *integer)) ||
        !failed(makeTraitExpression(arena, {}, Constructor::ExpressionBinary,
                                    *integer, *integer)) ||
        !failed(makeTraitExpression(arena, {},
                                    Constructor::ExpressionSizeofType,
                                    std::nullopt, *integer)) ||
        !failed(makeTraitExpression(arena, {},
                                    Constructor::ExpressionSizeofExpression,
                                    *integer, *integer)) ||
        !failed(makeUnresolvedSizeofPackExpression(arena, {}, "Ts", *lhs)) ||
        failed(unit.finish()))
        return false;

    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*resultGlobal, "(Tresult_global (Nglobal (Nid \"value\")))"},
        {*unary,
         "(core.Eunop Uminus (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum "
         "int_rank.Iint Signed))"},
        {*unresolvedUnary,
         "(Eunresolved_unop (Runop Uminus) (Eint 1 (Tnum int_rank.Iint "
         "Signed)))"},
        {*unsupportedUnary,
         "(core.Eunop (Uunsupported \"__real\") (Eint 1 (Tnum "
         "int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*unresolvedUnsupportedUnary,
         "(Eunresolved_unop (Runop (Uunsupported \"__imag\")) (Eint 1 "
         "(Tnum int_rank.Iint Signed)))"},
        {*unresolvedDeref,
         "(Eunresolved_unop Rstar (Eint 1 (Tnum int_rank.Iint Signed)))"},
        {*binary,
         "(core.Ebinop Badd (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 "
         "(Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*unresolvedBinary,
         "(Eunresolved_binop (Rbinop Badd) (Eint 1 (Tnum int_rank.Iint "
         "Signed)) (Eint 2 (Tnum int_rank.Iint Signed)))"},
        {*assignment,
         "(core.Eassign (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 (Tnum "
         "int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*unresolvedAssignment,
         "(Eunresolved_binop Rassign (Eint 1 (Tnum int_rank.Iint Signed)) "
         "(Eint 2 (Tnum int_rank.Iint Signed)))"},
        {*compound,
         "(core.Eassign_op Badd (Eint 1 (Tnum int_rank.Iint Signed)) (Eint "
         "2 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*unresolvedCompound,
         "(Eunresolved_binop (Rassign_op Badd) (Eint 1 (Tnum int_rank.Iint "
         "Signed)) (Eint 2 (Tnum int_rank.Iint Signed)))"},
        {*increment, "(core.Epreinc (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum "
                     "int_rank.Iint Signed))"},
        {*comma,
         "(core.Ecomma (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 (Tnum "
         "int_rank.Iint Signed)))"},
        {*subscript,
         "(core.Esubscript (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 "
         "(Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*sizeofType, "(core.Esizeof (inl (Tnum int_rank.Iint Signed)) (Tnum "
                      "int_rank.Iint Signed))"},
        {*alignofExpression,
         "(core.Ealignof (inr (Eint 1 (Tnum int_rank.Iint Signed))) (Tnum "
         "int_rank.Iint Signed))"},
        {*sizeofPack,
         "(Eunresolved_sizeof_pack \"Ts\" (Tnum int_rank.Iint Signed))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    auto binaryChildren = unit.nodes().children(*binary);
    auto compoundChildren = unit.nodes().children(*compound);
    auto traitChildren = unit.nodes().children(*sizeofType);
    return binaryChildren &&
           *binaryChildren == std::vector<NodeId>({*lhs, *rhs, *integer}) &&
           compoundChildren &&
           *compoundChildren == std::vector<NodeId>({*lhs, *rhs, *integer}) &&
           traitChildren &&
           *traitChildren == std::vector<NodeId>({*integer, *integer});
}

bool callMemberFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "f");
    auto name = atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
                       : llvm::Expected<NodeId>(atomic.takeError());
    auto field = makeAtomicIdentifier(arena, {source::OriginId(1)}, "field");
    auto lhs = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                               "1", *integer)
                       : llvm::Expected<NodeId>(integer.takeError());
    auto rhs = integer ? makeIntegerExpression(arena, {source::OriginId(1)},
                                               "2", *integer)
                       : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !name || !field || !lhs || !rhs)
        return false;

    auto resultUnary = makeResultUnarySyntaxType(
        arena, {source::OriginId(2)}, ScalarTerm::symbol("Rarrow"), *integer);
    auto resultCall =
        makeResultCallType(arena, {source::OriginId(2)}, *name, {*integer});
    auto resultMember =
        makeResultMemberType(arena, {source::OriginId(2)}, *integer, *name);
    auto globalMember = makeGlobalMemberExpression(arena, {source::OriginId(0)},
                                                   *name, *integer);
    auto call = makeCallExpression(arena, {source::OriginId(0)}, *lhs, {*rhs});
    auto unresolvedCall = makeUnresolvedCallExpression(
        arena, {source::OriginId(1)}, *name, {*rhs});
    auto member = makeMemberExpression(arena, {source::OriginId(0)}, true, *lhs,
                                       *field, true, *integer);
    auto ignored = makeMemberIgnoreExpression(arena, {source::OriginId(0)},
                                              false, *lhs, *rhs);
    auto unresolvedMember = makeUnresolvedMemberExpression(
        arena, {source::OriginId(1)}, *lhs, *name);
    auto directMemberCall = makeDirectMemberCallExpression(
        arena, {source::OriginId(0)}, false, *name,
        ScalarTerm::symbol("Direct"), *integer, *lhs, {*rhs});
    auto pointerMemberCall = makePointerMemberCallExpression(
        arena, {source::OriginId(0)}, true, *rhs, *lhs, {*rhs});
    auto functionOperator = makeFunctionOperatorCallExpression(
        arena, {source::OriginId(0)}, ScalarTerm::symbol("OOPlus"), *name,
        *integer, {*lhs, *rhs});
    auto methodOperator = makeMethodOperatorCallExpression(
        arena, {source::OriginId(0)}, ScalarTerm::symbol("OOStar"), *name,
        ScalarTerm::symbol("Virtual"), *integer, {*lhs, *rhs});
    auto staticMethodOperator = makeMethodOperatorCallExpression(
        arena, {source::OriginId(0)}, ScalarTerm::symbol("OOCall"), *name,
        ScalarTerm::symbol("Static_dispatch"), *integer, {*lhs});
    auto thisExpression =
        makeThisExpression(arena, {source::OriginId(0)}, *integer);
    auto implicit = makeImplicitExpression(arena, {source::OriginId(1)}, *lhs);
    auto pseudo = makePseudoDestructorExpression(arena, {source::OriginId(0)},
                                                 true, *integer, *lhs);
    if (!resultUnary || !resultCall || !resultMember || !globalMember ||
        !call || !unresolvedCall || !member || !ignored || !unresolvedMember ||
        !directMemberCall || !pointerMemberCall || !functionOperator ||
        !methodOperator || !staticMethodOperator || !thisExpression ||
        !implicit || !pseudo)
        return false;

    if (!failed(makeResultUnarySyntaxType(arena, {}, ScalarTerm::symbol("Rbad"),
                                          *integer)) ||
        !failed(makeResultUnarySyntaxType(
            arena, {}, ScalarTerm::symbol("Rarrow"), *lhs)) ||
        !failed(makeResultCallType(arena, {}, *lhs, {*integer})) ||
        !failed(makeResultCallType(arena, {}, *name, {*lhs})) ||
        !failed(makeResultMemberType(arena, {}, *lhs, *name)) ||
        !failed(makeGlobalMemberExpression(arena, {}, *lhs, *integer)) ||
        !failed(makeCallExpression(arena, {}, *integer, {*rhs})) ||
        !failed(makeCallExpression(arena, {}, *lhs, {*integer})) ||
        !failed(makeUnresolvedCallExpression(arena, {}, *lhs, {*rhs})) ||
        !failed(makeMemberExpression(arena, {}, false, *lhs, *name, false,
                                     *integer)) ||
        !failed(makeMemberIgnoreExpression(arena, {}, false, *integer, *rhs)) ||
        !failed(makeUnresolvedMemberExpression(arena, {}, *lhs, *integer)) ||
        !failed(makeDirectMemberCallExpression(arena, {}, false, *name,
                                               ScalarTerm::symbol("Static"),
                                               *integer, *lhs, {*rhs})) ||
        !failed(makePointerMemberCallExpression(arena, {}, false, *integer,
                                                *lhs, {*rhs})) ||
        !failed(makeFunctionOperatorCallExpression(
            arena, {}, ScalarTerm::symbol("OOBad"), *name, *integer, {*lhs})) ||
        !failed(makeMethodOperatorCallExpression(
            arena, {}, ScalarTerm::symbol("OOPlus"), *name,
            ScalarTerm::symbol("Bad"), *integer, {*lhs})) ||
        !failed(makeThisExpression(arena, {}, *lhs)) ||
        !failed(makeImplicitExpression(arena, {}, *integer)) ||
        !failed(makePseudoDestructorExpression(arena, {}, false, *lhs, *rhs)) ||
        failed(unit.finish()))
        return false;

    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*resultUnary, "(Tresult_unop Rarrow (Tnum int_rank.Iint Signed))"},
        {*resultCall,
         "(Tresult_call (Nglobal (Nid \"f\")) ((Tnum int_rank.Iint Signed) "
         ":: nil))"},
        {*resultMember,
         "(Tresult_member (Tnum int_rank.Iint Signed) (Nglobal (Nid "
         "\"f\")))"},
        {*globalMember,
         "(Eglobal_member (Nglobal (Nid \"f\")) (Tnum int_rank.Iint "
         "Signed))"},
        {*call,
         "(core.Ecall (Eint 1 (Tnum int_rank.Iint Signed)) ((Eint 2 (Tnum "
         "int_rank.Iint Signed)) :: nil))"},
        {*unresolvedCall,
         "(core.Eunresolved_call (Nglobal (Nid \"f\")) ((Eint 2 (Tnum "
         "int_rank.Iint Signed)) :: nil))"},
        {*member,
         "(core.Emember true (Eint 1 (Tnum int_rank.Iint Signed)) (Nid "
         "\"field\") true (Tnum int_rank.Iint Signed))"},
        {*ignored,
         "(core.Emember_ignore false (Eint 1 (Tnum int_rank.Iint Signed)) "
         "(Eint 2 (Tnum int_rank.Iint Signed)))"},
        {*unresolvedMember,
         "(core.Eunresolved_member (Eint 1 (Tnum int_rank.Iint Signed)) "
         "(Nglobal (Nid \"f\")))"},
        {*directMemberCall,
         "(core.Emember_call false (inl ((Nglobal (Nid \"f\")), Direct, "
         "(Tnum int_rank.Iint Signed))) (Eint 1 (Tnum int_rank.Iint "
         "Signed)) ((Eint 2 (Tnum int_rank.Iint Signed)) :: nil))"},
        {*pointerMemberCall,
         "(core.Emember_call true (inr (Eint 2 (Tnum int_rank.Iint "
         "Signed))) (Eint 1 (Tnum int_rank.Iint Signed)) ((Eint 2 (Tnum "
         "int_rank.Iint Signed)) :: nil))"},
        {*functionOperator,
         "(core.Eoperator_call OOPlus (operator_impl.Func (Nglobal (Nid "
         "\"f\")) (Tnum int_rank.Iint Signed)) ((Eint 1 (Tnum "
         "int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint Signed)) :: "
         "nil))"},
        {*methodOperator,
         "(core.Eoperator_call OOStar (operator_impl.MFunc (Nglobal (Nid "
         "\"f\")) Virtual (Tnum int_rank.Iint Signed)) ((Eint 1 (Tnum "
         "int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint Signed)) :: "
         "nil))"},
        {*staticMethodOperator,
         "(core.Eoperator_call OOCall (operator_impl.MFunc (Nglobal (Nid "
         "\"f\")) Static_dispatch (Tnum int_rank.Iint Signed)) ((Eint 1 "
         "(Tnum int_rank.Iint Signed)) :: nil))"},
        {*thisExpression, "(Ethis (Tnum int_rank.Iint Signed))"},
        {*implicit, "(Eimplicit (Eint 1 (Tnum int_rank.Iint Signed)))"},
        {*pseudo,
         "(Epseudo_destructor true (Tnum int_rank.Iint Signed) (Eint 1 "
         "(Tnum int_rank.Iint Signed)))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    auto directChildren = unit.nodes().children(*directMemberCall);
    auto operatorChildren = unit.nodes().children(*methodOperator);
    auto memberChildren = unit.nodes().children(*member);
    return directChildren &&
           *directChildren ==
               std::vector<NodeId>({*name, *integer, *lhs, *rhs}) &&
           operatorChildren &&
           *operatorChildren ==
               std::vector<NodeId>({*name, *integer, *lhs, *rhs}) &&
           memberChildren &&
           *memberChildren == std::vector<NodeId>({*lhs, *field, *integer});
}

bool constructionFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "C");
    auto name = atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
                       : llvm::Expected<NodeId>(atomic.takeError());
    auto field = makeAtomicIdentifier(arena, {source::OriginId(1)}, "field");
    auto first = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                                 "1", *integer)
                         : llvm::Expected<NodeId>(integer.takeError());
    auto second = integer ? makeIntegerExpression(arena, {source::OriginId(1)},
                                                  "2", *integer)
                          : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !name || !field || !first || !second)
        return false;

    auto construction = makeConstructorExpression(
        arena, {source::OriginId(0)}, *name, {*first, *second}, *integer);
    auto inherited = makeInheritedConstructorExpression(
        arena, {source::OriginId(0)}, *name, 2, *integer);
    auto unresolvedParen = makeUnresolvedInitializerListExpression(
        arena, {source::OriginId(0)},
        Constructor::ExpressionUnresolvedParenList, *integer,
        {*first, *second});
    auto unresolvedInit = makeUnresolvedInitializerListExpression(
        arena, {source::OriginId(0)}, Constructor::ExpressionUnresolvedInitList,
        std::nullopt, {*first});
    auto initList = makeInitListExpression(arena, {source::OriginId(0)},
                                           {*first, *second}, *first, *integer);
    auto unionInit = makeUnionInitListExpression(arena, {source::OriginId(0)},
                                                 *field, *first, *integer);
    auto andClean =
        makeAndCleanExpression(arena, {source::OriginId(0)}, *first);
    auto materialized = makeMaterializeTemporaryExpression(
        arena, {source::OriginId(0)}, *first, ScalarTerm::symbol("Lvalue"));
    auto implicitInit =
        makeImplicitInitExpression(arena, {source::OriginId(0)}, *integer);
    auto arrayLoop = makeArrayLoopInitExpression(
        arena, {source::OriginId(0)}, 3, *first, 1, "4", *second, *integer);
    auto arrayIndex =
        makeArrayLoopIndexExpression(arena, {source::OriginId(0)}, 1, *integer);
    auto opaque = makeOpaqueReferenceExpression(arena, {source::OriginId(0)}, 3,
                                                *integer);
    if (!construction || !inherited || !unresolvedParen || !unresolvedInit ||
        !initList || !unionInit || !andClean || !materialized ||
        !implicitInit || !arrayLoop || !arrayIndex || !opaque)
        return false;

    if (!failed(makeConstructorExpression(arena, {}, *first, {*second},
                                          *integer)) ||
        !failed(makeConstructorExpression(arena, {}, *name, {*integer},
                                          *integer)) ||
        !failed(
            makeInheritedConstructorExpression(arena, {}, *name, 1, *first)) ||
        !failed(makeUnresolvedInitializerListExpression(
            arena, {}, Constructor::ExpressionInitList, std::nullopt,
            {*first})) ||
        !failed(makeUnresolvedInitializerListExpression(
            arena, {}, Constructor::ExpressionUnresolvedInitList, *first,
            {*second})) ||
        !failed(makeInitListExpression(arena, {}, {*integer}, std::nullopt,
                                       *integer)) ||
        !failed(
            makeUnionInitListExpression(arena, {}, *name, *first, *integer)) ||
        !failed(makeAndCleanExpression(arena, {}, *integer)) ||
        !failed(makeMaterializeTemporaryExpression(
            arena, {}, *first, ScalarTerm::symbol("Glvalue"))) ||
        !failed(makeImplicitInitExpression(arena, {}, *first)) ||
        !failed(makeArrayLoopInitExpression(arena, {}, 0, *integer, 0, "1",
                                            *second, *integer)) ||
        !failed(makeArrayLoopIndexExpression(arena, {}, 0, *first)) ||
        !failed(makeOpaqueReferenceExpression(arena, {}, 0, *first)) ||
        failed(unit.finish()))
        return false;

    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*construction,
         "(Econstructor (Nglobal (Nid \"C\")) ((Eint 1 (Tnum "
         "int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint Signed)) :: "
         "nil) (Tnum int_rank.Iint Signed))"},
        {*inherited,
         "(Einherited_constructor (Nglobal (Nid \"C\")) ((localname.anon "
         "0) :: (localname.anon 1) :: nil) (Tnum int_rank.Iint Signed))"},
        {*unresolvedParen,
         "(Eunresolved_parenlist (Some (Tnum int_rank.Iint Signed)) ((Eint "
         "1 (Tnum int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint "
         "Signed)) :: nil))"},
        {*unresolvedInit,
         "(Eunresolved_initlist None ((Eint 1 (Tnum int_rank.Iint Signed)) "
         ":: nil))"},
        {*initList,
         "(Einitlist ((Eint 1 (Tnum int_rank.Iint Signed)) :: (Eint 2 "
         "(Tnum int_rank.Iint Signed)) :: nil) (Some (Eint 1 (Tnum "
         "int_rank.Iint Signed))) (Tnum int_rank.Iint Signed))"},
        {*unionInit, "(Einitlist_union (Nid \"field\") (Some (Eint 1 (Tnum "
                     "int_rank.Iint Signed))) (Tnum int_rank.Iint Signed))"},
        {*andClean, "(Eandclean (Eint 1 (Tnum int_rank.Iint Signed)))"},
        {*materialized,
         "(Ematerialize_temp (Eint 1 (Tnum int_rank.Iint Signed)) Lvalue)"},
        {*implicitInit, "(Eimplicit_init (Tnum int_rank.Iint Signed))"},
        {*arrayLoop,
         "(Earrayloop_init 3 (Eint 1 (Tnum int_rank.Iint Signed)) 1 4 (Eint "
         "2 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*arrayIndex, "(Earrayloop_index 1 (Tnum int_rank.Iint Signed))"},
        {*opaque, "(Eopaque_ref 3 (Tnum int_rank.Iint Signed))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    auto constructionChildren = unit.nodes().children(*construction);
    auto inheritedChildren = unit.nodes().children(*inherited);
    auto unresolvedChildren = unit.nodes().children(*unresolvedParen);
    auto initChildren = unit.nodes().children(*initList);
    auto unionChildren = unit.nodes().children(*unionInit);
    auto loopChildren = unit.nodes().children(*arrayLoop);
    return constructionChildren &&
           *constructionChildren ==
               std::vector<NodeId>({*name, *first, *second, *integer}) &&
           inheritedChildren &&
           *inheritedChildren == std::vector<NodeId>({*name, *integer}) &&
           unresolvedChildren &&
           *unresolvedChildren ==
               std::vector<NodeId>({*integer, *first, *second}) &&
           initChildren &&
           *initChildren ==
               std::vector<NodeId>({*first, *second, *first, *integer}) &&
           unionChildren &&
           *unionChildren == std::vector<NodeId>({*field, *first, *integer}) &&
           loopChildren &&
           *loopChildren == std::vector<NodeId>({*first, *second, *integer});
}

bool allocationFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto voidType =
        makeLeafType(arena, Constructor::TypeVoid, {source::OriginId(0)});
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "alloc");
    auto name = atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
                       : llvm::Expected<NodeId>(atomic.takeError());
    auto first = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                                 "1", *integer)
                         : llvm::Expected<NodeId>(integer.takeError());
    auto second = integer ? makeIntegerExpression(arena, {source::OriginId(1)},
                                                  "2", *integer)
                          : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !voidType || !name || !first || !second)
        return false;

    auto allocating =
        makeNewExpression(arena, {source::OriginId(0)}, *name, *integer, {},
                          false, false, *integer, std::nullopt, *first);
    auto alignedArray =
        makeNewExpression(arena, {source::OriginId(0)}, *name, *integer, {},
                          false, true, *integer, *first, std::nullopt);
    auto nonAllocating = makeNewExpression(
        arena, {source::OriginId(0)}, *name, *integer, {*first}, true, false,
        *integer, std::nullopt, std::nullopt);
    auto deletion = makeDeleteExpression(arena, {source::OriginId(0)}, true,
                                         *name, *first, *integer);
    auto unresolved = makeUnsupportedExpression(arena, {source::OriginId(0)},
                                                "unresolved delete", *voidType);
    auto functionNew = makeFunctionAllocationOperatorCallExpression(
        arena, {source::OriginId(0)}, false, true, *name, *integer,
        {*first, *second});
    auto methodDelete = makeMethodAllocationOperatorCallExpression(
        arena, {source::OriginId(0)}, true, true, *name,
        ScalarTerm::symbol("Static_dispatch"), *integer, {*first});
    if (!allocating || !alignedArray || !nonAllocating || !deletion ||
        !unresolved || !functionNew || !methodDelete)
        return false;

    if (!failed(makeNewExpression(arena, {}, *first, *integer, {}, false, false,
                                  *integer, std::nullopt, std::nullopt)) ||
        !failed(makeNewExpression(arena, {}, *name, *first, {}, false, false,
                                  *integer, std::nullopt, std::nullopt)) ||
        !failed(makeNewExpression(arena, {}, *name, *integer, {*integer}, false,
                                  false, *integer, std::nullopt,
                                  std::nullopt)) ||
        !failed(makeNewExpression(arena, {}, *name, *integer, {}, true, true,
                                  *integer, std::nullopt, std::nullopt)) ||
        !failed(makeNewExpression(arena, {}, *name, *integer, {}, true, false,
                                  *integer, std::nullopt, std::nullopt)) ||
        !failed(makeNewExpression(arena, {}, *name, *integer, {}, false, false,
                                  *first, std::nullopt, std::nullopt)) ||
        !failed(makeDeleteExpression(arena, {}, false, *first, *second,
                                     *integer)) ||
        !failed(makeFunctionAllocationOperatorCallExpression(
            arena, {}, false, false, *first, *integer, {*second})) ||
        !failed(makeMethodAllocationOperatorCallExpression(
            arena, {}, true, false, *name, ScalarTerm::symbol("Bad"), *integer,
            {*first})) ||
        !failed(makeMethodAllocationOperatorCallExpression(
            arena, {}, true, false, *name, ScalarTerm::symbol("Direct"),
            *integer, {*first})) ||
        failed(unit.finish()))
        return false;

    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*allocating,
         "(Enew ((Nglobal (Nid \"alloc\")), (Tnum int_rank.Iint Signed)) "
         "nil (new_form.Allocating false) (Tnum int_rank.Iint Signed) None "
         "(Some (Eint 1 (Tnum int_rank.Iint Signed))))"},
        {*alignedArray,
         "(Enew ((Nglobal (Nid \"alloc\")), (Tnum int_rank.Iint Signed)) "
         "nil (new_form.Allocating true) (Tnum int_rank.Iint Signed) (Some "
         "(Eint 1 (Tnum int_rank.Iint Signed))) None)"},
        {*nonAllocating,
         "(Enew ((Nglobal (Nid \"alloc\")), (Tnum int_rank.Iint Signed)) "
         "((Eint 1 (Tnum int_rank.Iint Signed)) :: nil) "
         "new_form.NonAllocating (Tnum int_rank.Iint Signed) None None)"},
        {*deletion, "(Edelete true (Nglobal (Nid \"alloc\")) (Eint 1 (Tnum "
                    "int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))"},
        {*unresolved, "(Eunsupported \"unresolved delete\" (Tvoid))"},
        {*functionNew,
         "(core.Eoperator_call (OONew true) (operator_impl.Func (Nglobal "
         "(Nid \"alloc\")) (Tnum int_rank.Iint Signed)) ((Eint 1 (Tnum "
         "int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint Signed)) :: "
         "nil))"},
        {*methodDelete,
         "(core.Eoperator_call (OODelete true) (operator_impl.MFunc (Nglobal "
         "(Nid \"alloc\")) Static_dispatch (Tnum int_rank.Iint Signed)) ((Eint "
         "1 "
         "(Tnum int_rank.Iint Signed)) :: nil))"}};
    for (const auto &[id, text] : expected) {
        auto rendered = emitter.renderNode(unit, id);
        if (!rendered || *rendered != text)
            return false;
    }
    auto newChildren = unit.nodes().children(*allocating);
    auto nonAllocatingChildren = unit.nodes().children(*nonAllocating);
    auto deleteChildren = unit.nodes().children(*deletion);
    auto unresolvedChildren = unit.nodes().children(*unresolved);
    auto functionChildren = unit.nodes().children(*functionNew);
    return newChildren &&
           *newChildren ==
               std::vector<NodeId>({*name, *integer, *integer, *first}) &&
           nonAllocatingChildren &&
           *nonAllocatingChildren ==
               std::vector<NodeId>({*name, *integer, *first, *integer}) &&
           deleteChildren &&
           *deleteChildren == std::vector<NodeId>({*name, *first, *integer}) &&
           unresolvedChildren &&
           *unresolvedChildren == std::vector<NodeId>({*voidType}) &&
           functionChildren &&
           *functionChildren ==
               std::vector<NodeId>({*name, *integer, *first, *second});
}

bool lambdaAtomicFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto atomicName =
        makeAtomicIdentifier(arena, {source::OriginId(0)}, "lambda");
    auto name = atomicName
                    ? makeGlobalName(arena, {source::OriginId(0)}, *atomicName)
                    : llvm::Expected<NodeId>(atomicName.takeError());
    auto first = integer ? makeIntegerExpression(arena, {source::OriginId(0)},
                                                 "1", *integer)
                         : llvm::Expected<NodeId>(integer.takeError());
    auto second = integer ? makeIntegerExpression(arena, {source::OriginId(1)},
                                                  "2", *integer)
                          : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !name || !first || !second)
        return false;
    auto atomic =
        makeAtomicExpression(arena, {source::OriginId(0)}, "AtomicLoad",
                             {*first, *second}, *integer);
    auto vaArg =
        makeVaArgExpression(arena, {source::OriginId(0)}, *first, *integer);
    auto lambda = makeLambdaExpression(arena, {source::OriginId(0)}, *name,
                                       {*first, *second});
    if (!atomic || !vaArg || !lambda ||
        !failed(makeAtomicExpression(arena, {}, "", {*first}, *integer)) ||
        !failed(makeAtomicExpression(arena, {}, "AtomicLoad", {*integer},
                                     *integer)) ||
        !failed(
            makeAtomicExpression(arena, {}, "AtomicLoad", {*first}, *first)) ||
        !failed(makeVaArgExpression(arena, {}, *integer, *integer)) ||
        !failed(makeVaArgExpression(arena, {}, *first, *first)) ||
        !failed(makeLambdaExpression(arena, {}, *first, {*second})) ||
        !failed(makeLambdaExpression(arena, {}, *name, {*integer})) ||
        failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    auto atomicTerm = emitter.renderNode(unit, *atomic);
    auto vaArgTerm = emitter.renderNode(unit, *vaArg);
    auto lambdaTerm = emitter.renderNode(unit, *lambda);
    if (!atomicTerm ||
        *atomicTerm !=
            "(Eatomic \"AtomicLoad\" ((Eint 1 (Tnum int_rank.Iint Signed)) "
            ":: (Eint 2 (Tnum int_rank.Iint Signed)) :: nil) (Tnum "
            "int_rank.Iint Signed))" ||
        !vaArgTerm ||
        *vaArgTerm != "(Eva_arg (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum "
                      "int_rank.Iint Signed))" ||
        !lambdaTerm ||
        *lambdaTerm !=
            "(Elambda (Nglobal (Nid \"lambda\")) ((Eint 1 (Tnum "
            "int_rank.Iint Signed)) :: (Eint 2 (Tnum int_rank.Iint Signed)) "
            ":: nil))")
        return false;
    auto atomicChildren = unit.nodes().children(*atomic);
    auto vaArgChildren = unit.nodes().children(*vaArg);
    auto lambdaChildren = unit.nodes().children(*lambda);
    return atomicChildren &&
           *atomicChildren ==
               std::vector<NodeId>({*first, *second, *integer}) &&
           vaArgChildren &&
           *vaArgChildren == std::vector<NodeId>({*first, *integer}) &&
           lambdaChildren &&
           *lambdaChildren == std::vector<NodeId>({*name, *first, *second});
}

bool conditionalFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    if (!integer)
        return false;
    auto first =
        makeIntegerExpression(arena, {source::OriginId(0)}, "1", *integer);
    auto second =
        makeIntegerExpression(arena, {source::OriginId(0)}, "2", *integer);
    auto third =
        makeIntegerExpression(arena, {source::OriginId(0)}, "3", *integer);
    if (!first || !second || !third)
        return false;
    auto conditional = makeConditionalExpression(
        arena, {source::OriginId(0)}, *first, *second, *third, *integer);
    auto binary =
        makeBinaryConditionalExpression(arena, {source::OriginId(0)}, 4, *first,
                                        *second, *third, *first, *integer);
    auto offset = makeOffsetOfExpression(arena, {source::OriginId(0)}, *integer,
                                         "field", *integer);
    if (!conditional || !binary || !offset ||
        !failed(makeConditionalExpression(arena, {}, *integer, *second, *third,
                                          *integer)) ||
        !failed(makeConditionalExpression(arena, {}, *first, *second, *third,
                                          *first)) ||
        !failed(makeBinaryConditionalExpression(arena, {}, 0, *first, *integer,
                                                *third, *first, *integer)) ||
        !failed(makeBinaryConditionalExpression(arena, {}, 0, *first, *second,
                                                *third, *first, *first)) ||
        !failed(makeOffsetOfExpression(arena, {}, *first, "field", *integer)) ||
        !failed(makeOffsetOfExpression(arena, {}, *integer, "", *integer)) ||
        !failed(makeOffsetOfExpression(arena, {}, *integer, "field", *first)) ||
        failed(unit.finish()))
        return false;
    SemanticRocqEmitter emitter;
    auto conditionalTerm = emitter.renderNode(unit, *conditional);
    auto binaryTerm = emitter.renderNode(unit, *binary);
    auto offsetTerm = emitter.renderNode(unit, *offset);
    if (!conditionalTerm ||
        *conditionalTerm !=
            "(Eif (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 (Tnum "
            "int_rank.Iint Signed)) (Eint 3 (Tnum int_rank.Iint Signed)) "
            "(Tnum int_rank.Iint Signed))" ||
        !binaryTerm ||
        *binaryTerm !=
            "(Eif2 4%N (Eint 1 (Tnum int_rank.Iint Signed)) (Eint 2 (Tnum "
            "int_rank.Iint Signed)) (Eint 3 (Tnum int_rank.Iint Signed)) "
            "(Eint 1 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint "
            "Signed))" ||
        !offsetTerm ||
        *offsetTerm != "(Eoffsetof (Tnum int_rank.Iint Signed) \"field\" (Tnum "
                       "int_rank.Iint Signed))")
        return false;
    auto conditionalChildren = unit.nodes().children(*conditional);
    auto binaryChildren = unit.nodes().children(*binary);
    auto offsetChildren = unit.nodes().children(*offset);
    return conditionalChildren &&
           *conditionalChildren ==
               std::vector<NodeId>({*first, *second, *third, *integer}) &&
           binaryChildren &&
           *binaryChildren == std::vector<NodeId>({*first, *second, *third,
                                                   *first, *integer}) &&
           offsetChildren &&
           *offsetChildren == std::vector<NodeId>({*integer, *integer});
}

bool declarationFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    const OriginList origin{source::OriginId(0)};
    auto atom = makeAtomicIdentifier(arena, origin, "C");
    auto fieldAtom = makeAtomicIdentifier(arena, origin, "field");
    auto name = atom ? makeGlobalName(arena, origin, *atom)
                     : llvm::Expected<NodeId>(atom.takeError());
    auto type =
        makeNumberType(arena, origin, ScalarTerm::symbol("int_rank.Iint"),
                       ScalarTerm::symbol("Signed"));
    auto expression = type ? makeIntegerExpression(arena, origin, "1", *type)
                           : llvm::Expected<NodeId>(type.takeError());
    auto statement = makeUnsupportedStatement(arena, origin, "body");
    auto initExpression =
        expression
            ? makeGlobalInitializer(arena, Constructor::GlobalInitExpression,
                                    origin, *expression)
            : llvm::Expected<NodeId>(expression.takeError());
    auto initNone = makeGlobalInitializer(arena, Constructor::GlobalInitNone,
                                          origin, std::nullopt);
    auto initImplicit = makeGlobalInitializer(
        arena, Constructor::GlobalInitImplicit, origin, std::nullopt);
    auto initDelayed = makeGlobalInitializer(
        arena, Constructor::GlobalInitDelayed, origin, std::nullopt);
    auto initExtern = makeGlobalInitializer(
        arena, Constructor::GlobalInitExtern, origin, std::nullopt);
    auto implementation =
        statement
            ? makeFunctionBody(arena, Constructor::FunctionBodyImplementation,
                               origin, *statement)
            : llvm::Expected<NodeId>(statement.takeError());
    auto builtin = makeFunctionBody(arena, Constructor::FunctionBodyBuiltin,
                                    origin, std::nullopt, "__builtin_demo");
    auto defaulted = makeDefaultStatementBody(
        arena, Constructor::DefaultStatementBodyDefaulted, origin,
        std::nullopt);
    auto userBody =
        statement ? makeDefaultStatementBody(
                        arena, Constructor::DefaultStatementBodyUserDefined,
                        origin, *statement)
                  : llvm::Expected<NodeId>(statement.takeError());
    auto compilerBody =
        statement
            ? makeDefaultStatementBody(
                  arena, Constructor::DefaultStatementBodyCompilerProvided,
                  origin, *statement)
            : llvm::Expected<NodeId>(statement.takeError());
    auto path =
        fieldAtom
            ? makeInitializerPath(arena, Constructor::InitializerFieldPath,
                                  origin, *fieldAtom)
            : llvm::Expected<NodeId>(fieldAtom.takeError());
    auto basePath =
        name ? makeInitializerPath(arena, Constructor::InitializerBasePath,
                                   origin, *name)
             : llvm::Expected<NodeId>(name.takeError());
    auto thisPath = makeInitializerPath(arena, Constructor::InitializerThisPath,
                                        origin, std::nullopt);
    auto initializer =
        path && expression
            ? makeInitializerRecord(arena, origin, *path, *expression)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto constructorBody =
        initializer && statement
            ? makeConstructorBody(arena,
                                  Constructor::ConstructorBodyUserDefined,
                                  origin, {*initializer}, *statement)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto constructorDefault = makeConstructorBody(
        arena, Constructor::ConstructorBodyDefaulted, origin, {}, std::nullopt);
    auto constructorCompiler =
        initializer && statement
            ? makeConstructorBody(arena,
                                  Constructor::ConstructorBodyCompilerProvided,
                                  origin, {*initializer}, *statement)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    std::vector<DeclarationParameter> parameters;
    if (type) {
        parameters.push_back({ScalarTerm::localIdentifier("x"), *type});
        parameters.push_back({ScalarTerm::anonymousLocal(1), *type});
    }
    auto function =
        type && implementation
            ? makeFunctionRecord(arena, origin, *type, parameters,
                                 ScalarTerm::symbol("CC_C"),
                                 ScalarTerm::symbol("Ar_Definite"),
                                 ScalarTerm::symbol("exception_spec.MayThrow"),
                                 *implementation)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto method =
        type && name && userBody
            ? makeMethodRecord(
                  arena, origin, *type, *name, ScalarTerm::symbol("QC"),
                  parameters, ScalarTerm::symbol("CC_C"),
                  ScalarTerm::symbol("Ar_Definite"),
                  ScalarTerm::symbol("exception_spec.NoThrow"), *userBody)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto constructor =
        name && constructorBody
            ? makeConstructorRecord(
                  arena, origin, *name, parameters, ScalarTerm::symbol("CC_C"),
                  ScalarTerm::symbol("Ar_Definite"),
                  ScalarTerm::symbol("exception_spec.NoThrow"),
                  *constructorBody)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto destructor =
        name && compilerBody
            ? makeDestructorRecord(
                  arena, origin, *name, ScalarTerm::symbol("CC_C"),
                  ScalarTerm::symbol("exception_spec.NoThrow"), *compilerBody)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto memberLayout = makeLayoutInfo(arena, origin, "4");
    auto baseLayout = makeLayoutInfo(arena, origin, "0");
    auto member = fieldAtom && type && expression && memberLayout
                      ? makeMemberRecord(arena, origin, *fieldAtom, *type, true,
                                         *expression, *memberLayout)
                      : llvm::Expected<NodeId>(llvm::createStringError(
                            std::errc::invalid_argument, "missing"));
    auto structure =
        name && member && baseLayout
            ? makeStructRecord(arena, origin, {{*name, *baseLayout}}, {*member},
                               {{*name, *name}}, {{*name, *name}}, *name, false,
                               *name, ScalarTerm::symbol("Standard"), "8", "4")
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto unionValue = name && member
                          ? makeUnionRecord(arena, origin, {*member}, *name,
                                            true, std::nullopt, "4", "4")
                          : llvm::Expected<NodeId>(llvm::createStringError(
                                std::errc::invalid_argument, "missing"));
    auto objectVariable =
        type && initNone
            ? makeVariableObjectValue(arena, origin, *type, *initNone)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto objectFunction =
        function ? makeObjectValue(arena, Constructor::ObjectFunction, origin,
                                   *function)
                 : llvm::Expected<NodeId>(function.takeError());
    auto objectMethod =
        method
            ? makeObjectValue(arena, Constructor::ObjectMethod, origin, *method)
            : llvm::Expected<NodeId>(method.takeError());
    auto objectConstructor =
        constructor ? makeObjectValue(arena, Constructor::ObjectConstructor,
                                      origin, *constructor)
                    : llvm::Expected<NodeId>(constructor.takeError());
    auto objectDestructor =
        destructor ? makeObjectValue(arena, Constructor::ObjectDestructor,
                                     origin, *destructor)
                   : llvm::Expected<NodeId>(destructor.takeError());
    auto globalType = makeGlobalDeclaration(arena, Constructor::GlobalType,
                                            origin, std::nullopt);
    auto globalStruct =
        structure ? makeGlobalDeclaration(arena, Constructor::GlobalStruct,
                                          origin, *structure)
                  : llvm::Expected<NodeId>(structure.takeError());
    auto globalUnion =
        unionValue ? makeGlobalDeclaration(arena, Constructor::GlobalUnion,
                                           origin, *unionValue)
                   : llvm::Expected<NodeId>(unionValue.takeError());
    auto globalEnum =
        type ? makeEnumGlobalDeclaration(arena, origin, *type, {"A", "B"})
             : llvm::Expected<NodeId>(type.takeError());
    auto globalTypedef = type ? makeGlobalTypedef(arena, origin, *type)
                              : llvm::Expected<NodeId>(type.takeError());
    auto globalConstant =
        type && expression
            ? makeConstantGlobalDeclaration(arena, origin, *type, *expression)
            : llvm::Expected<NodeId>(llvm::createStringError(
                  std::errc::invalid_argument, "missing"));
    auto globalUnsupported = makeUnsupportedGlobalDeclaration(
        arena, origin, "unsupported declaration");
    if (!atom || !fieldAtom || !name || !type || !expression || !statement ||
        !initExpression || !initNone || !initImplicit || !initDelayed ||
        !initExtern || !implementation || !builtin || !defaulted || !userBody ||
        !compilerBody || !path || !basePath || !thisPath || !initializer ||
        !constructorBody || !constructorDefault || !constructorCompiler ||
        !function || !method || !constructor || !destructor || !memberLayout ||
        !baseLayout || !member || !structure || !unionValue ||
        !objectVariable || !objectFunction || !objectMethod ||
        !objectConstructor || !objectDestructor || !globalType ||
        !globalStruct || !globalUnion || !globalEnum || !globalTypedef ||
        !globalConstant || !globalUnsupported) {
        std::cerr << "declaration factory construction failed\n";
        return false;
    }

    auto childrenEqual = [&](NodeId node, std::vector<NodeId> expected) {
        auto children = arena.children(node);
        return children && *children == expected;
    };
    if (!childrenEqual(*function, {*type, *type, *type, *implementation}) ||
        !childrenEqual(*method, {*type, *name, *type, *type, *userBody}) ||
        !childrenEqual(*constructor, {*name, *type, *type, *constructorBody}) ||
        !childrenEqual(*destructor, {*name, *compilerBody}) ||
        !childrenEqual(*initializer, {*path, *expression}) ||
        !childrenEqual(*constructorBody, {*initializer, *statement}) ||
        !childrenEqual(*member,
                       {*fieldAtom, *type, *expression, *memberLayout}) ||
        !childrenEqual(*structure, {*name, *baseLayout, *member, *name, *name,
                                    *name, *name, *name, *name}) ||
        !childrenEqual(*unionValue, {*member, *name}) ||
        !childrenEqual(*objectVariable, {*type, *initNone}) ||
        !childrenEqual(*globalEnum, {*type}) ||
        !childrenEqual(*globalConstant, {*type, *expression})) {
        std::cerr << "declaration factory children failed\n";
        return false;
    }

    if (!failed(makeGlobalInitializer(arena, Constructor::GlobalInitExpression,
                                      {}, std::nullopt)) ||
        !failed(makeFunctionBody(arena, Constructor::FunctionBodyBuiltin, {},
                                 *statement, "builtin")) ||
        !failed(makeDefaultStatementBody(
            arena, Constructor::DefaultStatementBodyDefaulted, {},
            *statement)) ||
        !failed(makeConstructorBody(arena,
                                    Constructor::ConstructorBodyDefaulted, {},
                                    {*initializer}, std::nullopt)) ||
        !failed(makeFunctionRecord(
            arena, {}, *expression, {}, ScalarTerm::symbol("CC_C"),
            ScalarTerm::symbol("Ar_Definite"),
            ScalarTerm::symbol("exception_spec.MayThrow"), std::nullopt)) ||
        !failed(makeMethodRecord(
            arena, {}, *type, *expression, ScalarTerm::symbol("QM"), {},
            ScalarTerm::symbol("CC_C"), ScalarTerm::symbol("Ar_Definite"),
            ScalarTerm::symbol("exception_spec.MayThrow"), std::nullopt)) ||
        !failed(makeInitializerPath(arena, Constructor::InitializerBasePath, {},
                                    *fieldAtom)) ||
        !failed(makeInitializerPath(arena, Constructor::InitializerThisPath, {},
                                    *name)) ||
        !failed(makeInitializerRecord(arena, {}, *expression, *expression)) ||
        !failed(makeConstructorRecord(
            arena, {}, *expression, {}, ScalarTerm::symbol("CC_C"),
            ScalarTerm::symbol("Ar_Definite"),
            ScalarTerm::symbol("exception_spec.MayThrow"), std::nullopt)) ||
        !failed(makeDestructorRecord(
            arena, {}, *expression, ScalarTerm::symbol("CC_C"),
            ScalarTerm::symbol("exception_spec.MayThrow"), std::nullopt)) ||
        !failed(makeLayoutInfo(arena, {}, "")) ||
        !failed(makeMemberRecord(arena, {}, *name, *type, false, std::nullopt,
                                 *memberLayout)) ||
        !failed(makeStructRecord(arena, {}, {{*name, *type}}, {}, {}, {}, *name,
                                 true, std::nullopt, ScalarTerm::symbol("POD"),
                                 "1", "1")) ||
        !failed(makeUnionRecord(arena, {}, {*function}, *name, true,
                                std::nullopt, "1", "1")) ||
        !failed(
            makeObjectValue(arena, Constructor::ObjectMethod, {}, *function)) ||
        !failed(makeVariableObjectValue(arena, {}, *type, *expression)) ||
        !failed(makeGlobalDeclaration(arena, Constructor::GlobalStruct, {},
                                      *unionValue)) ||
        !failed(makeEnumGlobalDeclaration(arena, {}, *expression, {"A"})) ||
        !failed(makeConstantGlobalDeclaration(arena, {}, *type, *statement)) ||
        !failed(makeUnsupportedGlobalDeclaration(arena, {}, ""))) {
        std::cerr << "declaration malformed factory accepted input\n";
        return false;
    }
    if (failed(unit.finish())) {
        std::cerr << "declaration finish failed\n";
        return false;
    }
    SemanticRocqEmitter emitter;
    const std::vector<std::pair<NodeId, std::string>> expected{
        {*initExpression,
         "(global_init.Init (Eint 1 (Tnum int_rank.Iint Signed)))"},
        {*initNone, "(global_init.NoInit)"},
        {*initImplicit, "(global_init.ImplicitInit)"},
        {*initDelayed, "(global_init.Delayed)"},
        {*initExtern, "(global_init.Extern)"},
        {*implementation, "(Impl (Sunsupported \"body\"))"},
        {*builtin, "(Builtin \"__builtin_demo\")"},
        {*defaulted, "(Defaulted)"},
        {*userBody, "(UserDefined (Sunsupported \"body\"))"},
        {*compilerBody, "(CompilerProvided (Sunsupported \"body\"))"},
        {*path, "(InitField (Nid \"field\"))"},
        {*basePath, "(InitBase (Nglobal (Nid \"C\")))"},
        {*thisPath, "(InitThis)"},
        {*initializer, "(Build_Initializer (InitField (Nid \"field\")) (Eint 1 "
                       "(Tnum int_rank.Iint Signed)))"},
        {*constructorBody,
         "(UserDefined (((Build_Initializer (InitField (Nid \"field\")) "
         "(Eint 1 (Tnum int_rank.Iint Signed))) :: nil), "
         "(Sunsupported \"body\")))"},
        {*constructorDefault, "(Defaulted)"},
        {*constructorCompiler,
         "(CompilerProvided (((Build_Initializer (InitField (Nid "
         "\"field\")) (Eint 1 (Tnum int_rank.Iint Signed))) :: nil), "
         "(Sunsupported \"body\")))"},
        {*function,
         "(Build_Func (Tnum int_rank.Iint Signed) ((\"x\", (Tnum "
         "int_rank.Iint Signed)) :: ((localname.anon 1%N), (Tnum "
         "int_rank.Iint Signed)) :: nil) CC_C Ar_Definite "
         "exception_spec.MayThrow (Some (Impl (Sunsupported \"body\"))))"},
        {*method,
         "(Build_Method (Tnum int_rank.Iint Signed) (Nglobal (Nid \"C\")) "
         "QC ((\"x\", (Tnum int_rank.Iint Signed)) :: "
         "((localname.anon 1%N), (Tnum int_rank.Iint Signed)) :: nil) CC_C "
         "Ar_Definite exception_spec.NoThrow (Some (UserDefined "
         "(Sunsupported \"body\"))))"},
        {*constructor,
         "(Build_Ctor (Nglobal (Nid \"C\")) ((\"x\", (Tnum "
         "int_rank.Iint Signed)) :: ((localname.anon 1%N), (Tnum "
         "int_rank.Iint Signed)) :: nil) CC_C Ar_Definite "
         "exception_spec.NoThrow (Some (UserDefined (((Build_Initializer "
         "(InitField (Nid \"field\")) (Eint 1 (Tnum int_rank.Iint "
         "Signed))) :: nil), (Sunsupported \"body\")))))"},
        {*destructor,
         "(Build_Dtor (Nglobal (Nid \"C\")) CC_C exception_spec.NoThrow "
         "(Some (CompilerProvided (Sunsupported \"body\"))))"},
        {*memberLayout, "(Build_LayoutInfo 4)"},
        {*baseLayout, "(Build_LayoutInfo 0)"},
        {*member, "(mkMember (Nid \"field\") (Tnum int_rank.Iint Signed) true "
                  "(Some (Eint 1 (Tnum int_rank.Iint Signed))) "
                  "(Build_LayoutInfo 4))"},
        {*structure,
         "(Build_Struct (((Nglobal (Nid \"C\")), (Build_LayoutInfo 0)) :: "
         "nil) ((mkMember (Nid \"field\") (Tnum int_rank.Iint Signed) "
         "true (Some (Eint 1 (Tnum int_rank.Iint Signed))) "
         "(Build_LayoutInfo 4)) :: nil) (((Nglobal (Nid \"C\")), "
         "(Some (Nglobal (Nid \"C\")))) :: nil) (((Nglobal (Nid "
         "\"C\")), (Nglobal (Nid \"C\"))) :: nil) (Nglobal (Nid \"C\")) "
         "false (Some (Nglobal (Nid \"C\"))) Standard 8 4)"},
        {*unionValue,
         "(Build_Union ((mkMember (Nid \"field\") (Tnum int_rank.Iint "
         "Signed) true (Some (Eint 1 (Tnum int_rank.Iint Signed))) "
         "(Build_LayoutInfo 4)) :: nil) (Nglobal (Nid \"C\")) true None 4 "
         "4)"},
        {*objectVariable,
         "(Ovar (Tnum int_rank.Iint Signed) (global_init.NoInit))"},
        {*objectFunction,
         "(Ofunction (Build_Func (Tnum int_rank.Iint Signed) ((\"x\", "
         "(Tnum int_rank.Iint Signed)) :: ((localname.anon 1%N), (Tnum "
         "int_rank.Iint Signed)) :: nil) CC_C Ar_Definite "
         "exception_spec.MayThrow (Some (Impl (Sunsupported \"body\")))))"},
        {*objectMethod,
         "(Omethod (Build_Method (Tnum int_rank.Iint Signed) (Nglobal (Nid "
         "\"C\")) QC ((\"x\", (Tnum int_rank.Iint Signed)) :: "
         "((localname.anon 1%N), (Tnum int_rank.Iint Signed)) :: nil) CC_C "
         "Ar_Definite exception_spec.NoThrow (Some (UserDefined "
         "(Sunsupported \"body\")))))"},
        {*objectConstructor,
         "(Oconstructor (Build_Ctor (Nglobal (Nid \"C\")) ((\"x\", "
         "(Tnum int_rank.Iint Signed)) :: ((localname.anon 1%N), (Tnum "
         "int_rank.Iint Signed)) :: nil) CC_C Ar_Definite "
         "exception_spec.NoThrow (Some (UserDefined (((Build_Initializer "
         "(InitField (Nid \"field\")) (Eint 1 (Tnum int_rank.Iint "
         "Signed))) :: nil), (Sunsupported \"body\"))))))"},
        {*objectDestructor,
         "(Odestructor (Build_Dtor (Nglobal (Nid \"C\")) CC_C "
         "exception_spec.NoThrow (Some (CompilerProvided (Sunsupported "
         "\"body\")))))"},
        {*globalType, "(Gtype)"},
        {*globalStruct,
         "(Gstruct (Build_Struct (((Nglobal (Nid \"C\")), "
         "(Build_LayoutInfo 0)) :: nil) ((mkMember (Nid \"field\") (Tnum "
         "int_rank.Iint Signed) true (Some (Eint 1 (Tnum int_rank.Iint "
         "Signed))) (Build_LayoutInfo 4)) :: nil) (((Nglobal (Nid "
         "\"C\")), (Some (Nglobal (Nid \"C\")))) :: nil) (((Nglobal (Nid "
         "\"C\")), (Nglobal (Nid \"C\"))) :: nil) (Nglobal (Nid \"C\")) "
         "false (Some (Nglobal (Nid \"C\"))) Standard 8 4))"},
        {*globalUnion,
         "(Gunion (Build_Union ((mkMember (Nid \"field\") (Tnum "
         "int_rank.Iint Signed) true (Some (Eint 1 (Tnum int_rank.Iint "
         "Signed))) (Build_LayoutInfo 4)) :: nil) (Nglobal (Nid \"C\")) "
         "true None 4 4))"},
        {*globalEnum,
         "(Genum (Tnum int_rank.Iint Signed) (\"A\" :: \"B\" :: nil))"},
        {*globalTypedef, "(Gtypedef (Tnum int_rank.Iint Signed))"},
        {*globalConstant,
         "(Gconstant (Tnum int_rank.Iint Signed) (Some (Eint 1 (Tnum "
         "int_rank.Iint Signed))))"},
        {*globalUnsupported, "(Gunsupported \"unsupported declaration\")"}};
    for (const auto &[node, text] : expected) {
        auto rendered = emitter.renderNode(unit, node);
        if (!rendered || *rendered != text) {
            std::cerr << "declaration render mismatch expected: " << text
                      << "\nactual: " << (rendered ? *rendered : "<error>")
                      << '\n';
            return false;
        }
    }
    return true;
}

bool statementAndLocalFactories() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto integer = makeNumberType(arena, {source::OriginId(0)},
                                  ScalarTerm::symbol("int_rank.Iint"),
                                  ScalarTerm::symbol("Signed"));
    auto atomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "global");
    auto name = atomic ? makeGlobalName(arena, {source::OriginId(0)}, *atomic)
                       : llvm::Expected<NodeId>(atomic.takeError());
    auto expression =
        integer
            ? makeIntegerExpression(arena, {source::OriginId(0)}, "1", *integer)
            : llvm::Expected<NodeId>(integer.takeError());
    if (!integer || !name || !expression)
        return false;
    auto variable = makeVariableDeclaration(arena, {source::OriginId(0)},
                                            "local", *integer, *expression);
    auto bindingVariable = makeBindingDeclaration(
        arena, Constructor::BindingVariable, {source::OriginId(0)}, "held",
        *integer, *expression);
    auto bindingReference = makeBindingDeclaration(
        arena, Constructor::BindingReference, {source::OriginId(0)}, "bound",
        *integer, *expression);
    if (!variable || !bindingVariable || !bindingReference)
        return false;
    auto decomposition =
        makeVariableDecomposition(arena, {source::OriginId(0)}, *expression, 0,
                                  {*bindingVariable, *bindingReference});
    auto staticVariable = makeStaticVariableDeclaration(
        arena, {source::OriginId(0)}, true, *name, *integer, std::nullopt);
    auto expressionStatement =
        makeExpressionStatement(arena, {source::OriginId(0)}, *expression);
    auto returnValue =
        makeReturnStatement(arena, {source::OriginId(0)}, *expression);
    auto returnVoid =
        makeReturnStatement(arena, {source::OriginId(0)}, std::nullopt);
    auto empty = makeStatementSequence(arena, {source::OriginId(0)}, {});
    if (!decomposition || !staticVariable || !expressionStatement ||
        !returnValue || !returnVoid || !empty)
        return false;
    auto declaration =
        makeDeclarationStatement(arena, {source::OriginId(0)},
                                 {*variable, *decomposition, *staticVariable});
    auto ifStatement =
        makeIfStatement(arena, {source::OriginId(0)}, *expressionStatement,
                        *variable, *expression, *expressionStatement, *empty);
    auto ifConsteval = makeIfConstevalStatement(arena, {source::OriginId(0)},
                                                *expressionStatement, *empty);
    auto whileStatement = makeWhileStatement(arena, {source::OriginId(0)},
                                             *variable, *expression, *empty);
    auto forStatement =
        makeForStatement(arena, {source::OriginId(0)}, *expressionStatement,
                         *expression, std::nullopt, *empty);
    auto doStatement =
        makeDoStatement(arena, {source::OriginId(0)}, *empty, *expression);
    auto switchStatement =
        makeSwitchStatement(arena, {source::OriginId(0)}, std::nullopt,
                            *variable, *expression, *empty);
    auto caseStatement = makeCaseStatement(arena, {source::OriginId(0)},
                                           ScalarTerm::switchBranchExact("1"));
    auto defaultStatement = makeLeafStatement(
        arena, Constructor::StatementDefault, {source::OriginId(0)});
    auto breakStatement = makeLeafStatement(arena, Constructor::StatementBreak,
                                            {source::OriginId(0)});
    auto continueStatement = makeLeafStatement(
        arena, Constructor::StatementContinue, {source::OriginId(0)});
    auto attribute = makeAttributeStatement(arena, {source::OriginId(0)},
                                            {"nodiscard"}, *empty);
    auto asmStatement = makeAsmStatement(arena, {source::OriginId(0)}, "mov",
                                         true, {{"r", *expression}},
                                         {{"=r", *expression}}, {"memory"});
    auto labeled =
        makeLabeledStatement(arena, {source::OriginId(0)}, "label", *empty);
    auto goTo = makeGotoStatement(arena, {source::OriginId(0)}, "label");
    auto unsupported = makeUnsupportedStatement(arena, {source::OriginId(0)},
                                                "empty statement");
    auto requireBuilt = [&](llvm::Expected<NodeId> &value,
                            llvm::StringRef label) {
        if (value)
            return true;
        std::cerr << label.str() << ": " << llvm::toString(value.takeError())
                  << '\n';
        return false;
    };
    if (!requireBuilt(declaration, "declaration") ||
        !requireBuilt(ifStatement, "if") ||
        !requireBuilt(ifConsteval, "if consteval") ||
        !requireBuilt(whileStatement, "while") ||
        !requireBuilt(forStatement, "for") ||
        !requireBuilt(doStatement, "do") ||
        !requireBuilt(switchStatement, "switch") ||
        !requireBuilt(caseStatement, "case") ||
        !requireBuilt(defaultStatement, "default") ||
        !requireBuilt(breakStatement, "break") ||
        !requireBuilt(continueStatement, "continue") ||
        !requireBuilt(attribute, "attribute") ||
        !requireBuilt(asmStatement, "asm") || !requireBuilt(labeled, "label") ||
        !requireBuilt(goTo, "goto") ||
        !requireBuilt(unsupported, "unsupported"))
        return false;
    const std::vector<bool> rejected{
        failed(makeVariableDeclaration(arena, {}, "bad", *expression,
                                       std::nullopt)),
        failed(makeVariableDeclaration(arena, {}, "bad", *integer, *integer)),
        failed(makeStaticVariableDeclaration(arena, {}, true, *expression,
                                             *integer, std::nullopt)),
        failed(makeStaticVariableDeclaration(arena, {}, true, *name,
                                             *expression, std::nullopt)),
        failed(makeStaticVariableDeclaration(arena, {}, true, *name, *integer,
                                             *integer)),
        failed(makeBindingDeclaration(arena, Constructor::VariableDeclaration,
                                      {}, "bad", *integer, *expression)),
        failed(makeBindingDeclaration(arena, Constructor::BindingVariable, {},
                                      "bad", *expression, *expression)),
        failed(makeBindingDeclaration(arena, Constructor::BindingReference, {},
                                      "bad", *integer, *integer)),
        failed(makeVariableDecomposition(arena, {}, *integer, 0,
                                         {*bindingVariable})),
        failed(
            makeVariableDecomposition(arena, {}, *expression, 0, {*variable})),
        failed(makeExpressionStatement(arena, {}, *integer)),
        failed(makeReturnStatement(arena, {}, *integer)),
        failed(makeStatementSequence(arena, {},
                                     {*expressionStatement, *expression})),
        failed(makeDeclarationStatement(arena, {}, {*expression})),
        failed(makeIfStatement(arena, {}, *expression, *variable, *expression,
                               *empty, *empty)),
        failed(makeIfStatement(arena, {}, *expressionStatement, *expression,
                               *expression, *empty, *empty)),
        failed(makeIfStatement(arena, {}, *expressionStatement, *variable,
                               *integer, *empty, *empty)),
        failed(makeIfConstevalStatement(arena, {}, *expression, *empty)),
        failed(makeWhileStatement(arena, {}, *expression, *expression, *empty)),
        failed(makeWhileStatement(arena, {}, *variable, *integer, *empty)),
        failed(makeForStatement(arena, {}, *expression, *expression,
                                std::nullopt, *empty)),
        failed(makeForStatement(arena, {}, *expressionStatement, *integer,
                                std::nullopt, *empty)),
        failed(makeForStatement(arena, {}, *expressionStatement, *expression,
                                *integer, *empty)),
        failed(makeForStatement(arena, {}, *expressionStatement, *expression,
                                std::nullopt, *integer)),
        failed(makeDoStatement(arena, {}, *expression, *expression)),
        failed(makeDoStatement(arena, {}, *empty, *integer)),
        failed(makeSwitchStatement(arena, {}, *expression, *variable,
                                   *expression, *empty)),
        failed(makeSwitchStatement(arena, {}, *expressionStatement, *expression,
                                   *expression, *empty)),
        failed(makeSwitchStatement(arena, {}, *expressionStatement, *variable,
                                   *integer, *empty)),
        failed(makeSwitchStatement(arena, {}, *expressionStatement, *variable,
                                   *expression, *integer)),
        failed(makeLeafStatement(arena, Constructor::StatementSequence, {})),
        failed(makeCaseStatement(arena, {}, ScalarTerm::string("bad"))),
        failed(makeAttributeStatement(arena, {}, {""}, *empty)),
        failed(makeAttributeStatement(arena, {}, {"ok"}, *expression)),
        failed(makeAsmStatement(arena, {}, "mov", false, {{"r", *integer}}, {},
                                {})),
        failed(makeAsmStatement(arena, {}, "mov", false, {}, {{"=r", *integer}},
                                {})),
        failed(makeLabeledStatement(arena, {}, "", *empty)),
        failed(makeLabeledStatement(arena, {}, "label", *expression)),
        failed(makeGotoStatement(arena, {}, "")),
        failed(makeUnsupportedStatement(arena, {}, ""))};
    for (std::size_t index = 0; index < rejected.size(); ++index)
        if (!rejected[index]) {
            std::cerr << "malformed statement/local accepted: " << index
                      << '\n';
            return false;
        }
    if (auto failure = unit.finish()) {
        std::cerr << "statement/local finish: "
                  << llvm::toString(std::move(failure)) << '\n';
        return false;
    }
    SemanticRocqEmitter emitter;
    const std::string typeTerm = "(Tnum int_rank.Iint Signed)";
    const std::string expressionTerm = "(Eint 1 " + typeTerm + ")";
    const std::string nameTerm = "(Nglobal (Nid \"global\"))";
    const std::string variableText =
        "(Dvar \"local\" " + typeTerm + " (Some " + expressionTerm + "))";
    const std::string bindingVariableText =
        "(Bvar \"held\" " + typeTerm + " " + expressionTerm + ")";
    const std::string bindingReferenceText =
        "(Bbind \"bound\" " + typeTerm + " " + expressionTerm + ")";
    const std::string decompositionText =
        "(Ddecompose " + expressionTerm + " (localname.anon 0%N) (" +
        bindingVariableText + " :: " + bindingReferenceText + " :: nil))";
    const std::string staticVariableText =
        "(Dinit true " + nameTerm + " " + typeTerm + " None)";
    const std::string expressionStatementText =
        "(Sexpr " + expressionTerm + ")";
    const std::string emptyText = "(Sseq nil)";
    const std::string declarationText =
        "(Sdecl (" + variableText + " :: " + decompositionText +
        " :: " + staticVariableText + " :: nil))";
    const std::string ifText = "(Sif (Some " + expressionStatementText +
                               ") (Some " + variableText + ") " +
                               expressionTerm + " " + expressionStatementText +
                               " " + emptyText + ")";
    const std::string asmText = "(Sasm \"mov\" true ((\"r\", " +
                                expressionTerm + ") :: nil) ((\"=r\", " +
                                expressionTerm +
                                ") :: nil) (\"memory\" :: nil))";
    const std::vector<std::pair<NodeId, std::string>> rendered{
        {*variable, variableText},
        {*bindingVariable, bindingVariableText},
        {*bindingReference, bindingReferenceText},
        {*decomposition, decompositionText},
        {*staticVariable, staticVariableText},
        {*expressionStatement, expressionStatementText},
        {*returnValue, "(Sreturn (Some " + expressionTerm + "))"},
        {*returnVoid, "(Sreturn None)"},
        {*empty, emptyText},
        {*declaration, declarationText},
        {*ifStatement, ifText},
        {*ifConsteval,
         "(Sif_consteval " + expressionStatementText + " " + emptyText + ")"},
        {*whileStatement, "(Swhile (Some " + variableText + ") " +
                              expressionTerm + " " + emptyText + ")"},
        {*forStatement, "(Sfor (Some " + expressionStatementText + ") (Some " +
                            expressionTerm + ") None " + emptyText + ")"},
        {*doStatement, "(Sdo " + emptyText + " " + expressionTerm + ")"},
        {*switchStatement, "(Sswitch None (Some " + variableText + ") " +
                               expressionTerm + " " + emptyText + ")"},
        {*caseStatement, "(Scase (Exact 1%Z))"},
        {*defaultStatement, "(Sdefault)"},
        {*breakStatement, "(Sbreak)"},
        {*continueStatement, "(Scontinue)"},
        {*attribute, "(Sattr (\"nodiscard\" :: nil) " + emptyText + ")"},
        {*asmStatement, asmText},
        {*labeled, "(Slabeled \"label\" " + emptyText + ")"},
        {*goTo, "(Sgoto \"label\")"},
        {*unsupported, "(Sunsupported \"empty statement\")"}};
    for (const auto &[node, expected] : rendered) {
        auto actual = emitter.renderNode(unit, node);
        if (!actual || *actual != expected) {
            std::cerr << "statement/local rendering mismatch: expected "
                      << expected << " got ";
            if (actual)
                std::cerr << *actual;
            else
                std::cerr << llvm::toString(actual.takeError());
            std::cerr << '\n';
            return false;
        }
    }
    auto childrenAre = [&](NodeId node, std::vector<NodeId> expected) {
        auto actual = unit.nodes().children(node);
        return actual && *actual == expected;
    };
    return childrenAre(*variable, {*integer, *expression}) &&
           childrenAre(*bindingVariable, {*integer, *expression}) &&
           childrenAre(*bindingReference, {*integer, *expression}) &&
           childrenAre(*decomposition,
                       {*expression, *bindingVariable, *bindingReference}) &&
           childrenAre(*staticVariable, {*name, *integer}) &&
           childrenAre(*expressionStatement, {*expression}) &&
           childrenAre(*returnValue, {*expression}) &&
           childrenAre(*returnVoid, {}) && childrenAre(*empty, {}) &&
           childrenAre(*declaration,
                       {*variable, *decomposition, *staticVariable}) &&
           childrenAre(*ifStatement,
                       {*expressionStatement, *variable, *expression,
                        *expressionStatement, *empty}) &&
           childrenAre(*ifConsteval, {*expressionStatement, *empty}) &&
           childrenAre(*whileStatement, {*variable, *expression, *empty}) &&
           childrenAre(*forStatement,
                       {*expressionStatement, *expression, *empty}) &&
           childrenAre(*doStatement, {*empty, *expression}) &&
           childrenAre(*switchStatement, {*variable, *expression, *empty}) &&
           childrenAre(*caseStatement, {}) &&
           childrenAre(*defaultStatement, {}) &&
           childrenAre(*breakStatement, {}) &&
           childrenAre(*continueStatement, {}) &&
           childrenAre(*attribute, {*empty}) &&
           childrenAre(*asmStatement, {*expression, *expression}) &&
           childrenAre(*labeled, {*empty}) && childrenAre(*goTo, {}) &&
           childrenAre(*unsupported, {});
}

bool sharingMetadataAndAnalysis() {
    TranslationUnitIR unit;
    (void)unit.setSources(tables());
    auto &arena = unit.buildingArena();
    using namespace ir::factory;
    auto recordAtomic = makeAtomicIdentifier(arena, {source::OriginId(0)}, "R");
    auto recordName =
        recordAtomic
            ? makeGlobalName(arena, {source::OriginId(0)}, *recordAtomic)
            : llvm::Expected<NodeId>(recordAtomic.takeError());
    auto named = recordName
                     ? makeNamedType(arena, {source::OriginId(0)}, *recordName)
                     : llvm::Expected<NodeId>(recordName.takeError());
    auto pointer0 = named ? makeUnaryType(arena, Constructor::TypePointer,
                                          {source::OriginId(0)}, *named)
                          : llvm::Expected<NodeId>(named.takeError());
    auto pointer1 = named ? makeUnaryType(arena, Constructor::TypePointer,
                                          {source::OriginId(1)}, *named)
                          : llvm::Expected<NodeId>(named.takeError());
    auto functionAtomic =
        pointer0
            ? makeAtomicFunction(arena, {source::OriginId(0)},
                                 ScalarTerm::symbol("function_qualifiers.N"),
                                 "f", {*pointer0})
            : llvm::Expected<NodeId>(pointer0.takeError());
    auto functionName =
        functionAtomic
            ? makeGlobalName(arena, {source::OriginId(0)}, *functionAtomic)
            : llvm::Expected<NodeId>(functionAtomic.takeError());
    auto ineligible =
        makeLeafType(arena, Constructor::TypeBoolean, {source::OriginId(0)});
    if (!recordName || !named || !pointer0 || !pointer1 || !functionName ||
        !ineligible)
        return false;
    auto name0 = unit.addShareClass(ShareClassKind::Name);
    auto type0 = unit.addShareClass(ShareClassKind::Type);
    auto type1 = unit.addShareClass(ShareClassKind::Type);
    auto name1 = unit.addShareClass(ShareClassKind::Name);
    auto ineligibleClass = unit.addShareClass(ShareClassKind::Type);
    if (!name0 || !type0 || !type1 || !name1 || !ineligibleClass ||
        failed(arena.setShareClass(*recordName, *name0)) ||
        failed(arena.setShareClass(*named, *type0)) ||
        failed(arena.setShareClass(*pointer0, *type1)) ||
        failed(arena.setShareClass(*pointer1, *type1)) ||
        failed(arena.setShareClass(*functionName, *name1)) ||
        failed(arena.setShareClass(*ineligible, *ineligibleClass)) ||
        failed(unit.finish()))
        return false;
    auto plan = IRSharing::analyze(
        unit, {{SharingSeedKind::Ordinary, *pointer0, *functionName}});
    if (!plan || plan->definitions().size() != 4 ||
        plan->definitions()[0].localName != "n1" ||
        plan->definitions()[1].localName != "t1" ||
        plan->definitions()[2].localName != "t2" ||
        plan->definitions()[3].localName != "n2")
        return false;
    SemanticRocqEmitter shared;
    SemanticRocqEmitter inlineEmitter({false});
    auto reference = shared.renderNode(unit, *pointer1, *plan);
    auto inlined = inlineEmitter.renderNode(unit, *pointer1, *plan);
    auto definitions = shared.emitSharingDefinitions(unit, *plan);
    SemanticRocqEmitter production({true, true, false});
    auto productionDefinitions = production.emitSharingDefinitions(unit, *plan);
    if (!reference || *reference != "t2" || !inlined ||
        *inlined != "(Tptr (Tnamed (Nglobal (Nid \"R\"))))" || !definitions ||
        !contains(*definitions, "Definition t2") || !productionDefinitions ||
        !contains(*productionDefinitions, "#[local] Definition t2 : type :=") ||
        !contains(*productionDefinitions, "#[local] Definition n2 : name :=") ||
        !failed(arena.setShareClass(*pointer0, *type1)) ||
        !failed(unit.addShareClass(ShareClassKind::Type)))
        return false;

    auto rejectsPlan = [&](std::vector<SharingDefinition> malformed) {
        SharingPlan candidate =
            SharingPlan::fromUnvalidatedDefinitions(std::move(malformed));
        return failed(IRSharing::validate(unit, candidate)) &&
               failed(shared.emitSharingDefinitions(unit, candidate)) &&
               failed(shared.renderNode(unit, *pointer1, candidate));
    };
    const std::vector<SharingDefinition> valid = plan->definitions();
    auto invalidClass = valid;
    invalidClass[0].shareClass = ShareClassId(99);
    auto wrongPlanKind = valid;
    wrongPlanKind[0].kind = ShareClassKind::Type;
    auto wrongRepresentative = valid;
    wrongRepresentative[0].representative = *functionName;
    auto ineligibleDefinition = valid;
    ineligibleDefinition.push_back(
        {*ineligibleClass, ShareClassKind::Type, *ineligible, "t3"});
    auto invalidOrder = valid;
    std::swap(invalidOrder[1].shareClass, invalidOrder[2].shareClass);
    std::swap(invalidOrder[1].representative, invalidOrder[2].representative);
    auto duplicate = valid;
    duplicate.push_back(valid[0]);
    auto unstableName = valid;
    unstableName[0].localName = "n9";
    if (!rejectsPlan(std::move(invalidClass)) ||
        !rejectsPlan(std::move(wrongPlanKind)) ||
        !rejectsPlan(std::move(wrongRepresentative)) ||
        !rejectsPlan(std::move(ineligibleDefinition)) ||
        !rejectsPlan(std::move(invalidOrder)) ||
        !rejectsPlan(std::move(duplicate)) ||
        !rejectsPlan(std::move(unstableName)))
        return false;

    // Reusing a structurally indexed plan with another unit must recheck the
    // target unit's class semantics instead of trusting coincident IDs.
    TranslationUnitIR cross;
    (void)cross.setSources(tables());
    auto &crossArena = cross.buildingArena();
    auto crossAtomic = makeAtomicIdentifier(crossArena, {}, "R");
    auto crossName = crossAtomic
                         ? makeGlobalName(crossArena, {}, *crossAtomic)
                         : llvm::Expected<NodeId>(crossAtomic.takeError());
    auto crossNamed = crossName ? makeNamedType(crossArena, {}, *crossName)
                                : llvm::Expected<NodeId>(crossName.takeError());
    auto crossPointer0 =
        crossNamed ? makeUnaryType(crossArena, Constructor::TypePointer, {},
                                   *crossNamed)
                   : llvm::Expected<NodeId>(crossNamed.takeError());
    auto crossPointer1 =
        crossNamed ? makeUnaryType(crossArena, Constructor::TypeLvalueReference,
                                   {}, *crossNamed)
                   : llvm::Expected<NodeId>(crossNamed.takeError());
    auto crossFunctionAtomic =
        crossPointer0
            ? makeAtomicFunction(crossArena, {},
                                 ScalarTerm::symbol("function_qualifiers.N"),
                                 "f", {*crossPointer0})
            : llvm::Expected<NodeId>(crossPointer0.takeError());
    auto crossFunction =
        crossFunctionAtomic
            ? makeGlobalName(crossArena, {}, *crossFunctionAtomic)
            : llvm::Expected<NodeId>(crossFunctionAtomic.takeError());
    auto crossIneligible =
        makeLeafType(crossArena, Constructor::TypeBoolean, {});
    auto crossName0 = cross.addShareClass(ShareClassKind::Name);
    auto crossType0 = cross.addShareClass(ShareClassKind::Type);
    auto crossType1 = cross.addShareClass(ShareClassKind::Type);
    auto crossName1 = cross.addShareClass(ShareClassKind::Name);
    auto crossUnused = cross.addShareClass(ShareClassKind::Type);
    if (!crossName || !crossNamed || !crossPointer0 || !crossPointer1 ||
        !crossFunction || !crossIneligible || !crossName0 || !crossType0 ||
        !crossType1 || !crossName1 || !crossUnused ||
        failed(crossArena.setShareClass(*crossName, *crossName0)) ||
        failed(crossArena.setShareClass(*crossNamed, *crossType0)) ||
        failed(crossArena.setShareClass(*crossPointer0, *crossType1)) ||
        failed(crossArena.setShareClass(*crossPointer1, *crossType1)) ||
        failed(crossArena.setShareClass(*crossFunction, *crossName1)) ||
        failed(crossArena.setShareClass(*crossIneligible, *crossUnused)) ||
        failed(cross.finish()) || !failed(IRSharing::validate(cross, *plan)) ||
        !failed(shared.emitSharingDefinitions(cross, *plan)) ||
        !failed(shared.renderNode(cross, *crossPointer1, *plan)))
        return false;

    TranslationUnitIR unequal;
    (void)unequal.setSources(tables());
    auto &unequalArena = unequal.buildingArena();
    auto atomic = makeAtomicIdentifier(unequalArena, {}, "seed");
    auto seedName = atomic ? makeGlobalName(unequalArena, {}, *atomic)
                           : llvm::Expected<NodeId>(atomic.takeError());
    auto boolean = makeLeafType(unequalArena, Constructor::TypeBoolean, {});
    auto voidType = makeLeafType(unequalArena, Constructor::TypeVoid, {});
    auto badClass = unequal.addShareClass(ShareClassKind::Type);
    if (!seedName || !boolean || !voidType || !badClass ||
        failed(unequalArena.setShareClass(*boolean, *badClass)) ||
        failed(unequalArena.setShareClass(*voidType, *badClass)) ||
        failed(unequal.finish()) ||
        !failed(IRSharing::analyze(
            unequal, {{SharingSeedKind::Ordinary, *boolean, *seedName}})))
        return false;

    TranslationUnitIR invalid;
    (void)invalid.setSources(tables());
    auto invalidType =
        makeLeafType(invalid.buildingArena(), Constructor::TypeBoolean, {});
    if (!invalidType ||
        failed(invalid.buildingArena().setShareClass(*invalidType,
                                                     ShareClassId(99))) ||
        !failed(invalid.finish()))
        return false;

    TranslationUnitIR wrongKind;
    (void)wrongKind.setSources(tables());
    auto wrongType =
        makeLeafType(wrongKind.buildingArena(), Constructor::TypeBoolean, {});
    auto wrongClass = wrongKind.addShareClass(ShareClassKind::Name);
    if (!wrongType || !wrongClass ||
        failed(
            wrongKind.buildingArena().setShareClass(*wrongType, *wrongClass)) ||
        !failed(wrongKind.finish()))
        return false;
    return true;
}

bool unfinishedEmissionRejected() {
    TranslationUnitIR unit;
    Built built = buildCore(unit);
    return failed(SemanticRocqEmitter().emit(unit)) &&
           failed(LocationRocqEmitter().emit(unit)) &&
           failed(LocationRocqEmitter().renderTree(unit, built.object));
}

std::string boundaryMacroName(std::uint32_t index) {
    return "BOUNDARY_MACRO_" + std::to_string(index) + "_" +
           std::string(80, 'x');
}

bool emitIndexedBoundaryFixture(const std::string &path) {
    constexpr std::uint32_t originCount = 8193;
    constexpr std::uint32_t rangeCount = 4096;
    constexpr std::uint32_t presumedCount = 4095;
    constexpr std::uint32_t frameCount = 4097;

    source::Tables sources;
    sources.files.push_back({"boundary.cpp", std::nullopt,
                             source::FileKind::User, true, std::nullopt});
    const source::FileId file(0);
    sources.origins.reserve(originCount);
    for (std::uint32_t index = 0; index < originCount; ++index) {
        source::Origin origin;
        if (index < rangeCount) {
            const source::PhysicalPoint point{file, index * 4ULL, index + 1, 1};
            const source::Range range{point, std::nullopt,
                                      source::RangeKind::Character,
                                      std::nullopt};
            origin.spelling = range;
            if (index == 0) {
                origin.expansion = range;
                origin.pointOfInstantiation = point;
            }
        }
        if (index == 0) {
            origin.presumedBegin =
                source::PresumedPoint{"boundary-logical.cpp", 100, 101};
            origin.presumedEnd =
                source::PresumedPoint{"boundary-logical.cpp", 102, 103};
            origin.anchor = source::OriginId(1);
            origin.derivedFrom = {source::OriginId(1)};
        } else if (index <= presumedCount - 2) {
            origin.presumedBegin = source::PresumedPoint{
                "boundary-logical.cpp", index + 200, index + 300};
        }
        const std::uint32_t frame =
            index < frameCount ? index : index - frameCount;
        origin.macroStack.push_back({boundaryMacroName(frame),
                                     source::MacroOriginKind::Body,
                                     std::nullopt, std::nullopt});
        if (index + 1 == originCount)
            origin.kind = source::OriginKind::Inherited;
        sources.origins.push_back(std::move(origin));
    }

    TranslationUnitIR unit;
    if (failed(unit.setSources(std::move(sources))) || failed(unit.finish()))
        return false;

    namespace location_encoding = ir::location::encoding;
    location_encoding::EncodedLocations boundaryDag;
    boundaryDag.sourceOriginCount = originCount;
    constexpr std::uint32_t shapeCount = 4097;
    boundaryDag.shapes.reserve(shapeCount);
    for (std::uint32_t index = 0; index < shapeCount; ++index) {
        location_encoding::EncodedShape shape;
        if (index != 0)
            shape.children.push_back(location_encoding::ShapeId(index - 1));
        boundaryDag.shapes.push_back(std::move(shape));
    }
    boundaryDag.nodes.reserve(originCount);
    for (std::uint32_t index = 0; index < originCount; ++index) {
        location_encoding::EncodedLocationNode node;
        if (index < shapeCount) {
            node.shape = location_encoding::ShapeId(index);
            if (index != 0)
                node.children.push_back(
                    location_encoding::LocationNodeId(index - 1));
        } else {
            node.shape = location_encoding::ShapeId(0);
        }
        node.origins.push_back(source::OriginId(index));
        boundaryDag.nodes.push_back(std::move(node));
    }
    boundaryDag.stats.shapeRows = boundaryDag.shapes.size();
    boundaryDag.stats.locationNodeRows = boundaryDag.nodes.size();

    LocationRocqEmitter emitter;
    auto contents = emitter.emit(unit);
    auto renderedDag = emitter.renderLocationDagForTest(boundaryDag);
    if (!contents || !renderedDag)
        return false;
    const std::string dagStartMarker = "#[local] Definition location_shapes :";
    const std::string dagEndMarker = "\n#[local] Close Scope uint63_scope";
    const std::size_t dagStart = contents->find(dagStartMarker);
    const std::size_t dagEnd = contents->find(dagEndMarker, dagStart);
    if (dagStart == std::string::npos || dagEnd == std::string::npos)
        return false;
    contents->replace(dagStart, dagEnd - dagStart, *renderedDag);

    std::ofstream output(path);
    output << *contents;
    return output.good();
}

using Test = std::pair<const char *, std::function<bool()>>;

} // namespace

int main(int argc, char **argv) {
    if (argc == 3 && std::string(argv[1]) == "--emit-indexed-boundary")
        return emitIndexedBoundaryFixture(argv[2]) ? 0 : 1;
    if (argc != 1) {
        std::cerr << "usage: cpp2v-unit-tests "
                     "[--emit-indexed-boundary OUTPUT.v]\n";
        return 2;
    }
    const std::vector<Test> tests = {
        {"constructor registry completeness", registryComplete},
        {"named factories and occurrence cloning", factoriesAndCloning},
        {"function record and builtin factories", functionAndBuiltinFactories},
        {"cast and literal factories", castAndLiteralFactories},
        {"built-in operator factories", operatorFactories},
        {"call and member factories", callMemberFactories},
        {"construction factories", constructionFactories},
        {"allocation factories", allocationFactories},
        {"lambda and atomic factories", lambdaAtomicFactories},
        {"conditional factories", conditionalFactories},
        {"declaration factories", declarationFactories},
        {"statement and local factories", statementAndLocalFactories},
        {"all value shapes and flattening", allValueShapesAndFlattening},
        {"origins, occurrences, and trees", originsOccurrencesAndTrees},
        {"four roots and deterministic sharing modes",
         directRootsAndDeterminism},
        {"complete typed non-root events", completeNonRootEvents},
        {"Rocq escaping", escaping},
        {"empty tables and events", emptyTablesAndEvents},
        {"root event singleton encoding", rootEventEncoding},
        {"source interning and rendering", sourceInterningAndRendering},
        {"normalized source encoding", sourceEncoding},
        {"exact location DAG encoding", locationDagEncoding},
        {"invalid categories and shapes", invalidCategoryAndShape},
        {"invalid root and non-root events", invalidRootsAndNonRoots},
        {"semantic graph cycle", semanticCycle},
        {"invalid sources and provenance", invalidSourcesAndProvenance},
        {"opaque reachability and finish boundary",
         opaqueReachabilityAndFinishBoundary},
        {"selected result validation boundary", selectedValidationBoundary},
        {"sharing metadata and pure analysis", sharingMetadataAndAnalysis},
        {"unfinished emission rejection", unfinishedEmissionRejected},
    };
    unsigned failures = 0;
    for (const auto &[name, test] : tests) {
        if (!test()) {
            std::cerr << "FAIL: " << name << '\n';
            ++failures;
        }
    }
    return failures == 0 ? 0 : 1;
}
