/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "IR.hpp"

#include <algorithm>
#include <cctype>
#include <functional>
#include <limits>
#include <system_error>

#include <llvm/Support/Error.h>

namespace ir {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

ValueShape scalarShape(ScalarKind kind) {
    return {ShapeKind::Scalar, std::nullopt, kind, {}, {}};
}
ValueShape nodeShape(Category category) {
    return {ShapeKind::Node, category, std::nullopt, {}, {}};
}
ValueShape optionalShape(ValueShape element) {
    return {ShapeKind::Optional,
            std::nullopt,
            std::nullopt,
            {std::move(element)},
            {}};
}
ValueShape sequenceShape(ValueShape element) {
    return {ShapeKind::Sequence,
            std::nullopt,
            std::nullopt,
            {std::move(element)},
            {}};
}
ValueShape productShape(std::vector<ValueShape> fields) {
    return {ShapeKind::Product, std::nullopt, std::nullopt,
            std::move(fields),  {},           {}};
}
ValueShape constructedProductShape(std::string constructor,
                                   std::vector<ValueShape> fields) {
    return {ShapeKind::Product, std::nullopt, std::nullopt,
            std::move(fields),  {},           std::move(constructor)};
}
ValueShape sumShape(std::string constructor, ValueShape payload) {
    return {ShapeKind::Sum,
            std::nullopt,
            std::nullopt,
            {std::move(payload)},
            std::move(constructor)};
}
ValueShape opaqueShape() {
    return {ShapeKind::Opaque, std::nullopt, std::nullopt, {}, {}};
}

constexpr RootKindMask rootBit(RootKind kind) {
    return static_cast<RootKindMask>(1u << static_cast<unsigned>(kind));
}

std::vector<ValueShape> noArgumentsShape() { return {}; }
std::vector<ValueShape> atomicIdentifierShape() {
    return {scalarShape(ScalarKind::String)};
}
std::vector<ValueShape> atomicAnonymousIndexShape() {
    return {scalarShape(ScalarKind::Numeral)};
}
std::vector<ValueShape> globalNameShape() {
    return {nodeShape(Category::AtomicName)};
}
std::vector<ValueShape> scopedNameShape() {
    return {nodeShape(Category::Name), nodeShape(Category::AtomicName)};
}
std::vector<ValueShape> atomicFunctionShape() {
    return {scalarShape(ScalarKind::Symbol), scalarShape(ScalarKind::String),
            sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> atomicConstructorShape() {
    return {sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> atomicOperatorShape() {
    return {scalarShape(ScalarKind::Symbol), scalarShape(ScalarKind::Symbol),
            sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> atomicNewOperatorShape() {
    return {
        scalarShape(ScalarKind::Symbol),
        constructedProductShape("OONew", {scalarShape(ScalarKind::Boolean)}),
        sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> atomicDeleteOperatorShape() {
    return {
        scalarShape(ScalarKind::Symbol),
        constructedProductShape("OODelete", {scalarShape(ScalarKind::Boolean)}),
        sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> atomicConversionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Type)};
}
std::vector<ValueShape> atomicLiteralOperatorShape() {
    return {scalarShape(ScalarKind::String),
            sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> nameInstantiationShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::TemplateArgument))};
}
std::vector<ValueShape> nameDependentShape() {
    return {nodeShape(Category::Type)};
}
std::vector<ValueShape> namedTypeShape() { return {nodeShape(Category::Name)}; }
std::vector<ValueShape> typeNumberShape() {
    return {scalarShape(ScalarKind::Symbol), scalarShape(ScalarKind::Symbol)};
}
std::vector<ValueShape> typeLeafSymbolShape() {
    return {scalarShape(ScalarKind::Symbol)};
}
std::vector<ValueShape> unaryTypeShape() { return {nodeShape(Category::Type)}; }
std::vector<ValueShape> binaryTypeShape() {
    return {nodeShape(Category::Type), nodeShape(Category::Type)};
}
std::vector<ValueShape> typeArrayShape() {
    return {nodeShape(Category::Type), scalarShape(ScalarKind::Numeral)};
}
std::vector<ValueShape> typeVariableArrayShape() {
    return {nodeShape(Category::Type), nodeShape(Category::Expression)};
}
std::vector<ValueShape> typeQualifiedShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Type)};
}
std::vector<ValueShape> typeFunctionShape() {
    // [FunctionType]'s decltype, calling-convention, and arity arguments are
    // implicit in BRiCk.  The explicit application keeps all of them in the
    // final value rather than relying on parser notation after IR creation.
    return {constructedProductShape(
        "@FunctionType",
        {scalarShape(ScalarKind::Symbol), scalarShape(ScalarKind::Symbol),
         scalarShape(ScalarKind::Symbol), nodeShape(Category::Type),
         sequenceShape(nodeShape(Category::Type))})};
}
std::vector<ValueShape> unaryExpressionTypeShape() {
    return {nodeShape(Category::Expression)};
}
std::vector<ValueShape> typeArchitectureShape() {
    return {optionalShape(scalarShape(ScalarKind::Numeral)),
            scalarShape(ScalarKind::String)};
}
std::vector<ValueShape> integerExpressionShape() {
    return {scalarShape(ScalarKind::Numeral), nodeShape(Category::Type)};
}
std::vector<ValueShape> booleanExpressionShape() {
    return {scalarShape(ScalarKind::Boolean)};
}
std::vector<ValueShape> characterExpressionShape() {
    return {scalarShape(ScalarKind::Natural), nodeShape(Category::Type)};
}
std::vector<ValueShape> stringExpressionShape() {
    return {constructedProductShape(
                "literal_string.of_list_N",
                {sequenceShape(scalarShape(ScalarKind::Natural))}),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> floatExpressionShape() {
    return {scalarShape(ScalarKind::Symbol),
            constructedProductShape("float_value.of_bits",
                                    {scalarShape(ScalarKind::Symbol),
                                     scalarShape(ScalarKind::Numeral)})};
}
std::vector<ValueShape> unsupportedExpressionShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type)};
}
std::vector<ValueShape> explicitCastExpressionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Type),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> pathCastShape() {
    return {sequenceShape(nodeShape(Category::Type)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unsupportedCastShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type)};
}
std::vector<ValueShape> globalExpressionShape() {
    return {nodeShape(Category::Name), nodeShape(Category::Type)};
}
std::vector<ValueShape> unaryNameShape() { return {nodeShape(Category::Name)}; }
std::vector<ValueShape> resultCallTypeShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::Type))};
}
std::vector<ValueShape> resultUnarySyntaxTypeShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Type)};
}
std::vector<ValueShape> resultMemberTypeShape() {
    return {nodeShape(Category::Type), nodeShape(Category::Name)};
}
std::vector<ValueShape> enumConstantExpressionShape() {
    return {nodeShape(Category::Name), scalarShape(ScalarKind::String)};
}
std::vector<ValueShape> localNamedExpressionShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type)};
}
std::vector<ValueShape> localAnonymousExpressionShape() {
    return {constructedProductShape("localname.anon",
                                    {scalarShape(ScalarKind::Numeral)}),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unaryOperatorExpressionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Expression),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unsupportedUnaryOperatorExpressionShape() {
    return {constructedProductShape("Uunsupported",
                                    {scalarShape(ScalarKind::String)}),
            nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape> unresolvedUnaryExpressionShape() {
    return {constructedProductShape("Runop", {scalarShape(ScalarKind::Symbol)}),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> unresolvedUnsupportedUnaryExpressionShape() {
    return {constructedProductShape(
                "Runop",
                {constructedProductShape("Uunsupported",
                                         {scalarShape(ScalarKind::String)})}),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> unresolvedUnarySyntaxExpressionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Expression)};
}
std::vector<ValueShape> unaryExpressionNoOperationShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape> assignmentExpressionShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Expression),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unresolvedBinaryExpressionShape() {
    return {
        constructedProductShape("Rbinop", {scalarShape(ScalarKind::Symbol)}),
        nodeShape(Category::Expression), nodeShape(Category::Expression)};
}
std::vector<ValueShape> unresolvedBinarySyntaxExpressionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Expression),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> unresolvedCompoundAssignmentExpressionShape() {
    return {constructedProductShape("Rassign_op",
                                    {scalarShape(ScalarKind::Symbol)}),
            nodeShape(Category::Expression), nodeShape(Category::Expression)};
}
std::vector<ValueShape> castExpressionShape() {
    return {nodeShape(Category::Cast), nodeShape(Category::Expression)};
}
std::vector<ValueShape> binaryExpressionShape() {
    return {scalarShape(ScalarKind::Symbol), nodeShape(Category::Expression),
            nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape> binaryExpressionNoTypeShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Expression)};
}
std::vector<ValueShape> subscriptExpressionShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Expression),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> traitTypeExpressionShape() {
    return {sumShape("inl", nodeShape(Category::Type)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> traitExpressionExpressionShape() {
    return {sumShape("inr", nodeShape(Category::Expression)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unresolvedSizeofPackShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type)};
}
std::vector<ValueShape> callExpressionShape() {
    return {nodeShape(Category::Expression),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> unresolvedCallExpressionShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> memberExpressionShape() {
    return {scalarShape(ScalarKind::Boolean), nodeShape(Category::Expression),
            nodeShape(Category::AtomicName), scalarShape(ScalarKind::Boolean),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> memberIgnoreExpressionShape() {
    return {scalarShape(ScalarKind::Boolean), nodeShape(Category::Expression),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> unresolvedMemberExpressionShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Name)};
}
std::vector<ValueShape> directMemberCallExpressionShape() {
    return {scalarShape(ScalarKind::Boolean),
            sumShape("inl", productShape({nodeShape(Category::Name),
                                          scalarShape(ScalarKind::Symbol),
                                          nodeShape(Category::Type)})),
            nodeShape(Category::Expression),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> pointerMemberCallExpressionShape() {
    return {scalarShape(ScalarKind::Boolean),
            sumShape("inr", nodeShape(Category::Expression)),
            nodeShape(Category::Expression),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> functionOperatorCallExpressionShape() {
    return {scalarShape(ScalarKind::Symbol),
            constructedProductShape(
                "operator_impl.Func",
                {nodeShape(Category::Name), nodeShape(Category::Type)}),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> methodOperatorCallExpressionShape() {
    return {scalarShape(ScalarKind::Symbol),
            constructedProductShape("operator_impl.MFunc",
                                    {nodeShape(Category::Name),
                                     scalarShape(ScalarKind::Symbol),
                                     nodeShape(Category::Type)}),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> constructorExpressionShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::Expression)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> inheritedConstructorExpressionShape() {
    return {nodeShape(Category::Name),
            sequenceShape(constructedProductShape(
                "localname.anon", {scalarShape(ScalarKind::Numeral)})),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unresolvedInitializerListShape() {
    return {optionalShape(nodeShape(Category::Type)),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> initListExpressionShape() {
    return {sequenceShape(nodeShape(Category::Expression)),
            optionalShape(nodeShape(Category::Expression)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> unionInitListExpressionShape() {
    return {nodeShape(Category::AtomicName),
            optionalShape(nodeShape(Category::Expression)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> materializeTemporaryExpressionShape() {
    return {nodeShape(Category::Expression), scalarShape(ScalarKind::Symbol)};
}
std::vector<ValueShape> arrayLoopInitExpressionShape() {
    return {scalarShape(ScalarKind::Numeral), nodeShape(Category::Expression),
            scalarShape(ScalarKind::Numeral), scalarShape(ScalarKind::Numeral),
            nodeShape(Category::Expression),  nodeShape(Category::Type)};
}
std::vector<ValueShape> arrayLoopIndexExpressionShape() {
    return {scalarShape(ScalarKind::Numeral), nodeShape(Category::Type)};
}
std::vector<ValueShape> allocatingNewExpressionShape() {
    return {
        productShape({nodeShape(Category::Name), nodeShape(Category::Type)}),
        sequenceShape(nodeShape(Category::Expression)),
        constructedProductShape("new_form.Allocating",
                                {scalarShape(ScalarKind::Boolean)}),
        nodeShape(Category::Type),
        optionalShape(nodeShape(Category::Expression)),
        optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> nonAllocatingNewExpressionShape() {
    return {
        productShape({nodeShape(Category::Name), nodeShape(Category::Type)}),
        sequenceShape(nodeShape(Category::Expression)),
        scalarShape(ScalarKind::Symbol),
        nodeShape(Category::Type),
        optionalShape(nodeShape(Category::Expression)),
        optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> deleteExpressionShape() {
    return {scalarShape(ScalarKind::Boolean), nodeShape(Category::Name),
            nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape>
functionAllocationOperatorCallExpressionShape(llvm::StringRef operation) {
    return {constructedProductShape(operation.str(),
                                    {scalarShape(ScalarKind::Boolean)}),
            constructedProductShape(
                "operator_impl.Func",
                {nodeShape(Category::Name), nodeShape(Category::Type)}),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape>
methodAllocationOperatorCallExpressionShape(llvm::StringRef operation) {
    return {constructedProductShape(operation.str(),
                                    {scalarShape(ScalarKind::Boolean)}),
            constructedProductShape("operator_impl.MFunc",
                                    {nodeShape(Category::Name),
                                     scalarShape(ScalarKind::Symbol),
                                     nodeShape(Category::Type)}),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> functionNewOperatorCallExpressionShape() {
    return functionAllocationOperatorCallExpressionShape("OONew");
}
std::vector<ValueShape> functionDeleteOperatorCallExpressionShape() {
    return functionAllocationOperatorCallExpressionShape("OODelete");
}
std::vector<ValueShape> methodNewOperatorCallExpressionShape() {
    return methodAllocationOperatorCallExpressionShape("OONew");
}
std::vector<ValueShape> methodDeleteOperatorCallExpressionShape() {
    return methodAllocationOperatorCallExpressionShape("OODelete");
}
std::vector<ValueShape> atomicExpressionShape() {
    return {scalarShape(ScalarKind::String),
            sequenceShape(nodeShape(Category::Expression)),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> vaArgExpressionShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape> lambdaExpressionShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> conditionalExpressionShape() {
    return {nodeShape(Category::Expression), nodeShape(Category::Expression),
            nodeShape(Category::Expression), nodeShape(Category::Type)};
}
std::vector<ValueShape> binaryConditionalExpressionShape() {
    return {scalarShape(ScalarKind::Natural), nodeShape(Category::Expression),
            nodeShape(Category::Expression),  nodeShape(Category::Expression),
            nodeShape(Category::Expression),  nodeShape(Category::Type)};
}
std::vector<ValueShape> offsetOfExpressionShape() {
    return {nodeShape(Category::Type), scalarShape(ScalarKind::String),
            nodeShape(Category::Type)};
}
std::vector<ValueShape> statementBlockExpressionShape() {
    return {nodeShape(Category::Statement), nodeShape(Category::Type)};
}
std::vector<ValueShape> pseudoDestructorExpressionShape() {
    return {scalarShape(ScalarKind::Boolean), nodeShape(Category::Type),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> statementExpressionShape() {
    return {nodeShape(Category::Expression)};
}
std::vector<ValueShape> statementReturnShape() {
    return {optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> statementSequenceShape() {
    return {sequenceShape(nodeShape(Category::Statement))};
}
std::vector<ValueShape> statementDeclarationShape() {
    return {sequenceShape(nodeShape(Category::VariableDeclaration))};
}
std::vector<ValueShape> statementIfShape() {
    return {optionalShape(nodeShape(Category::Statement)),
            optionalShape(nodeShape(Category::VariableDeclaration)),
            nodeShape(Category::Expression), nodeShape(Category::Statement),
            nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementIfConstevalShape() {
    return {nodeShape(Category::Statement), nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementWhileShape() {
    return {optionalShape(nodeShape(Category::VariableDeclaration)),
            nodeShape(Category::Expression), nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementForShape() {
    return {optionalShape(nodeShape(Category::Statement)),
            optionalShape(nodeShape(Category::Expression)),
            optionalShape(nodeShape(Category::Expression)),
            nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementDoShape() {
    return {nodeShape(Category::Statement), nodeShape(Category::Expression)};
}
std::vector<ValueShape> statementSwitchShape() {
    return {optionalShape(nodeShape(Category::Statement)),
            optionalShape(nodeShape(Category::VariableDeclaration)),
            nodeShape(Category::Expression), nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementCaseShape() {
    return {scalarShape(ScalarKind::SwitchBranch)};
}
std::vector<ValueShape> statementAttributeShape() {
    return {sequenceShape(scalarShape(ScalarKind::String)),
            nodeShape(Category::Statement)};
}
std::vector<ValueShape> statementAsmShape() {
    const auto operand = productShape(
        {scalarShape(ScalarKind::String), nodeShape(Category::Expression)});
    return {scalarShape(ScalarKind::String), scalarShape(ScalarKind::Boolean),
            sequenceShape(operand), sequenceShape(operand),
            sequenceShape(scalarShape(ScalarKind::String))};
}
std::vector<ValueShape> statementLabeledShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Statement)};
}
std::vector<ValueShape> variableDeclarationShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type),
            optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> variableDecompositionShape() {
    return {nodeShape(Category::Expression), scalarShape(ScalarKind::LocalName),
            sequenceShape(nodeShape(Category::BindingDeclaration))};
}
std::vector<ValueShape> variableStaticInitShape() {
    return {scalarShape(ScalarKind::Boolean), nodeShape(Category::Name),
            nodeShape(Category::Type),
            optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> bindingDeclarationShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> templateParameterTypeShape() {
    return {scalarShape(ScalarKind::String)};
}
std::vector<ValueShape> templateParameterValueShape() {
    return {scalarShape(ScalarKind::String), nodeShape(Category::Type)};
}
std::vector<ValueShape> templateParameterTemplateShape() {
    return {scalarShape(ScalarKind::String),
            sequenceShape(nodeShape(Category::TemplateParameter))};
}
std::vector<ValueShape> templateArgumentTypeShape() {
    return {nodeShape(Category::Type)};
}
std::vector<ValueShape> templateArgumentValueShape() {
    return {nodeShape(Category::Expression)};
}
std::vector<ValueShape> templateArgumentPackShape() {
    return {sequenceShape(nodeShape(Category::TemplateArgument))};
}
std::vector<ValueShape> templateArgumentTemplateShape() {
    return {nodeShape(Category::Name)};
}
std::vector<ValueShape> emptyShape() { return {}; }
std::vector<ValueShape> globalInitExpressionShape() {
    return {nodeShape(Category::Expression)};
}
std::vector<ValueShape> functionBodyImplementationShape() {
    return {nodeShape(Category::Statement)};
}
std::vector<ValueShape> functionBodyBuiltinShape() {
    return {scalarShape(ScalarKind::String)};
}
std::vector<ValueShape> defaultStatementBodyShape() {
    return {nodeShape(Category::Statement)};
}
std::vector<ValueShape> constructorBodyShape() {
    return {productShape({sequenceShape(nodeShape(Category::Initializer)),
                          nodeShape(Category::Statement)})};
}
ValueShape declarationParametersShape() {
    return sequenceShape(productShape(
        {scalarShape(ScalarKind::LocalName), nodeShape(Category::Type)}));
}
std::vector<ValueShape> functionRecordShape() {
    return {nodeShape(Category::Type),
            declarationParametersShape(),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            optionalShape(nodeShape(Category::FunctionBody))};
}
std::vector<ValueShape> methodRecordShape() {
    return {nodeShape(Category::Type),
            nodeShape(Category::Name),
            scalarShape(ScalarKind::Symbol),
            declarationParametersShape(),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            optionalShape(nodeShape(Category::DefaultStatementBody))};
}
std::vector<ValueShape> initializerBasePathShape() {
    return {nodeShape(Category::Name)};
}
std::vector<ValueShape> initializerFieldPathShape() {
    return {nodeShape(Category::AtomicName)};
}
std::vector<ValueShape> initializerRecordShape() {
    return {nodeShape(Category::InitializerPath),
            nodeShape(Category::Expression)};
}
std::vector<ValueShape> constructorRecordShape() {
    return {nodeShape(Category::Name),
            declarationParametersShape(),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            optionalShape(nodeShape(Category::ConstructorBody))};
}
std::vector<ValueShape> destructorRecordShape() {
    return {nodeShape(Category::Name), scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Symbol),
            optionalShape(nodeShape(Category::DefaultStatementBody))};
}
std::vector<ValueShape> layoutInfoShape() {
    return {scalarShape(ScalarKind::Numeral)};
}
std::vector<ValueShape> memberRecordShape() {
    return {nodeShape(Category::AtomicName), nodeShape(Category::Type),
            scalarShape(ScalarKind::Boolean),
            optionalShape(nodeShape(Category::Expression)),
            nodeShape(Category::LayoutInfo)};
}
std::vector<ValueShape> structRecordShape() {
    const ValueShape base = productShape(
        {nodeShape(Category::Name), nodeShape(Category::LayoutInfo)});
    const ValueShape virtualMethod = productShape(
        {nodeShape(Category::Name), optionalShape(nodeShape(Category::Name))});
    const ValueShape overrideMethod =
        productShape({nodeShape(Category::Name), nodeShape(Category::Name)});
    return {sequenceShape(base),
            sequenceShape(nodeShape(Category::Member)),
            sequenceShape(virtualMethod),
            sequenceShape(overrideMethod),
            nodeShape(Category::Name),
            scalarShape(ScalarKind::Boolean),
            optionalShape(nodeShape(Category::Name)),
            scalarShape(ScalarKind::Symbol),
            scalarShape(ScalarKind::Numeral),
            scalarShape(ScalarKind::Numeral)};
}
std::vector<ValueShape> unionRecordShape() {
    return {sequenceShape(nodeShape(Category::Member)),
            nodeShape(Category::Name),
            scalarShape(ScalarKind::Boolean),
            optionalShape(nodeShape(Category::Name)),
            scalarShape(ScalarKind::Numeral),
            scalarShape(ScalarKind::Numeral)};
}
std::vector<ValueShape> objectVariableShape() {
    return {nodeShape(Category::Type), nodeShape(Category::GlobalInitializer)};
}
std::vector<ValueShape> objectFunctionShape() {
    return {nodeShape(Category::Function)};
}
std::vector<ValueShape> objectMethodShape() {
    return {nodeShape(Category::Method)};
}
std::vector<ValueShape> objectConstructorShape() {
    return {nodeShape(Category::Constructor)};
}
std::vector<ValueShape> objectDestructorShape() {
    return {nodeShape(Category::Destructor)};
}
std::vector<ValueShape> globalUnionShape() {
    return {nodeShape(Category::Union)};
}
std::vector<ValueShape> globalStructShape() {
    return {nodeShape(Category::Struct)};
}
std::vector<ValueShape> globalEnumShape() {
    return {nodeShape(Category::Type),
            sequenceShape(scalarShape(ScalarKind::String))};
}
std::vector<ValueShape> globalTypedefShape() {
    return {nodeShape(Category::Type)};
}
std::vector<ValueShape> globalConstantShape() {
    return {nodeShape(Category::Type),
            optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> globalUnsupportedShape() {
    return {scalarShape(ScalarKind::String)};
}
ValueShape templateParametersShape() {
    return sequenceShape(
        productShape({nodeShape(Category::TemplateParameter),
                      optionalShape(nodeShape(Category::TemplateArgument))}));
}
std::vector<ValueShape> templateObjectRootShape() {
    return {templateParametersShape(), nodeShape(Category::ObjectValue)};
}
std::vector<ValueShape> templateGlobalRootShape() {
    return {templateParametersShape(), nodeShape(Category::GlobalDeclaration)};
}
std::vector<ValueShape> templateAliasShape() {
    return {templateParametersShape(), nodeShape(Category::Type)};
}
std::vector<ValueShape> templatePreInstantiationShape() {
    return {nodeShape(Category::Name),
            sequenceShape(nodeShape(Category::TemplateArgument))};
}
std::vector<ValueShape> initIndirectShape() {
    return {sequenceShape(productShape(
                {nodeShape(Category::AtomicName), nodeShape(Category::Name)})),
            nodeShape(Category::AtomicName)};
}
std::vector<ValueShape> optionalFixtureShape() {
    return {optionalShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> sequenceFixtureShape() {
    return {sequenceShape(nodeShape(Category::Expression))};
}
std::vector<ValueShape> productFixtureShape() {
    return {productShape(
        {scalarShape(ScalarKind::Symbol), nodeShape(Category::Expression)})};
}
std::vector<ValueShape> sumFixtureShape() {
    return {sumShape("inl", nodeShape(Category::Expression))};
}
std::vector<ValueShape> identTypeListShape() {
    return {sequenceShape(productShape(
        {scalarShape(ScalarKind::String), nodeShape(Category::Type)}))};
}
std::vector<ValueShape> nameOptionalNameListShape() {
    return {sequenceShape(
        productShape({nodeShape(Category::Name),
                      optionalShape(nodeShape(Category::Name))}))};
}
std::vector<ValueShape> structureOverridesShape() {
    return {sequenceShape(
        productShape({nodeShape(Category::Name), nodeShape(Category::Name)}))};
}
std::vector<ValueShape> opaqueFixtureShape() { return {opaqueShape()}; }

RootKindMask NoRoots() { return 0; }
RootKindMask SymbolRoot() { return rootBit(RootKind::Symbol); }
RootKindMask TypeRoot() { return rootBit(RootKind::Type); }
RootKindMask TemplateSymbolRoot() { return rootBit(RootKind::TemplateSymbol); }
RootKindMask TemplateTypeRoot() { return rootBit(RootKind::TemplateType); }
constexpr bool Real = false;
constexpr bool TestOnly = true;

const std::vector<ConstructorSpec> registry = {
#define IR_CONSTRUCTOR(NAME, SPELLING, CATEGORY, ROOTS, STATUS, SHAPE)         \
    {Constructor::NAME, SPELLING, Category::CATEGORY, ROOTS(), STATUS, SHAPE()},
#include "IRConstructors.def"
#undef IR_CONSTRUCTOR
};

bool validNode(NodeId id, const Arena &arena) {
    return id.valid() && id.value() < arena.size();
}

bool validOrigin(source::OriginId id, const source::Tables &tables) {
    return id.valid() && id.value() < tables.origins.size();
}

bool validStructuredNatural(llvm::StringRef text) {
    if (!text.consume_back("%N") || text.empty())
        return false;
    return std::all_of(text.begin(), text.end(),
                       [](unsigned char value) { return std::isdigit(value); });
}

bool validStructuredInteger(llvm::StringRef text) {
    if (!text.consume_back("%Z") || text.empty())
        return false;
    if (text.consume_front("(")) {
        if (!text.consume_back(")") || !text.consume_front("-") || text.empty())
            return false;
    }
    return std::all_of(text.begin(), text.end(),
                       [](unsigned char value) { return std::isdigit(value); });
}

bool validSwitchBranch(llvm::StringRef text) {
    if (!text.consume_front("(") || !text.consume_back(")"))
        return false;
    if (text.consume_front("Exact "))
        return validStructuredInteger(text);
    if (!text.consume_front("Range "))
        return false;
    const auto split = text.split(' ');
    return !split.second.empty() && validStructuredInteger(split.first) &&
           validStructuredInteger(split.second);
}

bool validLocalName(llvm::StringRef text) {
    if (!text.consume_front("(localname.anon "))
        return !text.empty();
    return text.consume_back(")") && validStructuredNatural(text);
}

bool validSymbolAtom(const std::string &text) {
    if (text.empty() || text.find("(*") != std::string::npos ||
        text.find("*)") != std::string::npos ||
        text.find("//") != std::string::npos ||
        text.find("/*") != std::string::npos ||
        text.find("*/") != std::string::npos)
        return false;
    auto identifierStart = [](unsigned char c) {
        return std::isalpha(c) || c == '_';
    };
    auto identifierRest = [&](unsigned char c) {
        return identifierStart(c) || std::isdigit(c) || c == '\'';
    };
    std::size_t first = text.front() == '@' ? 1 : 0;
    if (first == text.size())
        return false;
    if (identifierStart(static_cast<unsigned char>(text[first]))) {
        bool segmentStart = false;
        for (std::size_t index = first; index < text.size(); ++index) {
            const unsigned char c = text[index];
            if (c == '.') {
                if (segmentStart)
                    return false;
                segmentStart = true;
            } else if (segmentStart) {
                if (!identifierStart(c))
                    return false;
                segmentStart = false;
            } else if (!identifierRest(c)) {
                return false;
            }
        }
        return !segmentStart;
    }
    const std::string operators = "+-*/%<>=!&|^~?:";
    for (unsigned char c : text)
        if (operators.find(static_cast<char>(c)) == std::string::npos)
            return false;
    return true;
}

llvm::Error validateValue(const Value &value, const ValueShape &shape,
                          const Arena &arena) {
    auto mismatch = [] {
        return error("value does not match constructor shape");
    };
    switch (shape.kind) {
    case ShapeKind::Scalar: {
        const auto *scalar = std::get_if<ScalarTerm>(&value.payload);
        if (!scalar)
            return mismatch();
        if (!shape.scalarKind || scalar->kind != *shape.scalarKind)
            return error("scalar term has the wrong structured kind");
        if (scalar->kind == ScalarKind::Symbol &&
            !validSymbolAtom(scalar->text))
            return error("symbol scalar term is not a safe atom");
        if (scalar->kind == ScalarKind::Boolean && scalar->text != "true" &&
            scalar->text != "false")
            return error("boolean scalar term is malformed");
        if (scalar->kind == ScalarKind::SwitchBranch &&
            !validSwitchBranch(scalar->text))
            return error("switch-branch scalar term is malformed");
        if (scalar->kind == ScalarKind::LocalName &&
            !validLocalName(scalar->text))
            return error("local-name scalar term is malformed");
        if (scalar->kind == ScalarKind::Numeral ||
            scalar->kind == ScalarKind::Natural) {
            std::size_t first = scalar->kind == ScalarKind::Numeral &&
                                !scalar->text.empty() && scalar->text[0] == '-';
            if (first == scalar->text.size())
                return error("numeral scalar term is malformed");
            for (std::size_t i = first; i < scalar->text.size(); ++i)
                if (!std::isdigit(static_cast<unsigned char>(scalar->text[i])))
                    return error("numeral scalar term is malformed");
        }
        return llvm::Error::success();
    }
    case ShapeKind::Node: {
        const auto *reference = std::get_if<NodeRef>(&value.payload);
        if (!reference || !validNode(reference->value, arena))
            return error(
                "constructor shape contains an invalid node reference");
        auto node = arena.get(reference->value);
        if (!node)
            return node.takeError();
        if (shape.nodeCategory && (*node)->category != *shape.nodeCategory)
            return error(
                "constructor shape contains a node of the wrong category");
        return llvm::Error::success();
    }
    case ShapeKind::Optional: {
        const auto *optional = std::get_if<OptionalValue>(&value.payload);
        if (!optional || shape.children.size() != 1)
            return mismatch();
        if (!optional->value)
            return llvm::Error::success();
        return validateValue(*optional->value, shape.children[0], arena);
    }
    case ShapeKind::Sequence: {
        const auto *sequence = std::get_if<SequenceValue>(&value.payload);
        if (!sequence || shape.children.size() != 1)
            return mismatch();
        for (const auto &element : sequence->elements)
            if (auto failure = validateValue(element, shape.children[0], arena))
                return failure;
        return llvm::Error::success();
    }
    case ShapeKind::Product: {
        const auto *product = std::get_if<ProductValue>(&value.payload);
        if (!product || product->fields.size() != shape.children.size())
            return mismatch();
        if (shape.productConstructor) {
            if (!product->constructor ||
                product->constructor->kind != ScalarKind::Symbol ||
                product->constructor->text != *shape.productConstructor)
                return error("product value has the wrong constructor");
        } else if (product->constructor) {
            return error("tuple product unexpectedly has a constructor");
        }
        for (std::size_t i = 0; i < product->fields.size(); ++i)
            if (auto failure =
                    validateValue(product->fields[i], shape.children[i], arena))
                return failure;
        return llvm::Error::success();
    }
    case ShapeKind::Sum: {
        const auto *sum = std::get_if<SumValue>(&value.payload);
        if (!sum || !sum->payload || shape.children.size() != 1)
            return mismatch();
        if (shape.sumConstructor &&
            (sum->activeConstructor.kind != ScalarKind::Symbol ||
             sum->activeConstructor.text != *shape.sumConstructor))
            return error("sum value has the wrong active constructor");
        return validateValue(*sum->payload, shape.children[0], arena);
    }
    case ShapeKind::Opaque:
        if (!std::holds_alternative<OpaqueValue>(value.payload))
            return mismatch();
        return llvm::Error::success();
    }
    return error("unknown value shape");
}

void flattenValue(const Value &value, std::vector<NodeId> &result) {
    if (const auto *reference = std::get_if<NodeRef>(&value.payload)) {
        result.push_back(reference->value);
    } else if (const auto *optional =
                   std::get_if<OptionalValue>(&value.payload)) {
        if (optional->value)
            flattenValue(*optional->value, result);
    } else if (const auto *sequence =
                   std::get_if<SequenceValue>(&value.payload)) {
        for (const auto &element : sequence->elements)
            flattenValue(element, result);
    } else if (const auto *product =
                   std::get_if<ProductValue>(&value.payload)) {
        for (const auto &field : product->fields)
            flattenValue(field, result);
    } else if (const auto *sum = std::get_if<SumValue>(&value.payload)) {
        if (sum->payload)
            flattenValue(*sum->payload, result);
    }
}

bool containsOpaque(const Value &value) {
    if (std::holds_alternative<OpaqueValue>(value.payload))
        return true;
    if (const auto *optional = std::get_if<OptionalValue>(&value.payload))
        return optional->value && containsOpaque(*optional->value);
    if (const auto *sequence = std::get_if<SequenceValue>(&value.payload)) {
        for (const auto &element : sequence->elements)
            if (containsOpaque(element))
                return true;
    }
    if (const auto *product = std::get_if<ProductValue>(&value.payload)) {
        for (const auto &field : product->fields)
            if (containsOpaque(field))
                return true;
    }
    if (const auto *sum = std::get_if<SumValue>(&value.payload))
        return sum->payload && containsOpaque(*sum->payload);
    return false;
}

} // namespace

OptionalValue::OptionalValue(const OptionalValue &other) {
    if (other.value)
        value = std::make_unique<Value>(*other.value);
}
OptionalValue &OptionalValue::operator=(const OptionalValue &other) {
    if (this != &other)
        value = other.value ? std::make_unique<Value>(*other.value) : nullptr;
    return *this;
}

SumValue::SumValue(ScalarTerm constructor, std::unique_ptr<Value> value)
    : activeConstructor(std::move(constructor)), payload(std::move(value)) {}
SumValue::SumValue(const SumValue &other)
    : activeConstructor(other.activeConstructor) {
    if (other.payload)
        payload = std::make_unique<Value>(*other.payload);
}
SumValue &SumValue::operator=(const SumValue &other) {
    if (this != &other) {
        activeConstructor = other.activeConstructor;
        payload =
            other.payload ? std::make_unique<Value>(*other.payload) : nullptr;
    }
    return *this;
}

ScalarTerm ScalarTerm::symbol(std::string value) {
    return {ScalarKind::Symbol, std::move(value)};
}
ScalarTerm ScalarTerm::string(std::string value) {
    return {ScalarKind::String, std::move(value)};
}
ScalarTerm ScalarTerm::numeral(std::string value) {
    return {ScalarKind::Numeral, std::move(value)};
}
ScalarTerm ScalarTerm::natural(std::uint64_t value) {
    return {ScalarKind::Natural, std::to_string(value)};
}
ScalarTerm ScalarTerm::boolean(bool value) {
    return {ScalarKind::Boolean, value ? "true" : "false"};
}
ScalarTerm ScalarTerm::byteString(std::string value) {
    return {ScalarKind::ByteString, std::move(value)};
}
ScalarTerm ScalarTerm::switchBranchExact(std::string value) {
    if (!value.empty() && value.front() == '-')
        value = "(" + value + ")";
    return {ScalarKind::SwitchBranch, "(Exact " + value + "%Z)"};
}
ScalarTerm ScalarTerm::switchBranchRange(std::string low, std::string high) {
    if (!low.empty() && low.front() == '-')
        low = "(" + low + ")";
    if (!high.empty() && high.front() == '-')
        high = "(" + high + ")";
    return {ScalarKind::SwitchBranch, "(Range " + low + "%Z " + high + "%Z)"};
}
ScalarTerm ScalarTerm::localIdentifier(std::string value) {
    return {ScalarKind::LocalName, std::move(value)};
}
ScalarTerm ScalarTerm::anonymousLocal(std::uint64_t value) {
    return {ScalarKind::LocalName,
            "(localname.anon " + std::to_string(value) + "%N)"};
}

Value Value::scalar(ScalarTerm value) { return {std::move(value)}; }
Value Value::node(NodeId value) { return {NodeRef{value}}; }
Value Value::optional(std::optional<Value> value) {
    OptionalValue result;
    if (value)
        result.value = std::make_unique<Value>(std::move(*value));
    return {std::move(result)};
}
Value Value::sequence(std::vector<Value> elements) {
    return {SequenceValue{std::move(elements)}};
}
Value Value::product(std::vector<Value> fields) {
    return {ProductValue{std::nullopt, std::move(fields)}};
}
Value Value::constructedProduct(ScalarTerm constructor,
                                std::vector<Value> fields) {
    return {ProductValue{std::move(constructor), std::move(fields)}};
}
Value Value::sum(ScalarTerm constructor, Value payload) {
    return {SumValue{std::move(constructor),
                     std::make_unique<Value>(std::move(payload))}};
}
Value Value::opaque(std::string diagnostic) {
    return {OpaqueValue{std::move(diagnostic)}};
}

const std::vector<ConstructorSpec> &constructorRegistry() { return registry; }

const ConstructorSpec *findConstructorSpec(Constructor constructor) {
    for (const auto &spec : registry)
        if (spec.constructor == constructor)
            return &spec;
    return nullptr;
}

const ConstructorSpec &constructorSpec(Constructor constructor) {
    if (const auto *spec = findConstructorSpec(constructor))
        return *spec;
    llvm_unreachable("validated constructor missing from IR registry");
}

llvm::Expected<NodeId> Arena::add(Node node) {
    if (finished_)
        return error("cannot add an IR node after finish");
    if (nodes_.size() >= std::numeric_limits<NodeId::value_type>::max())
        return error("too many IR nodes");
    NodeId id(static_cast<NodeId::value_type>(nodes_.size()));
    nodes_.push_back(std::move(node));
    return id;
}

llvm::Error Arena::setShareClass(NodeId id, ShareClassId shareClass) {
    if (finished_)
        return error("cannot assign sharing metadata after finish");
    if (!validNode(id, *this))
        return error("sharing metadata node ID is out of range");
    nodes_[id.value()].shareClass = shareClass;
    return llvm::Error::success();
}

llvm::Expected<const Node *> Arena::get(NodeId id) const {
    if (!validNode(id, *this))
        return error("IR node ID is out of range");
    return &nodes_[id.value()];
}

llvm::Expected<std::vector<NodeId>> Arena::children(NodeId id) const {
    auto node = get(id);
    if (!node)
        return node.takeError();
    std::vector<NodeId> result;
    for (const auto &argument : (*node)->arguments)
        flattenValue(argument, result);
    return result;
}

llvm::Error TranslationUnitIR::setSources(source::Tables sources) {
    if (finished_)
        return error("cannot replace source tables after finish");
    sources_ = std::move(sources);
    return llvm::Error::success();
}
llvm::Expected<ShareClassId>
TranslationUnitIR::addShareClass(ShareClassKind kind) {
    if (finished_)
        return error("cannot add a sharing class after finish");
    if (shareClasses_.size() >=
        std::numeric_limits<ShareClassId::value_type>::max())
        return error("too many sharing classes");
    ShareClassId id(
        static_cast<ShareClassId::value_type>(shareClasses_.size()));
    shareClasses_.push_back({kind});
    return id;
}
llvm::Error TranslationUnitIR::addRoot(RootEvent event) {
    if (finished_)
        return error("cannot add a root event after finish");
    orderedEvents_.push_back({OrderedEventKind::Root, rootEvents_.size()});
    rootEvents_.push_back(event);
    return llvm::Error::success();
}
llvm::Error TranslationUnitIR::addNonRoot(NonRootEvent event) {
    if (finished_)
        return error("cannot add a non-root event after finish");
    orderedEvents_.push_back(
        {OrderedEventKind::NonRoot, nonRootEvents_.size()});
    nonRootEvents_.push_back(std::move(event));
    return llvm::Error::success();
}
llvm::Error TranslationUnitIR::setAbi(AbiInfo abi) {
    if (finished_)
        return error("cannot replace ABI information after finish");
    abi_ = std::move(abi);
    return llvm::Error::success();
}
llvm::Error TranslationUnitIR::finish() {
    if (finished_)
        return error("IR was already finished");
    if (auto failure = IRValidator::validate(*this, false))
        return failure;
    nodes_.markFinished();
    finished_ = true;
    return llvm::Error::success();
}

llvm::Error IRValidator::validateSelected(const Arena &arena,
                                          llvm::ArrayRef<NodeId> selected,
                                          Category expected,
                                          llvm::StringRef label) {
    std::vector<bool> visited(arena.size(), false);
    std::vector<NodeId> pending(selected.begin(), selected.end());
    for (NodeId root : selected) {
        auto node = arena.get(root);
        if (!node)
            return node.takeError();
        if ((*node)->category != expected)
            return error("selected " + label.str() +
                         " has the wrong node category");
    }
    while (!pending.empty()) {
        const NodeId id = pending.back();
        pending.pop_back();
        auto node = arena.get(id);
        if (!node)
            return node.takeError();
        if (visited[id.value()])
            continue;
        visited[id.value()] = true;
        if (constructorSpec((*node)->constructor).testOnly)
            return error("selected " + label.str() +
                         " reaches a test-only/opaque constructor");
        auto children = arena.children(id);
        if (!children)
            return children.takeError();
        pending.insert(pending.end(), children->begin(), children->end());
    }
    return llvm::Error::success();
}

llvm::Error IRValidator::validate(const TranslationUnitIR &unit,
                                  bool requireFinished) {
    if (requireFinished && !unit.finished_)
        return error("IR must be finished before emission");
    if (unit.finished_ != unit.nodes_.finished())
        return error("IR finish state is inconsistent");
    if (auto failure = source::validate(unit.sources_))
        return failure;

    for (std::size_t i = 0; i < unit.nodes_.nodes_.size(); ++i) {
        const Node &node = unit.nodes_.nodes_[i];
        const auto *spec = findConstructorSpec(node.constructor);
        if (!spec)
            return error("IR node " + std::to_string(i) +
                         " has an unregistered constructor");
        if (node.category != spec->category)
            return error("IR node " + std::to_string(i) +
                         " has the wrong constructor category");
        if (node.arguments.size() != spec->arguments.size())
            return error("IR node " + std::to_string(i) +
                         " has the wrong constructor arity");
        for (std::size_t argument = 0; argument < node.arguments.size();
             ++argument)
            if (auto failure =
                    validateValue(node.arguments[argument],
                                  spec->arguments[argument], unit.nodes_))
                return failure;
        for (source::OriginId origin : node.origins)
            if (!validOrigin(origin, unit.sources_))
                return error("IR node has an out-of-range origin ID");
        if (node.shareClass) {
            if (!node.shareClass->valid() ||
                node.shareClass->value() >= unit.shareClasses_.size())
                return error("IR node has an out-of-range sharing class ID");
            const ShareClassKind kind =
                unit.shareClasses_[node.shareClass->value()].kind;
            if ((kind == ShareClassKind::Type &&
                 node.category != Category::Type) ||
                (kind == ShareClassKind::Name &&
                 node.category != Category::Name))
                return error("IR node has a sharing class of the wrong kind");
        }
    }

    auto category = [&](NodeId id, Category expected,
                        const char *where) -> llvm::Error {
        if (!validNode(id, unit.nodes_))
            return error(std::string(where) + " has an invalid node ID");
        if (unit.nodes_.nodes_[id.value()].category != expected)
            return error(std::string(where) + " has the wrong node category");
        return llvm::Error::success();
    };
    auto origins = [&](const std::vector<source::OriginId> &ids,
                       const char *where) -> llvm::Error {
        for (auto id : ids)
            if (!validOrigin(id, unit.sources_))
                return error(std::string(where) +
                             " has an out-of-range origin ID");
        return llvm::Error::success();
    };

    std::vector<NodeId> entryNodes;
    for (const RootEvent &root : unit.rootEvents_) {
        if (auto failure = category(root.semanticName, Category::Name,
                                    "root semantic name"))
            return failure;
        Category wanted;
        RootKindMask wantedMask;
        switch (root.kind) {
        case RootKind::Symbol:
            wanted = Category::ObjectValue;
            wantedMask = rootBit(RootKind::Symbol);
            break;
        case RootKind::Type:
            wanted = Category::GlobalDeclaration;
            wantedMask = rootBit(RootKind::Type);
            break;
        case RootKind::TemplateSymbol:
            wanted = Category::Template;
            wantedMask = rootBit(RootKind::TemplateSymbol);
            break;
        case RootKind::TemplateType:
            wanted = Category::Template;
            wantedMask = rootBit(RootKind::TemplateType);
            break;
        default:
            return error("root event has an invalid root kind");
        }
        if (auto failure =
                category(root.semanticValue, wanted, "root semantic value"))
            return failure;
        const Node &value = unit.nodes_.nodes_[root.semanticValue.value()];
        const ConstructorSpec *spec = findConstructorSpec(value.constructor);
        if (!spec || (spec->allowedRoots & wantedMask) == 0)
            return error(
                "root value constructor is not permitted for its table");
        entryNodes.push_back(root.semanticName);
        entryNodes.push_back(root.semanticValue);
    }

    for (const NonRootEvent &event : unit.nonRootEvents_) {
        llvm::Error failure = std::visit(
            [&](const auto &typed) -> llvm::Error {
                using T = std::decay_t<decltype(typed)>;
                if constexpr (std::is_same_v<T, NamespaceAliasEvent>) {
                    if (typed.from)
                        if (auto e = category(*typed.from, Category::Name,
                                              "namespace alias source"))
                            return e;
                    if (auto e = category(typed.to, Category::Name,
                                          "namespace alias target"))
                        return e;
                    if (auto e = origins(typed.origins, "namespace alias"))
                        return e;
                    if (typed.from)
                        entryNodes.push_back(*typed.from);
                    entryNodes.push_back(typed.to);
                } else if constexpr (std::is_same_v<T, StaticAssertEvent>) {
                    if (typed.message &&
                        typed.message->kind != ScalarKind::String)
                        return error(
                            "static assertion message is not a string scalar");
                    if (auto e = category(typed.condition, Category::Expression,
                                          "static assertion condition"))
                        return e;
                    if (auto e = origins(typed.origins, "static assertion"))
                        return e;
                    entryNodes.push_back(typed.condition);
                } else if constexpr (std::is_same_v<T, TemplateAliasEvent>) {
                    if (auto e = category(typed.semanticName, Category::Name,
                                          "template alias name"))
                        return e;
                    if (auto e =
                            category(typed.templateValue, Category::Template,
                                     "template alias value"))
                        return e;
                    if (unit.nodes_.nodes_[typed.templateValue.value()]
                            .constructor != Constructor::TemplateAliasValue)
                        return error(
                            "template alias has the wrong constructor");
                    if (auto e = origins(typed.origins, "template alias"))
                        return e;
                    entryNodes.push_back(typed.semanticName);
                    entryNodes.push_back(typed.templateValue);
                } else {
                    if (auto e = category(typed.canonicalKey, Category::Name,
                                          "template instance key"))
                        return e;
                    if (auto e = category(typed.value,
                                          Category::TemplatePreInstantiation,
                                          "template instance value"))
                        return e;
                    if (unit.nodes_.nodes_[typed.value.value()].constructor !=
                        Constructor::TemplatePreInstantiationValue)
                        return error(
                            "template instance has the wrong constructor");
                    if (auto e = origins(typed.origins, "template instance"))
                        return e;
                    entryNodes.push_back(typed.canonicalKey);
                    entryNodes.push_back(typed.value);
                }
                return llvm::Error::success();
            },
            event);
        if (failure)
            return failure;
    }

    if (unit.orderedEvents_.size() !=
        unit.rootEvents_.size() + unit.nonRootEvents_.size())
        return error("ordered TU event stream has the wrong cardinality");
    std::vector<bool> orderedRoots(unit.rootEvents_.size(), false);
    std::vector<bool> orderedNonRoots(unit.nonRootEvents_.size(), false);
    for (const OrderedEventRef &event : unit.orderedEvents_) {
        std::vector<bool> *seen = event.kind == OrderedEventKind::Root
                                      ? &orderedRoots
                                      : &orderedNonRoots;
        if (event.index >= seen->size() || (*seen)[event.index])
            return error("ordered TU event stream has an invalid reference");
        (*seen)[event.index] = true;
    }

    // Validate the complete semantic graph for cycles, even disconnected
    // components, so later roots cannot expose a latent malformed subgraph.
    std::vector<unsigned char> color(unit.nodes_.size(), 0);
    std::function<llvm::Error(NodeId)> visit = [&](NodeId id) -> llvm::Error {
        auto &state = color[id.value()];
        if (state == 1)
            return error("IR semantic graph contains a cycle");
        if (state == 2)
            return llvm::Error::success();
        state = 1;
        auto children = unit.nodes_.children(id);
        if (!children)
            return children.takeError();
        for (NodeId child : *children)
            if (auto failure = visit(child))
                return failure;
        state = 2;
        return llvm::Error::success();
    };
    for (std::size_t i = 0; i < unit.nodes_.size(); ++i)
        if (auto failure = visit(NodeId(static_cast<std::uint32_t>(i))))
            return failure;

    // Opaque is an explicit migration form but may not be reachable from any
    // root or non-root event at the immutable boundary.
    std::vector<bool> seen(unit.nodes_.size(), false);
    std::function<llvm::Error(NodeId)> rejectOpaque =
        [&](NodeId id) -> llvm::Error {
        if (seen[id.value()])
            return llvm::Error::success();
        seen[id.value()] = true;
        const auto &node = unit.nodes_.nodes_[id.value()];
        for (const auto &argument : node.arguments)
            if (containsOpaque(argument))
                return error(
                    "reachable IR node contains a temporary opaque value");
        auto children = unit.nodes_.children(id);
        if (!children)
            return children.takeError();
        for (NodeId child : *children)
            if (auto failure = rejectOpaque(child))
                return failure;
        return llvm::Error::success();
    };
    for (NodeId entry : entryNodes)
        if (auto failure = rejectOpaque(entry))
            return failure;

    return llvm::Error::success();
}

} // namespace ir
