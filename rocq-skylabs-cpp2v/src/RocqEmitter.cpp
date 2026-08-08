/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "RocqEmitter.hpp"

#include <sstream>
#include <system_error>

#include <llvm/Support/Error.h>

namespace ir {
namespace {

llvm::Error error(const std::string &message) {
    return llvm::createStringError(std::errc::invalid_argument, "%s",
                                   message.c_str());
}

std::string rocqString(const std::string &value) {
    std::string result = "\"";
    for (unsigned char byte : value) {
        result.push_back(static_cast<char>(byte));
        if (byte == '"')
            result.push_back('"');
    }
    result.push_back('"');
    return result;
}

std::string rocqComment(const std::string &value) {
    std::string result = "(* ";
    for (std::size_t index = 0; index < value.size(); ++index) {
        const char current = value[index];
        result.push_back(current);
        if ((current == '(' || current == '*') && index + 1 < value.size()) {
            const char next = value[index + 1];
            if ((current == '(' && next == '*') ||
                (current == '*' && next == ')'))
                result.push_back(' ');
        }
    }
    result += " *)";
    return result;
}

std::string join(const std::vector<std::string> &values,
                 const char *separator) {
    std::string result;
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i)
            result += separator;
        result += values[i];
    }
    return result;
}

} // namespace

std::string SemanticRocqEmitter::renderScalar(const ScalarTerm &scalar) const {
    switch (scalar.kind) {
    case ScalarKind::String:
        return rocqString(scalar.text);
    case ScalarKind::Symbol:
    case ScalarKind::Boolean:
        return scalar.text;
    case ScalarKind::Numeral:
        return llvm::StringRef(scalar.text).starts_with("-")
                   ? "(" + scalar.text + ")%Z"
                   : scalar.text;
    case ScalarKind::Natural:
        return scalar.text + "%N";
    case ScalarKind::SwitchBranch:
        return scalar.text;
    case ScalarKind::LocalName:
        return llvm::StringRef(scalar.text).starts_with("(localname.")
                   ? scalar.text
                   : rocqString(scalar.text);
    case ScalarKind::ByteString: {
        std::vector<std::string> bytes;
        bytes.reserve(scalar.text.size());
        for (unsigned char byte : scalar.text)
            bytes.push_back(std::to_string(static_cast<unsigned>(byte)) + "%N");
        const std::string list =
            bytes.empty() ? "nil" : "(" + join(bytes, " :: ") + " :: nil)";
        return "(literal_string.of_list_N " + list + ")";
    }
    }
    return {};
}

llvm::Expected<std::string> SemanticRocqEmitter::renderValue(
    const TranslationUnitIR &unit, const Value &value,
    const std::vector<NodeId> &projectedChildren, std::size_t &nextChild,
    const SharingPlan *plan, std::optional<ShareClassId> suppressed) const {
    if (const auto *scalar = std::get_if<ScalarTerm>(&value.payload))
        return renderScalar(*scalar);
    if (const auto *reference = std::get_if<NodeRef>(&value.payload)) {
        if (nextChild >= projectedChildren.size() ||
            projectedChildren[nextChild] != reference->value)
            return error(
                "Arena::children projection disagrees with Value grouping");
        return renderNodeUnchecked(unit, projectedChildren[nextChild++], plan,
                                   suppressed);
    }
    if (const auto *optional = std::get_if<OptionalValue>(&value.payload)) {
        if (!optional->value)
            return std::string("None");
        auto rendered = renderValue(unit, *optional->value, projectedChildren,
                                    nextChild, plan, suppressed);
        if (!rendered)
            return rendered.takeError();
        return "(Some " + *rendered + ")";
    }
    if (const auto *sequence = std::get_if<SequenceValue>(&value.payload)) {
        if (sequence->elements.empty())
            return std::string("nil");
        std::vector<std::string> elements;
        for (const auto &element : sequence->elements) {
            auto rendered = renderValue(unit, element, projectedChildren,
                                        nextChild, plan, suppressed);
            if (!rendered)
                return rendered.takeError();
            elements.push_back(std::move(*rendered));
        }
        return "(" + join(elements, " :: ") + " :: nil)";
    }
    if (const auto *product = std::get_if<ProductValue>(&value.payload)) {
        std::vector<std::string> fields;
        for (const auto &field : product->fields) {
            auto rendered = renderValue(unit, field, projectedChildren,
                                        nextChild, plan, suppressed);
            if (!rendered)
                return rendered.takeError();
            fields.push_back(std::move(*rendered));
        }
        if (product->constructor) {
            std::string result = "(" + renderScalar(*product->constructor);
            if (!fields.empty())
                result += " " + join(fields, " ");
            return result + ")";
        }
        if (fields.empty())
            return std::string("tt");
        if (fields.size() == 1)
            return "(" + fields.front() + ",)";
        return "(" + join(fields, ", ") + ")";
    }
    if (const auto *sum = std::get_if<SumValue>(&value.payload)) {
        if (!sum->payload)
            return error("sum value has no payload");
        auto payload = renderValue(unit, *sum->payload, projectedChildren,
                                   nextChild, plan, suppressed);
        if (!payload)
            return payload.takeError();
        return "(" + renderScalar(sum->activeConstructor) + " " + *payload +
               ")";
    }
    return error("temporary opaque value cannot be rendered");
}

llvm::Expected<std::string> SemanticRocqEmitter::renderNodeUnchecked(
    const TranslationUnitIR &unit, NodeId id, const SharingPlan *plan,
    std::optional<ShareClassId> suppressed) const {
    auto node = unit.nodes().get(id);
    if (!node)
        return node.takeError();
    if (options_.sharing && plan && (*node)->shareClass &&
        (!suppressed || *suppressed != *(*node)->shareClass))
        if (const SharingDefinition *definition =
                plan->lookup(*(*node)->shareClass))
            return definition->localName;
    const auto &spec = constructorSpec((*node)->constructor);
    auto projectedChildren = unit.nodes().children(id);
    if (!projectedChildren)
        return projectedChildren.takeError();
    std::size_t nextChild = 0;
    std::vector<std::string> arguments;
    for (const auto &argument : (*node)->arguments) {
        auto rendered = renderValue(unit, argument, *projectedChildren,
                                    nextChild, plan, suppressed);
        if (!rendered)
            return rendered.takeError();
        arguments.push_back(std::move(*rendered));
    }
    if (nextChild != projectedChildren->size())
        return error("semantic emitter did not consume every projected child");
    std::string result = "(" + std::string(spec.rocqSpelling);
    if (!arguments.empty())
        result += " " + join(arguments, " ");
    return result + ")";
}

llvm::Expected<std::string>
SemanticRocqEmitter::renderNode(const TranslationUnitIR &unit,
                                NodeId id) const {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);
    return renderNodeUnchecked(unit, id);
}

llvm::Expected<std::string>
SemanticRocqEmitter::renderNode(const TranslationUnitIR &unit, NodeId id,
                                const SharingPlan &plan) const {
    if (auto failure = IRSharing::validate(unit, plan))
        return std::move(failure);
    return renderNodeUnchecked(unit, id, &plan);
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitSharingDefinitions(const TranslationUnitIR &unit,
                                            const SharingPlan &plan) const {
    if (auto failure = IRSharing::validate(unit, plan))
        return std::move(failure);
    if (!options_.sharing)
        return std::string();
    std::ostringstream output;
    for (const SharingDefinition &definition : plan.definitions()) {
        auto value = renderNodeUnchecked(unit, definition.representative, &plan,
                                         definition.shareClass);
        if (!value)
            return value.takeError();
        if (options_.localSharingDefinitions)
            output << "#[local] ";
        output << "Definition " << definition.localName << " : ";
        if (options_.metaSharingTypes)
            output << (definition.kind == ShareClassKind::Type ? "Mtype"
                                                               : "Mname");
        else
            output << (definition.kind == ShareClassKind::Type ? "type"
                                                               : "name");
        output << " := " << *value << ".\n";
    }
    return output.str();
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitEvents(const TranslationUnitIR &unit,
                                std::optional<bool> templatePartition,
                                const SharingPlan *plan) const {
    if (plan) {
        if (auto failure = IRSharing::validate(unit, *plan))
            return std::move(failure);
    } else if (auto failure = IRValidator::validate(unit)) {
        return std::move(failure);
    }

    auto inPartition = [&](RootKind kind) {
        if (!templatePartition)
            return true;
        const bool isTemplate =
            kind == RootKind::TemplateSymbol || kind == RootKind::TemplateType;
        return isTemplate == *templatePartition;
    };
    auto inPartitionNonRoot = [&](const NonRootEvent &event) {
        if (!templatePartition)
            return true;
        const bool isTemplate =
            std::holds_alternative<TemplateAliasEvent>(event) ||
            std::holds_alternative<TemplateInstanceEvent>(event);
        return isTemplate == *templatePartition;
    };

    std::ostringstream output;
    auto renderRoot =
        [&](const RootEvent &root) -> llvm::Expected<std::string> {
        auto name = renderNodeUnchecked(unit, root.semanticName, plan);
        if (!name)
            return name.takeError();
        auto value = renderNodeUnchecked(unit, root.semanticValue, plan);
        if (!value)
            return value.takeError();
        const char *insertion = nullptr;
        switch (root.kind) {
        case RootKind::Symbol:
            insertion = "Dobj_value";
            break;
        case RootKind::Type:
            insertion = "Dglob_decl";
            break;
        case RootKind::TemplateSymbol:
            insertion = "Dtemplated_obj_value";
            break;
        case RootKind::TemplateType:
            insertion = "Dtemplated_glob_decl";
            break;
        default:
            return error("semantic emitter received an invalid root kind");
        }
        const std::string comment =
            root.diagnosticName ? rocqComment(*root.diagnosticName) + " " : "";
        return "(" + std::string(insertion) + " " + comment + *name + " " +
               *value + ")";
    };
    auto renderNonRoot =
        [&](const NonRootEvent &event) -> llvm::Expected<std::string> {
        return std::visit(
            [&](const auto &typed) -> llvm::Expected<std::string> {
                using T = std::decay_t<decltype(typed)>;
                if constexpr (std::is_same_v<T, NamespaceAliasEvent>) {
                    auto to = renderNodeUnchecked(unit, typed.to, plan);
                    if (!to)
                        return to.takeError();
                    if (typed.from) {
                        auto from =
                            renderNodeUnchecked(unit, *typed.from, plan);
                        if (!from)
                            return from.takeError();
                        return "(Dusing_namespace " + *from + " " + *to + ")";
                    }
                    return "(Dglobal_using_namespace " + *to + ")";
                } else if constexpr (std::is_same_v<T, StaticAssertEvent>) {
                    std::string message = "None";
                    if (typed.message)
                        message = "(Some " + renderScalar(*typed.message) + ")";
                    auto condition =
                        renderNodeUnchecked(unit, typed.condition, plan);
                    if (!condition)
                        return condition.takeError();
                    return "(Dstatic_assert " + message + " " + *condition +
                           ")";
                } else if constexpr (std::is_same_v<T, TemplateAliasEvent>) {
                    auto name =
                        renderNodeUnchecked(unit, typed.semanticName, plan);
                    if (!name)
                        return name.takeError();
                    auto value =
                        renderNodeUnchecked(unit, typed.templateValue, plan);
                    if (!value)
                        return value.takeError();
                    const std::string comment =
                        typed.diagnosticName
                            ? rocqComment(*typed.diagnosticName) + " "
                            : "";
                    return "(Dtemplated_type_alias " + comment + *name + " " +
                           *value + ")";
                } else {
                    auto key =
                        renderNodeUnchecked(unit, typed.canonicalKey, plan);
                    if (!key)
                        return key.takeError();
                    auto value = renderNodeUnchecked(unit, typed.value, plan);
                    if (!value)
                        return value.takeError();
                    const std::string keyComment =
                        typed.diagnosticKey
                            ? rocqComment(*typed.diagnosticKey) + " "
                            : "";
                    const std::string targetComment =
                        typed.diagnosticTarget
                            ? rocqComment(*typed.diagnosticTarget) + " "
                            : "";
                    return "(Dtemplate_preinst " + keyComment + *key + " " +
                           targetComment + *value + ")";
                }
            },
            event);
    };
    for (const OrderedEventRef &event : unit.orderedEvents()) {
        if (event.kind == OrderedEventKind::Root &&
            !inPartition(unit.rootEvents()[event.index].kind))
            continue;
        if (event.kind == OrderedEventKind::NonRoot &&
            !inPartitionNonRoot(unit.nonRootEvents()[event.index]))
            continue;
        llvm::Expected<std::string> rendered =
            event.kind == OrderedEventKind::Root
                ? renderRoot(unit.rootEvents()[event.index])
                : renderNonRoot(unit.nonRootEvents()[event.index]);
        if (!rendered)
            return rendered.takeError();
        output << *rendered << "\n";
    }
    return output.str();
}

llvm::Expected<std::string>
SemanticRocqEmitter::emit(const TranslationUnitIR &unit) const {
    return emitEvents(unit, std::nullopt, nullptr);
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitOrdinary(const TranslationUnitIR &unit) const {
    return emitEvents(unit, false, nullptr);
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitOrdinary(const TranslationUnitIR &unit,
                                  const SharingPlan &plan) const {
    return emitEvents(unit, false, &plan);
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitTemplates(const TranslationUnitIR &unit) const {
    return emitEvents(unit, true, nullptr);
}

llvm::Expected<std::string>
SemanticRocqEmitter::emitTemplates(const TranslationUnitIR &unit,
                                   const SharingPlan &plan) const {
    return emitEvents(unit, true, &plan);
}

} // namespace ir
