/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "LocationEmitter.hpp"

#include <sstream>
#include <system_error>

#include <llvm/Support/Error.h>

namespace ir {
namespace {

std::string stringLiteral(const std::string &value) {
    std::string result = "\"";
    for (unsigned char byte : value) {
        result.push_back(static_cast<char>(byte));
        if (byte == '"')
            result.push_back('"');
    }
    result.push_back('"');
    return result;
}

template <typename Range, typename Render>
llvm::Expected<std::string> renderList(const Range &values, Render render) {
    if (values.empty())
        return std::string("nil");
    std::string result = "(";
    for (const auto &value : values) {
        auto item = render(value);
        if (!item)
            return item.takeError();
        result += *item + " :: ";
    }
    return result + "nil)";
}

const char *fileKind(source::FileKind kind) {
    switch (kind) {
    case source::FileKind::User:
        return "FKUser";
    case source::FileKind::System:
        return "FKSystem";
    case source::FileKind::ExternCSystem:
        return "FKExternCSystem";
    case source::FileKind::UserModuleMap:
        return "FKUserModuleMap";
    case source::FileKind::SystemModuleMap:
        return "FKSystemModuleMap";
    case source::FileKind::Builtin:
        return "FKBuiltin";
    case source::FileKind::CommandLine:
        return "FKCommandLine";
    case source::FileKind::Scratch:
        return "FKScratch";
    case source::FileKind::Predefined:
        return "FKPredefined";
    case source::FileKind::Other:
        return "FKOther";
    }
    return "FKOther";
}

const char *originKind(source::OriginKind kind) {
    switch (kind) {
    case source::OriginKind::Explicit:
        return "ExplicitOrigin";
    case source::OriginKind::Implicit:
        return "ImplicitOrigin";
    case source::OriginKind::ClangTransformed:
        return "ClangTransformedOrigin";
    case source::OriginKind::Cpp2vSynthesized:
        return "Cpp2vSynthesizedOrigin";
    case source::OriginKind::Inherited:
        return "InheritedOrigin";
    }
    return "ExplicitOrigin";
}

std::string renderPoint(const source::PhysicalPoint &point) {
    return "(Build_physical_point " + std::to_string(point.file.value()) + " " +
           std::to_string(point.byteOffset) + "%N " +
           std::to_string(point.line) + "%N " +
           std::to_string(point.byteColumn) + "%N)";
}

std::string renderPresumed(const source::PresumedPoint &point) {
    return "(Build_presumed_point " + stringLiteral(point.file) + " " +
           std::to_string(point.line) + "%N " + std::to_string(point.column) +
           "%N)";
}

template <typename T, typename Render>
std::string renderOption(const std::optional<T> &value, Render render) {
    return value ? "(Some " + render(*value) + ")" : "None";
}

std::string renderRange(const source::Range &range) {
    std::string normalized = "None";
    if (range.normalizedHalfOpen)
        normalized = "(Some (" + renderPoint(range.normalizedHalfOpen->first) +
                     ", " + renderPoint(range.normalizedHalfOpen->second) +
                     "))";
    return "(Build_source_range " + renderOption(range.begin, renderPoint) +
           " " + renderOption(range.end, renderPoint) + " " +
           (range.endSemantics == source::RangeKind::Token ? "TokenRange"
                                                           : "CharacterRange") +
           " " + normalized + ")";
}

std::string renderFrame(const source::MacroFrame &frame) {
    return "(Build_macro_frame " + renderOption(frame.name, stringLiteral) +
           " " +
           (frame.kind == source::MacroOriginKind::Body ? "MacroBody"
                                                        : "MacroArgument") +
           " " + renderOption(frame.spelling, renderRange) + " " +
           renderOption(frame.expansion, renderRange) + ")";
}

llvm::Expected<std::string> renderOrigin(const source::Origin &origin) {
    auto frames = renderList(origin.macroStack, [](const auto &frame) {
        return llvm::Expected<std::string>(renderFrame(frame));
    });
    if (!frames)
        return frames.takeError();
    auto derived = renderList(origin.derivedFrom, [](source::OriginId id) {
        return llvm::Expected<std::string>(std::to_string(id.value()));
    });
    if (!derived)
        return derived.takeError();
    return "(Build_source_origin " + std::string(originKind(origin.kind)) +
           " " + renderOption(origin.spelling, renderRange) + " " +
           renderOption(origin.expansion, renderRange) + " " +
           renderOption(origin.presumedBegin, renderPresumed) + " " +
           renderOption(origin.presumedEnd, renderPresumed) + " " + *frames +
           " " + renderOption(origin.pointOfInstantiation, renderPoint) + " " +
           renderOption(
               origin.anchor,
               [](source::OriginId id) { return std::to_string(id.value()); }) +
           " " + *derived + ")";
}

llvm::Expected<std::string> renderFile(const source::File &file) {
    std::string parent = "None";
    if (file.includeParent)
        parent = "(Some (" + std::to_string(file.includeParent->first.value()) +
                 ", " + std::to_string(file.includeParent->second) + "%N))";
    return "(Build_source_file " + stringLiteral(file.physicalName) + " " +
           renderOption(file.requestedName, stringLiteral) + " " +
           fileKind(file.kind) + " " + (file.isMain ? "true" : "false") + " " +
           parent + ")";
}

} // namespace

llvm::Expected<std::string>
LocationRocqEmitter::renderTreeUnchecked(const TranslationUnitIR &unit,
                                         NodeId root) const {
    auto node = unit.nodes().get(root);
    if (!node)
        return node.takeError();
    auto origins = renderList((*node)->origins, [](source::OriginId origin) {
        return llvm::Expected<std::string>(std::to_string(origin.value()));
    });
    if (!origins)
        return origins.takeError();

    // This is intentionally the only recursion point. It has no constructor or
    // container cases: all recursive shape is mechanically projected here.
    auto childIds = unit.nodes().children(root);
    if (!childIds)
        return childIds.takeError();
    auto children = renderList(*childIds, [&](NodeId child) {
        return renderTreeUnchecked(unit, child);
    });
    if (!children)
        return children.takeError();
    return "(LocNode " + *origins + " " + *children + ")";
}

llvm::Expected<std::string>
LocationRocqEmitter::renderTree(const TranslationUnitIR &unit,
                                NodeId root) const {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);
    return renderTreeUnchecked(unit, root);
}

llvm::Expected<std::string>
LocationRocqEmitter::emit(const TranslationUnitIR &unit) const {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);

    auto files = renderList(unit.sources().files, renderFile);
    if (!files)
        return files.takeError();
    auto origins = renderList(unit.sources().origins, renderOrigin);
    if (!origins)
        return origins.takeError();

    std::vector<std::string> events;
    for (const OrderedEventRef &ordered : unit.orderedEvents()) {
        if (ordered.kind != OrderedEventKind::Root)
            continue;
        if (ordered.index >= unit.rootEvents().size())
            return llvm::createStringError(
                std::errc::invalid_argument,
                "location emitter received an invalid ordered root index");
        const RootEvent &root = unit.rootEvents()[ordered.index];
        const bool isTemplate = root.kind == RootKind::TemplateSymbol ||
                                root.kind == RootKind::TemplateType;
        if (isTemplate && !options_.includeTemplates)
            continue;

        // emit() validates the whole unit once. Inline rendering deliberately
        // bypasses ordinary-module sharing and does not repeat that validation
        // for every event in a large translation unit.
        auto name = semantic_.renderNodeUnchecked(unit, root.semanticName);
        if (!name)
            return name.takeError();
        auto value = semantic_.renderNodeUnchecked(unit, root.semanticValue);
        if (!value)
            return value.takeError();
        auto tree = renderTreeUnchecked(unit, root.semanticValue);
        if (!tree)
            return tree.takeError();
        const char *constructor = nullptr;
        switch (root.kind) {
        case RootKind::Symbol:
            constructor = "Construction.LESymbol";
            break;
        case RootKind::Type:
            constructor = "Construction.LEType";
            break;
        case RootKind::TemplateSymbol:
            constructor = "Construction.LEMsymbol";
            break;
        case RootKind::TemplateType:
            constructor = "Construction.LEMtype";
            break;
        default:
            return llvm::createStringError(
                std::errc::invalid_argument,
                "location emitter received an invalid root kind");
        }
        events.push_back("(" + std::string(constructor) + " " + *name + " " +
                         *value + " " + *tree + ")");
    }
    auto eventList = renderList(events, [](const std::string &event) {
        return llvm::Expected<std::string>(event);
    });
    if (!eventList)
        return eventList.takeError();

    std::ostringstream output;
    output << "Require Import skylabs.lang.cpp.syntax.source_location.\n"
              "Require Import skylabs.lang.cpp.parser.\n"
              "Require Import skylabs.lang.cpp.mparser.\n"
              "Require Import skylabs.lang.cpp.parser.source_location.\n\n"
              "#[local] Open Scope pstring_scope.\n\n";
    output << "#[local] Definition source_files : list source_file := "
           << *files << ".\n";
    output << "#[local] Definition source_origins : list source_origin := "
           << *origins << ".\n";
    output << "#[local] Definition located_root_events : list "
              "Construction.located_root_event := "
           << *eventList << ".\n\n";
    output << "Definition source_locations : source_map.\n"
              "Proof.\n"
              "  Construction.build_source_map_or_fail source_files "
              "source_origins located_root_events.\n"
              "Defined.\n";
    return output.str();
}

} // namespace ir
