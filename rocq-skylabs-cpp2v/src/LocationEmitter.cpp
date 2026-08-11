/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "LocationEmitter.hpp"
#include "LocationDAGEncoding.hpp"
#include "SourceInfoEncoding.hpp"

#include <algorithm>
#include <sstream>
#include <system_error>
#include <type_traits>

#include <llvm/Support/Error.h>

namespace ir {
namespace {

constexpr std::size_t kTableChunkSize = 4096;

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

template <typename T, typename Render>
std::string renderOption(const std::optional<T> &value, Render render) {
    return value ? "(Some " + render(*value) + ")" : "None";
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

const char *rangeKind(source::RangeKind kind) {
    return kind == source::RangeKind::Token ? "TokenRange" : "CharacterRange";
}

const char *macroKind(source::MacroOriginKind kind) {
    return kind == source::MacroOriginKind::Body ? "MacroBody"
                                                 : "MacroArgument";
}

std::string renderEncodedPhysicalPoint(const source::PhysicalPoint &point) {
    return "EP(" + std::to_string(point.file.value()) + ", " +
           std::to_string(point.byteOffset) + "%N, " +
           std::to_string(point.line) + "%N, " +
           std::to_string(point.byteColumn) + "%N)";
}

template <typename Id> std::string renderTableId(Id id) {
    return std::to_string(id.value());
}

std::string
renderEncodedPoint(const source::encoding::EncodedPresumedPoint &point) {
    return "(Encoded.Build_encoded_presumed_point " +
           renderTableId(point.file) + " " + std::to_string(point.line) +
           "%N " + std::to_string(point.column) + "%N)";
}

std::string renderEncodedRange(const source::encoding::EncodedRange &range) {
    return std::visit(
        [](const auto &value) -> std::string {
            using T = std::decay_t<decltype(value)>;
            if constexpr (std::is_same_v<T, source::encoding::RawRange>) {
                return "(Encoded.EncodedRawRange " +
                       renderOption(value.begin,
                                    [](auto id) { return renderTableId(id); }) +
                       " " +
                       renderOption(value.end,
                                    [](auto id) { return renderTableId(id); }) +
                       " " + rangeKind(value.endSemantics) + ")";
            } else if constexpr (
                std::is_same_v<T, source::encoding::SameBeginNormalizedRange>) {
                return "(Encoded.EncodedSameBeginRange " +
                       renderTableId(value.begin) + " " +
                       renderTableId(value.end) + " " +
                       rangeKind(value.endSemantics) + " " +
                       renderTableId(value.normalizedEnd) + ")";
            } else {
                return "(Encoded.EncodedGeneralRange " +
                       renderTableId(value.begin) + " " +
                       renderTableId(value.end) + " " +
                       rangeKind(value.endSemantics) + " " +
                       renderTableId(value.normalizedBegin) + " " +
                       renderTableId(value.normalizedEnd) + ")";
            }
        },
        range);
}

std::string
renderEncodedFrame(const source::encoding::EncodedMacroFrame &frame) {
    return "(Encoded.Build_encoded_macro_frame " +
           renderOption(frame.name, stringLiteral) + " " +
           macroKind(frame.kind) + " " +
           renderOption(frame.spelling,
                        [](auto id) { return renderTableId(id); }) +
           " " +
           renderOption(frame.expansion,
                        [](auto id) { return renderTableId(id); }) +
           ")";
}

llvm::Expected<std::string> renderFile(const source::File &file) {
    std::string parent = "None";
    if (file.includeParent)
        parent = "(Some ((Build_file_id " +
                 std::to_string(file.includeParent->first.value()) + "), " +
                 std::to_string(file.includeParent->second) + "%N))";
    return "(Build_source_file " + stringLiteral(file.physicalName) + " " +
           renderOption(file.requestedName, stringLiteral) + " " +
           fileKind(file.kind) + " " + (file.isMain ? "true" : "false") + " " +
           parent + ")";
}

template <typename T, typename Render>
std::string renderIndexedTable(const std::string &name, const std::string &type,
                               const std::vector<T> &rows,
                               const std::string &defaultRow, Render render) {
    std::ostringstream output;
    std::size_t chunk = 0;
    for (std::size_t first = 0; first < rows.size();
         first += kTableChunkSize, ++chunk) {
        const std::size_t last = std::min(first + kTableChunkSize, rows.size());
        output << "#[local] Definition " << name << "_chunk_" << chunk
               << " : PArray.array " << type << " :=\n  [|\n";
        for (std::size_t index = first; index < last; ++index) {
            output << "    " << render(rows[index]);
            if (index + 1 != last)
                output << ";";
            output << "\n";
        }
        output << "  | " << defaultRow << " |].\n";
    }
    output << "#[local] Definition " << name << " : Encoded.indexed_table "
           << type << " :=\n  Encoded.Build_indexed_table " << rows.size()
           << "\n  [|\n";
    for (std::size_t index = 0; index < chunk; ++index) {
        output << "    " << name << "_chunk_" << index;
        if (index + 1 != chunk)
            output << ";";
        output << "\n";
    }
    output << "  | [| | " << defaultRow << " |] |].\n";
    return output.str();
}

template <typename Id> std::string renderRawIds(const std::vector<Id> &ids) {
    if (ids.empty())
        return "nil";
    std::string result = "(";
    for (Id id : ids)
        result += std::to_string(id.value()) + " :: ";
    return result + "nil)";
}

std::string renderPublicOriginIds(const std::vector<source::OriginId> &ids) {
    if (ids.empty())
        return "nil";
    std::string result = "(";
    for (source::OriginId id : ids)
        result += "(Build_origin_id " + std::to_string(id.value()) + ") :: ";
    return result + "nil)";
}

std::string renderMacroStack(const source::encoding::EncodedOrigin &origin,
                             const source::encoding::EncodedTables &tables,
                             bool references) {
    if (origin.macroStack.empty())
        return "nil";
    std::string result = "(";
    for (source::encoding::MacroFrameId id : origin.macroStack) {
        if (id.value() >= tables.macroFrames.size())
            return "(* invalid macro frame ID *)";
        result +=
            references
                ? "(Encoded.MacroFrameReference " + renderTableId(id) + ")"
                : "(Encoded.InlineMacroFrame " +
                      renderEncodedFrame(tables.macroFrames[id.value()]) + ")";
        result += " :: ";
    }
    return result + "nil)";
}

std::string renderEncodedOrigin(const source::encoding::EncodedOrigin &origin,
                                const source::encoding::EncodedTables &tables,
                                bool references) {
    return "(Encoded.Build_encoded_origin " +
           std::string(originKind(origin.kind)) + " " +
           renderOption(origin.spelling,
                        [](auto id) { return renderTableId(id); }) +
           " " +
           renderOption(origin.expansion,
                        [](auto id) { return renderTableId(id); }) +
           " " +
           renderOption(origin.presumedBegin,
                        [](auto id) { return renderTableId(id); }) +
           " " +
           renderOption(origin.presumedEnd,
                        [](auto id) { return renderTableId(id); }) +
           " " + renderMacroStack(origin, tables, references) + " " +
           renderOption(origin.pointOfInstantiation,
                        [](auto id) { return renderTableId(id); }) +
           " " +
           renderOption(origin.anchor,
                        [](auto id) { return renderTableId(id); }) +
           " " + renderRawIds(origin.derivedFrom) + ")";
}

std::string
renderCommonProvenance(const source::encoding::EncodedTables &tables) {
    std::string result;
    result += renderIndexedTable(
        "presumed_filenames", "PrimString.string", tables.presumedFilenames,
        "Encoded.default_presumed_filename", stringLiteral);
    result += renderIndexedTable(
        "physical_points", "Encoded.encoded_physical_point",
        tables.physicalPoints, "Encoded.default_encoded_physical_point",
        renderEncodedPhysicalPoint);
    result += renderIndexedTable(
        "presumed_points", "Encoded.encoded_presumed_point",
        tables.presumedPoints, "Encoded.default_encoded_presumed_point",
        renderEncodedPoint);
    result += renderIndexedTable("source_ranges", "Encoded.encoded_range",
                                 tables.ranges, "Encoded.default_encoded_range",
                                 renderEncodedRange);
    return result;
}

std::string
renderMacroDependentProvenance(const source::encoding::EncodedTables &tables,
                               bool references) {
    static const std::vector<source::encoding::EncodedMacroFrame> noFrames;
    const std::vector<source::encoding::EncodedMacroFrame> &frameRows =
        references ? tables.macroFrames : noFrames;
    std::string result = renderIndexedTable(
        "macro_frames", "Encoded.encoded_macro_frame", frameRows,
        "Encoded.default_encoded_macro_frame", renderEncodedFrame);
    result += renderIndexedTable(
        "encoded_origins", "Encoded.encoded_origin", tables.origins,
        "Encoded.default_encoded_origin", [&](const auto &origin) {
            return renderEncodedOrigin(origin, tables, references);
        });
    return result;
}

std::string
renderEncodedLocationShape(const location::encoding::EncodedShape &shape) {
    return "LS(" + renderRawIds(shape.children) + ")";
}

std::string
renderEncodedLocationNode(const location::encoding::EncodedLocationNode &node) {
    return "LN(" + renderTableId(node.shape) + ", " +
           renderRawIds(node.origins) + ", " + renderRawIds(node.children) +
           ")";
}

std::string
renderLocationDag(const location::encoding::EncodedLocations &locations) {
    std::string result = renderIndexedTable(
        "location_shapes", "Encoded.encoded_location_shape", locations.shapes,
        "Encoded.default_encoded_location_shape", renderEncodedLocationShape);
    result += renderIndexedTable(
        "location_nodes", "Encoded.encoded_location_node", locations.nodes,
        "Encoded.default_encoded_location_node", renderEncodedLocationNode);
    result += "#[local] Definition source_location_dag : "
              "Encoded.indexed_location_dag :=\n  "
              "Encoded.Build_indexed_location_dag location_shapes "
              "location_nodes.\n";
    return result;
}

llvm::Expected<std::string>
renderProvenance(const source::encoding::EncodedTables &tables) {
    // The encoder itself establishes these IDs. This guard keeps a corrupt
    // test producer from serializing either a fabricated inline frame or an
    // invalid private table reference.
    for (const auto &origin : tables.origins)
        for (source::encoding::MacroFrameId id : origin.macroStack)
            if (!id.valid() || id.value() >= tables.macroFrames.size())
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "normalized provenance has an invalid macro frame ID");

    std::string common = renderCommonProvenance(tables);
    std::string inlineTail = renderMacroDependentProvenance(tables, false);
    std::string referencedTail = renderMacroDependentProvenance(tables, true);
    const bool references = referencedTail.size() < inlineTail.size();
    std::string selectedTail =
        references ? std::move(referencedTail) : std::move(inlineTail);
    if (references)
        std::string().swap(inlineTail);
    else
        std::string().swap(referencedTail);

    common.reserve(common.size() + selectedTail.size() + 300);
    common += selectedTail;
    common += "#[local] Definition source_provenance : "
              "Encoded.indexed_provenance :=\n  "
              "Encoded.Build_indexed_provenance presumed_filenames "
              "physical_points presumed_points source_ranges macro_frames "
              "encoded_origins.\n";
    return common;
}

} // namespace

llvm::Error LocationRocqEmitter::appendTreeUnchecked(
    std::string &output, const TranslationUnitIR &unit, NodeId root) const {
    auto node = unit.nodes().get(root);
    if (!node)
        return node.takeError();
    output += "(LocNode ";
    output += renderPublicOriginIds((*node)->origins);
    output += " ";

    // This is intentionally the only recursion point. It has no constructor or
    // container cases: all recursive shape is mechanically projected here.
    auto childIds = unit.nodes().children(root);
    if (!childIds)
        return childIds.takeError();
    if (childIds->empty()) {
        output += "nil)";
        return llvm::Error::success();
    }
    output += "(";
    for (NodeId child : *childIds) {
        if (auto failure = appendTreeUnchecked(output, unit, child))
            return failure;
        output += " :: ";
    }
    output += "nil))";
    return llvm::Error::success();
}

llvm::Expected<std::string>
LocationRocqEmitter::renderTreeUnchecked(const TranslationUnitIR &unit,
                                         NodeId root) const {
    std::string output;
    if (auto failure = appendTreeUnchecked(output, unit, root))
        return std::move(failure);
    return output;
}

llvm::Expected<std::string>
LocationRocqEmitter::renderTree(const TranslationUnitIR &unit,
                                NodeId root) const {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);
    return renderTreeUnchecked(unit, root);
}

llvm::Expected<std::string> LocationRocqEmitter::renderLocationDagForTest(
    const location::encoding::EncodedLocations &locations) const {
    if (auto failure = location::encoding::validate(locations))
        return std::move(failure);
    return renderLocationDag(locations);
}

llvm::Expected<std::string>
LocationRocqEmitter::emit(const TranslationUnitIR &unit) const {
    if (auto failure = IRValidator::validate(unit))
        return std::move(failure);
    auto files = renderList(unit.sources().files, renderFile);
    if (!files)
        return files.takeError();
    auto provenance = [&]() -> llvm::Expected<std::string> {
        auto encoded = source::encoding::encode(unit.sources());
        if (!encoded)
            return encoded.takeError();
        return renderProvenance(*encoded);
    }();
    if (!provenance)
        return provenance.takeError();
    auto locations =
        location::encoding::encode(unit, options_.includeTemplates);
    if (!locations)
        return locations.takeError();
    std::string locationDag = renderLocationDag(*locations);

    std::string eventList;
    bool hasEvents = false;
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
        const char *constructor = nullptr;
        switch (root.kind) {
        case RootKind::Symbol:
            constructor = "Construction.ILESymbol";
            break;
        case RootKind::Type:
            constructor = "Construction.ILEType";
            break;
        case RootKind::TemplateSymbol:
            constructor = "Construction.ILEMsymbol";
            break;
        case RootKind::TemplateType:
            constructor = "Construction.ILEMtype";
            break;
        default:
            return llvm::createStringError(
                std::errc::invalid_argument,
                "location emitter received an invalid root kind");
        }
        if (ordered.index >= locations->eventRoots.size() ||
            !locations->eventRoots[ordered.index])
            return llvm::createStringError(
                std::errc::invalid_argument,
                "location DAG omitted a selected root event");
        const location::encoding::EncodedRoot encodedRoot =
            *locations->eventRoots[ordered.index];
        auto name = semantic_.renderNodeUnchecked(unit, root.semanticName);
        if (!name)
            return name.takeError();
        auto value = semantic_.renderNodeUnchecked(unit, root.semanticValue);
        if (!value)
            return value.takeError();
        if (!hasEvents) {
            eventList = "(";
            hasEvents = true;
        }
        eventList += "(";
        eventList += constructor;
        eventList += " ";
        eventList += *name;
        eventList += " ";
        eventList += *value;
        eventList += " ";
        eventList += renderTableId(encodedRoot.node);
        eventList += "%uint63 ";
        eventList += renderTableId(encodedRoot.shape);
        eventList += "%uint63) :: ";
    }
    eventList += hasEvents ? "nil)" : "nil";
    std::vector<location::encoding::EncodedShape>().swap(locations->shapes);
    std::vector<location::encoding::EncodedLocationNode>().swap(
        locations->nodes);
    std::vector<std::optional<location::encoding::EncodedRoot>>().swap(
        locations->eventRoots);

    constexpr const char *prefix =
        "Require Import skylabs.lang.cpp.syntax.source_location.\n"
        "Require Import skylabs.prelude.pstring.\n"
        "Require Import Stdlib.Array.PArray.\n"
        "Require Import Stdlib.NArith.NArith.\n"
        "Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.\n\n"
        "#[local] Set Warnings \"-abstract-large-number\".\n"
        "#[local] Open Scope pstring_scope.\n"
        "#[local] Open Scope array_scope.\n"
        "#[local] Open Scope uint63_scope.\n"
        "#[local] Notation "
        "\"'EP' '(' file ',' offset ',' line ',' column ')'\" :=\n"
        "  (Encoded.Build_encoded_physical_point file offset line column) "
        "(only parsing).\n"
        "#[local] Notation \"'LS' '(' children ')'\" :=\n"
        "  (Encoded.Build_encoded_location_shape children) "
        "(only parsing).\n"
        "#[local] Notation \"'LN' '(' shape ',' origins ',' children ')'\" "
        ":=\n"
        "  (Encoded.Build_encoded_location_node shape origins children) "
        "(only parsing).\n\n"
        "#[local] Definition source_files : list source_file := ";
    constexpr const char *sourceFilesEnd = ".\n";
    constexpr const char *middle =
        "\n#[local] Close Scope uint63_scope.\n"
        "#[local] Close Scope array_scope.\n\n"
        "Require Import skylabs.lang.cpp.parser.\n"
        "Require Import skylabs.lang.cpp.mparser.\n"
        "Require Import skylabs.lang.cpp.parser.source_location.\n\n"
        "#[local] Definition located_root_events : list "
        "Construction.indexed_located_root_event := ";
    constexpr const char *suffix =
        ".\n\nDefinition source_locations : source_map.\n"
        "Proof.\n"
        "  Construction.build_indexed_dag_source_map_or_fail source_files "
        "source_provenance source_location_dag located_root_events.\n"
        "Defined.\n";
    std::string output;
    output.reserve(std::char_traits<char>::length(prefix) + files->size() +
                   std::char_traits<char>::length(sourceFilesEnd) +
                   provenance->size() + locationDag.size() +
                   std::char_traits<char>::length(middle) + eventList.size() +
                   std::char_traits<char>::length(suffix));
    output += prefix;
    output += *files;
    output += sourceFilesEnd;
    output += *provenance;
    output += locationDag;
    output += middle;
    output += eventList;
    output += suffix;
    return output;
}

} // namespace ir
