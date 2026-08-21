/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#include "LocationEmitter.hpp"
#include "LocationDAGEncoding.hpp"
#include "RootEventEncoding.hpp"
#include "SourceInfoEncoding.hpp"

#include <algorithm>
#include <array>
#include <filesystem>
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

std::string renderStringList(const std::vector<std::string> &components) {
    if (components.empty())
        return "nil";
    std::string result = "(";
    for (const auto &component : components)
        result += stringLiteral(component) + " :: ";
    return result + "nil)";
}

struct EncodedRelativePath {
    std::size_t parents = 0;
    std::vector<std::string> components;
};

std::optional<EncodedRelativePath>
relativePath(const std::filesystem::path &base,
             const std::filesystem::path &target, bool allowParents) {
    const std::filesystem::path relative = target.lexically_relative(base);
    if (relative.empty() && target != base)
        return std::nullopt;

    EncodedRelativePath result;
    bool sawComponent = false;
    for (const auto &part : relative) {
        const std::string component = part.string();
        if (component.empty() || component == ".")
            continue;
        if (component == "..") {
            if (!allowParents || sawComponent)
                return std::nullopt;
            ++result.parents;
            continue;
        }
        sawComponent = true;
        result.components.push_back(component);
    }
    return result;
}

llvm::Expected<std::filesystem::path>
absoluteNormalizedPath(const std::string &value, const char *description) {
    std::error_code failure;
    std::filesystem::path result =
        std::filesystem::absolute(std::filesystem::path(value), failure);
    if (failure)
        return llvm::createStringError(failure, "could not make %s absolute",
                                       description);
    return result.lexically_normal();
}

std::filesystem::path weaklyCanonicalPath(const std::filesystem::path &path) {
    std::error_code failure;
    std::filesystem::path canonical =
        std::filesystem::weakly_canonical(path, failure);
    return failure ? path : canonical;
}

class SourceNameRenderer {
    struct Root {
        std::string name;
        std::filesystem::path path;
        std::size_t components = 0;
    };

public:
    static llvm::Expected<SourceNameRenderer>
    create(const LocationRocqEmitterOptions &options) {
        SourceNameRenderer result;
        if (options.astPath) {
            auto astPath =
                absoluteNormalizedPath(*options.astPath, "location AST path");
            if (!astPath)
                return astPath.takeError();
            result.astDirectory_ = astPath->parent_path();
        }

        for (const auto &mapping : options.sourceRoots) {
            if (mapping.name.empty())
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "location source root has an empty name");
            if (std::any_of(result.roots_.begin(), result.roots_.end(),
                            [&](const Root &root) {
                                return root.name == mapping.name;
                            }))
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "location source root '%s' is defined more than once",
                    mapping.name.c_str());
            auto path =
                absoluteNormalizedPath(mapping.path, "location source root");
            if (!path)
                return path.takeError();
            *path = weaklyCanonicalPath(*path);
            std::size_t components = 0;
            for (const auto &part : *path) {
                (void)part;
                ++components;
            }
            result.roots_.push_back(
                Root{mapping.name, std::move(*path), components});
        }
        std::stable_sort(result.roots_.begin(), result.roots_.end(),
                         [](const Root &left, const Root &right) {
                             return left.components > right.components;
                         });
        return result;
    }

    llvm::Expected<std::string> render(const source::SourceName &name) const {
        if (name.kind == source::SourceNameKind::Literal)
            return renderLiteral(name.value);
        if (!astDirectory_)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "filesystem source name requires an AST path anchor");
        auto path = absoluteNormalizedPath(name.value, "source path");
        if (!path)
            return path.takeError();
        return renderPath(*path);
    }

private:
    static std::string renderLiteral(const std::string &value) {
        return "(LiteralSourceName " + stringLiteral(value) + ")";
    }

    static std::string renderAstRelative(const EncodedRelativePath &path) {
        return "(AstRelativeSourceName (Build_relative_path " +
               std::to_string(path.parents) + " " +
               renderStringList(path.components) + "))";
    }

    static std::string renderNamedRoot(const std::string &root,
                                       const EncodedRelativePath &path) {
        return "(NamedRootSourceName " + stringLiteral(root) + " " +
               renderStringList(path.components) + ")";
    }

    llvm::Expected<std::string>
    renderPath(const std::filesystem::path &path) const {
        const std::filesystem::path canonicalPath = weaklyCanonicalPath(path);
        for (const Root &root : roots_) {
            auto relative = relativePath(root.path, canonicalPath, false);
            if (relative)
                return renderNamedRoot(root.name, *relative);
        }
        auto relative = relativePath(*astDirectory_, path, true);
        if (!relative)
            return llvm::createStringError(
                std::errc::invalid_argument,
                "source path is on a different filesystem root; configure "
                "--locations-source-root");
        return renderAstRelative(*relative);
    }

    std::optional<std::filesystem::path> astDirectory_;
    std::vector<Root> roots_;
};

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
           std::to_string(point.byteOffset) + ", " +
           std::to_string(point.line) + ", " +
           std::to_string(point.byteColumn) + ")";
}

template <typename Id> std::string renderTableId(Id id) {
    return std::to_string(id.value());
}

std::string
renderEncodedPoint(const source::encoding::EncodedPresumedPoint &point) {
    return "(Encoded.Build_encoded_presumed_point " +
           renderTableId(point.file) + " " + std::to_string(point.line) + " " +
           std::to_string(point.column) + ")";
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

llvm::Expected<std::string> renderFile(const source::File &file,
                                       const SourceNameRenderer &names) {
    std::string parent = "None";
    if (file.includeParent)
        parent = "(Some ((Build_file_id " +
                 std::to_string(file.includeParent->first.value()) + "), " +
                 std::to_string(file.includeParent->second) + "))";
    auto physicalName = names.render(file.physicalName);
    if (!physicalName)
        return physicalName.takeError();
    std::string requestedName = "None";
    if (file.requestedName) {
        auto rendered = names.render(*file.requestedName);
        if (!rendered)
            return rendered.takeError();
        requestedName = "(Some " + *rendered + ")";
    }
    return "(Build_source_file " + *physicalName + " " + requestedName + " " +
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

llvm::Expected<std::string>
renderCommonProvenance(const source::encoding::EncodedTables &tables,
                       const SourceNameRenderer &names) {
    std::vector<std::string> presumedFilenames;
    presumedFilenames.reserve(tables.presumedFilenames.size());
    for (const auto &filename : tables.presumedFilenames) {
        auto rendered = names.render(filename);
        if (!rendered)
            return rendered.takeError();
        presumedFilenames.push_back(std::move(*rendered));
    }

    std::string result;
    result += renderIndexedTable(
        "presumed_filenames", "source_name", presumedFilenames,
        "Encoded.default_presumed_filename",
        [](const std::string &value) { return value; });
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
renderProvenance(const source::encoding::EncodedTables &tables,
                 const SourceNameRenderer &names) {
    // The encoder itself establishes these IDs. This guard keeps a corrupt
    // test producer from serializing either a fabricated inline frame or an
    // invalid private table reference.
    for (const auto &origin : tables.origins)
        for (source::encoding::MacroFrameId id : origin.macroStack)
            if (!id.valid() || id.value() >= tables.macroFrames.size())
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "normalized provenance has an invalid macro frame ID");

    auto common = renderCommonProvenance(tables, names);
    if (!common)
        return common.takeError();
    std::string inlineTail = renderMacroDependentProvenance(tables, false);
    std::string referencedTail = renderMacroDependentProvenance(tables, true);
    const bool references = referencedTail.size() < inlineTail.size();
    std::string selectedTail =
        references ? std::move(referencedTail) : std::move(inlineTail);
    if (references)
        std::string().swap(inlineTail);
    else
        std::string().swap(referencedTail);

    common->reserve(common->size() + selectedTail.size() + 300);
    *common += selectedTail;
    *common += "#[local] Definition source_provenance : "
               "Encoded.indexed_provenance :=\n  "
               "Encoded.Build_indexed_provenance presumed_filenames "
               "physical_points presumed_points source_ranges macro_frames "
               "encoded_origins.\n";
    return std::move(*common);
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
    auto names = SourceNameRenderer::create(options_);
    if (!names)
        return names.takeError();
    const bool allFiles = options_.scope == LocationScope::AllFiles;
    std::optional<source::MainFileProjection> mainFileProjection;
    const source::Tables *sourceTables = &unit.sources();
    if (!allFiles) {
        auto projection = source::projectMainFile(unit.sources());
        if (!projection)
            return projection.takeError();
        mainFileProjection = std::move(*projection);
        sourceTables = &mainFileProjection->tables;
    }
    auto files = renderList(sourceTables->files, [&](const source::File &file) {
        return renderFile(file, *names);
    });
    if (!files)
        return files.takeError();
    auto provenance = [&]() -> llvm::Expected<std::string> {
        // Keep this literal all-files branch independent of the filtered
        // projection so its generated companion remains byte-for-byte stable.
        auto encoded = allFiles ? source::encoding::encode(unit.sources())
                                : source::encoding::encode(*sourceTables);
        if (!encoded)
            return encoded.takeError();
        return renderProvenance(*encoded, *names);
    }();
    if (!provenance)
        return provenance.takeError();

    std::vector<bool> includedEvents;
    llvm::Expected<location::encoding::EncodedLocations> locations =
        [&]() -> llvm::Expected<location::encoding::EncodedLocations> {
        if (allFiles)
            return location::encoding::encode(unit, options_.includeTemplates);
        auto initial = location::encoding::encode(
            unit, options_.includeTemplates,
            location::encoding::EncodeOptions{false, &*mainFileProjection,
                                              nullptr});
        if (!initial)
            return initial.takeError();
        auto filteredClasses = root_event::encoding::encode(
            unit, options_.includeTemplates,
            root_event::encoding::EncodeOptions{false,
                                                &initial->eventHasLocation});
        if (!filteredClasses)
            return filteredClasses.takeError();
        includedEvents.resize(filteredClasses->eventClasses.size());
        for (std::size_t index = 0; index < includedEvents.size(); ++index)
            includedEvents[index] = filteredClasses->eventClasses[index] !=
                                    root_event::encoding::EventClass::Excluded;
        return location::encoding::encode(
            unit, options_.includeTemplates,
            location::encoding::EncodeOptions{false, &*mainFileProjection,
                                              &includedEvents});
    }();
    if (!locations)
        return locations.takeError();
    std::string locationDag = renderLocationDag(*locations);
    auto rootEvents =
        [&]() -> llvm::Expected<root_event::encoding::EncodedRootEvents> {
        if (allFiles)
            return root_event::encoding::encode(unit,
                                                options_.includeTemplates);
        return root_event::encoding::encode(
            unit, options_.includeTemplates,
            root_event::encoding::EncodeOptions{false,
                                                &locations->eventHasLocation});
    }();
    if (!rootEvents)
        return rootEvents.takeError();
    if (rootEvents->stats.selectedEvents !=
        rootEvents->stats.singletonEvents + rootEvents->stats.residualEvents)
        return llvm::createStringError(
            std::errc::invalid_argument,
            "root-event classification did not partition selected events");

    std::array<std::string, 4> singletonLists;
    std::array<bool, 4> hasSingletons{};
    std::string residualList;
    bool hasResiduals = false;
    auto appendListEntry = [](std::string &list, bool &hasEntries,
                              std::string entry) {
        if (!hasEntries) {
            list = "(";
            hasEntries = true;
        }
        list += std::move(entry);
        list += " :: ";
    };
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
        if (ordered.index >= rootEvents->eventClasses.size())
            return llvm::createStringError(
                std::errc::invalid_argument,
                "root-event classification omitted a selected root event");
        const root_event::encoding::EventClass eventClass =
            rootEvents->eventClasses[ordered.index];
        if (eventClass == root_event::encoding::EventClass::Excluded) {
            if (allFiles)
                return llvm::createStringError(
                    std::errc::invalid_argument,
                    "root-event classification excluded a selected root event");
            continue;
        }
        const bool residual =
            eventClass == root_event::encoding::EventClass::Residual;
        std::size_t namespaceIndex = 0;
        const char *residualConstructor = nullptr;
        switch (root.kind) {
        case RootKind::Symbol:
            namespaceIndex = 0;
            residualConstructor = "CRS";
            break;
        case RootKind::Type:
            namespaceIndex = 1;
            residualConstructor = "CRT";
            break;
        case RootKind::TemplateSymbol:
            namespaceIndex = 2;
            residualConstructor = "CRMS";
            break;
        case RootKind::TemplateType:
            namespaceIndex = 3;
            residualConstructor = "CRMT";
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
        std::string entry;
        if (residual) {
            auto value =
                semantic_.renderNodeUnchecked(unit, root.semanticValue);
            if (!value)
                return value.takeError();
            const std::string constructor =
                allFiles ? residualConstructor
                         : (std::string("F") + residualConstructor);
            entry = "(" + constructor + "(" + *name + ", " + *value + ", " +
                    renderTableId(encodedRoot.node) + ", " +
                    renderTableId(encodedRoot.shape);
            if (!allFiles) {
                if (ordered.index >= locations->eventAtRoot.size() ||
                    ordered.index >= locations->eventHasLocation.size())
                    return llvm::createStringError(
                        std::errc::invalid_argument,
                        "location DAG omitted filtered event presence");
                entry += locations->eventAtRoot[ordered.index] ? ", true"
                                                               : ", false";
                entry += locations->eventHasLocation[ordered.index]
                             ? ", true))"
                             : ", false))";
            } else {
                entry += "))";
            }
            appendListEntry(residualList, hasResiduals, std::move(entry));
        } else {
            entry = "(CIL(" + *name + ", " + renderTableId(encodedRoot.node) +
                    ", " + renderTableId(encodedRoot.shape) + "))";
            appendListEntry(singletonLists[namespaceIndex],
                            hasSingletons[namespaceIndex], std::move(entry));
        }
    }
    for (std::size_t index = 0; index < singletonLists.size(); ++index)
        singletonLists[index] += hasSingletons[index] ? "nil)" : "nil";
    residualList += hasResiduals ? "nil)" : "nil";
    std::string eventSection =
        "(* compact root events: " +
        std::to_string(rootEvents->stats.selectedEvents) + " selected; " +
        std::to_string(rootEvents->stats.singletonEvents) + " singleton; " +
        std::to_string(rootEvents->stats.residualEvents) + " residual; " +
        std::to_string(rootEvents->stats.duplicateGroups) +
        " duplicate groups. *)\n"
        "#[local] Definition singleton_symbol_events : "
        "list (name * indexed_location) := " +
        singletonLists[0] +
        ".\n#[local] Definition singleton_type_events : "
        "list (name * indexed_location) := " +
        singletonLists[1] +
        ".\n#[local] Definition singleton_msymbol_events : "
        "list (name * indexed_location) := " +
        singletonLists[2] +
        ".\n#[local] Definition singleton_mtype_events : "
        "list (name * indexed_location) := " +
        singletonLists[3] +
        ".\n#[local] Definition singleton_root_events : "
        "singleton_root_locations :=\n  Build_singleton_root_locations "
        "singleton_symbol_events singleton_type_events "
        "singleton_msymbol_events singleton_mtype_events.\n"
        "#[local] Definition residual_root_events : list " +
        std::string(allFiles
                        ? "Construction.indexed_located_root_event"
                        : "Construction.filtered_indexed_located_root_event") +
        " := " + residualList;
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
        "#[local] Notation \"'CIL' '(' n ',' node ',' shape ')'\" :=\n"
        "  (n, StaticLocation node shape) (only parsing).\n"
        "#[local] Notation \"'CRS' '(' n ',' value ',' node ',' shape ')'\" "
        ":=\n"
        "  (Construction.ILESymbol n value node shape) "
        "(only parsing).\n"
        "#[local] Notation \"'CRT' '(' n ',' value ',' node ',' shape ')'\" "
        ":=\n"
        "  (Construction.ILEType n value node shape) "
        "(only parsing).\n"
        "#[local] Notation \"'CRMS' '(' n ',' value ',' node ',' shape ')'\" "
        ":=\n"
        "  (Construction.ILEMsymbol n value node shape) "
        "(only parsing).\n"
        "#[local] Notation \"'CRMT' '(' n ',' value ',' node ',' shape ')'\" "
        ":=\n"
        "  (Construction.ILEMtype n value node shape) "
        "(only parsing).\n\n"
        "#[local] Open Scope uint63_scope.\n\n";
    const std::string filteredMiddle =
        allFiles ? ""
                 : "#[local] Notation \"'FCRS' '(' n ',' value ',' node ',' "
                   "shape ',' at_root ',' in_tree ')'\" :=\n"
                   "  (Construction.FILESymbol n value node shape at_root "
                   "in_tree) (only parsing).\n"
                   "#[local] Notation \"'FCRT' '(' n ',' value ',' node ',' "
                   "shape ',' at_root ',' in_tree ')'\" :=\n"
                   "  (Construction.FILEType n value node shape at_root "
                   "in_tree) (only parsing).\n"
                   "#[local] Notation \"'FCRMS' '(' n ',' value ',' node ',' "
                   "shape ',' at_root ',' in_tree ')'\" :=\n"
                   "  (Construction.FILEMsymbol n value node shape at_root "
                   "in_tree) (only parsing).\n"
                   "#[local] Notation \"'FCRMT' '(' n ',' value ',' node ',' "
                   "shape ',' at_root ',' in_tree ')'\" :=\n"
                   "  (Construction.FILEMtype n value node shape at_root "
                   "in_tree) (only parsing).\n\n";
    const char *suffix =
        allFiles
            ? ".\n\n#[local] Close Scope uint63_scope.\n\n"
              "Definition source_locations : source_map.\n"
              "Proof.\n"
              "  "
              "Construction.build_lazy_compact_indexed_dag_source_map_or_fail "
              "source_files source_provenance source_location_dag "
              "singleton_root_events residual_root_events.\n"
              "Defined.\n"
            : ".\n\n#[local] Close Scope uint63_scope.\n\n"
              "Definition source_locations : source_map.\n"
              "Proof.\n"
              "  "
              "Construction.build_filtered_lazy_compact_indexed_dag_source_map_"
              "or_fail "
              "source_files source_provenance source_location_dag "
              "singleton_root_events residual_root_events.\n"
              "Defined.\n";
    std::string output;
    output.reserve(std::char_traits<char>::length(prefix) + files->size() +
                   std::char_traits<char>::length(sourceFilesEnd) +
                   provenance->size() + locationDag.size() +
                   std::char_traits<char>::length(middle) +
                   filteredMiddle.size() + eventSection.size() +
                   std::char_traits<char>::length(suffix));
    output += prefix;
    output += *files;
    output += sourceFilesEnd;
    output += *provenance;
    output += locationDag;
    output += middle;
    output += filteredMiddle;
    output += eventSection;
    output += suffix;
    return output;
}

} // namespace ir
