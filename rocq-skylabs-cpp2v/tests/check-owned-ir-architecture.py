#!/usr/bin/env python3
"""Static owned-IR semantic and location emission-boundary checks."""

from pathlib import Path
import os
import re
import sys

if source_root := os.environ.get("DUNE_SOURCEROOT"):
    PACKAGE = Path(source_root) / "fmdeps/BRiCk/rocq-skylabs-cpp2v"
else:
    PACKAGE = Path(__file__).resolve().parent.parent


def fail(message: str) -> None:
    print(f"owned IR architecture error: {message}", file=sys.stderr)
    raise SystemExit(1)


def text(relative: str) -> str:
    return (PACKAGE / relative).read_text()


builders = sorted((PACKAGE / "src").glob("Build*.cpp")) + [
    PACKAGE / "src/IRBuilder.cpp",
    PACKAGE / "src/IRBuilderInternal.hpp",
    PACKAGE / "include/IRBuilder.hpp",
]
for path in builders:
    contents = path.read_text()
    forbidden = re.search(
        r"CoqPrinter|fmt::Formatter|SemanticRocqEmitter|"
        r"LocationRocqEmitter|rocqSpelling|writeIRLines|writeRocqLines|"
        r"#\s*include\s*[<\"]Location\.hpp|\bloc::",
        contents,
    )
    if forbidden:
        fail(
            f"builder {path.relative_to(PACKAGE)} reaches output API "
            f"{forbidden.group(0)!r}"
        )

# A few mparser diagnostic payloads intentionally equal constructor spellings;
# they are data passed to Nunsupported, not constructor applications. This is a
# closed allowlist, so a new raw spelling in a builder requires explicit review.
allowed_payload_spellings = {
    "src/BuildName.cpp": {"Template"},
    "src/BuildExpr.cpp": {
        "Eaddrof",
        "Ecast",
        "Econstructor",
        "Einitlist",
        "Einitlist_union",
        "Elambda",
        "Eunresolved_binop",
        "Eunresolved_initlist",
        "Eunresolved_unop",
    },
}
registry = text("include/IRConstructors.def")
spellings = set(
    re.findall(r'IR_CONSTRUCTOR\([^,]+,\s*"([^"]+)"', registry)
)
for path in builders:
    relative = path.relative_to(PACKAGE).as_posix()
    found = {spelling for spelling in spellings if f'"{spelling}"' in path.read_text()}
    allowed = allowed_payload_spellings.get(relative, set())
    if found != allowed:
        fail(
            f"builder constructor-spelling allowlist mismatch in {relative}: "
            f"found={sorted(found)!r}, allowed={sorted(allowed)!r}"
        )

macro_files = {
    path.relative_to(PACKAGE).as_posix()
    for base in (PACKAGE / "include", PACKAGE / "src")
    for path in base.rglob("*")
    if path.is_file() and "IR_CONSTRUCTOR" in path.read_text(errors="ignore")
}
if macro_files != {"include/IR.hpp", "include/IRConstructors.def", "src/IR.cpp"}:
    fail(f"IR_CONSTRUCTOR escaped its registry boundary: {sorted(macro_files)!r}")

spelling_users = {
    path.relative_to(PACKAGE).as_posix()
    for base in (PACKAGE / "include", PACKAGE / "src")
    for path in base.rglob("*")
    if path.is_file() and "rocqSpelling" in path.read_text(errors="ignore")
}
allowed_spelling_users = {
    "include/IR.hpp",
    "src/RocqEmitter.cpp",
    "src/Sharing.cpp",
}
if spelling_users != allowed_spelling_users:
    fail(f"Rocq constructor spelling escaped emitter/registry: {sorted(spelling_users)!r}")

pure_files = [
    "include/IR.hpp",
    "include/IRFactories.hpp",
    "include/RocqEmitter.hpp",
    "include/LocationEmitter.hpp",
    "include/LocationDAGEncoding.hpp",
    "include/RootEventEncoding.hpp",
    "include/Sharing.hpp",
    "include/SourceInfoEncoding.hpp",
    "src/IR.cpp",
    "src/IRFactories.cpp",
    "src/RocqEmitter.cpp",
    "src/LocationEmitter.cpp",
    "src/LocationDAGEncoding.cpp",
    "src/RootEventEncoding.cpp",
    "src/Sharing.cpp",
    "src/SourceInfoEncoding.cpp",
]
for relative in pure_files:
    if re.search(r"#\s*include\s*[<\"]clang/|\bclang::", text(relative)):
        fail(f"pure IR/emitter file {relative} depends on Clang")

source_header = text("include/SourceInfo.hpp")
source_implementation = text("src/SourceInfo.cpp")
if "originIndex_" not in source_header:
    fail("source-origin interning must retain its hash index")
if re.search(r"std::find\s*\(\s*tables_\.origins", source_implementation):
    fail("source-origin interning regressed to a quadratic table scan")
if "tables_.origins[candidate.value()] == origin" not in source_implementation:
    fail("source-origin hash collisions are not equality-checked")

source_encoding = text("src/SourceInfoEncoding.cpp")
interner_match = re.search(
    r"template\s*<[^>]+>\s*class\s+Interner\s*\{(?P<body>.*?)\n\};",
    source_encoding,
    re.DOTALL,
)
if not interner_match:
    fail("normalized provenance encoder has no indexed interner")
interner_body = interner_match.group("body")
if not re.search(
    r"for\s*\(\s*Id\s+candidate\s*:\s*found->second\s*\).*?"
    r"values_\s*\[\s*candidate\.value\(\)\s*\]\s*==\s*value",
    interner_body,
    re.DOTALL,
):
    fail("normalized provenance collision buckets do not equality-check candidates")
if re.search(r"\bstd::find\s*\(", interner_body):
    fail("normalized provenance interning regressed to a table scan")
interner_domains = set(
    re.findall(r"Interner\s*<\s*(\w+)\s*,", source_encoding)
)
expected_interner_domains = {
    "FilenameId",
    "PhysicalPointId",
    "PresumedPointId",
    "RangeId",
    "MacroFrameId",
}
if interner_domains != expected_interner_domains:
    fail(
        "normalized provenance interner domains changed: "
        f"{sorted(interner_domains)!r}"
    )
if len(re.findall(r"options\.forceHashCollisions", source_encoding)) != 5:
    fail("forced-collision test seam does not cover every normalized table")

decode_origin_users = {
    path.relative_to(PACKAGE).as_posix()
    for base in (PACKAGE / "include", PACKAGE / "src")
    for path in base.rglob("*")
    if path.is_file() and "decodeOrigin(" in path.read_text(errors="ignore")
}
if decode_origin_users != {
    "include/SourceInfoEncoding.hpp",
    "src/SourceInfoEncoding.cpp",
}:
    fail(
        "test-only full provenance decoder escaped its boundary: "
        f"{sorted(decode_origin_users)!r}"
    )

for removed in ("src/PrintDecl.cpp", "src/PrePrint.cpp"):
    if (PACKAGE / removed).exists():
        fail(f"obsolete legacy semantic source remains: {removed}")
legacy_headers = text("include/ClangPrinter.hpp") + text("include/PrePrint.hpp")
for removed in ("printDecl(", "prePrintDecl(", "using PRINTER"):
    if removed in legacy_headers:
        fail(f"obsolete legacy callback remains: {removed!r}")

location_header_users = {
    path.relative_to(PACKAGE).as_posix()
    for base in (PACKAGE / "include", PACKAGE / "src")
    for path in base.rglob("*")
    if path.is_file() and "Location.hpp" in path.read_text(errors="ignore")
}
allowed_location_header_users = {
    "include/ClangPrinter.hpp",
    "src/Elaborate.cpp",
    "src/Location.cpp",
    "src/ModuleBuilder.cpp",
}
if location_header_users != allowed_location_header_users:
    fail(
        "ephemeral diagnostic Location.hpp escaped its boundary: "
        f"{sorted(location_header_users)!r}"
    )

orchestration = text("src/ToCoq.cpp")
for forbidden in (
    "printCache",
    ".printDecl(",
    ".printType(",
    ".printExpr(",
    "use_" + "ir_",
    "CPP2V_" + "USE_IR",
):
    if forbidden in orchestration:
        fail(f"production orchestration retains legacy semantic seam {forbidden!r}")
if orchestration.count("IRBuilder::buildModule(") != 1:
    fail("production orchestration must build exactly one module IR")
if "if (semanticOutput)" not in orchestration:
    fail("name-test-only requests are not isolated from full semantic IR construction")
if orchestration.count("cprint.printName(") != 1:
    fail("legacy diagnostic access must be exactly the isolated --name-test call")
if "locationEmitter.emit(*ownedUnit)" not in orchestration:
    fail("location output must consume the same finished module IR")
if "with_open_file(locations_file_" not in orchestration:
    fail("location output does not use atomic per-file publication")

location_emitter = text("src/LocationEmitter.cpp")
location_dag_encoder = text("src/LocationDAGEncoding.cpp")
root_event_encoder = text("src/RootEventEncoding.cpp")
if location_dag_encoder.count("unit.nodes().children(id)") != 1:
    fail("location DAG must have exactly one Arena::children projection source")
for required in (
    "for (const OrderedEventRef &ordered : unit.orderedEvents())",
    "forceHashCollisions",
    "values_[candidate.value()] == value",
    "child.value() >= index",
    "sourceOriginCount",
):
    if required not in location_dag_encoder:
        fail(f"exact location DAG encoder omits {required!r}")
for forbidden in ("SharingPlan", "ownedSharing", "shareClass"):
    if forbidden in location_dag_encoder:
        fail(f"location DAG encoder reaches semantic sharing API {forbidden!r}")
for required in (
    "IRSharing::semanticallyEqual",
    "forceHashCollisions",
    "for (const OrderedEventRef &ordered : unit.orderedEvents())",
    "Constructor::GlobalTypedef",
):
    if required not in root_event_encoder:
        fail(f"root-event encoder omits {required!r}")
if "clang::" in root_event_encoder:
    fail("root-event encoder depends on Clang")
source_location_syntax = (
    PACKAGE.parent
    / "rocq-skylabs-brick/theories/lang/cpp/syntax/source_location.v"
).read_text()
for required in (
    "Record file_id : Set := Build_file_id",
    "file_id_value : PrimInt63.int",
    "Record origin_id : Set := Build_origin_id",
    "origin_id_value : PrimInt63.int",
    "Definition table_id : Set := PrimInt63.int",
    "Definition table_chunk_size : table_id := 4096%uint63",
    "Definition nat_to_table_id",
    "Definition table_get_nat",
    "Record encoded_physical_point",
    "encoded_anchor_origin : option table_id",
    "encoded_derived_from : list table_id",
    "Record encoded_location_shape",
    "Record encoded_location_node",
    "Record indexed_location_dag",
    "Inductive indexed_location",
    "MergeLocations",
    "AddRootOrigins",
    "Inductive location_store",
    "Record singleton_root_locations",
    "CompactIndexedLocations",
    "MalformedLocationDag",
    "MalformedCompactLocations",
    "Fixpoint find_unique_singleton",
    "Definition find_compact_root",
    "Fixpoint descend_indexed",
    "Definition validate_location_dag",
):
    if required not in source_location_syntax:
        fail(f"indexed provenance storage omits {required!r}")
for forbidden in (
    "Definition file_id : Set := nat",
    "Definition origin_id : Set := nat",
):
    if forbidden in source_location_syntax:
        fail(f"source-location API retains unary public ID {forbidden!r}")
if source_location_syntax.count("validate_location_dag") != 1:
    fail("eager location-DAG validation escaped its diagnostic definition")
parser_location = (
    PACKAGE.parent
    / "rocq-skylabs-brick/theories/lang/cpp/parser/source_location.v"
).read_text()
for required in (
    "Inductive indexed_located_root_event",
    "Definition merge_indexed_location",
    "Fixpoint fold_indexed_events_from",
    "Definition fold_indexed_events",
    "Ltac build_indexed_dag_source_map_or_fail",
    "eval vm_compute in (fold_indexed_events events)",
    "Inductive compact_indexed_located_root_event",
    "InvalidCompactEventClassification",
    "Record compact_indexed_state",
    "compact_state_symbols : NM.t indexed_location * NM.t unit",
    "compact_state_msymbols : TM.t indexed_location * TM.t unit",
    "Fixpoint fold_compact_indexed_events_from",
    "Definition fold_compact_indexed_events",
    "Ltac build_compact_indexed_dag_source_map_or_fail",
    "eval vm_compute in (fold_compact_indexed_events events)",
    "Definition assemble_lazy_compact_indexed_dag_source_map",
    "Ltac build_lazy_compact_indexed_dag_source_map_or_fail",
    "eval vm_compute in (fold_indexed_events residual_events)",
):
    if required not in parser_location:
        fail(f"indexed location-DAG construction omits {required!r}")
if "fold_indexed_events (events" not in parser_location:
    fail("indexed event fold does not remain independent of DAG tables")
if location_emitter.count("unit.nodes().children(root)") != 1:
    fail("expanded location-tree test oracle lost its children-only projection")
if "appendTreeUnchecked(eventList" in location_emitter:
    fail("production location events still expand recursive LocNode trees")
for forbidden in ("Constructor::", "clang::", "SharingPlan", "ownedSharing"):
    if forbidden in location_emitter:
        fail(f"location emitter reaches forbidden shape/sharing API {forbidden!r}")
if "for (const OrderedEventRef &ordered : unit.orderedEvents())" not in location_emitter:
    fail("location roots do not derive from the authoritative ordered event stream")
for required in (
    "#include \"SourceInfoEncoding.hpp\"",
    "source::encoding::encode(unit.sources())",
    "#[local] Definition source_files",
    "#include \"LocationDAGEncoding.hpp\"",
    "location::encoding::encode(unit, options_.includeTemplates)",
    "#include \"RootEventEncoding.hpp\"",
    "root_event::encoding::encode(unit, options_.includeTemplates)",
    "presumed_filenames",
    "physical_points",
    "presumed_points",
    "source_ranges",
    "macro_frames",
    "encoded_origins",
    "source_provenance",
    "location_shapes",
    "location_nodes",
    "source_location_dag",
    "Encoded.Build_encoded_location_shape",
    "Encoded.Build_encoded_location_node",
    "Encoded.Build_indexed_location_dag",
    'return "EP("',
    'return "LS("',
    'return "LN("',
    "(only parsing)",
    "Require Import Stdlib.NArith.NArith",
    "Require Import Stdlib.Numbers.Cyclic.Int63.Uint63",
    "Open Scope uint63_scope",
    'Set Warnings \\"-abstract-large-number\\"',
    "Encoded.Build_indexed_table",
    "PArray.array",
    '"_chunk_"',
    "Encoded.Build_indexed_provenance",
    "Encoded.InlineMacroFrame",
    "Encoded.MacroFrameReference",
    "Build_singleton_root_locations",
    "singleton_symbol_events",
    "singleton_type_events",
    "singleton_msymbol_events",
    "singleton_mtype_events",
    "singleton_root_events",
    "residual_root_events",
    "Construction.ILESymbol",
    "Construction.ILEType",
    "Construction.ILEMsymbol",
    "Construction.ILEMtype",
    "Construction.build_lazy_compact_indexed_dag_source_map_or_fail",
    "Definition source_locations : source_map",
    "Build_source_file",
    "Encoded.Build_encoded_physical_point",
):
    if required not in location_emitter:
        fail(f"standalone location companion omits {required!r}")
for forbidden in (
    "source_origins : list source_origin",
    "Build_source_origin",
    "Construction.build_source_map_or_fail",
    "Construction.build_indexed_source_map_or_fail",
    "Construction.LESymbol",
    "Construction.CILESingleton",
    "Construction.CILEResidual",
    "Construction.build_compact_indexed_dag_source_map_or_fail",
    'constructor = "Construction.ILE',
    "PArray.of_list",
    "decodeOrigin(",
):
    if forbidden in location_emitter:
        fail(f"location emitter retains expanded/eager provenance seam {forbidden!r}")
if not re.search(
    r"if\s*\(residual\)\s*\{.*?renderNodeUnchecked"
    r"\(unit,\s*root\.semanticValue\)",
    location_emitter,
    re.DOTALL,
):
    fail("location emitter renders semantic values outside the residual guard")
if location_emitter.find("Require Import skylabs.lang.cpp.parser") < location_emitter.find(
    "#[local] Close Scope array_scope"
):
    fail("location emitter imports parser before direct primitive-array syntax")
if "kTableChunkSize = 4096" not in location_emitter:
    fail("location emitter does not use fixed 4096-row provenance chunks")

for verbose_field in (
    "source_file_physical_name :=",
    "point_file :=",
    "presumed_file :=",
    "range_begin :=",
    "macro_name :=",
    "origin_class :=",
):
    if verbose_field in location_emitter:
        fail(
            "location emitter regressed to expanded record syntax for "
            f"{verbose_field!r}"
        )

cli = text("src/cpp2v.cpp")
for required in (
    'Locations("locations"',
    "--locations requires --module/-o",
    "--locations must name a file (not '-')",
    "--module and --locations paths must differ",
    "--locations is incompatible with --for-interactive",
):
    if required not in cli:
        fail(f"--locations validation/plumbing omits {required!r}")

package_sources = "\n".join(
    path.read_text(errors="ignore")
    for base in (PACKAGE / "include", PACKAGE / "src")
    for path in base.rglob("*")
    if path.is_file()
)
for removed in (
    "--use-" + "ir",
    "CPP2V_" + "USE_IR",
    "CPP2V_" + "PHASE5_PARITY",
    "cpp2v-legacy-" + "parity-probe",
):
    if removed in package_sources:
        fail(f"removed migration hook remains in production sources: {removed}")

insertion_helpers = {
    "Dobj_value",
    "Dglob_decl",
    "Dtemplated_obj_value",
    "Dtemplated_glob_decl",
    "Dtemplated_type_alias",
    "Dtemplate_preinst",
}
for helper in insertion_helpers:
    users = {
        path.relative_to(PACKAGE).as_posix()
        for base in (PACKAGE / "include", PACKAGE / "src")
        for path in base.rglob("*")
        if path.is_file() and helper in path.read_text(errors="ignore")
    }
    if users != {"src/RocqEmitter.cpp"}:
        fail(f"direct insertion helper {helper} has unexpected users {sorted(users)!r}")

print(
    "owned IR architecture: one builder, registered constructors, "
    "Clang-free semantic/location emitters"
)
