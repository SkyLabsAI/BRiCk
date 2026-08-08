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
    "include/Sharing.hpp",
    "src/IR.cpp",
    "src/IRFactories.cpp",
    "src/RocqEmitter.cpp",
    "src/LocationEmitter.cpp",
    "src/Sharing.cpp",
]
for relative in pure_files:
    if re.search(r"#\s*include\s*[<\"]clang/|\bclang::", text(relative)):
        fail(f"pure IR/emitter file {relative} depends on Clang")

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
if location_emitter.count("unit.nodes().children(root)") != 1:
    fail("location-tree shape must have exactly one Arena::children recursion source")
for forbidden in ("Constructor::", "clang::", "SharingPlan", "ownedSharing"):
    if forbidden in location_emitter:
        fail(f"location emitter reaches forbidden shape/sharing API {forbidden!r}")
if "for (const OrderedEventRef &ordered : unit.orderedEvents())" not in location_emitter:
    fail("location roots do not derive from the authoritative ordered event stream")
for required in (
    "#[local] Definition source_files",
    "#[local] Definition source_origins",
    "#[local] Definition located_root_events",
    "Definition source_locations : source_map",
    "Construction.build_source_map_or_fail",
):
    if required not in location_emitter:
        fail(f"standalone location companion omits {required!r}")

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
