#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "sexpdata==1.0.2",
# ]
# ///

#
# Copyright (C) 2026 SkyLabs AI, Inc.
# All rights reserved.
import argparse
from dataclasses import dataclass
import difflib
import heapq
import os
from pathlib import Path
import subprocess
import sys

import sexpdata


PRUNE_DIRS = {".git", "_build", "_opam"}
EXIT_SUCCESS = 0
EXIT_CHANGES_NEEDED = 1
EXIT_ERROR = 2


class SyncError(Exception):
    pass


@dataclass(frozen=True)
class Span:
    start: int
    end: int


@dataclass(frozen=True)
class TheoryStanza:
    file_path: Path
    name: str
    direct_deps: tuple[str, ...]
    theory_span: Span
    theories_span: Span | None


def parse_arguments():
    parser = argparse.ArgumentParser(
        description=(
            "Rewrite rocq.theory theories stanzas to include recursive local "
            "dependencies in topological order."
        )
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Print unified diffs instead of rewriting files in place.",
    )
    parser.add_argument(
        "--no-normalize",
        action="store_true",
        help=(
            "Only append newly discovered dependencies. Existing dependency "
            "order is preserved, and files are unchanged when no new "
            "dependencies are needed."
        ),
    )
    return parser.parse_args()


def atom_to_text(value):
    if isinstance(value, sexpdata.Symbol):
        return value.value()
    if isinstance(value, str):
        return value
    raise SyncError(f"Unsupported dune atom: {value!r}")


def is_named_list(form, name):
    return (
        isinstance(form, list)
        and len(form) >= 1
        and isinstance(form[0], sexpdata.Symbol)
        and form[0].value() == name
    )


def find_field(form, name):
    for item in form[1:]:
        if is_named_list(item, name):
            return item[1:]
    return None


def find_top_level_field(items, name):
    for item in items:
        if is_named_list(item, name):
            return item[1:]
    return None


def skip_comment(text, index):
    while index < len(text) and text[index] != "\n":
        index += 1
    return index


def skip_string(text, index):
    index += 1
    while index < len(text):
        if text[index] == "\\":
            index += 2
            continue
        if text[index] == '"':
            return index + 1
        index += 1
    raise SyncError("Unterminated string literal")


def iter_list_spans(text, *, offset=0):
    # sexpdata parses the S-expressions themselves, but it does not preserve
    # source locations. We still need this lightweight scanner so we can find
    # exact list spans and rewrite only the `(theories ...)` subform without
    # reserializing the rest of the dune file.
    depth = 0
    start = None
    index = 0

    while index < len(text):
        char = text[index]
        if char == ";":
            index = skip_comment(text, index)
            continue
        if char == '"':
            index = skip_string(text, index)
            continue
        if char == "(":
            if depth == 0:
                start = index
            depth += 1
            index += 1
            continue
        if char == ")":
            if depth == 0:
                raise SyncError("Unexpected closing parenthesis")
            depth -= 1
            index += 1
            if depth == 0:
                yield Span(offset + start, offset + index)
                start = None
            continue
        index += 1

    if depth != 0:
        raise SyncError("Unterminated list expression")


def parse_list(text, *, context):
    try:
        return sexpdata.loads(text)
    except Exception as exc:  # pragma: no cover - sexpdata exception types vary
        raise SyncError(f"{context}: {exc}") from exc


def find_child_list_span(form_text, name):
    body_text = form_text[1:-1]
    for child_span in iter_list_spans(body_text, offset=1):
        child_text = form_text[child_span.start:child_span.end]
        child_form = parse_list(child_text, context=f"invalid child form for {name}")
        if is_named_list(child_form, name):
            return child_span
    return None


def parse_theory_stanzas(file_path):
    text = file_path.read_text(encoding="utf-8")
    stanzas = []

    for span in iter_list_spans(text):
        form_text = text[span.start:span.end]
        form = parse_list(form_text, context=f"invalid form in {file_path}")
        if not is_named_list(form, "rocq.theory"):
            continue

        name_field = find_field(form, "name")
        if name_field is None or len(name_field) != 1:
            raise SyncError(f"{file_path}: rocq.theory stanza is missing a single (name ...) field")
        name = atom_to_text(name_field[0])

        theories_field = find_field(form, "theories")
        direct_deps = ()
        if theories_field is not None:
            direct_deps = tuple(atom_to_text(value) for value in theories_field)

        stanzas.append(
            TheoryStanza(
                file_path=file_path,
                name=name,
                direct_deps=direct_deps,
                theory_span=span,
                theories_span=find_child_list_span(form_text, "theories"),
            )
        )

    return text, stanzas


def discover_workspace_root():
    command = [
        "dune",
        "describe",
        "workspace",
        "--format=sexp",
        "--lang=0.1",
        "--no-print-directory",
    ]
    proc = subprocess.run(
        command,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise SyncError(
            "Failed to discover Dune workspace root:\n"
            f"command: {' '.join(command)}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )

    workspace = parse_list(proc.stdout, context="invalid output from dune describe workspace")
    root_field = find_top_level_field(workspace, "root")
    if root_field is None or len(root_field) != 1:
        raise SyncError("Could not find a single workspace root in dune describe output")
    return Path(atom_to_text(root_field[0])).resolve()


def find_dune_files(root):
    dune_files = []
    for current_root, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(name for name in dirnames if name not in PRUNE_DIRS)
        if "dune" in filenames:
            dune_files.append((Path(current_root) / "dune").resolve())
    return sorted(dune_files)


def display_path(path, cwd):
    try:
        return str(path.relative_to(cwd))
    except ValueError:
        return str(path)


def dedupe_sorted(values):
    return sorted(set(values))


def resolve_theory(name, theory_index):
    stanzas = theory_index.get(name, ())
    if not stanzas:
        raise SyncError(f"Unresolved theory dependency {name!r}")
    if len(stanzas) != 1:
        locations = "\n- ".join(str(stanza.file_path) for stanza in stanzas)
        raise SyncError(f"Ambiguous theory dependency {name!r} defined in:\n- {locations}")
    return stanzas[0]


def compute_recursive_closure(root_deps, theory_index):
    closure = set()
    visit_state = {}
    stack = []

    def visit(name):
        try:
            stanza = resolve_theory(name, theory_index)
        except SyncError as exc:
            path = " -> ".join(stack + [name])
            raise SyncError(f"{exc} while resolving {path}") from exc

        state = visit_state.get(name)
        if state == "done":
            return
        if state == "visiting":
            cycle_start = stack.index(name)
            cycle = stack[cycle_start:] + [name]
            raise SyncError(f"Dependency cycle detected: {' -> '.join(cycle)}")

        visit_state[name] = "visiting"
        stack.append(name)
        for dep in dedupe_sorted(stanza.direct_deps):
            visit(dep)
        stack.pop()
        visit_state[name] = "done"
        closure.add(name)

    for dep in dedupe_sorted(root_deps):
        visit(dep)

    return closure


def topological_order(theory_names, theory_index):
    adjacency = {name: set() for name in theory_names}
    indegree = {name: 0 for name in theory_names}
    resolved = {name: resolve_theory(name, theory_index) for name in theory_names}

    for name in theory_names:
        stanza = resolved[name]
        for dep in dedupe_sorted(stanza.direct_deps):
            if dep not in theory_names:
                continue
            if name not in adjacency[dep]:
                adjacency[dep].add(name)
                indegree[name] += 1

    ready = [name for name, count in indegree.items() if count == 0]
    heapq.heapify(ready)

    ordered = []
    while ready:
        name = heapq.heappop(ready)
        ordered.append(name)
        for dependent in sorted(adjacency[name]):
            indegree[dependent] -= 1
            if indegree[dependent] == 0:
                heapq.heappush(ready, dependent)

    if len(ordered) != len(theory_names):
        raise SyncError("Dependency cycle detected during topological ordering")

    return ordered


def compute_ordered_dependencies(stanza, theory_index):
    closure = compute_recursive_closure(stanza.direct_deps, theory_index)
    return topological_order(closure, theory_index)


def compute_updated_dependencies(stanza, theory_index, *, no_normalize):
    ordered_dependencies = compute_ordered_dependencies(stanza, theory_index)
    if not no_normalize:
        return ordered_dependencies, True

    existing_dependencies = list(stanza.direct_deps)
    existing_set = set(existing_dependencies)
    missing_dependencies = [dep for dep in ordered_dependencies if dep not in existing_set]
    if not missing_dependencies:
        return existing_dependencies, False
    return existing_dependencies + missing_dependencies, True


def line_indent(text, index):
    line_start = text.rfind("\n", 0, index)
    if line_start == -1:
        return text[:index]
    return text[line_start + 1:index]


def format_theories_block(indent, dependencies):
    if not dependencies:
        return "(theories)"

    lines = ["(theories"]
    lines.extend(f"{indent} {dependency}" for dependency in dependencies)
    lines.append(f"{indent})")
    return "\n".join(lines)


def apply_replacements(text, replacements):
    updated = text
    for span, replacement in sorted(replacements, key=lambda item: item[0].start, reverse=True):
        updated = updated[:span.start] + replacement + updated[span.end:]
    return updated


def build_workspace_data(workspace_root):
    theory_index = {}
    file_texts = {}
    file_stanzas = {}
    errors = []

    for dune_file in find_dune_files(workspace_root):
        try:
            text, stanzas = parse_theory_stanzas(dune_file)
        except SyncError as exc:
            errors.append(str(exc))
            continue

        file_texts[dune_file] = text
        file_stanzas[dune_file] = stanzas

        for stanza in stanzas:
            theory_index.setdefault(stanza.name, []).append(stanza)

    return theory_index, file_texts, file_stanzas, errors


def analyze_targets(*, cwd, theory_index, file_texts, file_stanzas, no_normalize):
    changes = {}
    errors = []

    target_files = sorted(
        path for path in file_stanzas if file_stanzas[path] and path.is_relative_to(cwd)
    )

    for dune_file in target_files:
        original_text = file_texts[dune_file]
        replacements = []

        for stanza in file_stanzas[dune_file]:
            try:
                dependencies, should_rewrite = compute_updated_dependencies(
                    stanza,
                    theory_index,
                    no_normalize=no_normalize,
                )
            except SyncError as exc:
                errors.append(f"{display_path(dune_file, cwd)} [{stanza.name}]: {exc}")
                continue

            if not should_rewrite:
                continue

            if stanza.theories_span is None:
                if dependencies:
                    errors.append(
                        f"{display_path(dune_file, cwd)} [{stanza.name}]: "
                        "computed non-empty dependencies but found no (theories ...) field"
                    )
                continue

            absolute_span = Span(
                stanza.theory_span.start + stanza.theories_span.start,
                stanza.theory_span.start + stanza.theories_span.end,
            )
            indent = line_indent(original_text, absolute_span.start)
            replacement = format_theories_block(indent, dependencies)
            replacements.append((absolute_span, replacement))

        if replacements:
            updated_text = apply_replacements(original_text, replacements)
            if updated_text != original_text:
                changes[dune_file] = updated_text

    return changes, errors


def emit_diffs(changes, original_texts, cwd):
    for dune_file in sorted(changes):
        display = display_path(dune_file, cwd)
        diff = difflib.unified_diff(
            original_texts[dune_file].splitlines(keepends=True),
            changes[dune_file].splitlines(keepends=True),
            fromfile=display,
            tofile=display,
        )
        sys.stdout.writelines(diff)


def write_changes(changes):
    for dune_file, updated_text in changes.items():
        dune_file.write_text(updated_text, encoding="utf-8")


def main():
    args = parse_arguments()
    cwd = Path.cwd().resolve()

    try:
        workspace_root = discover_workspace_root()
        theory_index, file_texts, file_stanzas, errors = build_workspace_data(workspace_root)
        changes, analysis_errors = analyze_targets(
            cwd=cwd,
            theory_index=theory_index,
            file_texts=file_texts,
            file_stanzas=file_stanzas,
            no_normalize=args.no_normalize,
        )
        errors.extend(analysis_errors)
    except SyncError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_ERROR

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return EXIT_ERROR

    if args.check:
        emit_diffs(changes, file_texts, cwd)
        if changes:
            return EXIT_CHANGES_NEEDED
        return EXIT_SUCCESS

    try:
        write_changes(changes)
    except OSError as exc:
        print(f"error: failed to write updated dune files: {exc}", file=sys.stderr)
        return EXIT_ERROR

    return EXIT_SUCCESS


if __name__ == "__main__":
    sys.exit(main())
