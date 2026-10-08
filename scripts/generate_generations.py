#!/usr/bin/env python3
"""Regenerate GENERATIONS.md from the textual Lean import graph.

Definitions are individual dependency nodes.  A theorem and its matching
solution are treated as one dependency node, using the union of their imports.
Generation 1 contains nodes importing only external baseline modules
(``Mathlib``, ``Lean``, and the separately vendored ``TauCeti`` library).
A node is in generation n + 1 when n is the
largest generation among its local dependencies.  Both files in a
theorem/solution pair therefore always receive the same generation.

No Lean process is run.  By default the script atomically rewrites the
repository's ``GENERATIONS.md``.  Pass ``--check`` to report whether that file
is current without changing it, or ``--output -`` to print to stdout.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path


SOURCE_DIRECTORIES = ("Definitions", "Theorems", "Solutions")
PROJECTS = ("FLT", "MTT", "KN")
EXTERNAL_ROOTS = {"Mathlib", "Lean", "TauCeti"}
IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?import\s+"
    r"(?P<module>[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\b",
    re.MULTILINE,
)


class GenerationError(Exception):
    """An import graph cannot be classified safely."""


def strip_comments_and_strings(text: str, source: Path) -> str:
    """Replace Lean comments and strings with spaces, preserving newlines."""

    output: list[str] = []
    index = 0
    comment_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        pair = text[index:index + 2]
        if comment_depth:
            if pair == "/-":
                output.extend("  ")
                comment_depth += 1
                index += 2
            elif pair == "-/":
                output.extend("  ")
                comment_depth -= 1
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif pair == "/-":
            output.extend("  ")
            comment_depth = 1
            index += 2
        elif pair == "--":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        elif char == '"':
            output.append(" ")
            in_string = True
            index += 1
        else:
            output.append(char)
            index += 1

    if comment_depth:
        raise GenerationError(f"{source}: unterminated block comment")
    if in_string:
        raise GenerationError(f"{source}: unterminated string literal")
    return "".join(output)


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def discover_files(root: Path) -> list[Path]:
    files = {
        path.resolve()
        for directory in SOURCE_DIRECTORIES
        for path in (root / directory).rglob("*.lean")
        if path.is_file()
    }
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def imported_modules(path: Path) -> list[str]:
    clean = strip_comments_and_strings(path.read_text(encoding="utf-8"), path)
    return [match.group("module") for match in IMPORT_RE.finditer(clean)]


def dependency_nodes(
    files: list[Path], root: Path
) -> tuple[dict[str, str], dict[str, tuple[str, ...]]]:
    """Collapse each matching theorem/solution pair to one node."""

    modules = {module_name(path, root) for path in files}
    module_to_node: dict[str, str] = {}
    node_members: dict[str, list[str]] = defaultdict(list)

    for module in sorted(modules):
        parts = module.split(".")
        node = module
        if len(parts) == 3 and parts[0] in {"Theorems", "Solutions"}:
            directory, project, leaf = parts
            prefix = "Thm_" if directory == "Theorems" else "Sol_"
            if leaf.startswith(prefix):
                theorem = f"Theorems.{project}.Thm_{leaf[len(prefix):]}"
                solution = f"Solutions.{project}.Sol_{leaf[len(prefix):]}"
                if theorem in modules and solution in modules:
                    node = theorem
        module_to_node[module] = node
        node_members[node].append(module)

    return module_to_node, {
        node: tuple(members) for node, members in node_members.items()
    }


def import_graph(
    files: list[Path], root: Path
) -> tuple[
    dict[str, set[str]],
    dict[str, Path],
    dict[str, str],
    dict[str, tuple[str, ...]],
]:
    module_paths = {module_name(path, root): path for path in files}
    module_to_node, node_members = dependency_nodes(files, root)
    graph: dict[str, set[str]] = {node: set() for node in node_members}
    unresolved: list[tuple[Path, str]] = []

    for module, path in module_paths.items():
        node = module_to_node[module]
        for imported in imported_modules(path):
            if imported in module_paths:
                dependency = module_to_node[imported]
                if dependency != node:
                    graph[node].add(dependency)
            elif imported.split(".", 1)[0] not in EXTERNAL_ROOTS:
                unresolved.append((path, imported))

    if unresolved:
        details = "\n".join(
            f"  {path.relative_to(root)}: {imported}"
            for path, imported in unresolved
        )
        raise GenerationError(f"unresolved non-baseline imports:\n{details}")
    return graph, module_paths, module_to_node, node_members


def classify(graph: dict[str, set[str]]) -> dict[str, int]:
    generations: dict[str, int] = {}
    visiting: set[str] = set()
    stack: list[str] = []

    def generation(module: str) -> int:
        if module in generations:
            return generations[module]
        if module in visiting:
            start = stack.index(module)
            cycle = stack[start:] + [module]
            raise GenerationError("import cycle: " + " -> ".join(cycle))

        visiting.add(module)
        stack.append(module)
        dependencies = graph[module]
        value = 1 + max((generation(dep) for dep in dependencies), default=0)
        stack.pop()
        visiting.remove(module)
        generations[module] = value
        return value

    for module in sorted(graph):
        generation(module)
    return generations


def render(
    files: list[Path],
    root: Path,
    generations: dict[str, int],
    module_to_node: dict[str, str],
    node_members: dict[str, tuple[str, ...]],
) -> str:
    by_generation: dict[int, list[Path]] = defaultdict(list)
    for path in files:
        node = module_to_node[module_name(path, root)]
        by_generation[generations[node]].append(path)

    pair_count = sum(len(members) == 2 for members in node_members.values())

    lines = [
        "# File generations",
        "",
        "This is a fast, textual classification of every Lean file under "
        "`Definitions`, `Theorems`, and `Solutions` in this extracted tree, "
        "covering the FLT, MTT, and KN subprojects. No Lean command was run.",
        "",
        "Definitions are individual dependency nodes. Each matching "
        "`Thm_...`/`Sol_...` pair is one node, whose dependencies are the "
        "union of the imports in the two files; both files are consequently "
        "listed in the same generation. Already-merged or otherwise unmatched "
        "theorem and solution files remain individual nodes.",
        "",
        "Generation 1 means that a node has no imports from this extracted "
        "local filetree: its imports are only external baseline modules "
        "(`Mathlib...`, Lean’s core `Lean` module, or the separately vendored "
        "`TauCeti...` library), or it has no imports. "
        "For generation *n* > 1, all local dependency nodes have generation "
        "at most *n − 1*, and at least one has generation *n − 1*. "
        "Equivalently, the generation is one plus the maximum generation of "
        "the node’s local dependencies.",
        "",
        "The parser reads textual `import` and `public import` commands, "
        "resolves module names from file paths, and ignores comments after "
        "an import. This intentionally does not reproduce Lean’s elaboration "
        "or transitive module-loading behavior.",
        "",
        f"Classified files: **{len(files)} / {len(files)}** in "
        f"**{len(node_members)}** dependency nodes, including "
        f"**{pair_count}** theorem/solution pairs. "
        "Cycles found: **0**. Files with unresolved non-baseline imports: **0**.",
        "",
        "## Summary",
        "",
        "| Generation | Total files | FLT | MTT | KN |",
        "|---:|---:|---:|---:|---:|",
    ]

    for number in sorted(by_generation):
        paths = by_generation[number]
        project_counts = Counter(
            path.relative_to(root).parts[1]
            for path in paths
            if len(path.relative_to(root).parts) > 1
        )
        lines.append(
            f"| {number} | {len(paths)} | "
            + " | ".join(str(project_counts[project]) for project in PROJECTS)
            + " |"
        )

    for number in sorted(by_generation):
        lines.extend(["", f"## Generation {number}", ""])
        for path in by_generation[number]:
            lines.append(f"- `{path.relative_to(root).as_posix()}`")
    return "\n".join(lines) + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=path.name + ".", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as handle:
            handle.write(content)
        if path.exists():
            os.chmod(temporary, path.stat().st_mode)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (default: parent of this script's directory)",
    )
    parser.add_argument(
        "--output",
        default="GENERATIONS.md",
        help="output path relative to root, or - for stdout",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="exit 1 if the output file is missing or out of date",
    )
    args = parser.parse_args()
    root = args.root.resolve()

    try:
        files = discover_files(root)
        if not files:
            raise GenerationError("no Lean files found")
        graph, _, module_to_node, node_members = import_graph(files, root)
        generations = classify(graph)
        content = render(
            files, root, generations, module_to_node, node_members
        )
    except (GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if args.output == "-":
        if args.check:
            parser.error("--check cannot be combined with --output -")
        sys.stdout.write(content)
        return 0

    output = Path(args.output)
    if not output.is_absolute():
        output = root / output
    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != content:
            print(f"out of date: {output}", file=sys.stderr)
            return 1
        print(f"up to date: {output}")
        return 0

    atomic_write(output, content)
    print(f"wrote {output} ({len(files)} files, {max(generations.values())} generations)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
