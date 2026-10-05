#!/usr/bin/env python3
"""Find sections containing exactly one section/namespace and whitespace.

Accepts Lean paths, directories, or dotted module names (including GEN shell
variable lists). With no arguments, scans Definitions, Theorems and Solutions.
Only standalone structural command lines are recognised. This conservative
textual detector does not run Lean or modify files. Comments outside the inner
block count as content, so they prevent a report, just like open/variable/p2m
commands. Both blocks must have explicit matching ends.
Sections with public, private or noncomputable modifiers wrapping a namespace
are excluded, since those modifiers cannot be transferred to the namespace.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
import re
import sys

from find_empty_lean_blocks import lean_files, resolve_inputs, strip_comments_and_strings


NAME = r"[^\W\d][\w'.]*"
STRUCTURAL = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?P<modifiers>(?:(?:public|private|protected|noncomputable|unsafe)\s+)*)"
    rf"(?P<kind>section|namespace|end)(?:\s+(?P<name>{NAME}))?\s*$"
)


@dataclass
class Block:
    kind: str
    name: str | None
    start_line: int
    start: int
    body_start: int
    modifiers: frozenset[str] = frozenset()
    children: list[Block] = field(default_factory=list)
    end_line: int | None = None
    body_end: int | None = None
    end: int | None = None


def wrappers(text: str) -> list[tuple[Block, Block]]:
    """Match blocks, then test the original text around their sole child."""
    clean = strip_comments_and_strings(text)
    # A dotted namespace has several Lean scopes but only one source block.
    stack: list[tuple[str | None, Block]] = []
    blocks: list[Block] = []
    offset = 0
    for line_no, (raw_line, clean_line) in enumerate(
        zip(text.splitlines(keepends=True), clean.splitlines(keepends=True)), 1
    ):
        match = STRUCTURAL.fullmatch(clean_line)
        line_end = offset + len(raw_line)
        if match:
            kind, name = match.group("kind", "name")
            if kind != "end":
                if kind == "namespace" and name is None:
                    offset = line_end
                    continue
                block = Block(
                    kind, name, line_no, offset, line_end,
                    modifiers=frozenset(match.group("modifiers").split()),
                )
                if stack:
                    stack[-1][1].children.append(block)
                blocks.append(block)
                components = name.split(".") if kind == "namespace" else [name]
                stack.extend((component, block) for component in components)
            elif stack:
                if name is None:
                    block = stack[-1][1]
                    count = 1
                    while count < len(stack) and stack[-count - 1][1] is block:
                        count += 1
                else:
                    parts = name.split(".")
                    count = len(parts)
                    if count > len(stack) or [x[0] for x in stack[-count:]] != parts:
                        # Do not guess how a mismatched end closes blocks.
                        stack.clear()
                        offset = line_end
                        continue
                closed = stack[-count:]
                del stack[-count:]
                for _, block in reversed(closed):
                    if block.end is None and not any(b is block for _, b in stack):
                        block.body_end = offset
                        block.end = line_end
                        block.end_line = line_no
        offset = line_end

    findings = []
    for outer in blocks:
        if outer.kind != "section" or outer.end is None or len(outer.children) != 1:
            continue
        inner = outer.children[0]
        if inner.kind == "namespace" and outer.modifiers & {
            "noncomputable", "public", "private"
        }:
            continue
        if inner.end is None:
            continue
        before = text[outer.body_start:inner.start]
        after = text[inner.end:outer.body_end]
        if not before.strip() and not after.strip():
            # A comment on the inner command line is not whitespace either.
            opening = text[inner.start:inner.body_start]
            closing = text[inner.body_end:inner.end]
            if opening != strip_comments_and_strings(opening):
                continue
            if closing != strip_comments_and_strings(closing):
                continue
            findings.append((outer, inner))
    return findings


def describe(block: Block) -> str:
    name = f" {block.name}" if block.name else " (anonymous)"
    return f"{block.kind}{name} (lines {block.start_line}–{block.end_line})"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="Lean files, directories or module names")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    try:
        paths = resolve_inputs(args.paths, root) if args.paths else [
            root / name for name in ("Definitions", "Theorems", "Solutions")
        ]
        count = 0
        for path in sorted(lean_files(paths)):
            display = path.relative_to(root) if path.is_relative_to(root) else path
            for outer, inner in wrappers(path.read_text(encoding="utf-8")):
                print(f"{display}: wrapper {describe(outer)} contains only {describe(inner)}")
                count += 1
        print(f"Found {count} wrapper section(s).")
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
