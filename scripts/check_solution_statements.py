#!/usr/bin/env python3
"""Check that local solution statements match their theorem statements.

For each ``Solutions/**/Sol_X.lean``, the expected statement is read from the
corresponding ``Theorems/**/Thm_X.lean``.  The checker compares the token stream
between the declaration name and the declaration's proof assignment, so it is
insensitive to comments and whitespace but deliberately does not try to model
the effects of imports, notation, local instances, or preceding declarations.

This is a consistency check for accidental editing mistakes, not a substitute
for elaborating both declarations with Lean.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path


DECLARATION_RE = re.compile(r"\btheorem\s+([^\s({:]+)")
AMBIENT_VARIABLE_RE = re.compile(r"(?m)^\s*variable\s+(.+)$")

# These qualifications occur in accepted files on one side of the comparison
# while the other side opens or enters the corresponding namespace.  Removing
# them is intentionally a surface-level heuristic; see the module docstring.
IGNORED_QUALIFIERS = {
    "Affine",
    "AlgebraicCurve",
    "Cohomology",
    "CongruenceSubgroup",
    "HorizontalPadicL",
    "MTT",
    "ModularCurve",
    "MvPowerSeries",
    "Point",
    "UpperHalfPlane",
    "WeierstrassCurve",
}


@dataclass(frozen=True)
class Declaration:
    name: str
    name_end: int
    assignments: tuple[int, ...]


def without_comments(source: str) -> str:
    """Replace Lean comments by whitespace while preserving source offsets."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ""

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                result.append(char)
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                result.extend((" ", " "))
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if char == "-" and next_char == "-":
            in_line_comment = True
            result.extend((" ", " "))
            index += 2
        elif char == "/" and next_char == "-":
            block_depth = 1
            result.extend((" ", " "))
            index += 2
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string literal")
    return "".join(result)


def top_level_assignments(
    source: str, start: int, end: int | None = None
) -> tuple[int, ...]:
    """Return offsets of ``:=`` outside (), [], and {} after ``start``."""
    assignments: list[int] = []
    round_depth = square_depth = curly_depth = 0
    index = start
    in_string = False
    escaped = False

    stop = len(source) if end is None else end
    while index < stop - 1:
        char = source[index]
        next_char = source[index + 1]

        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue

        if char == "(":
            round_depth += 1
        elif char == ")":
            round_depth -= 1
        elif char == "[":
            square_depth += 1
        elif char == "]":
            square_depth -= 1
        elif char == "{":
            curly_depth += 1
        elif char == "}":
            curly_depth -= 1
        elif (
            char == ":"
            and next_char == "="
            and round_depth == square_depth == curly_depth == 0
        ):
            assignments.append(index)
        index += 1

    return tuple(assignments)


def declarations(source: str, *, comments_removed: bool = False) -> list[Declaration]:
    clean = source if comments_removed else without_comments(source)
    matches = list(DECLARATION_RE.finditer(clean))
    result: list[Declaration] = []
    for position, match in enumerate(matches):
        end = matches[position + 1].start() if position + 1 < len(matches) else len(clean)
        assignments = top_level_assignments(clean, match.end(), end)
        result.append(Declaration(match.group(1), match.end(), assignments))
    return result


def is_identifier_char(char: str) -> bool:
    category = unicodedata.category(char)
    return char == "_" or char == "'" or category[0] in {"L", "M", "N"}


def statement_tokens(
    source: str, start: int, end: int, *, comments_removed: bool = False
) -> tuple[str, ...]:
    """Tokenize a declaration signature, ignoring comments and whitespace."""
    clean = source if comments_removed else without_comments(source)
    text = clean[start:end]
    tokens: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char.isspace():
            index += 1
            continue
        if char == '"':
            finish = index + 1
            escaped = False
            while finish < len(text):
                current = text[finish]
                if escaped:
                    escaped = False
                elif current == "\\":
                    escaped = True
                elif current == '"':
                    finish += 1
                    break
                finish += 1
            tokens.append(text[index:finish])
            index = finish
            continue
        if is_identifier_char(char):
            finish = index + 1
            while finish < len(text) and is_identifier_char(text[finish]):
                finish += 1
            tokens.append(text[index:finish])
            index = finish
            continue
        tokens.append(char)
        index += 1
    return tuple(tokens)


def canonical_tokens(tokens: tuple[str, ...]) -> tuple[str, ...]:
    """Normalize harmless spelling differences seen in accepted submissions."""
    result: list[str] = []
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if (
            token in IGNORED_QUALIFIERS
            and index + 1 < len(tokens)
            and tokens[index + 1] == "."
        ):
            index += 2
            continue
        if token == "ℍ":
            token = "UpperHalfPlane"
        elif token.startswith("_") and len(token) > 1:
            token = token.lstrip("_")
        if token == "Type" and index + 1 < len(tokens):
            result.append(token)
            universe = tokens[index + 1]
            if universe.startswith("u") and universe.isidentifier():
                result.append("<universe>")
                index += 2
                continue
        result.append(token)
        index += 1

    # A named typeclass binder `[inst : C]` and an anonymous binder `[C]`
    # express the same statement when the binder name is not otherwise used.
    normalized: list[str] = []
    index = 0
    while index < len(result):
        if (
            result[index] == "["
            and index + 2 < len(result)
            and result[index + 1].isidentifier()
            and result[index + 2] == ":"
        ):
            normalized.append("[")
            index += 3
            continue
        normalized.append(result[index])
        index += 1

    # Mathlib accepts both `MvPowerSeries.order x` and projection notation
    # `x.order`; both forms occur in otherwise identical accepted statements.
    projection_normalized: list[str] = []
    index = 0
    while index < len(normalized):
        if (
            normalized[index] == "order"
            and index + 1 < len(normalized)
            and normalized[index + 1] == "("
        ):
            depth = 1
            finish = index + 2
            while finish < len(normalized) and depth:
                if normalized[finish] == "(":
                    depth += 1
                elif normalized[finish] == ")":
                    depth -= 1
                finish += 1
            if depth == 0:
                projection_normalized.extend(("(",))
                projection_normalized.extend(normalized[index + 2 : finish - 1])
                projection_normalized.extend((")", ".", "order"))
                index = finish
                continue
        projection_normalized.append(normalized[index])
        index += 1
    return tuple(projection_normalized)


def theorem_statement(source: str, path: Path) -> tuple[str, ...]:
    clean = without_comments(source)
    decls = declarations(clean, comments_removed=True)
    if len(decls) != 1:
        raise ValueError(f"expected one theorem declaration, found {len(decls)}")
    declaration = decls[0]
    candidates = [
        offset
        for offset in declaration.assignments
        if re.match(r":=\s*by\s+sorry\b", clean[offset:])
    ]
    if len(candidates) != 1:
        raise ValueError(
            f"expected one top-level `:= by sorry`, found {len(candidates)}"
        )
    ambient: list[str] = []
    for match in AMBIENT_VARIABLE_RE.finditer(clean[: declaration.name_end]):
        ambient.extend(
            statement_tokens(
                match.group(1), 0, len(match.group(1)), comments_removed=True
            )
        )
    declared = statement_tokens(
        clean, declaration.name_end, candidates[0], comments_removed=True
    )
    return canonical_tokens(tuple(ambient) + declared)


def solution_statement_candidates(
    source: str, expected: tuple[str, ...]
) -> list[tuple[str, ...]]:
    clean = without_comments(source)
    decls = [
        declaration
        for declaration in declarations(clean, comments_removed=True)
        if declaration.name.removeprefix("_root_.").split(".")[-1] == "solution"
    ]
    if not decls:
        raise ValueError("no theorem declaration whose name ends in `solution`")
    declaration = decls[-1]
    if not declaration.assignments:
        raise ValueError("final `theorem solution` has no top-level proof assignment")
    candidates: list[tuple[str, ...]] = []
    # The proof assignment is normally the first top-level `:=`.  A theorem
    # target can itself contain top-level `let` assignments, so retain a small
    # amount of headroom without scanning every assignment in a long proof.
    for offset in declaration.assignments[:32]:
        candidate = canonical_tokens(
            statement_tokens(
                clean, declaration.name_end, offset, comments_removed=True
            )
        )
        candidates.append(candidate)
        if candidate == expected:
            break
    return candidates


def compact_diff(expected: tuple[str, ...], actual: tuple[str, ...]) -> str:
    matcher = difflib.SequenceMatcher(None, expected, actual, autojunk=False)
    opcode = next((item for item in matcher.get_opcodes() if item[0] != "equal"), None)
    if opcode is None:
        return ""
    _, expected_start, expected_end, actual_start, actual_end = opcode
    context = 18
    expected_slice = expected[
        max(0, expected_start - context) : min(len(expected), expected_end + context)
    ]
    actual_slice = actual[
        max(0, actual_start - context) : min(len(actual), actual_end + context)
    ]
    return (
        "  theorem: " + " ".join(expected_slice) + "\n"
        "  solution: " + " ".join(actual_slice)
    )


def corresponding_theorem(root: Path, solution: Path) -> Path:
    relative = solution.relative_to(root / "Solutions")
    if not relative.name.startswith("Sol_"):
        raise ValueError("solution filename does not begin with `Sol_`")
    theorem_name = "Thm_" + relative.name.removeprefix("Sol_")
    return root / "Theorems" / relative.parent / theorem_name


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="workspace root (defaults to the parent of this script's directory)",
    )
    parser.add_argument(
        "--allow-missing-theorem",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "allow a solution with no theorem file; PATH is relative to the workspace "
            "root and may be repeated"
        ),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    allowed_missing = {Path(path).as_posix() for path in args.allow_missing_theorem}

    solution_dir = root / "Solutions"
    solutions = sorted(solution_dir.rglob("*.lean"))
    errors: list[str] = []
    checked = skipped = 0

    for solution in solutions:
        relative = solution.relative_to(root).as_posix()
        try:
            theorem = corresponding_theorem(root, solution)
        except ValueError as error:
            errors.append(f"{relative}: {error}")
            continue

        if not theorem.is_file():
            if relative in allowed_missing:
                print(f"SKIP  {relative}: no corresponding theorem file (allowed)")
                skipped += 1
            else:
                errors.append(
                    f"{relative}: missing corresponding theorem "
                    f"{theorem.relative_to(root).as_posix()}"
                )
            continue

        try:
            expected = theorem_statement(theorem.read_text(), theorem)
            candidates = solution_statement_candidates(solution.read_text(), expected)
        except ValueError as error:
            errors.append(f"{relative}: {error}")
            continue

        if expected not in candidates:
            closest = max(
                candidates,
                key=lambda candidate: difflib.SequenceMatcher(
                    None, expected, candidate, autojunk=False
                ).ratio(),
            )
            errors.append(
                f"{relative}: final solution statement does not match "
                f"{theorem.relative_to(root).as_posix()}\n"
                f"{compact_diff(expected, closest)}"
            )
            continue
        checked += 1

    for error in errors:
        print(f"ERROR {error}", file=sys.stderr)
    print(
        f"checked {checked} solution statement(s); "
        f"skipped {skipped}; errors {len(errors)}"
    )
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
