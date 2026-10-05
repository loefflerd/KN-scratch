#!/usr/bin/env python3
"""Merge anonymous sections wrapping exactly one anonymous section.

Only pairs reported by find_useless_wrapper_sections are considered: the
outer section contains exactly its inner block and whitespace. Both openings
must be anonymous `section` commands; both ends must be plain standalone
`end` commands. Supported Lean section tags (@[expose], public,
noncomputable, meta) are combined, deduplicated and put in Lean's order on
the retained section. Tags may occupy preceding lines. Unsupported tags,
comments on tag lines, named sections and namespaces are left unchanged.

Accepts paths, directories, and dotted module names, including GEN shell
variable lists. With no paths, scans Definitions, Theorems and Solutions.
Dry run by default; --in-place removes the outer opening/closing lines and
updates the retained header when needed. All other bytes are preserved.
This is a conservative textual transformation, not a Lean parser or build.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

from find_useless_wrapper_sections import Block, describe, wrappers
from find_empty_lean_blocks import lean_files, resolve_inputs, strip_comments_and_strings


def preceding_annotation(text: str, start: int) -> bool:
    """Do not strip a section attached to attributes/modifiers on earlier lines."""
    clean = strip_comments_and_strings(text[:start])
    previous = next((line.strip() for line in reversed(clean.splitlines()) if line.strip()), '')
    # A trailing ] may be a multiline attribute. Excluding other such lines
    # too is preferable to deleting a wrapper whose annotation is uncertain.
    return previous.endswith(']') or bool(re.fullmatch(
        r'(?:(?:public|private|protected|noncomputable|unsafe)\s*)+', previous
    ))


TAGS = ('public', 'noncomputable', 'meta')
ANONYMOUS_HEADER = re.compile(
    r'(?m)^[ \t]*(?:@\[\s*expose\s*\]\s+)?'
    r'(?:(?:public|noncomputable|meta)\s+)*section[ \t]*(?:\r?\n|$)'
)


def header_tags(text: str, block: Block) -> frozenset[str] | None:
    if block.kind != 'section' or block.name is not None:
        return None
    if block.body_end is None or block.end is None:
        return None
    raw = text[block.start:block.body_start]
    if strip_comments_and_strings(raw) != raw:
        return None
    expose = bool(re.search(r'@\[\s*expose\s*\]', raw))
    tokens = re.sub(r'@\[\s*expose\s*\]', '', raw).split()
    if not tokens or tokens[-1] != 'section' or any(t not in TAGS for t in tokens[:-1]):
        return None
    if not re.fullmatch(r'\s*end\s*', text[block.body_end:block.end]):
        return None
    if preceding_annotation(text, block.start):
        return None
    return frozenset(tokens[:-1] + (['expose'] if expose else []))


def detector_view(text: str) -> str:
    """Flatten multiline headers for the existing detector, retaining offsets."""
    def flatten(match: re.Match[str]) -> str:
        raw = match[0]
        ending = '\r\n' if raw.endswith('\r\n') else '\n' if raw.endswith('\n') else ''
        header = raw[:-len(ending)] if ending else raw
        header = header.replace('\r', ' ').replace('\n', ' ')
        # The shared detector predates meta sections; hide just that token
        # from its view. The original header remains available for merging.
        header = re.sub(r'\bmeta\b', '    ', header)
        return header + ending
    # Operate on lexically cleaned text so words inside comments/strings
    # cannot be mistaken for structural commands.
    clean = strip_comments_and_strings(text)
    return ANONYMOUS_HEADER.sub(flatten, clean)


def rewrite(text: str) -> tuple[str, list[tuple[Block, Block]]]:
    findings = [(outer, inner) for outer, inner in wrappers(detector_view(text))
                if header_tags(text, outer) is not None and header_tags(text, inner) is not None
                # The cleaned detector view must not hide comments outside
                # the inner block (these count as real wrapper content).
                and not text[outer.body_start:inner.start].strip()
                and not text[inner.end:outer.body_end].strip()]
    tags = {}
    replacements = {}
    for outer, inner in sorted(findings, key=lambda pair: pair[0].start):
        outer.start_line = text.count('\n', 0, outer.start) + 1
        outer.end_line = text.count('\n', 0, outer.body_end) + 1
        inner.start_line = text.count('\n', 0, inner.start) + 1
        inner.end_line = text.count('\n', 0, inner.body_end) + 1
        combined = tags.get(outer.start, header_tags(text, outer)) | header_tags(text, inner)
        tags[inner.start] = combined
        replacements[(outer.start, outer.body_start)] = ''
        replacements[(outer.body_end, outer.end)] = ''
        raw = text[inner.start:inner.body_start]
        if combined != header_tags(text, inner):
            indent = re.match(r'[ \t]*', raw)[0]
            newline = '\r\n' if raw.endswith('\r\n') else '\n' if raw.endswith('\n') else ''
            words = (['@[expose]'] if 'expose' in combined else [])
            words += [tag for tag in TAGS if tag in combined] + ['section']
            replacements[(inner.start, inner.body_start)] = indent + ' '.join(words) + newline
    result: list[str] = []
    position = 0
    for (begin, end), replacement in sorted(replacements.items()):
        assert begin is not None and end is not None and begin >= position
        result.append(text[position:begin])
        result.append(replacement)
        position = end
    result.append(text[position:])
    return ''.join(result), findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', help='Lean files, directories or module names')
    parser.add_argument('--in-place', action='store_true', help='apply the tag removals')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        inputs = resolve_inputs(args.paths, root) if args.paths else [
            root / name for name in ('Definitions', 'Theorems', 'Solutions')
        ]
        plans = []
        for path in sorted(lean_files(inputs)):
            original = path.read_bytes().decode('utf-8')
            replacement, findings = rewrite(original)
            if findings:
                plans.append((path, original, replacement, findings))
        count = sum(len(plan[3]) for plan in plans)
        if args.in_place:
            # Validate the entire batch before making any edits.
            for path, original, _, _ in plans:
                if path.read_bytes().decode('utf-8') != original:
                    raise ValueError(f'source changed while planning: {path}')
            for path, _, replacement, _ in plans:
                path.write_bytes(replacement.encode('utf-8'))
        for path, _, _, findings in plans:
            display = path.relative_to(root) if path.is_relative_to(root) else path
            for outer, inner in findings:
                action = 'Removed' if args.in_place else 'Would remove'
                print(f'{display}: {action} {describe(outer)}; retaining {describe(inner)}')
        action = 'Removed' if args.in_place else 'Found'
        print(f'{action} {count} wrapper(s) in {len(plans)} file(s).'
              + ('' if args.in_place else ' Dry run; use --in-place to apply.'))
    except (OSError, ValueError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
