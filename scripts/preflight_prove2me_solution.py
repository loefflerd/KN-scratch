#!/usr/bin/env python3
"""Static preflight checks for a Prove2Me solution or proof-sketch upload."""

import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("source", type=Path)
parser.add_argument("--target-module", help="Forbidden self-import, e.g. Theorems.Thm_Foo")
parser.add_argument("--payload", type=Path, help="Optional JSON upload payload")
parser.add_argument("--statement", action="store_true",
                    help="Check an open-theorem statement rather than a solution")
parser.add_argument("--expected-theorem",
                    help="Exact theorem name expected in a statement file")
parser.add_argument("--forbid-import", action="append", default=[],
                    help="Additional forbidden module import; may be repeated")
args = parser.parse_args()

text = args.source.read_text()
errors = []
imports = re.findall(r"^import\s+(\S+)", text, re.MULTILINE)

if args.target_module and args.target_module in imports:
    errors.append(f"solution imports its own target: {args.target_module}")
for forbidden in args.forbid_import:
    if forbidden in imports:
        errors.append(f"source imports forbidden module: {forbidden}")
if not args.statement and re.search(r"\b(?:by\s+)?sorry\b", text):
    errors.append("solution source contains `sorry`")
if not args.statement and not re.search(
    r"(?m)^\s*(?:theorem|def)\s+(?:_root_\.)?solution\b", text
):
    errors.append("no top-level declaration named `solution` found")

if args.statement:
    if not args.expected_theorem:
        errors.append("statement preflight requires --expected-theorem")
    elif not re.search(
        rf"(?m)^\s*theorem\s+{re.escape(args.expected_theorem)}(?:\s|$)", text
    ):
        errors.append(
            f"statement does not declare expected theorem `{args.expected_theorem}`"
        )
    if not re.search(r":=\s*by\s+sorry\s*(?:\n|$)", text):
        errors.append("open-theorem statement does not end in `:= by sorry`")

# A namespace wrapper turns `solution` into a qualified declaration. Allow an
# explicit `_root_.solution`, otherwise require no open namespace at its line.
solution_match = re.search(
    r"(?m)^\s*(?:theorem|def)\s+((?:_root_\.)?solution)\b", text
)
if not args.statement and solution_match and solution_match.group(1) == "solution":
    prefix = text[: solution_match.start()]
    depth = len(re.findall(r"(?m)^\s*namespace\s+\S+", prefix)) - len(
        re.findall(r"(?m)^\s*end(?:\s+\S+)?\s*$", prefix)
    )
    if depth > 0:
        errors.append("`solution` appears inside a namespace; use `_root_.solution`")

if args.payload:
    payload = json.loads(args.payload.read_text())
    if payload.get("proof_type") == "sketch":
        errors.append('upload payload uses rejected proof_type "sketch"')

if errors:
    for error in errors:
        print(f"ERROR: {error}")
    raise SystemExit(1)
print("preflight passed")
