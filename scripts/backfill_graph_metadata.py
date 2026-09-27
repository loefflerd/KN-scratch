#!/usr/bin/env python3
"""Add metadata for locally present theorem and definition files to the graph.

The graph endpoint only contains nodes in the server-side mission graph.  A
local proof closure can contain additional imported theorem statements and
definitions, so this script scans both ``Theorems/Thm_*.lean`` and
``Definitions/Def_*.lean`` and fetches metadata for modules not already
represented in ``.server-sync/graph.json``.

Existing nodes and all graph edges are preserved.  Progress is written
atomically after every successful batch, making interrupted runs resumable.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import urllib.error
from pathlib import Path
from typing import Any

from download_mission_proofs import (
    DownloadError,
    formatting_normalized,
    module_name,
    search_theorems,
    statement_source,
)


SCRIPT = Path(__file__).resolve()
PROJECT = SCRIPT.parent.parent
DEFAULT_GRAPH = PROJECT / ".server-sync" / "graph.json"

DECL_RE = re.compile(
    r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
BLOCK_RE = re.compile(
    r"(?m)^\s*(namespace|section|end)\b"
    r"(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?"
)
RETRYABLE_HTTP_RE = re.compile(r"HTTP (?:429|5\d\d)\b")


class TransientDownloadError(DownloadError):
    """A network/server failure that remained after all retry attempts."""


def node_name_from_file(path: Path) -> str:
    """Recover the server node name represented by a local module file."""
    if path.parent.name == "Definitions" and path.name.startswith("Def_"):
        # Definition nodes are named by their module/package stem rather than
        # by one of the (often many) Lean declarations in their source.
        return path.stem.removeprefix("Def_")
    if path.parent.name != "Theorems" or not path.name.startswith("Thm_"):
        raise DownloadError(f"unsupported local module path: {path}")

    source = path.read_text()
    declarations = list(DECL_RE.finditer(source))
    if not declarations:
        raise DownloadError(f"no theorem or lemma declaration found in {path}")

    # Statement modules normally contain exactly one declaration.  Taking the
    # final match also avoids prose such as "theorem `uuid`" in doc comments.
    declaration = declarations[-1]
    short_name = declaration.group(1)

    # Track namespace/section blocks before the declaration.  Sections affect
    # which `end` closes next but do not contribute to the declaration name.
    stack: list[tuple[str, str | None]] = []
    for command in BLOCK_RE.finditer(source, 0, declaration.start()):
        kind, name = command.groups()
        if kind in {"namespace", "section"}:
            stack.append((kind, name))
            continue
        if not stack:
            continue
        if name is None:
            stack.pop()
            continue
        matching = next(
            (i for i in range(len(stack) - 1, -1, -1) if stack[i][1] == name),
            None,
        )
        if matching is None:
            stack.pop()
        else:
            del stack[matching:]

    namespaces: list[str] = []
    for kind, name in stack:
        if kind == "namespace" and name:
            namespaces.extend(name.split("."))

    qualified = ".".join([*namespaces, short_name]) if namespaces else short_name
    expected_stem = path.stem.removeprefix("Thm_")
    candidates = dict.fromkeys((short_name, qualified))
    matches = [name for name in candidates if name.replace(".", "_") == expected_stem]
    if len(matches) != 1:
        raise DownloadError(
            f"could not recover a unique theorem name from {path.relative_to(PROJECT)}; "
            f"declaration candidates: {list(candidates)}"
        )
    return matches[0]


def choose_record(name: str, path: Path) -> dict[str, Any]:
    expected_module = f"{path.parent.name}.{path.stem}"
    records = [
        record
        for record in search_theorems(theorem_name=name)
        if record.get("theorem_name") == name
        and module_name(record) == expected_module
    ]
    live_records = [record for record in records if record.get("deprecated_at") is None]
    preferred_records = live_records or records
    if len(preferred_records) == 1:
        return preferred_records[0]

    # If duplicate records exist, prefer the unique record whose complete
    # server source agrees with the local module modulo blank-line and
    # trailing-space formatting. Live records take precedence, but an exact
    # deprecated record is retained when its module still exists locally.
    local = formatting_normalized(path.read_text())
    matching_source: list[dict[str, Any]] = []
    for record in preferred_records:
        try:
            remote = formatting_normalized(statement_source(record))
        except DownloadError:
            continue
        if remote == local:
            matching_source.append(record)
    if len(matching_source) == 1:
        return matching_source[0]

    ids = [record.get("theorem_id") for record in preferred_records]
    raise DownloadError(
        f"expected one matching server record for {name!r}, "
        f"found {len(preferred_records)}: {ids}"
    )


def choose_record_with_retries(
    name: str, path: Path, *, retries: int, initial_delay: float
) -> dict[str, Any]:
    """Fetch one record, retrying DNS, connection, rate-limit, and 5xx errors."""
    for attempt in range(1, retries + 1):
        try:
            return choose_record(name, path)
        except DownloadError as error:
            if not RETRYABLE_HTTP_RE.search(str(error)):
                raise
            transient: Exception = error
        except (urllib.error.URLError, TimeoutError, ConnectionError) as error:
            transient = error
        except json.JSONDecodeError as error:
            transient = error

        if attempt == retries:
            raise TransientDownloadError(
                f"network/server failure after {retries} attempts: {transient}"
            ) from transient
        delay = min(initial_delay * (2 ** (attempt - 1)), 30.0)
        print(
            f"retry    {name}: attempt {attempt}/{retries} failed: {transient}; "
            f"waiting {delay:g}s",
            file=sys.stderr,
            flush=True,
        )
        time.sleep(delay)

    raise AssertionError("unreachable")


def write_graph(path: Path, graph: dict[str, Any]) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(graph, indent=2) + "\n")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    parser.add_argument(
        "--checkpoint-every",
        type=int,
        default=25,
        metavar="N",
        help="atomically save after every N additions (default: 25)",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="report missing nodes without fetching"
    )
    parser.add_argument(
        "--retries",
        type=int,
        default=7,
        metavar="N",
        help="attempt each transiently failing request N times (default: 7)",
    )
    parser.add_argument(
        "--retry-delay",
        type=float,
        default=1.0,
        metavar="SECONDS",
        help="initial exponential-backoff delay (default: 1)",
    )
    args = parser.parse_args()
    if args.checkpoint_every <= 0:
        parser.error("--checkpoint-every must be positive")
    if args.retries <= 0:
        parser.error("--retries must be positive")
    if args.retry_delay < 0:
        parser.error("--retry-delay must be nonnegative")

    graph = json.loads(args.graph.read_text())
    nodes = graph.get("nodes")
    if not isinstance(nodes, list):
        raise DownloadError(f"{args.graph} has no node list")

    indexed_modules = {
        module_name(node)
        for node in nodes
        if node.get("node_type") == "theorem"
    }
    local: list[tuple[str, Path]] = []
    for path in sorted((PROJECT / "Theorems").glob("Thm_*.lean")):
        local.append((node_name_from_file(path), path))
    for path in sorted((PROJECT / "Definitions").glob("Def_*.lean")):
        local.append((node_name_from_file(path), path))
    missing = [
        (name, path)
        for name, path in local
        if f"{path.parent.name}.{path.stem}" not in indexed_modules
    ]

    local_theorems = sum(path.parent.name == "Theorems" for _, path in local)
    local_definitions = len(local) - local_theorems
    missing_theorems = sum(path.parent.name == "Theorems" for _, path in missing)
    missing_definitions = len(missing) - missing_theorems

    print(
        f"found {local_theorems} local theorem files and "
        f"{local_definitions} local definition files; "
        f"{missing_theorems} theorems and {missing_definitions} definitions "
        f"are missing from {args.graph.relative_to(PROJECT)}",
        flush=True,
    )
    if args.dry_run:
        for name, path in missing:
            print(f"missing  {name} -> {path.relative_to(PROJECT)}")
        return 0

    added = 0
    failures: list[str] = []
    transient_failure: str | None = None
    for name, path in missing:
        try:
            record = choose_record_with_retries(
                name,
                path,
                retries=args.retries,
                initial_delay=args.retry_delay,
            )
        except TransientDownloadError as error:
            transient_failure = f"{name}: {error}"
            print(
                f"stopping {transient_failure}", file=sys.stderr, flush=True
            )
            break
        except (DownloadError, OSError, json.JSONDecodeError) as error:
            failures.append(f"{name}: {error}")
            print(f"error    {name}: {error}", file=sys.stderr, flush=True)
            continue
        node = {
            "node_type": "theorem",
            **record,
            "has_more_children": False,
            "has_more_parents": False,
        }
        nodes.append(node)
        indexed_modules.add(module_name(record))
        added += 1
        print(f"added    {name} ({record['theorem_id']})", flush=True)
        if added % args.checkpoint_every == 0:
            write_graph(args.graph, graph)

    if added:
        write_graph(args.graph, graph)
    print(
        f"complete: {added} metadata records added; {len(failures)} record failures"
        + ("; stopped on a persistent network/server failure" if transient_failure else ""),
        flush=True,
    )
    return 1 if failures or transient_failure else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (DownloadError, OSError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
