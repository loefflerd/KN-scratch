#!/usr/bin/env python3
"""Download the complete live proof closure of a Prove2Me mission goal.

By default the script works locally first: it starts at the local goal proof,
follows ``Definitions.*`` and ``Theorems.*`` imports on disk, and contacts the
server only when an imported statement, definition, or solution is missing.
Open frontier nodes are statements only. ``--server-graph`` enables the slower
full server comparison mode; combine it with ``--verify-existing`` to compare
every existing proof with the accepted server source.

Existing files are never silently replaced.  If an existing file differs from
the server, the run stops and explains that ``--replace`` is required.  A
successful run writes ``.server-sync/proof-download.json`` recording the exact
theorem and submission IDs selected.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


API = "https://prove2.me/api/v1"
SCRIPT = Path(__file__).resolve()
PROJECT = SCRIPT.parent.parent
CREDS = SCRIPT.parents[3] / "prove2me_workspace" / "credentials.json"
IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")


class DownloadError(RuntimeError):
    pass


def credentials() -> dict[str, Any]:
    data = json.loads(CREDS.read_text())
    if data.get("expires_at", 0) <= time.time() + 60:
        req = urllib.request.Request(
            API + "/agent/refresh",
            data=json.dumps({"api_key": data["api_key"]}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req) as response:
            refreshed = json.load(response)
        data["access_token"] = refreshed["access_token"]
        data["expires_at"] = refreshed["expires_at"]
        CREDS.write_text(json.dumps(data, indent=2) + "\n")
    return data


def request(path: str) -> dict[str, Any]:
    token = credentials()["access_token"]
    req = urllib.request.Request(
        API + path, headers={"Authorization": f"Bearer {token}"}
    )
    try:
        with urllib.request.urlopen(req) as response:
            return json.load(response)
    except urllib.error.HTTPError as error:
        body = error.read().decode(errors="replace")
        raise DownloadError(f"GET {path} failed with HTTP {error.code}: {body}") from error


def search_theorems(**params: str) -> list[dict[str, Any]]:
    """Return every page of a theorem search result."""
    page_size = 200
    offset = 0
    results: list[dict[str, Any]] = []
    while True:
        query = urllib.parse.urlencode(
            {**params, "limit": str(page_size), "offset": str(offset)}
        )
        data = request(f"/theorems?{query}")
        page = data.get("theorems", [])
        if not isinstance(page, list):
            raise DownloadError("theorem search returned a malformed response")
        results.extend(page)
        offset += len(page)
        total = data.get("total")
        if not page or (isinstance(total, int) and offset >= total):
            return results
        if total is None and len(page) < page_size:
            return results


def node_id(node: dict[str, Any]) -> str:
    return node.get("theorem_id") or node.get("node_id")


def module_stem(theorem_name: str) -> str:
    return theorem_name.replace(".", "_")


def module_name(record: dict[str, Any]) -> str:
    stem = module_stem(record["theorem_name"])
    prefix = "Definitions.Def_" if record["status"] == "Definition" else "Theorems.Thm_"
    return prefix + stem


def source_path(record: dict[str, Any]) -> Path:
    stem = module_stem(record["theorem_name"])
    if record["status"] == "Definition":
        return PROJECT / "Definitions" / f"Def_{stem}.lean"
    return PROJECT / "Theorems" / f"Thm_{stem}.lean"


def statement_source(record: dict[str, Any]) -> str:
    if record["status"] == "Definition":
        content = record.get("definition")
        if not isinstance(content, str) or not content.strip():
            raise DownloadError(f"definition source missing for {record['theorem_name']}")
        return content.rstrip() + "\n"
    preamble = record.get("preamble") or ""
    statement = record.get("formal_statement")
    if not isinstance(statement, str) or not statement.strip():
        raise DownloadError(f"formal statement missing for {record['theorem_name']}")
    if preamble.strip():
        return preamble.rstrip() + "\n\n" + statement.rstrip() + "\n"
    return statement.rstrip() + "\n"


def imports(source: str) -> list[str]:
    return IMPORT_RE.findall(source)


def sha256(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


def formatting_normalized(source: str) -> str:
    """Ignore trailing space and blank lines, but no non-whitespace Lean text."""
    return "\n".join(line.rstrip() for line in source.splitlines() if line.strip())


@dataclass
class Counters:
    statements_written: int = 0
    statements_present: int = 0
    solutions_written: int = 0
    solutions_present: int = 0


class Downloader:
    def __init__(
        self, goal_id: str, *, replace: bool, dry_run: bool, verify_existing: bool
    ) -> None:
        self.goal_id = goal_id
        self.replace = replace
        self.dry_run = dry_run
        self.verify_existing = verify_existing
        self.graph = request(f"/theorems/{goal_id}/graph")
        self.records: dict[str, dict[str, Any]] = {
            n["theorem_id"]: n
            for n in self.graph.get("nodes", [])
            if n.get("node_type") == "theorem"
        }
        self.by_module: dict[str, dict[str, Any]] = {
            module_name(n): n for n in self.records.values()
        }
        self.frontier = self.fetch_frontier()
        self.visited: set[str] = set()
        self.selected: dict[str, dict[str, Any]] = {}
        self.counters = Counters()

    def fetch_frontier(self) -> set[str]:
        data = request(f"/theorems/{self.goal_id}/open-leaves?limit=200&offset=0")
        if data.get("total", 0) > len(data.get("open_leaves", [])):
            raise DownloadError("frontier has more than 200 nodes; pagination is required")
        return {leaf["theorem_id"] for leaf in data.get("open_leaves", [])}

    def check_expected_frontier(self) -> None:
        manifest_path = PROJECT / ".server-sync" / "manifest.json"
        if not manifest_path.exists():
            return
        manifest = json.loads(manifest_path.read_text())
        expected = {x["theorem_id"] for x in manifest.get("frontier", [])}
        if expected and expected != self.frontier:
            raise DownloadError(
                "server frontier differs from .server-sync/manifest.json:\n"
                f"  expected only: {sorted(expected - self.frontier)}\n"
                f"  server only:   {sorted(self.frontier - expected)}\n"
                "Refresh the local server mirror and review the changed frontier first."
            )

    def get_record(self, theorem_id: str) -> dict[str, Any]:
        if theorem_id not in self.records:
            record = request(f"/theorems/{theorem_id}")
            self.records[theorem_id] = record
            self.by_module[module_name(record)] = record
        return self.records[theorem_id]

    def resolve_module(self, module: str) -> dict[str, Any]:
        if module in self.by_module:
            return self.by_module[module]
        leaf = module.rsplit(".", 1)[-1]
        for prefix in ("Def_", "Thm_"):
            if leaf.startswith(prefix):
                leaf = leaf[len(prefix):]
                break
        exact_matches = [
            record
            for record in search_theorems(theorem_name=leaf)
            if record.get("deprecated_at") is None and module_name(record) == module
        ]
        if len(exact_matches) == 1:
            record = exact_matches[0]
            self.records[record["theorem_id"]] = record
            self.by_module[module] = record
            return record
        # The server searches Lean names containing dots, while platform module
        # filenames replace those dots by underscores.  Try the whole module
        # stem first, then progressively shorter underscore-delimited suffixes.
        # The final canonical-module equality check prevents a fuzzy match from
        # resolving to the wrong declaration.
        queries = [leaf]
        queries += [leaf[i + 1 :] for i, char in enumerate(leaf) if char == "_"]
        matches_by_id: dict[str, dict[str, Any]] = {}
        for candidate in queries:
            for record in search_theorems(q=candidate):
                if record.get("deprecated_at") is None and module_name(record) == module:
                    matches_by_id[record["theorem_id"]] = record
            if matches_by_id:
                break
        matches = list(matches_by_id.values())
        if len(matches) != 1:
            names = [x.get("theorem_name") for x in matches]
            raise DownloadError(
                f"could not resolve import {module!r} uniquely; matches: {names}"
            )
        record = matches[0]
        self.records[record["theorem_id"]] = record
        self.by_module[module] = record
        return record

    def write_exact(
        self,
        path: Path,
        source: str,
        label: str,
        node_name: str,
        *,
        allow_formatting_difference: bool = False,
    ) -> bool:
        """Write source if missing; return True when a file was created/replaced."""
        if path.exists():
            old = path.read_text()
            if old == source:
                print(
                    f"present    {label}: {node_name} -> {path.relative_to(PROJECT)}",
                    flush=True,
                )
                return False
            if allow_formatting_difference and formatting_normalized(old) == formatting_normalized(source):
                print(
                    f"present    {label}: {node_name} -> {path.relative_to(PROJECT)} "
                    "(blank-line formatting differs)",
                    flush=True,
                )
                return False
            if self.dry_run:
                print(
                    f"would replace {label}: {node_name} -> {path.relative_to(PROJECT)}",
                    flush=True,
                )
                return True
            if not self.replace:
                raise DownloadError(
                    f"{path.relative_to(PROJECT)} differs from accepted server source; "
                    "rerun with --replace after reviewing the local changes"
                )
        action = "would write" if self.dry_run else "downloaded"
        print(
            f"{action:<10} {label}: {node_name} -> {path.relative_to(PROJECT)}",
            flush=True,
        )
        if not self.dry_run:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        return True

    def choose_submission(self, theorem_id: str) -> dict[str, Any]:
        data = request(
            f"/theorems/{theorem_id}/submissions"
            "?status=ACCEPTED,SKETCH_ACCEPTED&limit=200&offset=0"
        )
        submissions = [
            s for s in data.get("submissions", []) if s.get("deprecated_at") is None
        ]
        if not submissions:
            raise DownloadError(f"no nondeprecated accepted submission for {theorem_id}")

        # A completed reduction changes from SKETCH_ACCEPTED to ACCEPTED.  In
        # either case the newest live accepted submission is the current route;
        # this also selects clean rewiring submissions over superseded ones.
        submissions.sort(
            key=lambda s: (s.get("updated_at") or s.get("created_at") or "", s["id"]),
            reverse=True,
        )
        return submissions[0]

    def solution_path(self, record: dict[str, Any], submission: dict[str, Any]) -> Path:
        return PROJECT / "Solutions" / f"Sol_{module_stem(record['theorem_name'])}.lean"

    def existing_solution_path(self, record: dict[str, Any]) -> Path | None:
        stem = module_stem(record["theorem_name"])
        path = PROJECT / "Solutions" / f"Sol_{stem}.lean"
        return path if path.exists() else None

    def follow_imports(self, source: str) -> None:
        for module in imports(source):
            if not (module.startswith("Definitions.Def_") or module.startswith("Theorems.Thm_")):
                continue
            record = self.resolve_module(module)
            self.process(record["theorem_id"])

    def process(self, theorem_id: str) -> None:
        if theorem_id in self.visited:
            return
        self.visited.add(theorem_id)
        record = self.get_record(theorem_id)
        if record.get("deprecated_at") is not None:
            raise DownloadError(
                f"live proof closure reached deprecated node {record['theorem_name']}"
            )

        statement = statement_source(record)
        wrote = self.write_exact(
            source_path(record),
            statement,
            record["status"].lower(),
            record["theorem_name"],
            allow_formatting_difference=True,
        )
        if wrote:
            self.counters.statements_written += 1
        else:
            self.counters.statements_present += 1
        self.follow_imports(statement)

        if record["status"] == "Definition":
            return
        if theorem_id in self.frontier:
            print(f"frontier   {record['theorem_name']} (statement only)", flush=True)
            return

        existing = self.existing_solution_path(record)
        if existing is not None and not self.verify_existing:
            source = existing.read_text()
            print(
                f"present    local solution: {record['theorem_name']} -> "
                f"{existing.relative_to(PROJECT)} "
                "(use --verify-existing to compare with the accepted server source)",
                flush=True,
            )
            self.counters.solutions_present += 1
            self.selected[theorem_id] = {
                "theorem_name": record["theorem_name"],
                "theorem_status": record["status"],
                "submission_id": None,
                "submission_status": "LOCAL_EXISTING",
                "solution_path": str(existing.relative_to(PROJECT)),
                "sha256": sha256(source),
            }
            self.follow_imports(source)
            return

        submission = self.choose_submission(theorem_id)
        payload = request(f"/submissions/{submission['id']}/solution")
        source = payload.get("content")
        if not isinstance(source, str) or not source.strip():
            raise DownloadError(f"empty solution source for submission {submission['id']}")
        if not source.endswith("\n"):
            source += "\n"
        path = self.solution_path(record, submission)

        wrote = self.write_exact(
            path,
            source,
            f"{submission['status'].lower()} solution",
            record["theorem_name"],
        )
        if wrote:
            self.counters.solutions_written += 1
        else:
            self.counters.solutions_present += 1
        self.selected[theorem_id] = {
            "theorem_name": record["theorem_name"],
            "theorem_status": record["status"],
            "submission_id": submission["id"],
            "submission_status": submission["status"],
            "solution_path": str(path.relative_to(PROJECT)),
            "sha256": sha256(source),
        }
        self.follow_imports(source)

    def write_manifest(self) -> None:
        result = {
            "downloaded_at": datetime.now(timezone.utc).isoformat(),
            "goal_id": self.goal_id,
            "frontier_ids": sorted(self.frontier),
            "visited_theorem_count": len(self.visited),
            "proof_count": len(self.selected),
            "proofs": dict(sorted(self.selected.items())),
        }
        path = PROJECT / ".server-sync" / "proof-download.json"
        if self.dry_run:
            print(f"would write manifest: {path.relative_to(PROJECT)}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(result, indent=2) + "\n")

    def run(self) -> None:
        self.check_expected_frontier()
        self.process(self.goal_id)
        # Definitions are reusable environment nodes and need not all lie on
        # the currently selected proof route. Keep every definition advertised
        # by the mission graph locally, even when no traversed proof imports it.
        for record in list(self.records.values()):
            if record.get("status") == "Definition":
                self.process(record["theorem_id"])
        self.write_manifest()
        c = self.counters
        print(
            "complete: "
            f"{len(self.visited)} theorem/definition nodes visited; "
            f"{len(self.selected)} local proof files found or selected; "
            f"{c.statements_written} statements and {c.solutions_written} solutions written; "
            f"{c.statements_present} statements and {c.solutions_present} solutions already present; "
            f"{len(self.frontier)} open frontier nodes intentionally left without proofs"
        )


class LocalFirstDownloader:
    """Traverse local imports and ask the server only for missing artifacts."""

    def __init__(self, goal_id: str, *, dry_run: bool) -> None:
        self.goal_id = goal_id
        self.dry_run = dry_run
        graph_path = PROJECT / ".server-sync" / "graph.json"
        if not graph_path.exists():
            raise DownloadError("local-first mode requires .server-sync/graph.json")
        graph = json.loads(graph_path.read_text())
        self.records: dict[str, dict[str, Any]] = {
            n["theorem_id"]: n
            for n in graph.get("nodes", [])
            if n.get("node_type") == "theorem"
        }
        self.by_module: dict[str, dict[str, Any]] = {
            module_name(n): n for n in self.records.values()
        }
        frontier_path = PROJECT / ".server-sync" / "frontier.json"
        if not frontier_path.exists():
            raise DownloadError("local-first mode requires .server-sync/frontier.json")
        frontier = json.loads(frontier_path.read_text()).get("open_leaves", [])
        self.frontier_modules = {
            "Theorems.Thm_" + module_stem(leaf["theorem_name"]) for leaf in frontier
        }
        self.frontier_ids = {leaf["theorem_id"] for leaf in frontier}
        self.visited_modules: set[str] = set()
        self.local_solutions = 0
        self.downloaded_statements = 0
        self.downloaded_solutions = 0
        self.downloads: dict[str, dict[str, Any]] = {}

    @staticmethod
    def path_for_module(module: str) -> Path:
        return PROJECT.joinpath(*module.split(".")).with_suffix(".lean")

    @staticmethod
    def solution_candidates(module: str) -> tuple[Path]:
        stem = module.removeprefix("Theorems.Thm_")
        return (PROJECT / "Solutions" / f"Sol_{stem}.lean",)

    def resolve_remote_module(self, module: str) -> dict[str, Any]:
        if module in self.by_module:
            return self.by_module[module]
        leaf = module.rsplit(".", 1)[-1]
        for prefix in ("Def_", "Thm_"):
            if leaf.startswith(prefix):
                leaf = leaf[len(prefix):]
                break

        candidates: dict[str, dict[str, Any]] = {}
        for record in search_theorems(theorem_name=leaf):
            if record.get("deprecated_at") is None and module_name(record) == module:
                candidates[record["theorem_id"]] = record
        if not candidates:
            queries = [leaf]
            queries += [leaf[i + 1 :] for i, char in enumerate(leaf) if char == "_"]
            for candidate in queries:
                for record in search_theorems(q=candidate):
                    if record.get("deprecated_at") is None and module_name(record) == module:
                        candidates[record["theorem_id"]] = record
                if candidates:
                    break
        if len(candidates) != 1:
            raise DownloadError(
                f"could not resolve missing local import {module!r} uniquely; "
                f"matches: {[x.get('theorem_name') for x in candidates.values()]}"
            )
        record = next(iter(candidates.values()))
        self.records[record["theorem_id"]] = record
        self.by_module[module] = record
        return record

    @staticmethod
    def choose_submission(theorem_id: str) -> dict[str, Any]:
        data = request(
            f"/theorems/{theorem_id}/submissions"
            "?status=ACCEPTED,SKETCH_ACCEPTED&limit=200&offset=0"
        )
        submissions = [
            s for s in data.get("submissions", []) if s.get("deprecated_at") is None
        ]
        if not submissions:
            raise DownloadError(f"no nondeprecated accepted submission for {theorem_id}")
        submissions.sort(
            key=lambda s: (s.get("updated_at") or s.get("created_at") or "", s["id"]),
            reverse=True,
        )
        return submissions[0]

    def write_download(self, path: Path, source: str, kind: str, node_name: str) -> None:
        action = "would download" if self.dry_run else "downloaded"
        print(
            f"{action:<14} {kind}: {node_name} -> {path.relative_to(PROJECT)}",
            flush=True,
        )
        if not self.dry_run:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source if source.endswith("\n") else source + "\n")

    def walk_source(self, source: str) -> None:
        for module in imports(source):
            if module.startswith("Definitions.Def_") or module.startswith("Theorems.Thm_"):
                self.walk_module(module)

    def walk_module(self, module: str) -> None:
        if module in self.visited_modules:
            return
        self.visited_modules.add(module)
        path = self.path_for_module(module)
        record = self.by_module.get(module)

        if path.exists():
            statement = path.read_text()
        else:
            record = self.resolve_remote_module(module)
            statement = statement_source(record)
            self.write_download(path, statement, record["status"].lower(), record["theorem_name"])
            self.downloaded_statements += 1
        self.walk_source(statement)

        if not module.startswith("Theorems.Thm_"):
            return
        if module in self.frontier_modules:
            name = record["theorem_name"] if record else module.removeprefix("Theorems.Thm_")
            print(f"frontier       {name} (statement only)", flush=True)
            return

        existing = next((p for p in self.solution_candidates(module) if p.exists()), None)
        if existing is not None:
            self.local_solutions += 1
            self.walk_source(existing.read_text())
            return

        record = record or self.resolve_remote_module(module)
        submission = self.choose_submission(record["theorem_id"])
        payload = request(f"/submissions/{submission['id']}/solution")
        source = payload.get("content")
        if not isinstance(source, str) or not source.strip():
            raise DownloadError(f"empty solution source for submission {submission['id']}")
        solution_path = (
            PROJECT / "Solutions" / f"Sol_{module_stem(record['theorem_name'])}.lean"
        )
        self.write_download(
            solution_path,
            source,
            f"{submission['status'].lower()} solution",
            record["theorem_name"],
        )
        self.downloaded_solutions += 1
        self.downloads[record["theorem_id"]] = {
            "theorem_name": record["theorem_name"],
            "submission_id": submission["id"],
            "submission_status": submission["status"],
            "solution_path": str(solution_path.relative_to(PROJECT)),
            "sha256": sha256(source),
        }
        self.walk_source(source)

    def run(self) -> None:
        root = self.records.get(self.goal_id)
        if root is None:
            root = request(f"/theorems/{self.goal_id}")
            self.records[self.goal_id] = root
            self.by_module[module_name(root)] = root
        self.walk_module(module_name(root))
        # The cached graph is also the local node index. Download every indexed
        # definition, including reusable definitions outside the selected proof
        # route, and recursively follow their imports.
        definition_modules = sorted(
            module_name(record)
            for record in list(self.records.values())
            if record.get("status") == "Definition"
        )
        for module in definition_modules:
            self.walk_module(module)
        result = {
            "downloaded_at": datetime.now(timezone.utc).isoformat(),
            "mode": "local-first",
            "goal_id": self.goal_id,
            "frontier_ids": sorted(self.frontier_ids),
            "visited_module_count": len(self.visited_modules),
            "existing_solution_count": self.local_solutions,
            "downloaded_statement_count": self.downloaded_statements,
            "downloaded_solution_count": self.downloaded_solutions,
            "downloads": dict(sorted(self.downloads.items())),
        }
        manifest = PROJECT / ".server-sync" / "proof-download.json"
        if self.dry_run:
            print(f"would write manifest: {manifest.relative_to(PROJECT)}", flush=True)
        else:
            manifest.write_text(json.dumps(result, indent=2) + "\n")
        print(
            "complete: "
            f"{len(self.visited_modules)} local modules traversed; "
            f"{self.local_solutions} existing proofs reused; "
            f"{self.downloaded_statements} missing statements/definitions downloaded; "
            f"{self.downloaded_solutions} missing solutions downloaded; "
            f"{len(self.frontier_modules)} frontier nodes left open",
            flush=True,
        )


def default_goal() -> str | None:
    manifest = PROJECT / ".server-sync" / "manifest.json"
    if not manifest.exists():
        return None
    return json.loads(manifest.read_text()).get("goal_id")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--goal-id",
        default=default_goal(),
        help="mission goal theorem UUID (defaults to .server-sync/manifest.json)",
    )
    parser.add_argument(
        "--replace",
        action="store_true",
        help="in --server-graph mode, replace files differing from accepted server source",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="fetch and check everything without writing"
    )
    parser.add_argument(
        "--verify-existing",
        action="store_true",
        help="in --server-graph mode, compare existing proofs with accepted server sources",
    )
    parser.add_argument(
        "--server-graph",
        action="store_true",
        help="traverse a freshly fetched server graph instead of the fast local import closure",
    )
    args = parser.parse_args()
    if not args.goal_id:
        parser.error("--goal-id is required when no cached manifest supplies one")
    try:
        if args.server_graph:
            Downloader(
                args.goal_id,
                replace=args.replace,
                dry_run=args.dry_run,
                verify_existing=args.verify_existing,
            ).run()
        else:
            LocalFirstDownloader(args.goal_id, dry_run=args.dry_run).run()
    except (DownloadError, OSError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
