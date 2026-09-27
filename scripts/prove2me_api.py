#!/usr/bin/env python3
"""Small reusable Prove2Me API client for publishing and verifying local files."""

import argparse
import json
import mimetypes
import time
import urllib.error
import urllib.request
import uuid
from pathlib import Path

API = "https://prove2.me/api/v1"
CREDS = Path(__file__).resolve().parents[3] / "prove2me_workspace" / "credentials.json"


def credentials() -> dict:
    data = json.loads(CREDS.read_text())
    if data.get("expires_at", 0) <= time.time() + 60:
        req = urllib.request.Request(
            API + "/agent/refresh",
            data=json.dumps({"api_key": data["api_key"]}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        refreshed = json.load(urllib.request.urlopen(req))
        data["access_token"] = refreshed["access_token"]
        data["expires_at"] = refreshed["expires_at"]
        CREDS.write_text(json.dumps(data, indent=2) + "\n")
    return data


def request(path: str, *, method: str = "GET", data: bytes | None = None,
            headers: dict[str, str] | None = None) -> dict:
    token = credentials()["access_token"]
    all_headers = {"Authorization": f"Bearer {token}"}
    all_headers.update(headers or {})
    req = urllib.request.Request(API + path, data=data, headers=all_headers, method=method)
    try:
        with urllib.request.urlopen(req) as response:
            return json.load(response)
    except urllib.error.HTTPError as error:
        print(error.read().decode(errors="replace"))
        raise


def multipart(fields: dict[str, str], file_field: str, path: Path) -> tuple[bytes, str]:
    boundary = "----prove2me-" + uuid.uuid4().hex
    pieces: list[bytes] = []
    for name, value in fields.items():
        pieces += [
            f"--{boundary}\r\n".encode(),
            f'Content-Disposition: form-data; name="{name}"\r\n\r\n'.encode(),
            value.encode(), b"\r\n",
        ]
    mime = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
    pieces += [
        f"--{boundary}\r\n".encode(),
        (f'Content-Disposition: form-data; name="{file_field}"; '
         f'filename="{path.name}"\r\n').encode(),
        f"Content-Type: {mime}\r\n\r\n".encode(),
        path.read_bytes(), b"\r\n",
        f"--{boundary}--\r\n".encode(),
    ]
    return b"".join(pieces), boundary


parser = argparse.ArgumentParser()
sub = parser.add_subparsers(dest="command", required=True)

pget = sub.add_parser("get")
pget.add_argument("endpoint")

pjson = sub.add_parser("post-json")
pjson.add_argument("endpoint")
pjson.add_argument("payload", type=Path)

ppatch = sub.add_parser("patch-json")
ppatch.add_argument("endpoint")
ppatch.add_argument("payload", type=Path)

pproof = sub.add_parser("proof")
pproof.add_argument("theorem_id")
pproof.add_argument("source", type=Path)
pproof.add_argument("--explanation-file", type=Path)
pproof.add_argument("--proof-type", choices=["prove", "disprove"], default="prove")

ppoll = sub.add_parser("poll")
ppoll.add_argument("kind", choices=["job", "submission"])
ppoll.add_argument("id")
ppoll.add_argument("--interval", type=float, default=4)

args = parser.parse_args()
if args.command == "get":
    result = request(args.endpoint)
elif args.command == "post-json":
    result = request(
        args.endpoint, method="POST", data=args.payload.read_bytes(),
        headers={"Content-Type": "application/json"},
    )
elif args.command == "patch-json":
    result = request(
        args.endpoint, method="PATCH", data=args.payload.read_bytes(),
        headers={"Content-Type": "application/json"},
    )
elif args.command == "proof":
    fields = {"theorem_id": args.theorem_id, "proof_type": args.proof_type}
    if args.explanation_file:
        fields["explanation"] = args.explanation_file.read_text()
    body, boundary = multipart(fields, "file", args.source)
    result = request(
        "/verify", method="POST", data=body,
        headers={"Content-Type": f"multipart/form-data; boundary={boundary}"},
    )
else:
    endpoint = f"/publish-jobs/{args.id}" if args.kind == "job" else f"/submissions/{args.id}"
    terminal = {"PUBLISHED", "FAILED", "ERROR"} if args.kind == "job" else {
        "ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"
    }
    while True:
        result = request(endpoint)
        if result.get("status") in terminal:
            break
        time.sleep(args.interval)
print(json.dumps(result, indent=2))
