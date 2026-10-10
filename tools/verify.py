#!/usr/bin/env python3
"""Verify only the documented portable source entries, using Lean's kernel."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = {"propext", "Classical.choice", "Quot.sound"}


def source_tokens(text):
    """Discard nested comments and strings before looking for placeholders."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            out.append(" ")
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
            out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            out.append(" ")
        elif text[i] == '"':
            string = True
            i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return re.findall(r"(?<![\w'])\b(?:sorry|admit)\b(?![\w'])", "".join(out))


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources-only", action="store_true",
                        help="Check custody hashes and portable-entry source scan without compiling")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "docs/SOURCE_MANIFEST.json").read_text())
    files = manifest["files"]
    for entry in files:
        path = ROOT / entry["release_path"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise SystemExit(f"Source custody mismatch: {entry['release_path']}")
        if entry.get("portable_entry") and path.suffix == ".lean":
            if source_tokens(path.read_text()):
                raise SystemExit(f"Placeholder in portable entry: {entry['release_path']}")
    print(f"PASS: {len(files)} custody hashes; portable source scan")
    if args.sources_only:
        return
    run(["lake", "build", "MainTheorems"])
    expected = json.loads((ROOT / "docs/VERIFICATION.json").read_text())["fresh_root_axioms"]
    observed = {}
    for file in ["tools/Verify.lean"]:
        output = run(["lake", "env", "lean", file])
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
            used = {x.strip() for x in axioms.split(",") if x.strip()}
            if used - BASE:
                raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - BASE)}")
            observed[name] = sorted(used)
    if set(observed) != set(expected):
        raise SystemExit("Axiom output did not cover the exact documented fresh roots")
    print(f"PASS: source compilation and classical-base axiom audit of {len(observed)} roots")
    print("Historical native packages and open originals were not verified by this command.")


if __name__ == "__main__":
    main()
