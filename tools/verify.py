#!/usr/bin/env python3
"""Verify only the documented portable source entries, using Lean's kernel."""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = {"propext", "Classical.choice", "Quot.sound"}
RECEIVING = [
    "NativeTypeGuardA5", "NativeTypeGuard62", "VerifyBSection5",
    "VerifyB1AcceptedOperative", "VerifyOperativeB2Unaffected",
    "VerifyOperativeB3iUnaffected", "VerifyOperativeB3cUnaffected",
    "VerifyOperative55Unaffected54", "VerifyOperative57Unaffected",
    "Audit55ExpectedTypeKernelReplay", "AuditPresent18", "AuditCommon53",
    "AuditCommonUnionLiteralReceiving", "AuditCommonBTopologyFinalMainReceiving",
    "SchoenfliesTwoTypeFinalMainReceiving",
]


def payload_findings(text):
    """Inspect immutable serialized declaration payloads as well as Lean tokens."""
    literals = re.compile(r'(?:(?:ExactPaidSource\.(?:addJSON|guardJSON)|CommonTwentyFiniteCapturedTheoremGuards\.check)|(?:Lean\.)?ofExcept <\| Json\.parse)\s+("(?:\\.|[^"\\])*")')
    def contains_sorry(value):
        if isinstance(value, list):
            if len(value) >= 2 and value[0] == "const":
                def name(n):
                    return "" if n[0] == "anonymous" else (name(n[1]) + "." + str(n[2])).lstrip(".")
                if name(value[1]) == "sorryAx":
                    return True
            return any(contains_sorry(x) for x in value)
        if isinstance(value, dict):
            return any(contains_sorry(x) for x in value.values())
        return False
    for literal in literals.findall(text):
        value = json.loads(json.loads(literal))
        if value.get("kind") == "axiom" or contains_sorry(value):
            return True
    return False


def check_receiving(stem):
    report = ROOT / "tools/verification-reports" / (stem + ".txt")
    command = ["lake", "env", "lean"]
    if stem == "AuditCommonUnionLiteralReceiving":
        command.append("--run")
    command.append("tools/audits/" + stem + ".lean")
    if stem == "AuditCommonUnionLiteralReceiving":
        bundle = ROOT / "tools/verification-reports/union-one-absent-unused"
        bundle.mkdir(exist_ok=True)
        manifest = json.loads((ROOT / "tools/RECEIVING_MANIFEST.json").read_text())
        for entry in manifest["bounded_union_bundle"]:
            source = ROOT / entry["source"]
            if hashlib.sha256(source.read_bytes()).hexdigest() != entry["sha256"]:
                raise RuntimeError(f"Bounded union source custody mismatch: {entry['source']}")
            shutil.copyfile(source, bundle / source.name)
        command.append(str(bundle))
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    report.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"Receiving check failed: {stem}; see {report.relative_to(ROOT)}")
    return stem


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
            if source_tokens(path.read_text()) or payload_findings(path.read_text()):
                raise SystemExit(f"Placeholder in portable entry: {entry['release_path']}")
    print(f"PASS: {len(files)} custody hashes; portable source scan")
    if args.sources_only:
        return
    if json.loads((ROOT / "tools/RECEIVING_MANIFEST.json").read_text())["actual_fidelity_validator_status"] != "READY":
        raise SystemExit("Final actual-fidelity result validator is pending; complete package is not accepted")
    run(["lake", "build", "MainTheorems"])
    receiving_manifest = json.loads((ROOT / "tools/RECEIVING_MANIFEST.json").read_text())
    expected = receiving_manifest["root_names"]
    if receiving_manifest["native_original_root_count"] != 25 or receiving_manifest["support_root_count"] != 1 or len(receiving_manifest["source_ids"]) != 20:
        raise SystemExit("Receiving manifest must cover exactly the documented20 original results and25+1 roots")
    for entry in receiving_manifest["receiving_checks"] + receiving_manifest["generic_codec_sources"] + receiving_manifest["actual_fidelity_bundle"]:
        if hashlib.sha256((ROOT / entry["source"]).read_bytes()).hexdigest() != entry["sha256"]:
            raise SystemExit(f"Receiving source custody mismatch: {entry['source']}")
    observed = {}
    for file in ["tools/Verify.lean"]:
        output = run(["lake", "env", "lean", file])
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
            used = {x.strip() for x in axioms.split(",") if x.strip()}
            if used - BASE:
                raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - BASE)}")
            observed[name] = sorted(used)
    if len(expected) != 26 or set(observed) != set(expected):
        raise SystemExit("Axiom output did not cover the exact documented fresh roots")
    print(f"PASS: source compilation and classical-base axiom audit of {len(observed)} roots")
    (ROOT / "tools/verification-reports").mkdir(exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        for stem in pool.map(check_receiving, RECEIVING):
            print(f"PASS: {stem}")
    print(f"PASS: {len(RECEIVING)} complete literal and operative receiving checks")
    union_bundle = ROOT / "tools/verification-reports/union-one-absent-unused"
    union_bundle.mkdir(exist_ok=True)
    for entry in receiving_manifest["bounded_union_bundle"]:
        source = ROOT / entry["source"]
        if hashlib.sha256(source.read_bytes()).hexdigest() != entry["sha256"]:
            raise SystemExit(f"Bounded union source custody mismatch: {entry['source']}")
        shutil.copyfile(source, union_bundle / source.name)
    union_receipt = ROOT / "tools/verification-reports/UNION_ONE_ABSENT_UNUSED_VALIDATED_RECEIPT.json"
    run([sys.executable, "tools/fixtures/validate_union_one_absent_unused.py", "--base", str(union_bundle), "--repository", str(ROOT), "--receipt", str(union_receipt)])
    union_result = json.loads(union_receipt.read_text())
    if union_result["status"] != "PASS" or union_result["present_full_type_PASS"] != 928 or union_result["absent_unused"] != 1:
        raise SystemExit("Exact bounded union coverage failed")
    print("PASS: 928 present union entries plus one reviewed absent unused auxiliary; 396 operative equalities and 39 recursor checks")
    bundle = ROOT / "tools/verification-reports/actual-common"
    bundle.mkdir(exist_ok=True)
    for entry in receiving_manifest["actual_fidelity_bundle"]:
        source = ROOT / entry["source"]
        shutil.copyfile(source, bundle / source.name)
    run(["lake", "env", "lean", "--run", "tools/actual-common/AuditActualCommon.lean", "tools/verification-reports/actual-common"])
    validator_receipt = bundle / "ACTUAL_COMMON_VALIDATED_RECEIPT.json"
    run([sys.executable, "tools/actual-common/validate_actual_common.py", "--base", str(bundle), "--receipt", str(validator_receipt)])
    fidelity = json.loads(validator_receipt.read_text())
    if fidelity["status"] != "PASS" or fidelity["actual_records"] != 507 or fidelity["safe_operative_equality_PASS"] != 48:
        raise SystemExit("Exact actual common fidelity coverage failed")
    print("PASS: 507 exact actual common kernel records and safe-to-partial boundary")
    report = {"status": "PASS", "actual_fidelity": fidelity,
              "source_ids": receiving_manifest["source_ids"],
              "fresh_root_axioms": observed, "receiving_checks": receiving_manifest["receiving_checks"],
              "root_count": len(observed), "receiving_count": len(RECEIVING),
              "source_custody_file_count": len(files)}
    (ROOT / "tools/verification-reports/VERIFICATION_RUN.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
