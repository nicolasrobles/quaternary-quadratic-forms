#!/usr/bin/env python3
"""Check only the supplied large-frequency certificate and its existing imports."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re

import verify_certificate as verifier

ROOT = verifier.ROOT
require = verifier.require
command = verifier.command
digest = verifier.digest


def verify() -> dict:
    metadata = verifier.verify(metadata_only=True)
    evidence = verifier.read_json("certification/local/large_frequency_package_evidence.json")
    status = verifier.read_json("certification/status.json")
    expected = {e["declaration"]: e for e in evidence["checked_exports"]}
    require(len(expected) == 8, "Expected exactly eight focused theorem exports")
    files = evidence["files"]
    require(len(files) == 3, "Expected exactly three new proof modules")
    for entry in expected.values():
        require(digest(entry["file"]) == entry["source_sha256"],
                "Supplied proof bytes changed: " + entry["file"])
    modules = [f.removesuffix(".lean").replace("/", ".") for f in files]
    closure = set()

    def visit(module: str) -> None:
        if module in closure:
            return
        closure.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        for imported in re.findall(r"^import\s+(\S+)", path.read_text(), re.M):
            if imported.startswith("QuaternaryQuadraticForms."):
                visit(imported)

    for module in modules:
        visit(module)
    lean_version = command(["lean", "--version"])
    require("version 4.24.0," in lean_version, "Wrong Lean version")
    revisions = {}
    for package in verifier.read_json("lake-manifest.json")["packages"]:
        directory = ROOT / ".lake/packages" / package["name"]
        revision = command(["git", "rev-parse", "HEAD"], directory)
        require(revision == package["rev"], "Dependency revision changed")
        require(not command(["git", "status", "--porcelain", "--untracked-files=no"], directory),
                "Dependency working tree changed")
        revisions[package["name"]] = revision
    require(revisions["mathlib"] == verifier.MATHLIB_REV, "Wrong mathlib revision")
    build_output = command(["lake", "build", *modules])
    for path in files:
        command(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", path])
    inspection = command(["lake", "env", "lean", "-DwarningAsError=true",
                          "-DautoImplicit=false", "Checks/LargeFrequency.lean"])
    actual_axioms = {
        name: sorted(a.strip() for a in axioms.split(",") if a.strip())
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", inspection)
    }
    for name in re.findall(r"'([^']+)' does not depend on any axioms", inspection):
        actual_axioms[name] = []
    premises = {e["declaration"]: e for e in evidence["checked_external_inputs"]}
    require(set(actual_axioms) == set(expected) | set(premises), "Inspection name mismatch")
    ledger = {e["declaration"]: e for e in status["supporting_exports"]}
    checked = []
    for name, supplied in expected.items():
        actual_type = verifier.inspected_type(inspection, name)
        require(verifier.normalized_type(actual_type) ==
                verifier.normalized_type(supplied["actual_type"]), "Theorem type changed: " + name)
        require(actual_axioms[name] == sorted(supplied["axioms"]), "Theorem axioms changed: " + name)
        require(set(actual_axioms[name]) <= set(ledger[name]["allowed_axioms"]),
                "Theorem exceeds registered axiom allowance: " + name)
        checked.append({**supplied, "actual_type": actual_type, "axioms": actual_axioms[name]})
    registered = {e["declaration"]: e for e in status["accepted_lean_inputs"]}
    checked_inputs = []
    for name, supplied in premises.items():
        actual_type = verifier.inspected_type(inspection, name)
        type_hash = hashlib.sha256(verifier.normalized_type(actual_type).encode()).hexdigest()
        require(type_hash == registered[name]["type_sha256"] == supplied["type_sha256"],
                "Literature premise type changed: " + name)
        require(actual_axioms[name] == sorted(supplied["axioms"]), "Premise axioms changed")
        checked_inputs.append({**supplied, "actual_type": actual_type, "axioms": actual_axioms[name]})
    paths = sorted(m.replace(".", "/") + ".lean" for m in closure)
    paths += ["lean-toolchain", "lakefile.lean", "lake-manifest.json",
              "certification/reference_inputs.json", "Checks/LargeFrequency.lean",
              "scripts/verify_large_frequency.py", "certification/local/large_frequency_package_evidence.json"]
    return {
        "schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Lemma 5.2 first clause only: eight theorem exports in three supplied modules",
        "checked_commit": os.environ.get("GITHUB_SHA", command(["git", "rev-parse", "HEAD"])),
        "workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        "workflow_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "manuscript_sha256": metadata["manuscript_sha256"],
        "metadata_checks_passed": True,
        "lean_executed": True,
        "whole_paper_certified": False,
        "lean_version": lean_version,
        "dependency_revisions": revisions,
        "new_proof_modules": files,
        "project_import_closure_count": len(closure),
        "proof_input_sha256": {path: digest(path) for path in paths},
        "checked_exports": checked,
        "checked_external_inputs": checked_inputs,
        "actual_types_and_axioms_match_supplied_records": True,
        "build_output": build_output,
        "lean_inspection_output": inspection,
    }


if __name__ == "__main__":
    result = verify()
    serialized = json.dumps(result, ensure_ascii=False, separators=(",", ":"))
    destination = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "large_frequency_verification.json"
    destination.write_text(serialized + "\n")
    print("LARGE_FREQUENCY_REPORT_JSON=" + serialized)
