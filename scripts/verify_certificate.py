#!/usr/bin/env python3
"""Check the frozen source, proof map, toolchain and actual Lean exports.

Successful execution checks the listed exports. It does not promote a
numbered manuscript result or replace the mathematical correspondence review.
Only the exact literature declarations explicitly registered in status.json
may be additional axioms. Their kinds, source records, and type hashes are
inspected separately from proved exports.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from graphlib import TopologicalSorter

ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a"
TOOLCHAIN = "leanprover/lean4:v4.24.0"
MATHLIB_REV = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
LOCK_SHA = "08645a4980232706e7e92fcde4cbab1a9003d623f9c9fefb086de9eebbb4a937"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: str):
    return json.loads((ROOT / path).read_text())


def digest(path: str | Path) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def command(args: list[str], cwd: Path = ROOT) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError("Command failed: " + " ".join(args) + "\n"
                           + result.stdout + result.stderr)
    return (result.stdout + result.stderr).strip()


def lean_code(text: str) -> str:
    """Remove nested comments and strings before the source-policy scan."""
    out, i, depth = [], 0, 0
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
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def normalized_type(text: str) -> str:
    """Ignore pretty-printer line wrapping, but no mathematical tokens."""
    return re.sub(r"\s+", " ", text).strip()


def inspected_type(output: str, name: str) -> str:
    match = re.search(r"^@?" + re.escape(name) + r"\s*:\s*(.*?)\n'",
                      output, re.S | re.M)
    require(match is not None, "Actual declaration type not printed: " + name)
    return match[1].strip()


def check_source_policy(path: Path, code: str, inputs: list[dict]) -> None:
    """Allow only fully qualified, registered premise declarations in their file."""
    registered = {entry["declaration"] for entry in inputs
                  if ROOT / entry["file"] == path}
    declared = re.findall(r"\baxiom\s+([A-Za-z_][A-Za-z_0-9.]*)", code)
    require(len(declared) == len(set(declared)) and set(declared) == registered,
            "Unregistered or missing axiom declaration in " + str(path.relative_to(ROOT)))
    # Remove only the individually matched declaration keywords. Any other
    # occurrence of `axiom`, and every proof-placeholder token, still fails.
    code = re.sub(r"\baxiom\s+([A-Za-z_][A-Za-z_0-9.]*)",
                  lambda match: match[1] if match[1] in registered else match[0], code)
    bad = re.search(r"\b(sorry|admit|axiom|constant|unsafe|partial|native_decide|mkSorry)\b", code)
    require(bad is None, "Disallowed proof token in " + str(path.relative_to(ROOT)))


def verify(metadata_only: bool) -> dict:
    source = read_json("certification/source.json")
    graph = read_json("certification/dependency_inventory.json")
    status = read_json("certification/status.json")
    refs = read_json("certification/reference_inputs.json")
    require(digest(source["repository_filename"]) == SOURCE_SHA == source["sha256"],
            "Frozen manuscript identity changed")
    require(digest(source["pdf_path"]) == source["pdf_sha256"],
            "Frozen PDF identity changed")
    require(graph["source_sha256"] == SOURCE_SHA, "Graph source identity mismatch")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Toolchain pin changed")
    require(digest("lake-manifest.json") == LOCK_SHA, "Dependency lock changed")

    tex = (ROOT / source["repository_filename"]).read_text()
    environments = list(re.finditer(
        r"\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}",
        tex, re.S))
    labels = []
    for environment in environments:
        label = re.search(r"\\label\{([^}]+)\}", environment[2])
        require(label is not None, "Unlabelled numbered result")
        labels.append(label[1])
    rows = graph["results"]
    require(len(labels) == len(rows) == 42, "Numbered-result count mismatch")
    require(labels == [row["label"] for row in rows], "Numbered inventory mismatch")
    require(set(status["numbered_results"]) == set(labels), "Status keys mismatch")
    lines = tex.splitlines()
    for row in rows:
        first, last = row["statement_lines"]
        statement = "\n".join(lines[first - 1:last]) + "\n"
        require(statement == row["statement_tex"], "Statement changed: " + row["label"])
        require(hashlib.sha256(statement.encode()).hexdigest() == row["statement_sha256"],
                "Statement hash mismatch: " + row["label"])
        require(source["compiled_labels"][row["label"]]["number"] == row["number"],
                "Number mismatch: " + row["label"])

    auxiliary = graph["auxiliary_obligations"]
    require(len(auxiliary) == 33, "Auxiliary/supplementary group count changed")
    all_nodes = {row["label"] for row in rows} | {a["id"] for a in auxiliary}
    require(len(all_nodes) == 75, "Duplicate internal node")
    require(set(status["supplementary_groups"]) == {a["id"] for a in auxiliary},
            "Supplementary status keys mismatch")
    require(refs["inputs"] == graph["external_input_catalog"],
            "Reference registries disagree")
    dependency_map = {}
    for row in rows + auxiliary:
        name = row.get("label", row.get("id"))
        prerequisites = (row.get("principal_internal_dependencies",
                                row.get("internal_dependencies", []))
                         + row.get("auxiliary_dependencies", []))
        require(set(prerequisites) <= all_nodes, "Unknown dependency for " + name)
        require(set(row.get("external_inputs", [])) <= set(refs["inputs"]),
                "Unregistered literature input for " + name)
        dependency_map[name] = set(prerequisites)
    order = list(TopologicalSorter(dependency_map).static_order())
    require(len(order) == 75, "Invalid dependency graph")

    exports = status["supporting_exports"]
    export_names = {entry["declaration"] for entry in exports}
    require(len(export_names) == len(exports), "Duplicate export")
    counts = Counter()
    correspondence_records = set()
    claim_entries = list(status["numbered_results"].items()) + list(
        status["supplementary_groups"].items())
    for label, entry in claim_entries:
        require(entry["status"] in {"Pending", "Active", "Partial", "Certified"},
                "Invalid claim status: " + label)
        if label in status["numbered_results"]:
            counts[entry["status"]] += 1
        if entry["status"] in {"Partial", "Certified"}:
            require(entry["checked_exports"], "Status without exports: " + label)
            require(set(entry["checked_exports"]) <= export_names,
                    "Uninspected claim export: " + label)
            record = entry.get("correspondence_record")
            require(record and (ROOT / record).is_file(),
                    "Missing correspondence review: " + label)
            correspondence_records.add(ROOT / record)
        if entry["status"] == "Partial":
            require(entry.get("completed_clauses") and entry.get("remaining_clauses"),
                    "Partial claim needs completed and remaining clauses: " + label)

    inputs = status["accepted_lean_inputs"]
    input_names = {entry["declaration"] for entry in inputs}
    require(len(input_names) == len(inputs), "Duplicate literature declaration")
    require(not input_names & export_names, "A premise cannot also be a proved export")
    catalog_names = {name for entry in refs["inputs"].values()
                     for name in entry["lean_declarations"]}
    require(catalog_names == input_names, "Literature declaration registries disagree")
    for entry in inputs:
        name = entry["declaration"]
        require(entry["kind"] == "axiom" and
                name.startswith("QuaternaryQuadraticForms.Trusted."),
                "Literature premises need a separate named axiom declaration")
        require(entry["reference_id"] in refs["inputs"], "Unknown premise source: " + name)
        reference = refs["inputs"][entry["reference_id"]]
        require(name in reference["lean_declarations"], "Premise registered to wrong source")
        components = entry.get("source_components", [entry["reference_id"]])
        require(isinstance(components, list) and components and
                len(components) == len(set(components)) and
                entry["reference_id"] in components and
                set(components) <= set(refs["inputs"]),
                "Invalid premise source components: " + name)
        require(components == reference.get("source_components", [entry["reference_id"]]),
                "Composite premise source registries disagree: " + name)
        for component in components:
            component_record = refs["inputs"][component]
            require(component_record.get("source_url") and component_record.get("locator"),
                    "Premise component needs an exact source locator: " + component)
            if component != entry["reference_id"]:
                require(name in component_record.get("composite_declarations", []),
                        "Premise component does not register the combined declaration: " + component)
        record = entry.get("correspondence_record")
        require(record == reference.get("correspondence_record") and
                record and (ROOT / record).is_file(), "Missing premise correspondence review")
        require(reference.get("source_url") and reference.get("lean_statement"),
                "Premise needs an exact source locator and mathematical interface")
        correspondence_records.add(ROOT / record)
        expected = entry.get("expected_type")
        require(isinstance(expected, str) and expected,
                "Premise needs an inspected expected Lean type: " + name)
        require(hashlib.sha256(normalized_type(expected).encode()).hexdigest() ==
                entry.get("type_sha256"), "Premise expected-type hash mismatch: " + name)
        require((ROOT / entry["file"]).is_file(), "Missing premise declaration file")
    proof_files = sorted((ROOT / "QuaternaryQuadraticForms").rglob("*.lean"))
    require({ROOT / entry["file"] for entry in inputs} <= set(proof_files),
            "Every premise file must be an inspected project module")
    root_module = ROOT / "QuaternaryQuadraticForms.lean"
    local_files = proof_files + [root_module, ROOT / "Checks/Exports.lean"]
    for path in local_files:
        code = lean_code(path.read_text())
        check_source_policy(path, code, inputs)
    imports = set(re.findall(r"^\s*import\s+(\S+)", root_module.read_text(), re.M))
    modules = {str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
               for path in proof_files}
    require(modules <= imports, "Root module does not import every proof module")
    for entry in exports:
        require((ROOT / entry["file"]).is_file(), "Missing export file")
        require(set(entry["allowed_axioms"]) <= FOUNDATIONS | input_names,
                "Export allows an unregistered axiom: " + entry["declaration"])

    report = {
        "schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Listed Lean exports plus frozen-source/dependency/status checks",
        "manuscript_sha256": SOURCE_SHA,
        "numbered_results": dict(sorted(counts.items())),
        "numbered_total": 42,
        "auxiliary_supplementary_groups": len(auxiliary),
        "internal_dependency_edges": sum(map(len, dependency_map.values())),
        "trusted_reference_groups_mapped": len(refs["inputs"]),
        "registered_external_lean_inputs": len(inputs),
        "whole_paper_certified": False,
        "metadata_checks_passed": True,
        "lean_executed": False,
        "input_sha256": {
            str(path.relative_to(ROOT)): digest(path)
            for path in local_files + sorted(correspondence_records) + [
                ROOT / "lean-toolchain", ROOT / "lakefile.lean",
                ROOT / "lake-manifest.json", ROOT / "certification/source.json",
                ROOT / "certification/dependency_inventory.json",
                ROOT / "certification/status.json", ROOT / "certification/reference_inputs.json",
                ROOT / "scripts/verify_certificate.py",
            ]
        },
    }
    if metadata_only:
        return report

    report["lean_version"] = command(["lean", "--version"])
    require("version 4.24.0," in report["lean_version"], "Wrong actual Lean version")
    manifest = read_json("lake-manifest.json")
    package_revisions = {}
    for package in manifest["packages"]:
        directory = ROOT / ".lake/packages" / package["name"]
        rev = command(["git", "rev-parse", "HEAD"], directory)
        require(rev == package["rev"], "Wrong dependency checkout: " + package["name"])
        require(not command(["git", "status", "--porcelain", "--untracked-files=no"], directory),
                "Modified dependency checkout: " + package["name"])
        package_revisions[package["name"]] = rev
    require(package_revisions["mathlib"] == MATHLIB_REV, "Wrong actual mathlib")
    report["dependency_revisions"] = package_revisions
    report["lake_build_output"] = command(["lake", "build"])
    for path in proof_files:
        command(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false",
                 str(path.relative_to(ROOT))])
    output = command(["lake", "env", "lean", "-DwarningAsError=true", "-DautoImplicit=false",
                      "Checks/Exports.lean"])
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    found_map = {name: sorted(a.strip() for a in axioms.split(",") if a.strip())
                 for name, axioms in found}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        found_map[name] = []
    require(set(found_map) == export_names | input_names,
            "Actual axiom-inspection declaration set mismatch")
    report["checked_external_inputs"] = []
    for entry in inputs:
        name = entry["declaration"]
        actual_type = inspected_type(output, name)
        actual_hash = hashlib.sha256(normalized_type(actual_type).encode()).hexdigest()
        require(actual_hash == entry["type_sha256"], "Actual premise type changed: " + name)
        require(name in found_map[name] and set(found_map[name]) <= FOUNDATIONS | {name},
                "Unexpected premise dependency: " + name)
        report["checked_external_inputs"].append({
            "declaration": name, "kind": "axiom", "actual_type": actual_type,
            "type_sha256": actual_hash, "reference_id": entry["reference_id"],
            "source_components": entry.get("source_components", [entry["reference_id"]]),
            "axioms": found_map[name], "file": entry["file"],
            "source_sha256": digest(entry["file"]), "scope": entry["scope"],
        })
    report["checked_exports"] = []
    for entry in exports:
        name = entry["declaration"]
        require(set(found_map[name]) <= FOUNDATIONS | input_names,
                "Unexpected axiom dependency: " + name)
        require(set(found_map[name]) <= set(entry["allowed_axioms"]),
                "Export exceeds its recorded axiom allowance: " + name)
        report["checked_exports"].append({
            "declaration": name, "kind": "theorem", "actual_type": inspected_type(output, name),
            "axioms": found_map[name], "file": entry["file"],
            "source_sha256": digest(entry["file"]), "scope": entry["scope"],
        })
    report["lean_export_inspection_output"] = output
    report["lean_executed"] = True
    report["whole_paper_certified"] = counts["Certified"] == 42 and all(
        v["status"] == "Certified" for v in status["supplementary_groups"].values())
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--metadata-only", action="store_true",
                        help="Check the source and graph only; never claim Lean execution")
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.metadata_only), indent=2, ensure_ascii=False))
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
