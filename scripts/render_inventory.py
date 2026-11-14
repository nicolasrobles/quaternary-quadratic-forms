#!/usr/bin/env python3
"""Render the readable inventory from the reviewed proof map and live ledger."""
from collections import Counter
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BT = chr(96)
graph = json.loads((ROOT / "certification/dependency_inventory.json").read_text())
status = json.loads((ROOT / "certification/status.json").read_text())
source = json.loads((ROOT / "certification/source.json").read_text())
source_path = source["repository_filename"]
rows = graph["results"]
proof_files = sorted((ROOT / "QuaternaryQuadraticForms").rglob("*.lean"))
cache_roots = sorted({
    module
    for path in proof_files
    for module in re.findall(r"^\s*import\s+(Mathlib\.\S+)", path.read_text(), re.M)
})
foundations = {"propext", "Classical.choice", "Quot.sound"}
premise_names = {
    "QuaternaryQuadraticForms.Trusted.weil_simple_roots": "Weil",
    "QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data": "Katz with general hypersurface geometry",
    "QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants": "Lang",
}
export_dependencies = Counter(
    tuple(sorted(set(entry["allowed_axioms"]) - foundations))
    for entry in status["supporting_exports"]
)
claim_entries = list(status["numbered_results"].values()) + list(
    status["supplementary_groups"].values())
correspondence_records = {
    ROOT / entry["correspondence_record"]
    for entry in claim_entries
    if entry["status"] in {"Partial", "Certified"}
}
correspondence_records.update(
    ROOT / entry["correspondence_record"] for entry in status["accepted_lean_inputs"]
)
# Match the verifier's input categories, without relying on a previous report.
verification_inputs = set(proof_files) | correspondence_records | {
    ROOT / path for path in [
        "QuaternaryQuadraticForms.lean", "Checks/Exports.lean", "lean-toolchain",
        "lakefile.lean", "lake-manifest.json", "certification/source.json",
        "certification/dependency_inventory.json", "certification/status.json",
        "certification/reference_inputs.json", "scripts/verify_certificate.py",
    ]
}


def cell(text):
    return str(text).replace("|", r"\|").replace("\n", " ")


def source_link(row):
    a, b = row["statement_lines"]
    return f'[{row["display"]}]({source_path}#L{a}-L{b})'


def export_links(exports):
    records = {e["declaration"]: e for e in status["supporting_exports"]}
    return "; ".join(f'[{BT}{name}{BT}]({records[name]["file"]})' for name in exports)


counts = Counter(r["status"] for r in status["numbered_results"].values())
numbered_total = len(rows)
auxiliary_total = len(graph["auxiliary_obligations"])
premise_total = len(status["accepted_lean_inputs"])
premise_phrase = "premise is" if premise_total == 1 else "premises are"
premise_declaration_phrase = "premise declaration is" if premise_total == 1 else "premise declarations are"
weil_exports = sum("QuaternaryQuadraticForms.Trusted.weil_simple_roots" in e["allowed_axioms"]
                   for e in status["supporting_exports"])
katz_exports = sum("QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data" in e["allowed_axioms"]
                   for e in status["supporting_exports"])
lang_exports = sum("QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants" in e["allowed_axioms"]
                   for e in status["supporting_exports"])
lines = [
    "# Certification inventory", "",
    "Frozen manuscript: v35, renamed without content changes for this repository.", "",
    f'**{counts["Certified"]} of {numbered_total} numbered results are certified.** '
    f'{counts["Partial"]} are partial, {counts["Active"]} are active numbered targets, '
    f'and {counts["Pending"]} are pending.', "",
    "The current checkpoint proves Lemma 4.1(i): the literal bad-prime set is "
    "finite, and its modulus N_G satisfies a coefficient-height bound with "
    "constants chosen before the form G. The registered Lang resultant theorem "
    "supplies a general homogeneous elimination family; the actual gradient "
    "equations, coefficient specialization, nonzero integer witness, prime "
    "divisibility, and height bound are proved deductions. Lemma 4.1 remains "
    "Partial because its exceptional-plane assertion in part (ii) is unfinished. "
    "The complete Lemma 5.9 now follows from characteristic-zero smoothness and "
    "p not dividing the literal N_G: its final exports assume neither a separate "
    "finiteness proof nor good reduction. Lemmas 2.5, 2.7, 4.2–4.3 and Corollary "
    "2.6 remain certified. The weight properties, ray identity (4.5), and "
    "zero-frequency clause of Lemma 4.4 remain checked; its uniform pointwise "
    "estimate is still pending, so that lemma remains Partial. Theorems 1.1 "
    "and 1.4 remain Pending. "
    f"The {auxiliary_total} auxiliary and supplementary groups are tracked separately; "
    "these are groups of assertions, not additional numbered results.", "",
    f'The verification scope contains **{len(status["supporting_exports"])} proved exports**, '
    f'**{len(proof_files)} proof modules**, and **{len(verification_inputs)} hashed input files**. '
    "These counts are derived from the live ledger and project files; they do not "
    "increase the number of certified manuscript results.", "",
    "[Manuscript source](manuscript/quadratic_character_sums_github.tex) · "
    "[PDF](manuscript/quadratic_character_sums_github.pdf) · "
    "[Dependency graphs](DEPENDENCIES.md) · [Trusted inputs](TRUSTED_INPUTS.md) · "
    "[Live proof ledger](certification/status.json)", "",
    "## Status convention", "",
    "- **Pending:** no accepted complete export for the frozen statement.",
    "- **Active:** currently being formalized; no completion is implied.",
    "- **Partial:** explicitly identified clauses have checked exports; remaining clauses are listed.",
    "- **Certified:** all clauses have kernel-checked proofs relative to registered literature "
    "inputs, and the statement and its dependencies have passed correspondence review.", "",
    "A successful build does not change these statuses. Imported literature theorems "
    "remain explicit inputs; applying them and verifying their hypotheses are manuscript "
    "proof obligations. A generic supporting identity is not counted as a numbered result.", "",
]
for section in sorted({r["number"].split(".")[0] for r in rows}, key=int):
    lines += [f"## Section {section}", "",
              "| Result | Content | Status | Checked export |",
              "|---|---|---|---|"]
    for row in rows:
        if row["number"].split(".")[0] != section:
            continue
        current = status["numbered_results"][row["label"]]
        exports = export_links(current["checked_exports"]) if current["checked_exports"] else "Pending"
        lines.append(f'| {source_link(row)} | {cell(row["content"])} | '
                     f'{current["status"]} | {exports} |')
    lines.append("")
lines += ["## Correspondence reviews for certified numbered results", ""]
for row in rows:
    current = status["numbered_results"][row["label"]]
    if current["status"] != "Certified":
        continue
    lines += [f'### {row["display"]}', "",
              "[Statement correspondence review](" + current["correspondence_record"] + ")", "",
              current.get("scope_note", ""), ""]
lines += ["## Scope of partially checked numbered results", ""]
for row in rows:
    current = status["numbered_results"][row["label"]]
    if current["status"] != "Partial":
        continue
    lines += [f'### {row["display"]}', "",
              "[Statement correspondence review](" + current["correspondence_record"] + ")", "",
              "Checked clauses:", ""]
    lines += ["- " + clause for clause in current["completed_clauses"]]
    lines += ["", "Remaining clauses:", ""]
    lines += ["- " + clause for clause in current["remaining_clauses"]]
    lines += ["", current.get("scope_note", ""), ""]
lines += [
    "## Checked exports and supporting declarations", "",
    "| Export | Precise scope | Status |",
    "|---|---|---|",
]
for entry in status["supporting_exports"]:
    lines.append(f'| [{BT}{entry["declaration"]}{BT}]({entry["file"]}) | '
                 f'{cell(entry["scope"])} | {entry["status"]} |')
lines += [
    "", "The allowed dependencies are the standard logical foundations "
    f'{BT}propext{BT}, {BT}Classical.choice{BT}, and {BT}Quot.sound{BT}. '
    "Individual exports may additionally use only the exact literature "
    "premises named in their ledger entry. Their actual Lean types and axiom dependencies are in the "
    "[verification report](certification/verification_report.json). "
    f'{premise_total} external Lean {premise_phrase} registered '
    "separately from these proved exports; see [Trusted inputs](TRUSTED_INPUTS.md).", "",
    "## Auxiliary and supplementary obligations", "",
    f"The following {auxiliary_total} groups retain their own correspondence review. "
    "The single numbered Remark 4.1 is represented by four of these groups. "
    "Final completion also requires a whole-manuscript correspondence review; "
    "the present grouping is not a reason to omit a subsequently identified assertion.", "",
    "| Group | Content and source | Status |",
    "|---|---|---|",
]
for row in graph["auxiliary_obligations"]:
    ranges = row.get("source_ranges", [])
    links = " ".join(f'[source]({source_path}#L{a}-L{b})' for a, b in ranges)
    current = status["supplementary_groups"][row["id"]]
    lines.append(f'| {BT}{row["id"]}{BT} | {cell(row["content"])} {links} | {current["status"]} |')
lines += [
    "", "## Frozen source and reproducibility", "",
    BT * 3 + "text", source["sha256"], BT * 3, "",
    "Official Lean 4.24.0 and official mathlib4 commit " +
    BT + "f897ebcf72cd16f89ab4577d0c826cd14afaafc7" + BT +
    " are pinned; the Lake manifest locks the transitive dependencies.", "",
    BT * 3 + "sh",
    "lake exe cache get " + " ".join(cache_roots),
    "python3 scripts/verify_certificate.py",
    BT * 3, "",
    f"The verifier checks source identities, all {numbered_total} statement locations, the dependency "
    "graph, status accounting, locked toolchain and dependency checkouts, every local "
    "proof module, declaration kinds, actual types, and permitted axioms. "
    "The frozen definitions and uniformity in varying coefficients must be preserved "
    "in every later export.", "",
    "## Next proof target", "",
    "Prove Lemma 4.1(ii): construct the exceptional-plane polynomial with its "
    "uniform degree bound and verify the geometric rank condition outside its "
    "zero set. Then complete Lemma 4.4 by combining the generic and exceptional "
    "frequency cases, the remaining section counts, and the exact ray identity. "
    "The proved bad-reduction and height result in Lemma 4.1(i), the full "
    "quadratic trace in Lemma 5.9, and the checked Katz, conic, and plane-section "
    "bounds remain available as inputs.", "",
]
(ROOT / "INVENTORY.md").write_text("\n".join(lines))

trusted = [
    "# Trusted literature inputs", "",
    "The authors authorize source-relative certification: exact cited inputs used "
    "by the proofs are trusted and are not reproved. Their mathematical statements, "
    "hypotheses, source locators, and Lean declarations must be registered before use. "
    "All specializations, hypothesis checks, coefficient uniformity, and deductions "
    "made in this manuscript remain proof obligations.", "",
    f'**{len(graph["external_input_catalog"])} input groups are mapped; {premise_total} external '
    f"{premise_declaration_phrase} currently registered in Lean.** "
    "Mapping an input is not the same as formalizing its interface. "
    "Use a suitable official mathlib result where available.", "",
    "| Input | Source locator | Accepted mathematical scope | Lean interface |",
    "|---|---|---|---|",
]
for key, entry in graph["external_input_catalog"].items():
    registered = [r for r in status["accepted_lean_inputs"] if r["reference_id"] == key]
    components = [r for r in status["accepted_lean_inputs"]
                  if r["reference_id"] != key and
                  (key in r.get("source_components", []) or
                   r["declaration"] in entry.get("composite_declarations", []))]
    links = [f'[{BT}{r["declaration"]}{BT}]({r["file"]})' for r in registered]
    links += [f'Component of [{BT}{r["declaration"]}{BT}]({r["file"]}) '
              "(no separate premise declaration)" for r in components]
    interfaces = "; ".join(links) or "Pending"
    trusted.append(f'| {BT}{key}{BT} | [{cell(entry["reference"])}], '
                   f'{cell(entry["locator"])} | {cell(entry["scope"])} | {interfaces} |')
trusted += ["", "## Registered premise inspection", ""]
for entry in status["accepted_lean_inputs"]:
    trusted += [f'### {BT}{entry["reference_id"]}{BT}', "",
                "[Exact source and correspondence review](" + entry["correspondence_record"] + "). "
                "The verifier checks the declaration kind, inspected Lean type, type hash, "
                "and actual axiom dependencies separately from proved exports.", "",
                "Expected type hash: " + BT + entry["type_sha256"] + BT + ".", ""]
    components = entry.get("source_components", [])
    if len(components) > 1:
        trusted += ["This is a composite interface with source components " +
                    ", ".join(BT + component + BT for component in components) + ". "
                    "Their combined statement is one registered Lean premise. The "
                    "correspondence review identifies the general geometric translations "
                    "and formulas included in that statement.", ""]
trusted += [
    "", "## Cited claims excluded from the premise registry", "",
    "The paper gives counterexamples to the following claims. They are comparison "
    "targets and must never be accepted as axioms of this certificate.", "",
    "| Source | Reason |", "|---|---|",
]
for entry in graph["excluded_comparison_claims"]:
    trusted.append(f'| [{entry["reference"]}], {entry["locator"]} | {cell(entry["reason"])} |')
trusted += [
    "", "Other citations used only for attribution, background, or a description of "
    "related work are not automatically Lean assumptions. In particular, the "
    "square/power-sieve references motivate the method; the manuscript's actual "
    "sieve inequality is a deduction to be proved.", "",
    "## Dependencies of proved exports", "",
    "The matrix geometry, ordered gradient minors, homogeneous coefficient "
    "reconstruction, coefficient specialization, polynomial-height estimates, "
    "and finite-product arithmetic use only the standard logical foundations. "
    "The ledger records " + str(weil_exports) + " exports with the exact Weil "
    "premise, " + str(katz_exports) + " with the general Katz surface premise, "
    "and " + str(lang_exports) + " with the Lang resultant premise. These counts "
    "overlap when an export uses more than one premise. The following table "
    "groups exports by their exact recorded allowance; actual axiom dependencies "
    "are inspected separately in the verification report.", "",
    "| Permitted literature premises | Proved exports |",
    "|---|---:|",
]
for dependencies, count in sorted(export_dependencies.items(), key=lambda item: (len(item[0]), item[0])):
    label = "; ".join(premise_names.get(name, BT + name + BT) for name in dependencies)
    trusted.append(f'| {label or "None (standard logical foundations only)"} | {count} |')
trusted += [
    "", "Lemma 4.1(i) uses Lang's general homogeneous resultant family. Its "
    "specialization to the actual F, G and gradient minors, the nonzero integer "
    "witness, finiteness of the literal bad-prime set, and the coefficient-height "
    "bound are proved internally. The complete Lemma 5.9 uses both Lang and Katz: "
    "Lang supplies the finiteness deduction needed to form the literal N_G, "
    "while Katz supplies the projective trace bound. The trace's integrality "
    "and divisibility are proved without either literature premise.", "",
    "The Katz premise explicitly combines its spectral theorem and trace formula "
    "with Fulton/Stacks general hypersurface geometry, adjunction, and degree "
    "formulas. The matrix-quadric geometry, the numerical coefficient "
    "2n²−4n+4, and the final scalar norm estimate are proved internally. "
    "Every future input must likewise be listed separately from proved exports "
    "and appear explicitly in the inspected axiom dependencies.", "",
]
(ROOT / "TRUSTED_INPUTS.md").write_text("\n".join(trusted))
print("Rendered INVENTORY.md and TRUSTED_INPUTS.md")
