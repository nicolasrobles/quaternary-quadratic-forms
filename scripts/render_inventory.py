#!/usr/bin/env python3
"""Render the readable inventory from the reviewed proof map and live ledger."""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BT = chr(96)
graph = json.loads((ROOT / "certification/dependency_inventory.json").read_text())
status = json.loads((ROOT / "certification/status.json").read_text())
source = json.loads((ROOT / "certification/source.json").read_text())
source_path = source["repository_filename"]
rows = graph["results"]


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
lines = [
    "# Certification inventory", "",
    "Frozen manuscript: v35, renamed without content changes for this repository.", "",
    f'**{counts["Certified"]} of {numbered_total} numbered results are certified.** '
    f'{counts["Partial"]} are partial, {counts["Active"]} are active numbered targets, '
    f'and {counts["Pending"]} are pending.', "",
    "The current checkpoint proves the complete quadric character-sum bound in "
    "Lemma 2.7. The quadric's actual geometric smoothness and irreducibility are "
    "proved from the matrix hypotheses. A general spectral input combines Katz's "
    "theorem with explicitly registered general hypersurface geometry, adjunction, "
    "and degree formulas; the quadric coefficient and scalar norm bound are proved "
    "deductions. The earlier Lemma 2.5, Corollary 2.6, and Lemmas 4.2–4.3 remain "
    "certified. The degree-two size bound in Lemma 5.9 is now checked under actual "
    "geometric good reduction, alongside its integrality and divisibility. Its "
    "literal N_G wrappers still require a proof that the exact bad-prime set is "
    "finite, so the numbered lemma remains Partial. The weight properties, "
    "ray identity (4.5), and zero-frequency clause of Lemma 4.4 remain checked; "
    "that lemma's pointwise estimate remains pending. Both numbered lemmas "
    "remain Partial. "
    f"The {auxiliary_total} auxiliary and supplementary groups are tracked separately; "
    "these are groups of assertions, not additional numbered results.", "",
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
    "lake exe cache get Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar "
    "Mathlib.Data.Fintype.BigOperators Mathlib.LinearAlgebra.Projectivization.Cardinality "
    "Mathlib.Analysis.Complex.Basic Mathlib.NumberTheory.DirichletCharacter.Bounds "
    "Mathlib.RingTheory.MvPolynomial.Homogeneous Mathlib.Data.Matrix.Mul "
    "Mathlib.FieldTheory.ChevalleyWarning Mathlib.NumberTheory.LegendreSymbol.Basic "
    "Mathlib.Algebra.Polynomial.Homogenize Mathlib.Data.Fin.VecNotation "
    "Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure "
    "Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.LinearAlgebra.Basis.VectorSpace "
    "Mathlib.LinearAlgebra.BilinearForm.Orthogonal Mathlib.LinearAlgebra.Dual.Lemmas "
    "Mathlib.LinearAlgebra.FiniteDimensional.Lemmas "
    "Mathlib.LinearAlgebra.LinearIndependent.Basic Mathlib.LinearAlgebra.LinearIndependent.Lemmas "
    "Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.BilinearForm "
    "Mathlib.LinearAlgebra.Matrix.Dual Mathlib.LinearAlgebra.Matrix.Rank "
    "Mathlib.RingTheory.MvPolynomial.EulerIdentity Mathlib.Tactic.FieldSimp "
    "Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex "
    "Mathlib.Data.Nat.Factorization.Basic Mathlib.Algebra.Polynomial.Coeff "
    "Mathlib.Tactic.IntervalCases Mathlib.Tactic.NormNum "
    "Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring",
    "python3 scripts/verify_certificate.py",
    BT * 3, "",
    f"The verifier checks source identities, all {numbered_total} statement locations, the dependency "
    "graph, status accounting, locked toolchain and dependency checkouts, every local "
    "proof module, declaration kinds, actual types, and permitted axioms. "
    "The frozen definitions and uniformity in varying coefficients must be preserved "
    "in every later export.", "",
    "## Next proof target", "",
    "Construct the nonzero elimination value in Lemma 4.1(i) and prove that every "
    "bad-reduction prime divides it. The checked arithmetic then proves finiteness "
    "of the actual bad-prime set and supplies the missing argument to the literal "
    "N_G wrappers in Lemma 5.9. The exceptional-plane construction in Lemma 4.1 "
    "and the remaining exceptional-section count and Fourier-bound assembly in "
    "Lemma 4.4 are separate obligations. Retain the checked Katz, conic, "
    "plane-section, exact-identity, and quadratic-trace results as inputs.", "",
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
    "The matrix geometry, polynomial calculations, and finite-product supporting exports use no external literature "
    "premises. The ledger records " + str(weil_exports) + " exports with the exact "
    "Weil premise, for the univariate, projective-line, and plane-section bounds, "
    "and " + str(katz_exports) + " with the general Katz surface premise, for "
    "Lemma 2.7 and the quadratic-trace bounds. Their actual axiom dependencies "
    "are inspected separately in the verification report.", "",
    "The Katz premise explicitly combines its spectral theorem and trace formula "
    "with Fulton/Stacks general hypersurface geometry, adjunction, and degree "
    "formulas. The matrix-quadric geometry, the numerical coefficient "
    "2n²−4n+4, and the final scalar norm estimate are proved internally. "
    "Every future input must likewise be listed separately from proved exports "
    "and appear explicitly in the inspected axiom dependencies.", "",
]
(ROOT / "TRUSTED_INPUTS.md").write_text("\n".join(trusted))
print("Rendered INVENTORY.md and TRUSTED_INPUTS.md")
