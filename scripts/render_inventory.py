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
    "QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent": "Bertini with general projective geometry",
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
bertini_exports = sum("QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent" in e["allowed_axioms"]
                      for e in status["supporting_exports"])
lines = [
    "# Certification inventory", "",
    "Frozen manuscript: [quadratic_character_sums_github.tex]"
    "(manuscript/quadratic_character_sums_github.tex).", "",
    f'**{counts["Certified"]} of {numbered_total} numbered results are certified.** '
    f'{counts["Partial"]} {"is" if counts["Partial"] == 1 else "are"} partial, '
    f'{counts["Active"]} are active numbered targets, '
    f'and {counts["Pending"]} are pending.', "",
    "The current checkpoint completes both clauses of Lemma 3.5, with "
    "the actual q₁=gcd(q,c) and q₂=q/q₁. The source matrix is "
    "symmetric and nonsingular over the integers, q≥1 is squarefree "
    "with (q,N)=1, rad(N_F)∣N, and the supplied prime weights are "
    "invariant under nonzero scalars. For (c,N_F)=1 the formula "
    "is 𝒮_{q,c}(u)=C_{q₂}(u) q₁c² χ(q₁c) ξ_{q₁}(adj(A)u) "
    "R_{q₁c}(F*(u)). On the dual cone F*(u)=0 it is "
    "𝒮_{q,c}(u)=C_{q₂}(u) q₁² χ(q₁) ξ_{q₁}(adj(A)u) S_c(u) "
    "for every positive c, including arbitrary bad-prime factors. "
    "The proofs use actual Ramanujan CRT, the zero-frequency unit "
    "count, φ(dc)=dφ(c) for d∣c, literal gcd/quotient arithmetic, "
    "and prime-power induction over actual complete sums. An actual "
    "supplied Dirichlet character is retained: agreement with the "
    "Jacobi coefficient at good composite moduli is proved from its "
    "stated good-prime Legendre values. The right-hand weight is the "
    "literal product of the original supplied prime functions. The "
    "bad/good modulus split is constructed, its gcd preservation is "
    "proved, and S_{c_bad}(u) is multiplied through both CRT "
    "identities without division, including when it vanishes. "
    "Both modulus-one boundaries are included. N≥1 is unused and "
    "is not inferred from (q,N)=1. Primitivity, the nonsquare "
    "condition, and the weight's zero value, norm bound and Fourier "
    "stratification bounds are also unnecessary for these identities. "
    "All 27 new exports in 11 modules passed strict targeted builds "
    "and actual type/axiom inspection: gcd_mul_blocks_coprime uses "
    "only propext, and the other 26 use exactly Classical.choice, "
    "Quot.sound, and propext. No literature premise is added or used. "
    "[Source correspondence review]"
    "(certification/correspondence/good_global_complete_sum.md). "
    "Aggregate verification and CI execution evidence are recorded "
    "separately in the checkpoint.", "",
    "The completed Lemma 3.4 retains the actual mixed "
    "sum: 𝒮_{p,p^k}(u)=χ(p)^(k+1) p^(2k+1) ξ_p(adj(A)u) "
    "R_{p^(k+1)}(F*(u)), for every source prime p∤N, k≥1, and "
    "integral frequency. The literal weighted sum 𝒰_j is expanded "
    "by actual residue digits; four-coordinate orthogonality selects "
    "2aAy+u=0 mod p. Multiplication by the adjugate gives "
    "adj(A)u=−(2a det A)y mod p, and invariance under the proved nonzero "
    "scalar identifies the selected weight. Lemma 3.2 evaluates the "
    "remaining unweighted complete sum. A separate actual unit-digit "
    "bijection and scalar orthogonality prove 𝒰_{k+1}=p 𝒮_{p,p^k}, "
    "with precisely the cone constraint p∣F(x). Cancelling only the "
    "nonzero scalar p gives the exact exponent 2k+1. The source "
    "wrapper uses rad(N_F)∣N and det A≠0 to derive good reduction "
    "and returns the original supplied local function on the right. "
    "The weight's zero value, norm bound and Fourier stratification "
    "bounds are unused; nonzero scalar invariance suffices, including "
    "at zero frequency. That milestone's 18 exports in eight modules passed "
    "strict targeted builds and actual type/axiom inspection, using "
    "exactly Classical.choice, Quot.sound, and propext. No new "
    "literature premise or undischarged weighted-sum hypothesis is "
    "introduced. [Source correspondence review]"
    "(certification/correspondence/ramified_complete_sum.md). "
    "Its aggregate scope was 571 exports, 128 modules and 155 input "
    "hashes. Aggregate verification and CI execution evidence are "
    "recorded separately in the checkpoint.", "",
    "The completed Lemma 3.3 proves the bound for the actual complete "
    "sum: |S_c(u)|≤4√|det A| c³ for every positive modulus and every "
    "integral frequency, assuming only symmetry and integer nonsingularity "
    "of the source matrix. Translation and composite-modulus additive "
    "orthogonality give the squared-norm bound by c⁴ times the actual "
    "residue kernel cardinality of 2A. Surjective coordinate reduction "
    "and the finite-endomorphism index theorem show that this cardinality "
    "divides the integer range index. Mathlib's proved determinant-index "
    "theorem, based on Smith normal form, identifies that index with "
    "|det(2A)|=16|det A|. The square-root and actual unit-count bounds "
    "then give the exact source constant. Modulus one, even moduli, and "
    "arbitrary bad-prime factors are included; no good-prime, oddness, "
    "nonzero-frequency, or nonsquare-determinant hypothesis is imposed. "
    "That milestone's 17 exports in eight modules passed strict targeted builds "
    "and actual type/axiom inspection, using exactly Classical.choice, "
    "Quot.sound, and propext. No kernel count or inner estimate remains "
    "assumed in the endpoint. Aggregate execution and CI evidence are "
    "recorded separately in the checkpoint.", "",
    "The completed Lemma 3.2 retains all three clauses for "
    "the actual general symmetric integral matrix: the full shifted "
    "prime-power Gauss evaluation, the Ramanujan formula for S_{p^k}, "
    "and the exact projective quadric count p²+(1+χ(p))p+1. The good-prime "
    "condition uses N_F=2|det A| and χ(p) is the stated Legendre symbol "
    "(det A/p). The orthogonal-basis prime calculation, actual residue-digit "
    "bijections, recurrence V_{k+2}=p⁴V_k, adjugate square completion, "
    "unit permutations and affine/projective counts are all internal "
    "proofs. The pure Gauss base case includes k=0; extracting an integer "
    "lift coprime to p from a unit modulo p^k correctly retains k≥1. "
    "No source-specific Gauss formula, recurrence or count remains an "
    "assumption in the final endpoint. That milestone added 54 public theorem "
    "exports in 16 modules and no literature premise. Actual type and "
    "dependency inspection, aggregate execution and CI evidence are "
    "recorded separately in the checkpoint.", "",
    "The completed Lemma 3.1 retains both clauses for the "
    "literal prime-product weights and mixed complete sums: CRT "
    "multiplicativity and invariance under every integer frequency scalar "
    "coprime to qc. The final source wrapper accepts local functions only "
    "at primes p ∤ N; its total-family extension is proved to agree with "
    "every factor used when (q,N)=1. Lift independence, shared primes "
    "between q and c within either CRT block, and modulus one are "
    "included. The gcd condition also retains the permitted t=0 case "
    "when qc=1. Direct supporting exports prove the squarefree C_q "
    "prime-factor product, multiplicativity of S_c, and the bridge to "
    "the existing prime Fourier sum. Those 66 exports have passed "
    "strict builds and actual type and axiom inspection, with only "
    "standard logical foundations. Aggregate execution and CI evidence "
    "are recorded separately in the checkpoint. Lemmas 2.5, 2.7, "
    "4.1–4.6 and 5.9 and Corollary 2.6 remain certified. This preserves "
    "the exact diagonal bad-prime modulus rad(|2αM|), the pencil formula "
    "with all four singular members, the integer projective trace, and "
    "the generic bound 2p^(3/2)+4p. The pencil formula and trace use no "
    "external premise; that bound uses only the existing Weil premise, "
    "with repeated-root cubics handled internally. The prime-field Gauss "
    "identities are proved using official mathlib results, so the four "
    "registered literature premises remain unchanged. No numbered result "
    "remains Partial. Theorems 1.1, 1.3 and 1.4 remain Pending: the "
    "asymptotic clause of Theorem 1.3 still depends on Theorem 1.1. "
    f"All {auxiliary_total} auxiliary and supplementary groups remain Pending and are tracked separately; "
    "these are groups of assertions, not additional numbered results.", "",
    f'The verification scope contains **{len(status["supporting_exports"])} proved exports**, '
    f'**{len(proof_files)} proof modules**, and **{len(verification_inputs)} hashed input files**. '
    "These counts are derived from the live ledger and project files; they do not "
    "increase the number of certified manuscript results. "
    "The whole-paper certification flag remains false.", "",
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
if not counts["Partial"]:
    lines += ["There are no partially checked numbered results at this checkpoint.", ""]
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
    "Full Lemma 3.6 (lem:genericmod), source lines 1292–1342, remains "
    "Pending and is the next target. For squarefree q=q₁q₂ with "
    "(q,N)=1, m=F*(u)≠0, X≥1 and each ε>0, prove the complete sum over "
    "1≤c≤X and gcd(c,q)=q₁ of |𝒮_{q,c}(u)|/c³ is at most "
    "a constant depending only on F and ε times "
    "|C_{q₂}(u)| q₁² 1_{q₁∣m} (X|m|)^ε, uniformly in q,u,X. "
    "The proof includes the bad-prime-supported modulus count from "
    "source lines 1288–1290, the actual Ramanujan prime-power "
    "valuation calculation, the local factor bound p²v_p(m), and "
    "the exact vanishing unless q₁∣m. The remaining divisor and "
    "harmonic-sum estimate is ∑_{n≤X}|R_n(m)|/n≤τ(|m|)(1+log X). "
    "Together these must give the intermediate factor "
    "τ(|m|)²(1+log X)^(1+ω(N_F)) and its uniform absorption into "
    "the final ε power. These summation, valuation, counting, "
    "indicator and uniformity claims remain proof obligations. "
    "Theorem 1.3 and the global analytic theorems remain Pending.", "",
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
    if key == "EXT.MV_GAUSS" and not links:
        interfaces = (
            "Needed prime-field identities [proved using official mathlib]"
            "(QuaternaryQuadraticForms/PrimeQuadraticGauss.lean); "
            "no external premise declaration"
        )
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
    "finite-product arithmetic, prime-field Gauss calculations, exact "
    "diagonal pencil evaluations, composite weights, scaled CRT, "
    "complete-sum factorizations, general matrix Gauss evaluations, "
    "prime-power residue recurrences, quadric point counts, uniform "
    "norm bounds, actual residue kernels, determinant-index "
    "comparisons, weighted stationary expansions, adjugate weight "
    "extraction, shared-prime complete-sum evaluations, actual "
    "Ramanujan multiplicativity, source-character agreement, and "
    "the global mixed-sum and dual-cone identities use only "
    "the standard logical foundations. "
    "The ledger records " + str(weil_exports) + " exports with the exact Weil "
    "premise, " + str(katz_exports) + " with the general Katz surface premise, "
    + str(lang_exports) + " with the Lang resultant premise, and "
    + str(bertini_exports) + " with the general composite Bertini premise. These counts "
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
    "Lemma 4.1(ii) combines Lang with the general composite Bertini interface. "
    "Hartshorne's theorem and the explicitly attributed projective Jacobian "
    "and tangent-space facts supply a transverse tangent direction for a "
    "general homogeneous system over an algebraically closed field. The "
    "rank-three consequence, actual second elimination system, coefficient "
    "specialization, descent of polynomial nonvanishing, and construction "
    "D_p = F* R_j(G,·) with a uniform degree bound are internal proofs. "
    "No rational transverse plane over the prime field is assumed.", "",
    "The complete uniform Fourier theorem in Lemma 4.4 uses all four existing "
    "premises through the checked results above. The given-polynomial integral "
    "theorem uses Weil, Katz and Lang; the prime-field estimate uses Weil and "
    "Katz. The exceptional section count, including tangent and singular "
    "sections, is proved with the official mathlib Schwartz–Zippel theorem "
    "and the actual projective-ray decomposition, with no external premise. "
    "The constant comparisons and assembly of the indicator bound are internal "
    "deductions. No new literature declaration is introduced.", "",
    "The complete diagonal bad-prime lemma, Lemma 4.5, uses none of the "
    "registered literature premises. The actual gradient-minor calculation, "
    "geometric singular witness, coefficient reduction, direct finiteness "
    "from M and exact radical product are proved using standard logical "
    "foundations and proved library results.", "",
    "The complete diagonal pencil lemma, Lemma 4.6, retains every regular "
    "and singular member of the actual Fourier sum. Its Gauss identities, "
    "reciprocal phases, Ramanujan factors and exact integer projective "
    "trace are proved internally with official mathlib results and no "
    "registered literature premise. The generic bound uses only the "
    "existing affine Weil premise in the separable cubic case. A "
    "nonseparable cubic is factored over the perfect prime field, and "
    "its character sum is evaluated exactly, so no separability "
    "assumption survives in the final bound. Those one-dimensional "
    "Gauss identities provide a proved ingredient for the full "
    "prime-power Lemma 3.2 described below.", "",
    "The complete CRT lemma, Lemma 3.1, uses none of the registered "
    "literature premises. Its actual prime-product weights, good-prime "
    "source-domain extension, representative independence, scaled residue "
    "and unit bijections, exact mixed phases, and frequency invariance "
    "are proved internally. Only invariance at primes dividing q is "
    "used; (q,N)=1 makes each factor one of the supplied good-prime "
    "functions. The direct C_q and S_c factorization corollaries and "
    "the prime polynomial-character Fourier bridge likewise use only "
    "standard logical foundations. No coprimality between q and c "
    "within a CRT block is imposed, and modulus-one cases are retained.", "",
    "The full prime-power Gauss lemma, Lemma 3.2, likewise uses none of "
    "the registered literature premises. An actual orthogonal basis "
    "diagonalizes the source's symmetric matrix over the prime field, "
    "and the change-of-basis determinant square is proved harmless "
    "under the quadratic character. Actual residue-digit bijections "
    "and additive orthogonality prove the recurrence at powers of p. "
    "Adjugate square completion uses the exact inverse phase; the "
    "good-prime condition N_F=2|det A| supplies the required units. "
    "The Ramanujan conclusion reindexes the actual unit group, and "
    "the projective count follows from the actual affine zero set "
    "and projective rays. All intermediate constant-Gauss hypotheses "
    "are discharged in the final source theorem. The pure modulus-one "
    "base and the k≥1 requirement when lifting a prime-power unit "
    "to an integer coprime to p are kept separate. No fifth "
    "literature premise is introduced.", "",
    "The uniform complete-sum estimate in Lemma 3.3 uses none of the "
    "registered literature premises. The squared-norm identity and "
    "additive orthogonality concern the actual sum at every positive "
    "modulus. The residue-kernel bound uses the actual integer range, "
    "surjective coordinate reduction, finite-endomorphism index, and "
    "mathlib's proved Smith-normal-form determinant-index theorem. "
    "Its new public kernel endpoint is the determinant bound; no "
    "separate exact gcd-product kernel formula is claimed. Doubling "
    "the source matrix gives the factor sixteen, and the checked "
    "nonnegative square-root calculation gives the constant four. "
    "The triangle inequality is applied to the existing complete sum "
    "over actual unit parameters. All inner-bound hypotheses are "
    "discharged from symmetry and integer nonsingularity in the "
    "final source theorem, including at modulus one and every bad "
    "prime. The 17 new exports have exactly the three standard "
    "logical axioms; no literature input is added or used.", "",
    "The full shared-prime identity in Lemma 3.4 uses none of the "
    "registered literature premises. Its actual weighted Gauss and "
    "unit sums, residue-digit phase calculation, stationary "
    "orthogonality, and adjugate multiplication are internal proofs. "
    "The equality adj(A)u=−(2a det A)y modulo p uses a proved nonzero scalar, "
    "so the original weight invariance supplies the constant weight "
    "on every surviving term. The completed Lemma 3.2 then evaluates "
    "the remaining sum. The actual unit-digit bijection proves "
    "𝒰_{k+1}=p 𝒮_{p,p^k} with the literal cone divisibility condition; "
    "cancelling the nonzero p gives the exponent 2k+1. The source "
    "radical hypothesis rad(N_F)∣N is used exactly, with det A≠0 "
    "ensuring N_F is nonzero. The supplied-prime family extension "
    "is proved equal to the original local weight on the right. "
    "Every k≥1 and integral frequency is included. The weight's "
    "zero value, norm and Fourier stratification bounds, and the "
    "global nonsquare assumption are unnecessary. All 18 new "
    "exports have exactly the three standard logical axioms. "
    "No stationary-phase, weighted-factor, or unit-lift conclusion "
    "is left as a premise in the final source theorem.", "",
    "Both clauses of Lemma 3.5 use none of the registered literature "
    "premises. Scaled CRT on actual units proves Ramanujan "
    "multiplicativity, and the zero-frequency unit count and proved "
    "totient identity supply the dual-cone coefficient. The actual "
    "Jacobi coefficient agrees at good positive composite moduli "
    "with the supplied DirichletCharacter, by a proved prime-induction "
    "argument using exactly the source's stated prime values. "
    "Primitivity and the quadratic-field construction are not "
    "replaced by a new abstract character or an assumed composite "
    "identity. Actual gcd/quotient arithmetic, prime-power induction "
    "and complete-sum CRT give the global good-modulus evaluation. "
    "The bad/good modulus factors are constructed; the possible "
    "zero value of S_{c_bad}(u) is retained multiplicatively in "
    "both CRT identities. The source radical condition derives "
    "coprimality with N_F, and the weight bridge returns the literal "
    "product of the original prime functions. N≥1 is unused, not "
    "deduced from (q,N)=1; the nonsquare, primitive-character, "
    "weight-zero, weight-norm and Fourier-stratification hypotheses "
    "are unnecessary after the actual source data and prime values "
    "are supplied. The 27 new inspected exports use only standard "
    "logical foundations: gcd_mul_blocks_coprime uses propext alone, "
    "and the other 26 use the standard triplet. No internal "
    "factorization or global evaluation remains assumed in the "
    "combined source endpoint.", "",
    "The Katz premise explicitly combines its spectral theorem and trace formula "
    "with Fulton/Stacks general hypersurface geometry, adjunction, and degree "
    "formulas. The matrix-quadric geometry, the numerical coefficient "
    "2n²−4n+4, and the final scalar norm estimate are proved internally. "
    "Every future input must likewise be listed separately from proved exports "
    "and appear explicitly in the inspected axiom dependencies.", "",
]
(ROOT / "TRUSTED_INPUTS.md").write_text("\n".join(trusted))
print("Rendered INVENTORY.md and TRUSTED_INPUTS.md")
