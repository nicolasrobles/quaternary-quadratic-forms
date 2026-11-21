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
    "QuaternaryQuadraticForms.Trusted.heathBrown_delta_data": "Heath–Brown fixed delta construction",
    "QuaternaryQuadraticForms.Trusted.simon_graph_area": "Simon general graph area formula",
    "QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization": "Heath–Brown uniform weight localization",
    "QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph": "Heath–Brown thin-slab graph limit",
    "QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation": "Heath–Brown zero-frequency approximation",
    "QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction": "Heath–Brown fixed-frequency integral reduction",
    "QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds": "Heath–Brown auxiliary oscillatory bounds",
    "QuaternaryQuadraticForms.Trusted.poisson_four_dimensional": "Four-dimensional Poisson summation",
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
auxiliary_counts = Counter(r["status"] for r in status["supplementary_groups"].values())
premise_total = len(status["accepted_lean_inputs"])
premise_phrase = "premise is" if premise_total == 1 else "premises are"
premise_declaration_phrase = "premise declaration is" if premise_total == 1 else "premise declarations are"
premise_export_counts = {
    name: sum(name in entry["allowed_axioms"] for entry in status["supporting_exports"])
    for name in premise_names
}
lines = [
    "# Certification inventory", "",
    "Frozen manuscript: [quadratic_character_sums_github.tex]"
    "(manuscript/quadratic_character_sums_github.tex).", "",
    f'**{counts["Certified"]} of {numbered_total} numbered results are certified.** '
    f'{counts["Partial"]} {"is" if counts["Partial"] == 1 else "are"} partial, '
    f'{counts["Active"]} are active numbered targets, '
    f'and {counts["Pending"]} are pending.', "",
    "The [second editorial manuscript revision](certification/manuscript_revisions/2026-11-20-editorial-2.json) preserves all 42 statement texts and hashes, all source ranges and label pages, and the existing certification scope. Eleven proof blocks have punctuation or prose edits only. The manuscript fingerprints were refreshed and metadata verification passed; the fresh GitHub Actions run is separate from earlier archived execution evidence.", "",
    "## Current checkpoint: Dual-cone count and modulus partial summation", "",
    "This checkpoint supplies two prerequisites for Lemma 5.3: source_dual_cone_count gives the reciprocal Euclidean norm sum over nonzero dual-cone frequencies of norm at most U, bounded by a constant times U^(1+epsilon), and Abel partial summation bounds the inner modulus sum. Two exact supplied modules total 280 lines: DualConeCounting.lean (118 lines, one export) and ConeFrequencyAbel.lean (162 lines, three exports). The four supporting theorem exports add no literature premise. [Focused source review](certification/correspondence/oncone_prerequisites.md).", "",
    f"The live status of aux:conecount is **{status['supplementary_groups']['aux:conecount']['status']}**; Lemma 5.3 remains **{status['numbered_results']['lem:oncone']['status']}**. "
    f"The ledger contains **{len(status['supporting_exports']):,} theorem exports, {len(proof_files)} proof modules, and {len(verification_inputs)} verifier input files**, with **{premise_total} registered literature premises**. "
    f"The numbered inventory is **{counts['Certified']} Complete, {counts['Partial']} Partial, {counts['Active']} Active, {counts['Pending']} Pending**; "
    f"supplementary coverage is **{auxiliary_counts['Certified']} Certified, {auxiliary_counts['Partial']} Partial, {auxiliary_counts['Active']} Active, {auxiliary_counts['Pending']} Pending**. "
    "Acceptance and focused execution evidence are recorded in [CHECKPOINT.md](CHECKPOINT.md). Only the auxiliary dual-cone count advances; no numbered result is promoted. The mixed-sum factors, Poisson normalization, and count assembly for the bounded on-cone contribution in Lemma 5.3 remain Pending.", "",
    "## Historical checkpoint: Lemma 5.2 complete", "",
    "That checkpoint assembled the actual averaged mixed complete sums and restored the Poisson factor c_Q B^2/q^3. The source_offcone endpoint returns both source clauses with the same localization delta and cutoff r0: with U=sqrt(q)*B^eta, frequencies with norm greater than U contribute O(1), and bounded nonzero off-cone frequencies contribute O((Bq)^(1+8 eta)). Three exact supplied modules totalled 247 lines: FrequencySourceData.lean (26 lines, definition only), OffConeModulusAverage.lean (123 lines, one export), and OffConeFrequencyTheorem.lean (98 lines, two exports). No new literature premise was added. [Focused source review](certification/correspondence/offcone_completion.md).", "",
    "At that checkpoint, Lemma 5.2 became **Certified**. Its historical ledger contained **1,183 theorem exports, 281 proof modules, and 325 verifier input files**, with **12 registered literature premises**. The numbered inventory was **27 Complete, 0 Partial, 0 Active, 15 Pending**; supplementary coverage was **6 Certified, 0 Partial, 0 Active, 27 Pending**. Completion acceptance and focused execution evidence are retained in [CHECKPOINT.md](CHECKPOINT.md). That checkpoint covered both clauses of Lemma 5.2; no other numbered result or supplementary status was promoted. The bounded on-cone contribution in Lemma 5.3 remained Pending.", "",
    "## Historical checkpoint: Lemma 5.2, off-cone reduction", "",
    "That checkpoint covered supporting gcd reduction, dual-form growth bounds, and average-scale bounds for the bounded off-cone clause of Lemma 5.2. The two exact supplied modules, OffConeFrequencyReduction.lean (130 lines, four exports) and OffConeFrequencyScales.lean (91 lines, two exports), totalled 221 lines and added six supporting theorem exports and no literature premise. [Focused source review](certification/correspondence/offcone_reduction.md).", "",
    "At that checkpoint, Lemma 5.2 remained **Partial**. Its historical ledger contained **1,180 theorem exports, 278 proof modules, and 322 verifier input files**, with **12 registered literature premises**. The numbered inventory was **26 Complete, 1 Partial, 0 Active, 15 Pending**; supplementary coverage was **6 Certified, 0 Partial, 0 Active, 27 Pending**. Supporting-export acceptance and focused execution evidence are retained in [CHECKPOINT.md](CHECKPOINT.md). No numbered clause, numbered status, or supplementary status was promoted. The large-frequency O(1) clause was complete; the bounded off-cone O((Bq)^(1+8 eta)) clause remained Pending until the final averaging and normalization assembly.", "",
    "## Historical checkpoint: Lemma 5.2, large-frequency clause", "",
    "That checkpoint was limited to the first clause of Lemma 5.2: frequencies with norm greater than U contribute O(1). Three exact supplied modules (403 lines) added eight supporting theorem exports and no literature premise. [Focused source review](certification/correspondence/large_frequency_truncation.md).", "",
    "At that checkpoint, Lemma 5.2 became **Partial**. Its historical ledger contained **1,174 theorem exports, 276 proof modules, and 320 verifier input files**, with **12 registered literature premises**. The numbered inventory was **26 Complete, 1 Partial, 0 Active, 15 Pending**; supplementary coverage was **6 Certified, 0 Partial, 0 Active, 27 Pending**. First-clause acceptance and focused execution evidence are retained in [CHECKPOINT.md](CHECKPOINT.md). The bounded off-cone clause, 0 < norm(u) <= U with F*(u) nonzero and contribution O((Bq)^(1+8 eta)), remained Pending. No other numbered result was promoted.", "",
    "## Earlier auxiliary checkpoint: equation (5.5)", "",
    "That checkpoint was limited to `aux:Ipiece`: the scaled-integral estimate, smoothness in the positive scale with frequency fixed, and the common localization and cutoff. Three supplied modules added six supporting theorem exports and no literature premise. [Focused source review](certification/correspondence/scaled_frequency_integrals.md).", "",
    "That auxiliary obligation became Certified, with six Certified and 27 Pending supplementary groups and no numbered-result promotion. Its historical scope was 1,166 theorem exports, 273 proof modules, and 316 verifier inputs; the numbered inventory was 26 Complete, 0 Partial, 0 Active, and 16 Pending. The checked proof commit is [fef53391ba75](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/fef53391ba75f764ebe891441362ce73c8af6d52); execution evidence is retained in [CHECKPOINT.md](CHECKPOINT.md). Lemma 5.2 remained Pending at that checkpoint.", "",
    "## Historical proof checkpoints", "",
    "The historical Lemma 5.1 checkpoint completed with the exact source delta–Poisson identity. The original supplied weights and mixed complete sums are retained, the lattice sum has finite support, only finitely many positive moduli contribute, and each frequency series converges absolutely. The prerequisite Lemma 2.1 is already certified. General affine Poisson summation is newly registered; residue reindexing, phase signs, delta insertion, Euclidean scaling, and the final B^2/q^3 factor are internal deductions. This milestone adds 45 theorem exports in 14 modules, for totals of 1,160 exports, 270 modules, 312 inspected inputs, 12 registered literature premises, 21 mapped source groups and nine pinned dependency revisions. Numbered status is 26 Certified and 16 Pending; supplementary status remains five Certified and 28 Pending. Proposition 5.1 and its separate remaining analytic obligations are Pending. Work stops after Lemma 5.1; the counts and pending obligations in this paragraph belong to that historical checkpoint, whose execution evidence is retained in CHECKPOINT.md.", "",
    "The preceding checkpoint completed Lemma 2.3 with the literal finite set of integer zeros in the Euclidean ball. For a fixed symmetric nonsingular rational 4-by-4 matrix with nonsquare rational determinant and every epsilon>0, one positive constant precedes all real U>=1 in the U^(2+epsilon) estimate. The rational normal form, discriminant obstruction, positive denominator clearing, injective lattice map, signed-divisor fibres, and zero binary-coordinate slice are proved internally. The 28 new exports use no literature premise. The registered totals are 1,115 theorem exports, 256 project modules, 296 inspected inputs and 11 unchanged registered literature premises; the numbered inventory is 25 Certified and 17 Pending. The five Certified supplementary groups are unchanged, and aux:conecount remains Pending. Work stops after Lemma 2.3; execution evidence is recorded separately in CHECKPOINT.md.", "",
    "The preceding checkpoint completes Lemma 2.2 and aux:weight_pieces, followed by the requested return to aux:Sxi and aux:Sxibound. For a fixed symmetric nonsingular form and a smooth complex weight family with common annular support and coordinate derivative bounds, the actual integral retains the fixed Heath–Brown kernel of Lemma 2.1, the actual localized weights, and the normalized Euclidean surface integral. One localization scale and cutoff precede every weight and center; all estimate constants precede every piece, positive scale, and frequency. The cutoff and its fixed-frequency derivative apply to every piece, and all four estimates apply to the exact family whose closed support meets the zero set. Actual surface integrability is proved for this family. The normalized four-dimensional bump, reconstruction, support containment and Euclidean radius 2*delta, and uniform derivative bounds are proved internally without a literature premise. The quadratic chart, Jacobian-to-gradient identity, coordinate transport, finite constant assembly, and extension from a bounded scale range to all r>0 are also internal deductions. Six new registered inputs supply five precise Heath–Brown analytic statements and Simon's general graph area formula. The coefficient continuation adds fourteen exports in three modules and no literature premise. The combined addition is 169 exports in 27 modules, giving 1,087 exports, 247 modules, and 286 inspected inputs; there are 24 Certified and 18 Pending numbered results, no Partial or Active numbered targets, 11 literature premises across 21 mapped source groups, and five Certified and 28 Pending supplementary groups. [Integral source review](certification/correspondence/delta_integrals.md). The combined strict declaration audit, local aggregate verification, and exact-commit GitHub evidence are recorded separately in CHECKPOINT.md.", "",
    'The coefficient identity uses the original Fourier sum and the actual increasing-modulus singular series: S_xi(q)=C_q(0)/q^3 * lim_(X→∞) sum_(1<=c<=X,(c,q)=1) S_c(0)/c^4 = S_F*prod_(p|q) C_p(0)/(p^3*sigma_p). For the fixed symmetric nonsingular integral form with nonsquare determinant, the original local Fourier hypothesis gives |S_xi(q)|<=|S_F|*(4K)^omega(q)/q<=C_(F,K,epsilon)*q^(-1+epsilon). For every K>=1 and epsilon>0, one positive constant is chosen before M, chi, N, xi, D, and the positive squarefree good modulus q. The proof identifies S_F with the ordered full series at modulus one, retaining the original supplied character and proving independence from its level. It includes q=1, possible S_F=0, and only inverts good-prime densities. The original zero-frequency local bound implies |C_p(0)|<=2Kp^2 without assuming D_p(0)=0; the good-prime density gives |sigma_p^(-1)|<=2. [Coefficient source review](certification/correspondence/main_coefficient.md). The fourteen coefficient exports use only standard logical foundations.', "",
    'The preceding checkpoint completed Lemma 2.1 with the actual fixed Heath–Brown bump, sampling sum, common smooth kernel, and normalization c(Q)=Q/S(Q). One registered source-construction input supplies the cited kernel properties, unnormalized identity, and raw sampling estimate. The positive lower bound for S(Q), uniform normalization for every real Q>=3, exact c(Q)/Q^2 factor, literal unit-residue phases, and finite modulus support are proved internally. Every error constant is selected before Q and the integer frequency; a real-order j>=1 corollary follows from the integer estimate by taking a ceiling. Its 29 new theorem exports in five modules gave a historical aggregate scope of 918 exports, 220 modules, and 256 inspected inputs. That checkpoint had 23 Certified and 19 Pending numbered results, with no Partial or Active numbered targets. Five literature premises were registered across 20 mapped source-reference groups; the supplementary counts were two Certified and 31 Pending. [Complete source review](certification/correspondence/delta_symbol.md). The successful local and exact-commit GitHub verification evidence retains that historical scope in CHECKPOINT.md.', "",
    'The earlier checkpoint completed Lemma 3.11 and the separate exact complete-sum factorization aux:Cfactor. The actual original-source Fourier sums have the prescribed inverse-Euclidean-norm average, with one positive constant depending only on real E, K, and epsilon before all matrix, polynomial, weight, modulus and radius choices. The prime product and divisor expansion are proved, and three epsilon/3 factors give the exact q^epsilon. All 14 new exports in six modules passed strict type/axiom inspection and independent source review using only standard logical foundations. [Complete source review](certification/correspondence/average_frequency.md). Its historical aggregate scope was 889 exports, 215 modules, and 250 inspected inputs. Observed local and exact-commit GitHub verification results retain that scope and are recorded in CHECKPOINT.md.', "",
    'The earlier Lemma 3.10 checkpoint completed both clauses and the separately tracked epsilon consequence of Lemma 2.4. The actual Euclidean solution set is finite, its count and original inverse-norm product-indicator sum satisfy the source bounds, and one constant depends only on the real degree bound and epsilon before every matrix, modulus and polynomial choice. The 37 new exports in ten modules passed strict type/axiom inspection and independent source review; no literature premise is used. [Complete source review](certification/correspondence/congruence_box.md). Its historical aggregate scope was 875 exports, 209 modules, and 243 inspected inputs. Observed local and exact-commit GitHub verification results retain that scope and are recorded in CHECKPOINT.md.', "",
    'The earlier Lemma 2.4 checkpoint completed the literal simultaneous polynomial-congruence count in arbitrary real intervals and exact constant C(n,E)=E+...+E^n. Independent prime polynomials, every degenerate fibre, modulus one, constant polynomials, and empty intervals are covered. The 49 new theorem exports in nine modules passed strict actual-type and axiom inspection; no literature premise is used. [Complete source review](certification/correspondence/polynomial_box.md). Its historical aggregate scope was 838 exports, 199 modules, and 232 inspected inputs. Observed local and exact-commit GitHub verification results retain that scope and are recorded in CHECKPOINT.md.', "",
    'The earlier Lemma 3.9 milestone completed the ordered restricted singular series, its exact original-character Euler identity, and the uniform real-cutoff tail. Its 789-export, 190-module, 222-input aggregate scope passed local and independent GitHub verification. [Source review](certification/correspondence/singular_series.md). The earlier evidence retains that scope.', "",
    'The earlier Lemma 3.8 checkpoint completed all four clauses of Lemma 3.8. For every prime, the actual normalized zero counts modulo p^k converge to a real density, and the literal series sum_(k>=0) S_(p^k)(0)/p^(4k) converges absolutely to that density. Actual residue-digit and unit partitions prove the finite counting identity, including exponent zero, the prime two, and all bad primes. At p not dividing N_F the density equals (1-chi(p)/p²)/(1-chi(p)/p), with a proved nonzero denominator. The corrected factors (1-chi(p)/p)sigma_p retain the original supplied character and actual counting density at every bad prime. Their absolute deviations from one are summable, so the corrected product and its norm product converge, including finite zero bad factors. All 30 new exports in nine modules passed strict compilation and actual type/axiom inspection; every new export has exactly Classical.choice, Quot.sound, and propext, with no literature premise. Independent source review covers every clause and boundary. [Source correspondence review](certification/correspondence/local_density.md). Its historical aggregate scope was 707 exports, 174 modules, and 205 inputs. Aggregate and exact-proof-commit CI execution outcomes are recorded separately in CHECKPOINT.md. Earlier verification evidence retains its own scope.', "",
    "The earlier Lemma 3.7 checkpoint completed the proof for the norm of the actual unweighted complete-sum modulus sum over positive c<=X with gcd(c,q)=q₁, on the integral dual cone F*(u)=0. For each fixed symmetric nonsingular integral A with nonsquare determinant and epsilon>0, one positive constant is chosen before the positive squarefree factorization q=q₁q₂, the frequency, and every real X>=1, with (q,N_F)=1. The conclusion is C_(F,epsilon) X³(Xq)^epsilon. The actual good Jacobi coefficient is proved periodic and nonprincipal from the original nonsquare determinant, so its complete period has zero sum. Cubic cancellation, actual Möbius/totient expansion, and exact finite gcd reindexing give one divisor-count factor and one harmonic factor. Exact bad/good factorization retains cancellation in the inner good-modulus sum before the bad-prime norm bound and prime-support count are applied. Uniform divisor/logarithm power estimates finish the theorem; the stronger core removes squarefreeness. All 40 new exports in 14 modules passed strict compilation and actual type/axiom inspection: 39 have exactly Classical.choice, Quot.sound, and propext; goodQuadraticChar_coprime_four_iff has only propext. No literature premise is added or used. [Source correspondence review](certification/correspondence/cone_modulus_bound.md). Its accepted historical aggregate scope is 677 exports, 165 modules, and 195 inputs. The local and exact-proof-commit GitHub verifiers passed for that scope; CHECKPOINT.md preserves its original run and artifact metadata and immutable proof-commit report link. That evidence retains its historical 677-export scope.", "",
    "The completed Lemma 3.6 covers the actual gcd-restricted absolute modulus sum at every real X≥1 and nonzero integral dual value m. For each fixed symmetric nonsingular integral A and ε>0, one positive constant is chosen before N, the original local functions, q=q₁q₂, the frequency, and X. The conclusion retains |C_(q₂)(u)| q₁² 1_(q₁∣m) (X|m|)^ε. Actual Ramanujan prime-power recurrences and CRT give the gcd bound and repeated-prime vanishing. The actual bad/good factorization and uniform bound are transported through an injective finite factor-pair map. The prime-support count and gcd harmonic bound give a stronger intermediate factor τ(|m|)(1+log X)^(1+ω(N_F)); uniform divisor and logarithm power estimates finish the theorem. The exact zero outside q₁∣m is proved for the actual sum. The source wrapper uses the literal prime family and radical condition; no character-cancellation premise is used. All 39 new exports in 12 modules passed strict compilation and actual type/axiom inspection using only standard logical foundations. No literature premise is added or used. [Source correspondence review](certification/correspondence/generic_modulus_bound.md). Its accepted historical aggregate scope is 637 exports, 151 modules, and 180 inputs. The local and exact-proof-commit GitHub verifiers passed for that scope; the checkpoint preserves the execution evidence and immutable proof-commit report link.", "",
    "The completed Lemma 3.5 covers both clauses, with "
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
    "identities are proved using official mathlib results, so that milestone "
    "added no premise to the four earlier algebraic/geometric inputs. At that checkpoint, no numbered result "
    "remained Partial. Theorems 1.1, 1.3 and 1.4 remain Pending: the "
    "asymptotic clause of Theorem 1.3 still depends on Theorem 1.1. "
    f"The {auxiliary_total} auxiliary and supplementary groups are tracked separately: "
    f"{auxiliary_counts['Certified']} Certified, {auxiliary_counts['Partial']} Partial, "
    f"{auxiliary_counts['Active']} Active, {auxiliary_counts['Pending']} Pending; "
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
    "premises named in their ledger entry. Their actual Lean types and axiom dependencies are preserved in the "
    "[execution records](CHECKPOINT.md). "
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
    "## Continuation status", "",
    "This step stops after the dual-cone count and inner-modulus partial summation. Acceptance and focused execution evidence are recorded in the live ledger and CHECKPOINT.md.",
    f"The numbered inventory is **{counts['Certified']} Complete, {counts['Partial']} Partial, {counts['Active']} Active, {counts['Pending']} Pending**; "
    f"supplementary coverage is **{auxiliary_counts['Certified']} Certified, {auxiliary_counts['Partial']} Partial, {auxiliary_counts['Active']} Active, {auxiliary_counts['Pending']} Pending**. "
    f"The auxiliary dual-cone count is {status['supplementary_groups']['aux:conecount']['status']}. The next target is the remaining assembly of Lemma 5.3: the mixed-sum factors, Poisson normalization, and dual-cone count must be combined for the bounded on-cone contribution. Lemma 5.3 remains {status['numbered_results']['lem:oncone']['status']}. "
    "Proposition 5.1 and absolute singular-integral convergence for weights whose support contains the origin remain Pending. The whole paper is not certified.", "",
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
    if key == "EXT.MV_DIRICHLET_L" and not links:
        interfaces = (
            "Euler products, analytic continuation, and boundary continuity "
            "[supplied by official mathlib](QuaternaryQuadraticForms/SingularSeriesLFactors.lean); "
            "[source specialization and boundary assembly]"
            "(certification/correspondence/singular_series.md) proved internally; "
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
    "Ramanujan multiplicativity, source-character agreement, "
    "the global mixed-sum and dual-cone identities, and the generic delta-symbol "
    "normalization and finite-support deductions, actual normalized weight "
    "pieces and reconstruction, uniform derivative bounds, quadratic gradient "
    "and Hessian calculations, positive-root charts, surface transport, "
    "and finite-family bound assembly use only "
    "the standard logical foundations. "
    "The ledger records " + "; ".join(
        f"{premise_export_counts[name]} exports with {label}"
        for name, label in premise_names.items()
    ) + ". These counts "
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
    "The complete uniform Fourier theorem in Lemma 4.4 uses the four earlier "
    "algebraic/geometric inputs, Weil, Katz, Lang, and Bertini, through the checked "
    "results above. The given-polynomial integral "
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
    "to an integer coprime to p are kept separate. That milestone "
    "introduced no literature premise.", "",
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
    'The complete Lemma 3.8 uses none of the registered literature premises. Actual residue-digit and unit bijections, composite-modulus orthogonality, and the exact vector-lift count prove the finite density identity. The previously checked uniform complete-sum bound gives absolute convergence at every prime; continuity and uniqueness identify the complex series with the actual real counting limit. The checked prime-power evaluation and geometric series prove the good-prime formula with a nonzero denominator. The original character is retained at bad primes, and summability of the corrected-factor deviations proves absolute product convergence even when a finite bad factor is zero. All 30 new exports have exactly the standard logical foundations. No counting identity, local-density existence, internal analytic estimate, primitive-character construction, or bad-prime character replacement is assumed. The four registered premises, 20 source-reference groups, and the then-pending 33 auxiliary groups were unchanged at that historical milestone.', "",
    "The complete Lemma 3.7 uses none of the registered literature premises. Nonsquareness of the original integer determinant produces an actual Jacobi value -1, proving nonprincipality and a zero period sum for the constructed good-modulus Dirichlet character. Periodic partial sums, finite summation by parts, actual Möbius/totient identities, and exact positive-index rearrangements supply the needed cancellation. The actual bad/good CRT preserves each inner good-modulus sum, and the existing uniform bound, prime-support count, and divisor/logarithm estimates complete the source theorem. No primitive-conductor statement or internal cancellation estimate is assumed. The 40 new exports use only standard logical foundations: 39 standard triplets and one propext-only export. The four registered premises, 20 source-reference groups, and the then-pending 33 auxiliary groups were unchanged at that historical milestone.", "",
    'The complete Lemma 3.10 and aux:polynomialbox_epsilon use no literature premise. Actual prime-polynomial vanishing, integral adjugate reduction, Euclidean lattice geometry, and finite dyadic halving give both bounds with one coefficient-independent constant. All 37 new theorem exports have exactly the three standard logical foundations. The original good-prime family and literal product indicator are retained, and the real degree bound is handled by its natural ceiling. At that checkpoint one supplementary group was Certified and 32 remained Pending. The four literature premises registered at that milestone and the 20 mapped reference groups were unchanged.', "",
    'The complete Lemma 3.11 and aux:Cfactor use no literature premise. Actual source-weight Fourier sums, their previously proved CRT product, the exact exceptional-divisor expansion, and the completed inverse-Euclidean-norm estimate prove the average with coefficient and weight uniformity. All fourteen new exports use exactly Classical.choice, Quot.sound, and propext. The local stratified bound is the explicit source hypothesis of Section 3; no internal product or counting estimate is assumed in the final theorem. The exact q factorization supplies all divisor coprimality conditions, and three epsilon/3 factors preserve the prescribed q^epsilon without any U loss. The original good-prime domains, real degree bound, and modulus-one boundaries are retained. That checkpoint left two supplementary groups Certified and 31 Pending; its four registered literature premises and 20 mapped source-reference groups were unchanged.', "",
    'The complete Lemma 2.1 uses one registered Heath–Brown source-construction input about the actual fixed bump, sampling sum, and common kernel. It supplies the cited bump properties, C∞ smoothness of the kernel on x>0, global kernel size and support, unnormalized delta identity, and raw sampling estimate. The uniform positive lower bound for S(Q) on every real Q>=3, positivity and rapid approximation of c(Q)=Q/S(Q), exact c(Q)/Q^2 normalization, original unit-residue exponential phases, and finite modulus support are internal deductions. The constants are chosen before the scale and integer frequency. The positive-integer-order estimate also gives the real j>=1 corollary by a proved ceiling comparison. The same explicitly defined kernel is used in the completed Lemma 2.2; no analytic regularity or normalized identity at Q=2 is assumed. The Lemma 2.1 milestone added the fifth literature premise; its historical scope had 20 mapped reference groups and supplementary counts of two Certified and 31 Pending. The 29 new theorem exports are tracked separately from that premise in the ledger and inspected dependency table.', "",
    "The complete Lemma 2.2 retains the existing fixed-kernel input and adds five precisely registered Heath–Brown analytic statements plus Simon's general graph area formula. Localization fixes its common scale before the weight and center; all derivative sequences and H-amplitude bounds are fixed before the varying weight, auxiliary amplitude, r, and frequency. The value and derivative reductions may use different witnesses with common controls, and the actual derivative holds frequency fixed. The source estimates retain a fixed bounded positive r-range. The actual quadratic Hessian and determinant bound, the positive-root selector, Jacobian-to-gradient ratio, graph-to-surface integration, signed-coordinate transports, finite common constants, and extension to all r>0 are proved internally. The surface measure is the unit-ball-volume/2^3 normalization of mathlib's raw diameter-cubed Hausdorff measure; its identification uses the separately registered general area formula. The analytic branch contains 155 proved exports; the coefficient continuation adds fourteen, giving 169 new proved exports counted separately from the six new premise declarations. The registry now has eleven premises and 21 mapped groups; four earlier algebraic and geometric inputs keep their previous scope. The newly Certified aux:weight_pieces is proved without literature premises, including its actual bump, unit integral, reconstruction, support, and uniform derivative bounds. The coefficient identity and bound are now proved without any literature premise. The general cone-vertex integrability obligation remains Pending.", "",
    'The completed aux:Sxi and aux:Sxibound retain the actual ordered singular series and original source Fourier sums. Their prime-product identity uses an explicit bijection of prime-index representations, the existing exact Fourier product, and the proved removal of good-prime density factors. The source constant equals singularSeriesValue 1 A 0 independently of every supplied admissible character and level. This puts the final epsilon constant before M, chi, N, xi, D, and q. The local source Fourier estimate and proved inverse-density bound give the explicit |S_F|*(4K)^omega(q)/q estimate, and the previously proved fixed-base prime-factor estimate gives q^(-1+epsilon). The empty prime product, q=1, and S_F=0 are covered without dividing by the global constant or any Fourier value. All fourteen new coefficient exports use standard logical foundations; no literature premise or internal coefficient identity is assumed.', "",
    "The complete Lemma 3.6 also uses none of the registered literature premises. Actual unit-digit recurrence and CRT prove the Ramanujan gcd bound and the shared-factor vanishing. The bad/good modulus split, source weight bounds, finite factor-pair injection, prime-support count, gcd harmonic estimate, and uniform divisor/logarithm power bounds are all internal proofs. The final positive constant is chosen before N, all local functions, q,q₁,q₂,u, and X; the exact divisibility indicator is retained. The stronger one-divisor-factor proof does not assume the manuscript's local infinite series. Its 39 new exports use only standard logical foundations. The full auxiliary Ramanujan-definition agreement remains separately Pending.", "",
    "The Katz premise explicitly combines its spectral theorem and trace formula "
    "with Fulton/Stacks general hypersurface geometry, adjunction, and degree "
    "formulas. The matrix-quadric geometry, the numerical coefficient "
    "2n²−4n+4, and the final scalar norm estimate are proved internally. "
    "Every future input must likewise be listed separately from proved exports "
    "and appear explicitly in the inspected axiom dependencies.", "",
]
(ROOT / "TRUSTED_INPUTS.md").write_text("\n".join(trusted))
print("Rendered INVENTORY.md and TRUSTED_INPUTS.md")
