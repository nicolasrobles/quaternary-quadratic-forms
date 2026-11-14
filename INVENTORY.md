# Certification inventory

Frozen manuscript: v35, renamed without content changes for this repository.

**5 of 42 numbered results are certified.** 2 are partial, 0 are active numbered targets, and 35 are pending.

The current checkpoint proves the complete quadric character-sum bound in Lemma 2.7. The quadric's actual geometric smoothness and irreducibility are proved from the matrix hypotheses. A general spectral input combines Katz's theorem with explicitly registered general hypersurface geometry, adjunction, and degree formulas; the quadric coefficient and scalar norm bound are proved deductions. The earlier Lemma 2.5, Corollary 2.6, and Lemmas 4.2–4.3 remain certified. The degree-two size bound in Lemma 5.9 is now checked under actual geometric good reduction, alongside its integrality and divisibility. Its literal N_G wrappers still require a proof that the exact bad-prime set is finite, so the numbered lemma remains Partial. The weight properties, ray identity (4.5), and zero-frequency clause of Lemma 4.4 remain checked; that lemma's pointwise estimate remains pending. Both numbered lemmas remain Partial. The 33 auxiliary and supplementary groups are tracked separately; these are groups of assertions, not additional numbered results.

[Manuscript source](manuscript/quadratic_character_sums_github.tex) · [PDF](manuscript/quadratic_character_sums_github.pdf) · [Dependency graphs](DEPENDENCIES.md) · [Trusted inputs](TRUSTED_INPUTS.md) · [Live proof ledger](certification/status.json)

## Status convention

- **Pending:** no accepted complete export for the frozen statement.
- **Active:** currently being formalized; no completion is implied.
- **Partial:** explicitly identified clauses have checked exports; remaining clauses are listed.
- **Certified:** all clauses have kernel-checked proofs relative to registered literature inputs, and the statement and its dependencies have passed correspondence review.

A successful build does not change these statuses. Imported literature theorems remain explicit inputs; applying them and verifying their hypotheses are manuscript proof obligations. A generic supporting identity is not counted as a numbered result.

## Section 1

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Theorem 1.1](manuscript/quadratic_character_sums_github.tex#L320-L345) | Coefficient-uniform quadratic-character asymptotic; bad-prime height bound and local-factor bounds | Pending | Pending |
| [Theorem 1.2](manuscript/quadratic_character_sums_github.tex#L363-L370) | Uniform bound for nonzero square values on the integral quadric | Pending | Pending |
| [Theorem 1.3](manuscript/quadratic_character_sums_github.tex#L388-L400) | Exact bad-prime product and diagonal local traces/factors | Pending | Pending |
| [Theorem 1.4](manuscript/quadratic_character_sums_github.tex#L420-L439) | Coefficient-uniform asymptotic for products of local characters of exact order r | Pending | Pending |
| [Corollary 1.1](manuscript/quadratic_character_sums_github.tex#L441-L453) | Uniform count of nonzero r-th powers, r>=3 | Pending | Pending |

## Section 2

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Lemma 2.1](manuscript/quadratic_character_sums_github.tex#L615-L626) | Heath-Brown delta identity, normalization and support, for Q >= 3 | Pending | Pending |
| [Lemma 2.2](manuscript/quadratic_character_sums_github.tex#L667-L688) | Uniform localization and delta-integral estimates, including r derivative bounds | Pending | Pending |
| [Lemma 2.3](manuscript/quadratic_character_sums_github.tex#L769-L776) | O(U^(2+epsilon)) integral zeros of a nonsingular quaternary form with nonsquare rational determinant | Pending | Pending |
| [Lemma 2.4](manuscript/quadratic_character_sums_github.tex#L832-L843) | Coefficient-uniform simultaneous polynomial-congruence count for squarefree moduli, exact constant C_(n,E) | Pending | Pending |
| [Lemma 2.5](manuscript/quadratic_character_sums_github.tex#L908-L915) | Weil bound (m-1) sqrt(p) for a nonprincipal character and a degree-m polynomial with simple geometric roots | Certified | [`QuaternaryQuadraticForms.weil_bound`](QuaternaryQuadraticForms/WeilBound.lean) |
| [Corollary 2.6](manuscript/quadratic_character_sums_github.tex#L926-L933) | Projective-line character-sum bound (n-1) sqrt(p)+1 | Certified | [`QuaternaryQuadraticForms.projective_weil_bound`](QuaternaryQuadraticForms/ProjectiveWeil.lean) |
| [Lemma 2.7](manuscript/quadratic_character_sums_github.tex#L951-L964) | Quadric character-sum bound (2n^2-4n+4)p under smooth branch divisor | Certified | [`QuaternaryQuadraticForms.katz_quadric_bound`](QuaternaryQuadraticForms/KatzBound.lean) |

## Section 3

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Lemma 3.1](manuscript/quadratic_character_sums_github.tex#L1048-L1056) | CRT multiplicativity of complete sums and invariance under unit scaling of frequency | Pending | Pending |
| [Lemma 3.2](manuscript/quadratic_character_sums_github.tex#L1092-L1108) | Prime-power quadratic Gauss evaluation, unramified complete sum, and projective quadric point count | Pending | Pending |
| [Lemma 3.3](manuscript/quadratic_character_sums_github.tex#L1156-L1161) | Uniform bound \|S_c(u)\| <= 4 sqrt(\|alpha\|) c^3, including bad primes | Pending | Pending |
| [Lemma 3.4](manuscript/quadratic_character_sums_github.tex#L1184-L1190) | Exact shared-prime identity for S_(p,p^k)(u) | Pending | Pending |
| [Lemma 3.5](manuscript/quadratic_character_sums_github.tex#L1240-L1252) | Global good-modulus formula and dual-cone ratio, including bad-prime factors in c | Pending | Pending |
| [Lemma 3.6](manuscript/quadratic_character_sums_github.tex#L1292-L1300) | Off-dual-cone absolute sum over c, retaining q1 \| F*(u) | Pending | Pending |
| [Lemma 3.7](manuscript/quadratic_character_sums_github.tex#L1348-L1354) | Cancellation bound for unweighted complete sums on the dual cone, with (c,q)=q1 | Pending | Pending |
| [Lemma 3.8](manuscript/quadratic_character_sums_github.tex#L1410-L1420) | Existence and series expression of local densities; explicit good-prime factor; absolute corrected Euler-product convergence | Pending | Pending |
| [Lemma 3.9](manuscript/quadratic_character_sums_github.tex#L1446-L1457) | Convergence, Euler-factor identity and uniform tail of the singular series excluding primes dividing q | Pending | Pending |
| [Lemma 3.10](manuscript/quadratic_character_sums_github.tex#L1539-L1552) | Exceptional congruence count in four variables and its inverse-norm-weighted form | Pending | Pending |
| [Lemma 3.11](manuscript/quadratic_character_sums_github.tex#L1569-L1576) | Average Fourier bound over exceptional frequencies with divisibility by q1 | Pending | Pending |

## Section 4

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Lemma 4.1](manuscript/quadratic_character_sums_github.tex#L1615-L1632) | Polynomial bound for bad-prime product and uniformly bounded-degree exceptional plane locus | Pending | Pending |
| [Lemma 4.2](manuscript/quadratic_character_sums_github.tex#L1712-L1724) | Uniform conic parametrization by binary quadratics over every extension field, with independent derivative vectors | Certified | [`QuaternaryQuadraticForms.conic_parametrization`](QuaternaryQuadraticForms/ConicParametrization.lean) |
| [Lemma 4.3](manuscript/quadratic_character_sums_github.tex#L1756-L1765) | Transverse plane-section character-sum bound (2n-1) sqrt(p)+1 | Certified | [`QuaternaryQuadraticForms.plane_section_bound`](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) |
| [Lemma 4.4](manuscript/quadratic_character_sums_github.tex#L1796-L1808) | Coefficient-uniform Fourier bounds with exceptional-locus term and exact zero-frequency projective identity | Partial | [`QuaternaryQuadraticForms.polynomialCharacterWeight_properties`](QuaternaryQuadraticForms/PolynomialWeights.lean); [`QuaternaryQuadraticForms.fourierSum_zero`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.fourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.integralFourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.integralFourierSum_of_dvd`](QuaternaryQuadraticForms/FourierRays.lean) |
| [Lemma 4.5](manuscript/quadratic_character_sums_github.tex#L1862-L1866) | Exact bad-prime criterion for diagonal quadratic G and N_G=rad(2 alpha M) | Pending | Pending |
| [Lemma 4.6](manuscript/quadratic_character_sums_github.tex#L1897-L1908) | Exact diagonal Fourier pencil formula, projective trace formula and generic 2p^(3/2)+4p bound | Pending | Pending |

## Section 5

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Proposition 5.1](manuscript/quadratic_character_sums_github.tex#L2030-L2039) | Uniform weighted asymptotic for abstract projectively invariant local functions | Pending | Pending |
| [Lemma 5.1](manuscript/quadratic_character_sums_github.tex#L2045-L2054) | Delta-symbol and Poisson identity with finite modulus sum and absolute frequency convergence | Pending | Pending |
| [Lemma 5.2](manuscript/quadratic_character_sums_github.tex#L2126-L2130) | Frequency truncation and off-dual-cone contribution | Pending | Pending |
| [Lemma 5.3](manuscript/quadratic_character_sums_github.tex#L2185-L2188) | Nonzero dual-cone contribution with cancellation in the modulus | Pending | Pending |
| [Lemma 5.4](manuscript/quadratic_character_sums_github.tex#L2234-L2239) | Zero-frequency main term and uniform error | Pending | Pending |
| [Lemma 5.5](manuscript/quadratic_character_sums_github.tex#L2313-L2321) | Uniform asymptotic for bounded families of annular weights | Pending | Pending |
| [Lemma 5.6](manuscript/quadratic_character_sums_github.tex#L2429-L2453) | Uniform general character-sum asymptotic and explicit local factors | Pending | Pending |
| [Corollary 5.7](manuscript/quadratic_character_sums_github.tex#L2543-L2552) | Centered quadratic-character product has no main term | Pending | Pending |
| [Lemma 5.8](manuscript/quadratic_character_sums_github.tex#L2582-L2591) | Square and power sieve with coefficient height retained | Pending | Pending |
| [Lemma 5.9](manuscript/quadratic_character_sums_github.tex#L2686-L2690) | Quadratic local trace is integral, divisible by p, and bounded by4p | Partial | [`QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.projectiveQuadraticTrace_abs_le`](QuaternaryQuadraticForms/QuadraticTraceBound.lean); [`QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd_bound`](QuaternaryQuadraticForms/QuadraticTraceBound.lean); [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_abs_le`](QuaternaryQuadraticForms/QuadraticTraceBound.lean); [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound`](QuaternaryQuadraticForms/QuadraticTraceBound.lean); [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd_bound_of_modulus`](QuaternaryQuadraticForms/QuadraticTraceBound.lean); [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) |
| [Lemma 5.10](manuscript/quadratic_character_sums_github.tex#L2710-L2722) | Lower bounds for nonzero local factors using integrality and cyclotomic norms | Pending | Pending |
| [Corollary 5.11](manuscript/quadratic_character_sums_github.tex#L2753-L2768) | Relative asymptotics in quadratic/general/cyclic cases | Pending | Pending |

## Section 6

| Result | Content | Status | Checked export |
|---|---|---|---|
| [Proposition 6.1](manuscript/quadratic_character_sums_github.tex#L2798-L2806) | Determinant-method bound for degree-r power values with explicit coefficient height | Pending | Pending |

## Correspondence reviews for certified numbered results

### Lemma 2.5

[Statement correspondence review](certification/correspondence/weil_input.md)

All clauses match the exact registered cited input EXT.WEIL. This is source-relative certification, not a reproof of the published Weil estimate.

### Corollary 2.6

[Statement correspondence review](certification/correspondence/projective_weil.md)

Complete bound for the actual projective-line sum. The charts, dehomogenization, degree drop, distinct-root condition, and contribution at infinity are proved; only EXT.WEIL is an external premise.

### Lemma 2.7

[Statement correspondence review](certification/correspondence/katz_quadric.md)

Complete Lemma 2.7 for the actual projective trace under the literal geometric rank-two condition. Quadric smoothness, geometric polynomial irreducibility, nonvanishing, the exact Chern coefficient, and the scalar norm estimate are proved internally. The registered composite input combines Katz spectral data with the separately attributed general hypersurface geometry, adjunction, and degree formulas.

### Lemma 4.2

[Statement correspondence review](certification/correspondence/conic_parametrization.md)

Both clauses are proved for one tuple of literal binary quadratic forms chosen over F_p before quantifying over every extension field. The projective bijection, independent formal derivatives, normal form, and scalar extension are constructed from the manuscript hypotheses. No external mathematical premise is used.

### Lemma 4.3

[Statement correspondence review](certification/correspondence/plane_section.md)

Complete bound for the actual projective plane-section sum under the literal geometric rank-three condition. Parametrization, nonvanishing, and the 2n distinct geometric roots are derived internally, including when p divides 2n. Only the previously registered EXT.WEIL premise is used.

## Scope of partially checked numbered results

### Lemma 4.4

[Statement correspondence review](certification/correspondence/fourier_rays.md)

Checked clauses:

- All three weight conditions in (3.1), with literal polynomial evaluation and multiplicative characters.
- The exact zero-frequency identity in (4.4).
- The complete intermediate ray identity (4.5), including integral coefficient and frequency reduction.

Remaining clauses:

- The coefficient-uniform pointwise estimate in (4.4), including the exceptional polynomial D_p and all generic and exceptional frequency cases.

Lemmas 2.7 and 4.3 now supply the global and transverse plane-section trace bounds. The exceptional polynomial from Lemma 4.1, the remaining exceptional-frequency counting, and the assembly of the full bound are still pending. None has been imported as a replacement axiom.

### Lemma 5.9

[Statement correspondence review](certification/correspondence/quadratic_trace.md)

Checked clauses:

- The projective quadratic-character trace a_p(G) is an integer, identified explicitly with the existing complex-valued trace.
- The odd prime p divides that actual integer trace, for both finite-field forms and reductions of the manuscript's integral coefficients.
- The bound |a_p(G)| ≤ 4p under the literal geometric good-reduction hypothesis, by the proved degree-two Katz specialization.
- The combined integrality, divisibility, and size conclusions under p not dividing the literal N_G, with finiteness of its actual bad-prime set still explicit.

Remaining clauses:

- Derive finiteness of the actual bad-reduction prime set from the manuscript's characteristic-zero smoothness hypothesis, via the elimination deduction in Lemma 4.1(i), and discharge that explicit argument in the N_G wrapper.

The divisibility proof needs only an odd prime and a homogeneous quadratic G. The size bound now follows from the completed Lemma 2.7. The exact N_G arithmetic is proved, but its finite-set argument has not yet been derived from characteristic-zero smoothness. That internal finiteness deduction is not a trusted input; Lemma 5.9 remains Partial.

## Checked exports and supporting declarations

| Export | Precise scope | Status |
|---|---|---|
| [`QuaternaryQuadraticForms.weighted_ray_sum`](QuaternaryQuadraticForms/RayAlgebra.lean) | Final finite-ring algebra combining evaluated ray contributions. | Checked locally |
| [`QuaternaryQuadraticForms.primitiveAddChar_units_sum`](QuaternaryQuadraticForms/FiniteCharacters.lean) | Primitive additive-character sum over the actual nonzero scalars of a finite field. | Checked locally |
| [`QuaternaryQuadraticForms.stdAddChar_units_sum`](QuaternaryQuadraticForms/FiniteCharacters.lean) | Standard complex additive character over F_p: the unit sum is p-1 at zero and -1 otherwise. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveRayVector_injective`](QuaternaryQuadraticForms/ProjectiveRays.lean) | The map (P,t) to t times the representative is injective for actual projective points and field units. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveRayVector_surjective`](QuaternaryQuadraticForms/ProjectiveRays.lean) | Every nonzero vector is a nonzero scalar multiple of a representative of its projective class. | Checked locally |
| [`QuaternaryQuadraticForms.invariant_rep_mk`](QuaternaryQuadraticForms/ProjectiveRays.lean) | A scalar-invariant function takes the same value on a vector and the chosen representative of its projective class. | Checked locally |
| [`QuaternaryQuadraticForms.cone_rep_mk`](QuaternaryQuadraticForms/ProjectiveRays.lean) | Membership of a scalar-stable cone is independent of projective representative. | Checked locally |
| [`QuaternaryQuadraticForms.sum_cone_weighted_eq_sum_projective`](QuaternaryQuadraticForms/ProjectiveRays.lean) | Actual affine-cone sum decomposed into projective points and nonzero scalars; partition proved from the quotient. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneous_eval_smul`](QuaternaryQuadraticForms/PolynomialWeights.lean) | Polynomial evaluation obeys G(tx)=t^n G(x), proved from homogeneity and monomial expansion. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneous_reduce_mod`](QuaternaryQuadraticForms/PolynomialWeights.lean) | Coefficient reduction of an integral homogeneous polynomial preserves its degree of homogeneity. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialCharacterWeight_properties`](QuaternaryQuadraticForms/PolynomialWeights.lean) | All three clauses of (3.1) for the literal weight psi(G(x)), including zero, norm and scalar invariance. | Checked locally |
| [`QuaternaryQuadraticForms.mem_projectiveQuadric_mk`](QuaternaryQuadraticForms/FourierRays.lean) | Projective-quadric membership is equivalent to the actual equation x^T A x=0 on any nonzero representative. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveWeight_rep_mk`](QuaternaryQuadraticForms/FourierRays.lean) | The polynomial character weight is well-defined on actual projective points. | Checked locally |
| [`QuaternaryQuadraticForms.hyperplane_rep_mk`](QuaternaryQuadraticForms/FourierRays.lean) | The condition u dot x=0 defining the projective section is independent of representative. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean) | The literal finite-field Fourier sum equals p*a_u-a for every reduced frequency, with a_0=a. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_zero`](QuaternaryQuadraticForms/FourierRays.lean) | Exact zero-frequency clause C_p(0)=(p-1)*a of Lemma 4.4; no Fourier estimate claimed. | Checked locally |
| [`QuaternaryQuadraticForms.reduceFrequency_eq_zero_iff`](QuaternaryQuadraticForms/FourierRays.lean) | An integral frequency reduces to zero exactly when p divides each of its four coordinates. | Checked locally |
| [`QuaternaryQuadraticForms.integralFourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean) | Equation (4.5) for integral matrix and polynomial coefficients and integral frequencies, after proved homogeneous reduction. | Checked locally |
| [`QuaternaryQuadraticForms.integralFourierSum_of_dvd`](QuaternaryQuadraticForms/FourierRays.lean) | The p-divides-u clause of (4.5), with explicit coordinatewise integer divisibility. | Checked locally |
| [`QuaternaryQuadraticForms.complexQuadraticChar_apply`](QuaternaryQuadraticForms/QuadraticCharacter.lean) | The complex quadratic character is the cast of the actual integer-valued character. | Checked locally |
| [`QuaternaryQuadraticForms.complexQuadraticChar_isQuadratic`](QuaternaryQuadraticForms/QuadraticCharacter.lean) | The complex quadratic character has values in 0, 1 and -1. | Checked locally |
| [`QuaternaryQuadraticForms.complexQuadraticChar_sq`](QuaternaryQuadraticForms/QuadraticCharacter.lean) | The square of the complex quadratic character is principal, with the correct zero-extension. | Checked locally |
| [`QuaternaryQuadraticForms.complexQuadraticChar_ne_one`](QuaternaryQuadraticForms/QuadraticCharacter.lean) | Nonprincipality of the actual complex quadratic character for odd primes. | Checked locally |
| [`QuaternaryQuadraticForms.complexQuadraticChar_intCast`](QuaternaryQuadraticForms/QuadraticCharacter.lean) | Agreement with the Legendre symbol on integer arguments. | Checked locally |
| [`QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial`](QuaternaryQuadraticForms/MatrixPolynomial.lean) | Evaluation of the explicit polynomial sum A_ij X_i X_j is x dot A*x. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_homogeneous`](QuaternaryQuadraticForms/MatrixPolynomial.lean) | The explicit matrix quadratic polynomial is homogeneous of degree two. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree_le`](QuaternaryQuadraticForms/MatrixPolynomial.lean) | The matrix quadratic polynomial has total degree at most two, including degenerate reductions. | Checked locally |
| [`QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial_quadraticValue`](QuaternaryQuadraticForms/MatrixPolynomial.lean) | Exact identification with the existing quaternary quadraticValue definition. | Checked locally |
| [`QuaternaryQuadraticForms.quadraticZeroIndicator_eval`](QuaternaryQuadraticForms/AffineDivisibility.lean) | The polynomial 1-F^(p-1) evaluates to the indicator of F=0 on the prime field. | Checked locally |
| [`QuaternaryQuadraticForms.quadraticCharacterPolynomial_sum_zero`](QuaternaryQuadraticForms/AffineDivisibility.lean) | The actual polynomial (1-F^(p-1))*G^(p/2) has zero sum over the four-dimensional prime field, by a proved strict degree bound. | Checked locally |
| [`QuaternaryQuadraticForms.affineQuadraticCharacterSum_dvd`](QuaternaryQuadraticForms/AffineDivisibility.lean) | The odd prime divides the integer quadratic-character sum on the affine zero set of a polynomial of degree at most two. | Checked locally |
| [`QuaternaryQuadraticForms.quadraticTraceWeight_rep_mk`](QuaternaryQuadraticForms/QuadraticTrace.lean) | The integer-valued quadratic weight is independent of projective representative for homogeneous quadratic G. | Checked locally |
| [`QuaternaryQuadraticForms.affineQuadraticTrace_complex`](QuaternaryQuadraticForms/QuadraticTrace.lean) | The complex cast of the actual integer affine trace equals the existing zero-frequency Fourier sum. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveQuadraticTrace_complex`](QuaternaryQuadraticForms/QuadraticTrace.lean) | The complex projective trace equals the cast of the actual integer projective sum. | Checked locally |
| [`QuaternaryQuadraticForms.affineQuadraticTrace_eq`](QuaternaryQuadraticForms/QuadraticTrace.lean) | The exact integer identity C=(p-1)*a, obtained from the checked Fourier ray identity and injective complex cast. | Checked locally |
| [`QuaternaryQuadraticForms.affineQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) | Affine divisibility for the literal matrix expression x^T A x. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) | The odd prime divides the actual integer-valued projective quadratic trace. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) | An explicit integer witness identifies the complex trace and proves divisibility; these are the completed clauses of Lemma 5.9. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) | Divisibility of the actual integer projective trace after reducing integral matrix and quadratic-form coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) | Source-level integrality and divisibility of the complex trace for the manuscript's integral coefficient data, with an explicit integer witness. | Checked locally |
| [`QuaternaryQuadraticForms.binaryVector_eq_vec`](QuaternaryQuadraticForms/ProjectiveLine.lean) | Agreement of the literal binary-vector definition with two-coordinate vector notation. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLinePoint_injective`](QuaternaryQuadraticForms/ProjectiveLine.lean) | Distinct affine points and infinity give distinct actual projective-line points. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLinePoint_surjective`](QuaternaryQuadraticForms/ProjectiveLine.lean) | Every actual projective-line point has an affine representative (z,1) or the representative (1,0). | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLinePoint_weight`](QuaternaryQuadraticForms/ProjectiveLine.lean) | A scalar-invariant weight on projective representatives equals its value on the standard chart representatives. | Checked locally |
| [`QuaternaryQuadraticForms.sum_projectiveLine`](QuaternaryQuadraticForms/ProjectiveLine.lean) | The actual projective-line sum is the affine-chart sum plus its value at infinity. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLinePoint_predicate`](QuaternaryQuadraticForms/ProjectiveLine.lean) | A scalar-stable zero condition is equivalent on chosen and standard chart representatives. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_eval`](QuaternaryQuadraticForms/BinaryForms.lean) | Evaluation of the literal substitution g(X,1) agrees with evaluation of the binary form at (z,1). | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_map`](QuaternaryQuadraticForms/BinaryForms.lean) | Dehomogenization commutes with coefficient extension. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_homogenize`](QuaternaryQuadraticForms/BinaryForms.lean) | Homogenizing the affine polynomial to the original homogeneous degree recovers the literal binary form. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_ne_zero`](QuaternaryQuadraticForms/BinaryForms.lean) | A nonzero homogeneous binary form has a nonzero affine polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_natDegree_le`](QuaternaryQuadraticForms/BinaryForms.lean) | The affine degree is at most the homogeneous degree. | Checked locally |
| [`QuaternaryQuadraticForms.homogenize_eval_infinity`](QuaternaryQuadraticForms/BinaryForms.lean) | Evaluation of a homogenization at (1,0) is the corresponding top coefficient. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_coeff_top`](QuaternaryQuadraticForms/BinaryForms.lean) | The degree-n affine coefficient is exactly the binary form value at infinity. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_natDegree_eq_iff`](QuaternaryQuadraticForms/BinaryForms.lean) | For a nonzero homogeneous form, affine degree n is equivalent to nonvanishing at infinity. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_natDegree_lt_of_infinity_zero`](QuaternaryQuadraticForms/BinaryForms.lean) | Vanishing at infinity strictly lowers the affine degree of a nonzero homogeneous form. | Checked locally |
| [`QuaternaryQuadraticForms.rootSet_card_le_natDegree`](QuaternaryQuadraticForms/GeometricRoots.lean) | The actual distinct root count over any field extension is at most the polynomial degree. | Checked locally |
| [`QuaternaryQuadraticForms.geometricRootCount_eq_natDegree_iff`](QuaternaryQuadraticForms/GeometricRoots.lean) | For a nonzero polynomial, full distinct-root count over the algebraic closure is equivalent to separability. | Checked locally |
| [`QuaternaryQuadraticForms.geometricRootCount_eq_natDegree`](QuaternaryQuadraticForms/GeometricRoots.lean) | A separable polynomial has degree-many distinct geometric roots. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneous_binary_zero_units_smul`](QuaternaryQuadraticForms/BinaryFormRoots.lean) | The zero condition of a homogeneous binary form is independent of nonzero scalar representatives. | Checked locally |
| [`QuaternaryQuadraticForms.binaryProjectiveZeros_card`](QuaternaryQuadraticForms/BinaryFormRoots.lean) | The literal projective zero count is the affine distinct-root count plus the possible point at infinity. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_degree_and_rootCount`](QuaternaryQuadraticForms/BinaryFormRoots.lean) | For n distinct projective zeros, the affine degree is n or n-1 according to infinity, is positive, and equals its distinct-root count. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_geometric_data`](QuaternaryQuadraticForms/BinaryFormRoots.lean) | The manuscript geometric-root hypothesis implies every affine polynomial hypothesis of the univariate Weil input. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_geometric_separable`](QuaternaryQuadraticForms/BinaryFormRoots.lean) | The affine polynomial is separable, derived from the literal projective geometric zeros. | Checked locally |
| [`QuaternaryQuadraticForms.weil_bound`](QuaternaryQuadraticForms/WeilBound.lean) | Lemma 2.5 with its explicit degree parameter and distinct geometric roots; exact specialization of the registered literature input. | Checked locally |
| [`QuaternaryQuadraticForms.weil_bound_of_separable`](QuaternaryQuadraticForms/WeilBound.lean) | The univariate character-sum bound after proving the geometric root-count condition from separability. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLineCharacterSum_chart`](QuaternaryQuadraticForms/ProjectiveWeil.lean) | The literal projective character sum splits into the value at infinity and the sum of the literal affine polynomial character weight. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveLineCharacterSum_bound_of_affine_roots`](QuaternaryQuadraticForms/ProjectiveWeil.lean) | The norm estimate after the affine root hypotheses have been checked, using the triangle inequality and the degree bound. | Checked locally |
| [`QuaternaryQuadraticForms.projective_weil_bound`](QuaternaryQuadraticForms/ProjectiveWeil.lean) | Complete Corollary 2.6 under the literal binary-form and distinct geometric projective-root hypotheses. | Checked locally |
| [`QuaternaryQuadraticForms.pderiv_aeval_chain_rule`](QuaternaryQuadraticForms/PolynomialChainRule.lean) | The algebraic chain rule for a finite tuple of polynomial substitutions. | Checked locally |
| [`QuaternaryQuadraticForms.eval_aeval_polynomial`](QuaternaryQuadraticForms/PolynomialChainRule.lean) | Evaluation commutes with polynomial substitution. | Checked locally |
| [`QuaternaryQuadraticForms.eval_pderiv_aeval_chain_rule`](QuaternaryQuadraticForms/PolynomialChainRule.lean) | The chain rule evaluated at a point. | Checked locally |
| [`QuaternaryQuadraticForms.mem_planeSubspace`](QuaternaryQuadraticForms/QuadraticPlane.lean) | Membership in the actual hyperplane is exactly the zero dot-product condition. | Checked locally |
| [`QuaternaryQuadraticForms.matrixBilin_isSymm`](QuaternaryQuadraticForms/QuadraticPlane.lean) | A symmetric matrix gives a symmetric bilinear form. | Checked locally |
| [`QuaternaryQuadraticForms.matrix_mulVec_adjugate`](QuaternaryQuadraticForms/QuadraticPlane.lean) | Multiplication by the matrix cancels its adjugate up to the determinant. | Checked locally |
| [`QuaternaryQuadraticForms.adjugate_bilin_self`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The adjugate normal has nonzero self-pairing under the dual-form hypothesis. | Checked locally |
| [`QuaternaryQuadraticForms.planeSubspace_eq_orthogonal`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The geometric plane is the orthogonal complement of the adjugate normal. | Checked locally |
| [`QuaternaryQuadraticForms.plane_bilin_nondegenerate`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The restriction to the plane section is nondegenerate. | Checked locally |
| [`QuaternaryQuadraticForms.planeFunctional_ne_zero`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The dual-form hypothesis makes the hyperplane functional nonzero. | Checked locally |
| [`QuaternaryQuadraticForms.planeSubspace_finrank`](QuaternaryQuadraticForms/QuadraticPlane.lean) | A nonzero hyperplane in four-space has dimension three. | Checked locally |
| [`QuaternaryQuadraticForms.eval_planePolynomial`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The actual linear plane polynomial evaluates to the dot product with the normal. | Checked locally |
| [`QuaternaryQuadraticForms.planePolynomial_totalDegree_le`](QuaternaryQuadraticForms/QuadraticPlane.lean) | The plane polynomial has total degree at most one. | Checked locally |
| [`QuaternaryQuadraticForms.plane_exists_isotropic`](QuaternaryQuadraticForms/QuadraticPlane.lean) | Chevalley--Warning produces an actual nonzero isotropic point in every four-variable quadratic hyperplane section over a prime field. | Checked locally |
| [`QuaternaryQuadraticForms.exists_hyperbolic_partner`](QuaternaryQuadraticForms/ConicNormalForm.lean) | Normalize an isotropic partner so that the mixed quadratic coefficient is one. | Checked locally |
| [`QuaternaryQuadraticForms.exists_common_orthogonal`](QuaternaryQuadraticForms/ConicNormalForm.lean) | In dimension three, two linear orthogonality conditions have a nonzero solution. | Checked locally |
| [`QuaternaryQuadraticForms.hyperbolic_triple_linearIndependent`](QuaternaryQuadraticForms/ConicNormalForm.lean) | An isotropic hyperbolic pair and a nonzero common orthogonal vector are linearly independent. | Checked locally |
| [`QuaternaryQuadraticForms.exists_ternary_hyperbolic_coordinates`](QuaternaryQuadraticForms/ConicNormalForm.lean) | A nondegenerate ternary form with an isotropic vector admits the exact hyperbolic normal form used in the conic parametrization. | Checked locally |
| [`QuaternaryQuadraticForms.plane_exists_hyperbolic_coordinates`](QuaternaryQuadraticForms/ConicNormalForm.lean) | The actual prime-field plane section has the required hyperbolic coordinates. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_apply_map`](QuaternaryQuadraticForms/ScalarExtension.lean) | The extended linear map agrees with coefficient extension on base-field vectors. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_comp`](QuaternaryQuadraticForms/ScalarExtension.lean) | Scalar extension of finite coordinate maps preserves composition. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_id`](QuaternaryQuadraticForms/ScalarExtension.lean) | Scalar extension preserves the identity coordinate map. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_injective`](QuaternaryQuadraticForms/ScalarExtension.lean) | An injective coordinate map remains injective over every extension field. | Checked locally |
| [`QuaternaryQuadraticForms.eval_coordinatePolynomial`](QuaternaryQuadraticForms/ScalarExtension.lean) | The coordinate polynomial evaluates to the corresponding component of the linear map. | Checked locally |
| [`QuaternaryQuadraticForms.coordinatePolynomial_homogeneous`](QuaternaryQuadraticForms/ScalarExtension.lean) | Each coordinate polynomial of a linear map is homogeneous of degree one. | Checked locally |
| [`QuaternaryQuadraticForms.coordinatePolynomial_map`](QuaternaryQuadraticForms/ScalarExtension.lean) | Mapping coefficients of the coordinate polynomial gives the coordinate polynomial of the extended map. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_mem_plane`](QuaternaryQuadraticForms/ScalarExtension.lean) | Extension of coefficients preserves the equation defining the plane. | Checked locally |
| [`QuaternaryQuadraticForms.planeSubspace_finrank_of_ne_zero`](QuaternaryQuadraticForms/ScalarExtension.lean) | The actual hyperplane has dimension three over any field. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_range_plane`](QuaternaryQuadraticForms/ScalarExtension.lean) | An injective three-coordinate parametrization of a hyperplane spans that same hyperplane after every extension of coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.map_aeval_polynomial`](QuaternaryQuadraticForms/ScalarExtension.lean) | Polynomial substitution commutes with extension of all coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_map`](QuaternaryQuadraticForms/ScalarExtension.lean) | The literal matrix quadratic polynomial commutes with coefficient extension. | Checked locally |
| [`QuaternaryQuadraticForms.extendCoordinateMap_quadratic`](QuaternaryQuadraticForms/ScalarExtension.lean) | The ternary normal-form identity is a polynomial identity and therefore persists over every field extension, including infinite extensions. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicVector_smul`](QuaternaryQuadraticForms/ConicCharts.lean) | The canonical binary quadratic vector scales by the square of the scalar. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicVector_ne_zero`](QuaternaryQuadraticForms/ConicCharts.lean) | The canonical quadratic vector is nonzero at every nonzero binary parameter. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicValue_vector`](QuaternaryQuadraticForms/ConicCharts.lean) | The canonical quadratic vector lies on the literal ternary conic. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicValue_smul`](QuaternaryQuadraticForms/ConicCharts.lean) | The ternary conic polynomial scales quadratically. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicValue_units_zero_iff`](QuaternaryQuadraticForms/ConicCharts.lean) | The conic equation is invariant under multiplication by a field unit. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicProjective_mk`](QuaternaryQuadraticForms/ConicCharts.lean) | The projective map agrees with the literal formula on any representative. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPoint_injective`](QuaternaryQuadraticForms/ConicCharts.lean) | Distinct projective parameters give distinct points of the conic. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicVector_surjective_projective`](QuaternaryQuadraticForms/ConicCharts.lean) | Every nonzero zero of the ternary form is a scalar multiple of a parametrized vector. This statement works over an arbitrary field. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPoint_surjective`](QuaternaryQuadraticForms/ConicCharts.lean) | Every actual projective zero lies in the parametrization. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConic_derivatives_independent`](QuaternaryQuadraticForms/ConicCharts.lean) | The two explicit tangent vectors are independent away from the origin in characteristic different from two. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_eval`](QuaternaryQuadraticForms/ConicPolynomials.lean) | Evaluation recovers the literal quadratic parametrization. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_homogeneous`](QuaternaryQuadraticForms/ConicPolynomials.lean) | Each coordinate polynomial is homogeneous of degree two. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_partial_s`](QuaternaryQuadraticForms/ConicPolynomials.lean) | The evaluated first partials are the explicit first tangent vector. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_partial_t`](QuaternaryQuadraticForms/ConicPolynomials.lean) | The evaluated second partials are the explicit second tangent vector. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_partials_independent`](QuaternaryQuadraticForms/ConicPolynomials.lean) | The actual polynomial partial derivatives are independent at every nonzero parameter, provided the characteristic is not two. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomials_map`](QuaternaryQuadraticForms/ConicPolynomials.lean) | Coefficient extension gives the same three coordinate forms over any extension field. | Checked locally |
| [`QuaternaryQuadraticForms.BinaryNonsingular.ne_zero`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Nonsingularity excludes the zero polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_derivative`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Differentiation in the affine variable commutes with dehomogenization. | Checked locally |
| [`QuaternaryQuadraticForms.binary_euler_eval`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Euler's identity for a binary form, evaluated at an arbitrary vector. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_euler`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Euler's identity after the literal affine substitution. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_derivative_ne_zero`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | A nonsingular binary form has no repeated root in its affine chart. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_separable_of_nonsingular`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Over an algebraically closed field, the affine polynomial is separable. | Checked locally |
| [`QuaternaryQuadraticForms.coeff_X_mul_derivative`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | The coefficient of `X f'` at degree `m` is `m` times the coefficient of `f`. | Checked locally |
| [`QuaternaryQuadraticForms.binaryDehom_degree_of_nonsingular_infinity`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | A nonsingular zero at infinity decreases the affine degree by exactly one. | Checked locally |
| [`QuaternaryQuadraticForms.binaryProjectiveZeros_card_of_nonsingular`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | A homogeneous nonsingular binary form over an algebraically closed field has exactly its degree many distinct projective zeros. | Checked locally |
| [`QuaternaryQuadraticForms.binary_nonsingular_geometric_roots`](QuaternaryQuadraticForms/BinaryNonsingular.lean) | The exact geometric-root hypothesis of Corollary 2.6 follows from the absence of a nonzero geometric common zero of the form and its partial derivatives. | Checked locally |
| [`QuaternaryQuadraticForms.independent_three_two_dot_impossible`](QuaternaryQuadraticForms/TransversePullback.lean) | Three independent covectors in four-space cannot annihilate two independent vectors. The covectors here are identified using the actual dot product. | Checked locally |
| [`QuaternaryQuadraticForms.pderiv_planePolynomial`](QuaternaryQuadraticForms/TransversePullback.lean) | Each partial derivative of the plane polynomial is its corresponding coefficient. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialGradient_plane`](QuaternaryQuadraticForms/TransversePullback.lean) | The gradient of the actual plane polynomial is its normal vector. | Checked locally |
| [`QuaternaryQuadraticForms.eval_pderiv_pullback`](QuaternaryQuadraticForms/TransversePullback.lean) | The evaluated polynomial chain rule as a dot product of actual vectors. | Checked locally |
| [`QuaternaryQuadraticForms.transverse_pullback_nonsingular`](QuaternaryQuadraticForms/TransversePullback.lean) | Transversality and the independent derivatives of a genuine conic parametrization imply that its polynomial pullback has no projective singular zero. | Checked locally |
| [`QuaternaryQuadraticForms.rank_three_iff_linearIndependent`](QuaternaryQuadraticForms/TransversalityRank.lean) | A three-row matrix over a field has rank three exactly when its rows are linearly independent. | Checked locally |
| [`QuaternaryQuadraticForms.planeTransverseRank_iff`](QuaternaryQuadraticForms/TransversalityRank.lean) | The source's matrix-rank formulation and the proof's linear-independence formulation of transversality are equivalent. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_eval`](QuaternaryQuadraticForms/EmbeddedConic.lean) | Evaluation of the four binary coordinate polynomials agrees with the embedded canonical vector. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_homogeneous`](QuaternaryQuadraticForms/EmbeddedConic.lean) | Each of the four embedded coordinate polynomials is homogeneous of degree two. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_map`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The same binary coordinate forms are obtained after extending every coefficient to an overfield. | Checked locally |
| [`QuaternaryQuadraticForms.coordinatePolynomial_pderiv`](QuaternaryQuadraticForms/EmbeddedConic.lean) | A coordinate of a linear map has its matrix entry as formal derivative. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_partial`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The derivative vector is transported by the same linear map. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_partials_independent`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The actual polynomial partials remain independent after the embedding. | Checked locally |
| [`QuaternaryQuadraticForms.eval_canonicalConicPolynomial`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The literal ternary quadratic polynomial evaluates to the canonical conic form. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomial_homogeneous`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The ternary canonical conic polynomial is homogeneous of degree two. | Checked locally |
| [`QuaternaryQuadraticForms.coordinateQuadratic_pullback`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The assumed normal form is an identity of quadratic polynomials. | Checked locally |
| [`QuaternaryQuadraticForms.canonicalConicPolynomial_substitution`](QuaternaryQuadraticForms/EmbeddedConic.lean) | Substituting the canonical quadratics into their conic equation is zero. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_quadric_identity`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The embedded quadratic parametrization satisfies the actual equation F=0 as a polynomial identity. | Checked locally |
| [`QuaternaryQuadraticForms.coordinatePlane_pullback`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The embedded linear coordinate map satisfies the plane equation as a polynomial identity. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicPolynomials_plane_identity`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The four binary quadratic coordinates satisfy the actual plane equation as a polynomial identity. | Checked locally |
| [`QuaternaryQuadraticForms.planeConic_units_iff`](QuaternaryQuadraticForms/EmbeddedConic.lean) | The two equations of the plane section are stable under nonzero scalars. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedCanonicalConicPoint_injective`](QuaternaryQuadraticForms/EmbeddedConic.lean) | Injectivity of the linear embedding gives injectivity on projective conics. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedCanonicalConicPoint_surjective`](QuaternaryQuadraticForms/EmbeddedConic.lean) | Spanning the hyperplane gives every projective point of the plane section. | Checked locally |
| [`QuaternaryQuadraticForms.embeddedConicEquiv_mk`](QuaternaryQuadraticForms/EmbeddedConic.lean) | On an arbitrary nonzero representative, the projective equivalence is the literal embedded quadratic formula. | Checked locally |
| [`QuaternaryQuadraticForms.goodPrime_ne_two`](QuaternaryQuadraticForms/GoodPrime.lean) | Nondivisibility of the actual modulus 2*\|det A\| excludes the prime two. | Checked locally |
| [`QuaternaryQuadraticForms.goodPrime_reduced_det_ne_zero`](QuaternaryQuadraticForms/GoodPrime.lean) | Nondivisibility of the actual modulus proves that the reduced matrix has nonzero determinant. | Checked locally |
| [`QuaternaryQuadraticForms.reduceQuadraticMatrix_symmetric`](QuaternaryQuadraticForms/GoodPrime.lean) | Symmetry of the integral matrix is preserved by coefficient reduction. | Checked locally |
| [`QuaternaryQuadraticForms.reduceQuadraticMatrix_adjugate`](QuaternaryQuadraticForms/GoodPrime.lean) | Reducing the integral adjugate equals the adjugate of the reduced matrix. | Checked locally |
| [`QuaternaryQuadraticForms.primeField_two_ne_zero`](QuaternaryQuadraticForms/ConicParametrization.lean) | Odd characteristic supplied by the prime-field hypothesis. | Checked locally |
| [`QuaternaryQuadraticForms.conic_parametrization_prime_field`](QuaternaryQuadraticForms/ConicParametrization.lean) | Lemma 4.2 over the prime field: one tuple of literal binary quadratic forms works over every field extension, with every parametrization clause proved. | Checked locally |
| [`QuaternaryQuadraticForms.conic_parametrization`](QuaternaryQuadraticForms/ConicParametrization.lean) | Complete Lemma 4.2: one tuple over F_p parametrizes the actual plane conic over every extension field, with independent formal partials, from the integral good-prime and dual-form hypotheses. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveSectionTrace_eq_sum_conic`](QuaternaryQuadraticForms/PlaneSectionBound.lean) | The filtered section trace is the sum over its actual projective zero subtype. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveSectionTrace_eq_projectiveLine`](QuaternaryQuadraticForms/PlaneSectionBound.lean) | The conic parametrization identifies the literal section trace with the projective-line character sum of the actual substituted polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.plane_section_bound_of_parametrization`](QuaternaryQuadraticForms/PlaneSectionBound.lean) | Lemma 4.3 after the conic parametrizations have been constructed over the prime field and its algebraic closure. All simple-root conditions are deductions. | Checked locally |
| [`QuaternaryQuadraticForms.plane_section_bound_prime_field`](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) | Lemma 4.3 over the prime field, with the actual geometric matrix-rank condition and with the required parametrizations constructed in the proof. | Checked locally |
| [`QuaternaryQuadraticForms.plane_section_bound`](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) | Complete Lemma 4.3 for the literal projective section trace, using the integral good-prime condition and the actual geometric rank-three transversality hypothesis. | Checked locally |
| [`QuaternaryQuadraticForms.rank_two_iff_linearIndependent`](QuaternaryQuadraticForms/GoodReduction.lean) | The rank-two condition is exactly independence of the two actual rows. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveIntersectionTransverseRank_iff`](QuaternaryQuadraticForms/GoodReduction.lean) | The literal geometric rank condition is equivalent to independence of the evaluated gradient vectors at every nonzero common zero. | Checked locally |
| [`QuaternaryQuadraticForms.mem_badReductionPrimes`](QuaternaryQuadraticForms/GoodReduction.lean) | For a prime, membership in the bad-prime set is exactly bad reduction away from the quadratic bad-prime modulus. | Checked locally |
| [`QuaternaryQuadraticForms.prime_dvd_primeRadical_iff`](QuaternaryQuadraticForms/GoodReduction.lean) | A prime divides the radical of a nonzero natural number exactly when it divides that number. | Checked locally |
| [`QuaternaryQuadraticForms.primeRadical_pos`](QuaternaryQuadraticForms/GoodReduction.lean) | The radical product is positive, including at zero under the library's empty prime-factor convention. The manuscript uses it only for nonzero `N_F`. | Checked locally |
| [`QuaternaryQuadraticForms.quadraticBadPrimeModulus_ne_zero`](QuaternaryQuadraticForms/GoodReduction.lean) | A nonsingular integral matrix has a nonzero quadratic bad-prime modulus. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialBadPrimeModulus_pos`](QuaternaryQuadraticForms/GoodReduction.lean) | The actual finite bad-prime product is a positive integer. | Checked locally |
| [`QuaternaryQuadraticForms.prime_dvd_product_primes_iff`](QuaternaryQuadraticForms/GoodReduction.lean) | A prime divides a finite product of distinct primes exactly when it is one of its factors. | Checked locally |
| [`QuaternaryQuadraticForms.not_dvd_polynomialBadPrimeModulus_iff`](QuaternaryQuadraticForms/GoodReduction.lean) | Excluding the actual `N_G` is equivalent to excluding `N_F` and having the literal geometric good-reduction property. Finiteness is an explicit proved-data argument, not a replacement premise for its elimination proof. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionPrimes_subset_primeFactors_of_common_divisor`](QuaternaryQuadraticForms/GoodReduction.lean) | A nonzero integer divisible by every bad prime contains the exact bad-prime set among its prime divisors. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionPrimes_finite_of_common_divisor`](QuaternaryQuadraticForms/GoodReduction.lean) | The arithmetic finiteness deduction used after elimination supplies a single nonzero integer divisible by every bad prime. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionPrimeProduct_dvd_common_divisor`](QuaternaryQuadraticForms/GoodReduction.lean) | The product of the actual bad primes divides any nonzero integer that is divisible by each of them. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialBadPrimeModulus_le_of_common_divisor`](QuaternaryQuadraticForms/GoodReduction.lean) | The resulting modulus bound before the elimination value is bounded in terms of the coefficient height. | Checked locally |
| [`QuaternaryQuadraticForms.eval_pderiv_matrixQuadraticPolynomial`](QuaternaryQuadraticForms/QuadricSmooth.lean) | A formal partial derivative of the matrix quadratic polynomial evaluates to the sum of the corresponding row and column pairings. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialGradient_matrixQuadraticPolynomial`](QuaternaryQuadraticForms/QuadricSmooth.lean) | For a symmetric matrix, the actual formal gradient is twice `A x`. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadratic_gradient_ne_zero`](QuaternaryQuadraticForms/QuadricSmooth.lean) | A nonsingular symmetric quadratic matrix in odd characteristic has no nonzero vector at which all formal partial derivatives vanish. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadratic_projective_smooth`](QuaternaryQuadraticForms/QuadricSmooth.lean) | The nonsingular matrix implies the literal projective Jacobian condition. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadratic_projective_smooth_map`](QuaternaryQuadraticForms/QuadricSmooth.lean) | A nonsingular symmetric matrix remains so after extending its field. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_ne_zero`](QuaternaryQuadraticForms/QuadricSmooth.lean) | The actual quadric polynomial is nonzero under the nonsingularity and odd-characteristic hypotheses. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree`](QuaternaryQuadraticForms/QuadricSmooth.lean) | The nonsingular matrix polynomial has the exact degree two. | Checked locally |
| [`QuaternaryQuadraticForms.eval_pderiv_eq_of_totalDegree_le_one`](QuaternaryQuadraticForms/QuadricSmooth.lean) | Every formal derivative of an affine-linear polynomial is constant as a function of its evaluation point. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialGradient_eq_of_totalDegree_le_one`](QuaternaryQuadraticForms/QuadricSmooth.lean) | The actual gradient of an affine-linear polynomial is the same at every point, including the origin. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadratic_not_mul_affine`](QuaternaryQuadraticForms/QuadricSmooth.lean) | A nonsingular quaternary quadratic polynomial cannot be a product of two affine-linear polynomials. Their two constant gradients cannot span the gradient image of a nonsingular four-dimensional quadratic form. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible`](QuaternaryQuadraticForms/QuadricSmooth.lean) | A nonsingular quaternary quadratic form in odd characteristic is an irreducible polynomial over its coefficient field. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible_map`](QuaternaryQuadraticForms/QuadricSmooth.lean) | Irreducibility persists over every field extension, so the projective quadric is geometrically irreducible in its polynomial presentation. | Checked locally |
| [`QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_coeff`](QuaternaryQuadraticForms/SurfaceChern.lean) | Only the first three coefficients of the Chern polynomial enter the surface section coefficient. | Checked locally |
| [`QuaternaryQuadraticForms.surfaceChernRelation_coefficients`](QuaternaryQuadraticForms/SurfaceChern.lean) | Adjunction determines the constant, linear, and quadratic coefficients without imposing any condition on the higher coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_of_relation`](QuaternaryQuadraticForms/SurfaceChern.lean) | The surface coefficient obtained from the general adjunction relation. | Checked locally |
| [`QuaternaryQuadraticForms.quadricChernPolynomial_relation`](QuaternaryQuadraticForms/SurfaceChern.lean) | The explicit quadric polynomial satisfies the adjunction relation. | Checked locally |
| [`QuaternaryQuadraticForms.quadric_surfaceSectionEulerCoefficient`](QuaternaryQuadraticForms/SurfaceChern.lean) | The manuscript's exact quadric coefficient, with no asymptotic estimate. | Checked locally |
| [`QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_quadric_of_relation`](QuaternaryQuadraticForms/SurfaceChern.lean) | The same quadric coefficient follows from any polynomial satisfying the degree-two adjunction relation. | Checked locally |
| [`QuaternaryQuadraticForms.norm_sum_le_card_mul`](QuaternaryQuadraticForms/SurfaceChern.lean) | A finite sum of complex numbers bounded by p has norm at most r p. | Checked locally |
| [`QuaternaryQuadraticForms.mem_projectiveHypersurfacePoints_mk`](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | The homogeneous equation descends to the actual projective quotient. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveHypersurfacePoints_matrix`](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | The general projective hypersurface set agrees with the literal matrix quadric set when its defining polynomial is the matrix polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveHypersurfaceTrace_matrix`](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | The general literature sum is exactly the manuscript's projective trace. | Checked locally |
| [`QuaternaryQuadraticForms.transverse_polynomial_ne_zero`](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | A rank-two transverse polynomial cannot vanish identically if the first equation has a nonzero geometric zero. | Checked locally |
| [`QuaternaryQuadraticForms.quadric_transverse_polynomial_ne_zero`](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | The literal nonzero zero of a prime-field quadric supplies the geometric point needed to exclude the zero transverse polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.katz_quadric_bound_prime_field`](QuaternaryQuadraticForms/KatzBound.lean) | Lemma 2.7 over the prime field, with all geometric hypotheses supplied by the actual matrix and the manuscript's rank-two condition. | Checked locally |
| [`QuaternaryQuadraticForms.katz_quadric_bound`](QuaternaryQuadraticForms/KatzBound.lean) | Complete Lemma 2.7 for the actual projective trace, with the integral good-prime condition and the geometric rank-two hypothesis. Every quadric-specific condition of the registered general spectral input and the exact constant are proved internally. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveQuadraticTrace_abs_le`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The degree-two Katz bound for the actual integer-valued projective trace. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd_bound`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | Integrality, divisibility, and the size bound for the actual complex quadratic trace over the prime field. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_abs_le`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The integer trace bound for integral coefficients and the actual geometric good-reduction condition. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The three quadratic-trace conclusions with integral input coefficients and explicit good reduction, tied to the existing complex trace. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd_bound_of_modulus`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The literal `N_G` condition gives divisibility and the size bound for the actual integer trace once the finite bad-prime set has been proved. | Checked locally |
| [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The full integrality, divisibility, and size conclusions for the actual complex trace under the literal N_G condition, conditional on the explicitly supplied finiteness proof. This is not full Lemma 5.9 until the characteristic-zero elimination bridge is proved. | Checked locally |

The allowed dependencies are the standard logical foundations `propext`, `Classical.choice`, and `Quot.sound`. Individual exports may additionally use only the exact literature premises named in their ledger entry. Their actual Lean types and axiom dependencies are in the [verification report](certification/verification_report.json). 2 external Lean premises are registered separately from these proved exports; see [Trusted inputs](TRUSTED_INPUTS.md).

## Auxiliary and supplementary obligations

The following 33 groups retain their own correspondence review. The single numbered Remark 4.1 is represented by four of these groups. Final completion also requires a whole-manuscript correspondence review; the present grouping is not a reason to omit a subsequently identified assertion.

| Group | Content and source | Status |
|---|---|---|
| `aux:weight_pieces` | Smooth bump theta of mass one and exact integral decomposition W=delta^-4 integral W_y dy, with support control [source](manuscript/quadratic_character_sums_github.tex#L647-L665) | Pending |
| `aux:singint_absolute` | Absolute convergence of sigma_infty for arbitrary compactly supported smooth weight, including the cone vertex [source](manuscript/quadratic_character_sums_github.tex#L756-L761) | Pending |
| `aux:conecount` | Dual-cone inverse-norm weighted lattice count O(U^(1+epsilon)) [source](manuscript/quadratic_character_sums_github.tex#L814-L824) | Pending |
| `aux:polynomialbox_epsilon` | Replace C_(n,E)^omega(m) by O_(n,E,epsilon)(m^epsilon) [source](manuscript/quadratic_character_sums_github.tex#L900-L901) | Pending |
| `aux:ramanujan` | Ramanujan-sum exponential and divisor definitions agree; prime-power values and multiplicativity are derived/verified library facts [source](manuscript/quadratic_character_sums_github.tex#L1042-L1046) | Pending |
| `aux:Cfactor` | C_q(u)=product_(p\|q) C_p(u) and multiplicativity of S_c(u) [source](manuscript/quadratic_character_sums_github.tex#L1089-L1090) | Pending |
| `aux:quadratic_gauss_1d` | Scalar quadratic Gauss identity and tau_p^2=chi_p(-1)p, extracted from proof of Lemma3.2 [source](manuscript/quadratic_character_sums_github.tex#L1127-L1137) | Pending |
| `aux:Sxi` | Identity between global-series and local-product definitions of the main coefficient S_xi(q) [source](manuscript/quadratic_character_sums_github.tex#L1515-L1521) | Pending |
| `aux:Sxibound` | Uniform main-coefficient bound \|S_xi(q)\| <= \|S_F\|(4K)^omega(q)/q << q^(-1+epsilon) [source](manuscript/quadratic_character_sums_github.tex#L1522-L1527) | Pending |
| `aux:fourier_instantiation` | Geometric weights satisfy Section3 framework with N=N_G, E=E_(F,n), K=2n^2 [source](manuscript/quadratic_character_sums_github.tex#L1850-L1853) | Pending |
| `aux:diagonal_strata` | Diagonal weights satisfy two-level bound (3.3) with K=8 and D_p(u)=F*(u)u1u2u3u4 [source](manuscript/quadratic_character_sums_github.tex#L1979-L1983) | Pending |
| `aux:Ipiece` | Localized scaled integral bound and differentiability used in the three frequency estimates [source](manuscript/quadratic_character_sums_github.tex#L2091-L2124) | Pending |
| `supp:matrix_representation` | Any integral quadratic polynomial becomes x^T A x with integral symmetric A after multiplying by2, without changing its zeros [source](manuscript/quadratic_character_sums_github.tex#L158-L165) | Pending |
| `supp:smooth_equivalence` | Rank-two condition is equivalent to the smooth complete-intersection curve formulation [source](manuscript/quadratic_character_sums_github.tex#L279-L293) | Pending |
| `supp:projective_values` | Projective well-definedness and local-cover point interpretation [source](manuscript/quadratic_character_sums_github.tex#L307-L318) [source](manuscript/quadratic_character_sums_github.tex#L411-L418) | Pending |
| `supp:local_mean_factor` | The Euler factor equals (1-p^(-2)) times the projective character mean [source](manuscript/quadratic_character_sums_github.tex#L347-L352) | Pending |
| `supp:nontrivial_range` | Power-saving range for quadratic-character sums relative to B^2 [source](manuscript/quadratic_character_sums_github.tex#L350-L353) | Pending |
| `supp:polynomial_height` | Polynomial coefficient heights recover the B^(5/3+epsilon) count uniformly [source](manuscript/quadratic_character_sums_github.tex#L372-L374) | Pending |
| `supp:diagonal_signs` | Product identity for kappa_i and possible quadratic trace signs [source](manuscript/quadratic_character_sums_github.tex#L402-L404) [source](manuscript/quadratic_character_sums_github.tex#L2531-L2536) | Pending |
| `supp:even_power_reduction` | Even power counts follow from the square-value theorem [source](manuscript/quadratic_character_sums_github.tex#L455-L457) | Pending |
| `supp:im_bound_recovered` | Recover the valid Iwaniec-Munshi character-sum bound in the good-modulus range [source](manuscript/quadratic_character_sums_github.tex#L234-L238) | Pending |
| `supp:mallesham_counterexample` | Diagonal sums have exact order B^2/q, contradicting the smaller proposed leading term in M Proposition2.1 [source](manuscript/quadratic_character_sums_github.tex#L238-L244) | Pending |
| `supp:hss_comparison` | Summing HSS individual residue-class error bounds loses a power of q [source](manuscript/quadratic_character_sums_github.tex#L254-L259) | Pending |
| `supp:remark41_zero` | Zero frequency gives genuinely p^2-sized C_p(0) in diagonal examples [source](manuscript/quadratic_character_sums_github.tex#L1985-L1989) | Pending |
| `supp:remark41_offcone` | Explicit off-dual-cone example with C_p(u)>=p(p-5) [source](manuscript/quadratic_character_sums_github.tex#L1989-L2001) | Pending |
| `supp:remark41_im` | Convert the off-cone example into the IM complete-sum counterexample [source](manuscript/quadratic_character_sums_github.tex#L2001-L2011) | Pending |
| `supp:remark41_ramified` | Explicit nonzero dual-cone example with ramified sum chi_p(2)p^4(p-1) [source](manuscript/quadratic_character_sums_github.tex#L2011-L2015) | Pending |
| `supp:relative_ranges` | Uniform relative-error convergence in all three modulus ranges [source](manuscript/quadratic_character_sums_github.tex#L2780-L2786) [source](manuscript/quadratic_character_sums_github.tex#L464-L474) | Pending |
| `supp:determinant_thresholds` | Compare determinant-method and logarithmic-height sieve bounds [source](manuscript/quadratic_character_sums_github.tex#L2862-L2878) | Pending |
| `supp:frequency_error_summary` | Identify which frequency contribution produces each error scale [source](manuscript/quadratic_character_sums_github.tex#L2889-L2901) | Pending |
| `supp:conditional_sieve` | Conditional improvement of the exponent with the height term retained [source](manuscript/quadratic_character_sums_github.tex#L2903-L2919) | Pending |
| `supp:abstract_weight_specialization` | Apply the abstract analytic proposition to other local functions satisfying its stated hypotheses [source](manuscript/quadratic_character_sums_github.tex#L2933-L2939) | Pending |
| `supp:square_determinant` | Square-determinant untwisted count has B^2 log B and B^2 terms with the stated error [source](manuscript/quadratic_character_sums_github.tex#L2944-L2947) | Pending |

## Frozen source and reproducibility

```text
d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33
```

Official Lean 4.24.0 and official mathlib4 commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are pinned; the Lake manifest locks the transitive dependencies.

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar Mathlib.Data.Fintype.BigOperators Mathlib.LinearAlgebra.Projectivization.Cardinality Mathlib.Analysis.Complex.Basic Mathlib.NumberTheory.DirichletCharacter.Bounds Mathlib.RingTheory.MvPolynomial.Homogeneous Mathlib.Data.Matrix.Mul Mathlib.FieldTheory.ChevalleyWarning Mathlib.NumberTheory.LegendreSymbol.Basic Mathlib.Algebra.Polynomial.Homogenize Mathlib.Data.Fin.VecNotation Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.LinearAlgebra.Basis.VectorSpace Mathlib.LinearAlgebra.BilinearForm.Orthogonal Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.LinearAlgebra.FiniteDimensional.Lemmas Mathlib.LinearAlgebra.LinearIndependent.Basic Mathlib.LinearAlgebra.LinearIndependent.Lemmas Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.BilinearForm Mathlib.LinearAlgebra.Matrix.Dual Mathlib.LinearAlgebra.Matrix.Rank Mathlib.RingTheory.MvPolynomial.EulerIdentity Mathlib.Tactic.FieldSimp Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex Mathlib.Data.Nat.Factorization.Basic Mathlib.Algebra.Polynomial.Coeff Mathlib.Tactic.IntervalCases Mathlib.Tactic.NormNum Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring
python3 scripts/verify_certificate.py
```

The verifier checks source identities, all 42 statement locations, the dependency graph, status accounting, locked toolchain and dependency checkouts, every local proof module, declaration kinds, actual types, and permitted axioms. The frozen definitions and uniformity in varying coefficients must be preserved in every later export.

## Next proof target

Construct the nonzero elimination value in Lemma 4.1(i) and prove that every bad-reduction prime divides it. The checked arithmetic then proves finiteness of the actual bad-prime set and supplies the missing argument to the literal N_G wrappers in Lemma 5.9. The exceptional-plane construction in Lemma 4.1 and the remaining exceptional-section count and Fourier-bound assembly in Lemma 4.4 are separate obligations. Retain the checked Katz, conic, plane-section, exact-identity, and quadratic-trace results as inputs.
