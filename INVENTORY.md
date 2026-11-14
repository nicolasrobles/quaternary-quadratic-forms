# Certification inventory

Frozen manuscript: [quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).

**8 of 42 numbered results are certified.** 0 are partial, 0 are active numbered targets, and 34 are pending.

The current checkpoint completes Lemma 4.4: all three weight properties, the exact zero-frequency identity, and the pointwise Fourier estimate with constant 2n² and the actual exceptional-polynomial indicator. The nonzero plane-section bound of 2p+2 points is proved internally, including tangent and singular sections, using a nonzero ternary restriction, the proved mathlib Schwartz–Zippel theorem and exact rays. The final theorem uses the literal N_G; its uniform wrapper chooses E before G,p and D_p before the character. All four existing literature premises remain unchanged. Lemmas 2.5, 2.7, 4.1–4.3 and 5.9 and Corollary 2.6 remain certified. No numbered result remains Partial. Theorems 1.1 and 1.4 remain Pending. The 33 auxiliary and supplementary groups are tracked separately; these are groups of assertions, not additional numbered results.

The verification scope contains **325 proved exports**, **66 proof modules**, and **87 hashed input files**. These counts are derived from the live ledger and project files; they do not increase the number of certified manuscript results.

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
| [Lemma 4.1](manuscript/quadratic_character_sums_github.tex#L1615-L1632) | Polynomial bound for bad-prime product and uniformly bounded-degree exceptional plane locus | Certified | [`QuaternaryQuadraticForms.badReductionPrimes_finite_of_smooth`](QuaternaryQuadraticForms/BadReductionResultants.lean); [`QuaternaryQuadraticForms.polynomialBadPrimeModulus_height_bound`](QuaternaryQuadraticForms/BadReductionHeight.lean); [`QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound`](QuaternaryQuadraticForms/BadReductionHeight.lean); [`QuaternaryQuadraticForms.exceptional_plane_polynomial`](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean) |
| [Lemma 4.2](manuscript/quadratic_character_sums_github.tex#L1712-L1724) | Uniform conic parametrization by binary quadratics over every extension field, with independent derivative vectors | Certified | [`QuaternaryQuadraticForms.conic_parametrization`](QuaternaryQuadraticForms/ConicParametrization.lean) |
| [Lemma 4.3](manuscript/quadratic_character_sums_github.tex#L1756-L1765) | Transverse plane-section character-sum bound (2n-1) sqrt(p)+1 | Certified | [`QuaternaryQuadraticForms.plane_section_bound`](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) |
| [Lemma 4.4](manuscript/quadratic_character_sums_github.tex#L1796-L1808) | Coefficient-uniform Fourier bounds with exceptional-locus term and exact zero-frequency projective identity | Certified | [`QuaternaryQuadraticForms.polynomialCharacterWeight_properties`](QuaternaryQuadraticForms/PolynomialWeights.lean); [`QuaternaryQuadraticForms.fourierSum_zero`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.fourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.integralFourierSum_ray_identity`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.integralFourierSum_of_dvd`](QuaternaryQuadraticForms/FourierRays.lean); [`QuaternaryQuadraticForms.fourier_bound`](QuaternaryQuadraticForms/FourierBound.lean); [`QuaternaryQuadraticForms.uniform_polynomial_fourier_bound`](QuaternaryQuadraticForms/FourierTheorem.lean) |
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
| [Lemma 5.9](manuscript/quadratic_character_sums_github.tex#L2686-L2690) | Quadratic local trace is integral, divisible by p, and bounded by4p | Certified | [`QuaternaryQuadraticForms.quadratic_projective_trace`](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean); [`QuaternaryQuadraticForms.quadratic_projective_trace_integer`](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean) |
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

### Lemma 4.1

[Statement correspondence review](certification/correspondence/bad_reduction.md)

Both parts of Lemma 4.1 are complete. The exact Lang generic-coefficient resultant system and general composite Bertini interface are registered literature premises. Both actual elimination systems, all rank-minor interpretations, parameter specialization, geometric nonvanishing descent, the literal bad-prime finiteness and height estimate, and construction of D_p with a uniform degree bound are internal deductions. Bertini is used only over the algebraic closure; no prime-field transverse plane is assumed.

### Lemma 4.2

[Statement correspondence review](certification/correspondence/conic_parametrization.md)

Both clauses are proved for one tuple of literal binary quadratic forms chosen over F_p before quantifying over every extension field. The projective bijection, independent formal derivatives, normal form, and scalar extension are constructed from the manuscript hypotheses. No external mathematical premise is used.

### Lemma 4.3

[Statement correspondence review](certification/correspondence/plane_section.md)

Complete bound for the actual projective plane-section sum under the literal geometric rank-three condition. Parametrization, nonvanishing, and the 2n distinct geometric roots are derived internally, including when p divides 2n. Only the previously registered EXT.WEIL premise is used.

### Lemma 4.4

[Statement correspondence review](certification/correspondence/fourier_rays.md)

Complete Lemma 4.4. The actual exceptional section count is proved internally using a nonzero ternary restriction, the proved mathlib Schwartz-Zippel theorem and exact projective-ray counting, including tangent and singular sections. The generic, exceptional and zero-frequency estimates are assembled with the exact constant 2n^2. The literal N_G hypothesis supplies all reduction conditions. The uniform theorem chooses D_p independently of the character and uses only the four previously registered literature premises; no new external premise or restriction that p be prime to n is introduced.

### Lemma 5.9

[Statement correspondence review](certification/correspondence/quadratic_trace.md)

Complete Lemma 5.9 for the actual quadratic projective trace: it is an integer divisible by p and has absolute value at most 4p. The final exports assume the manuscript's characteristic-zero rank condition and p not dividing its literal N_G. Finiteness of the defining bad-prime set and geometric good reduction at p are proved internally, with no extra finiteness or good-reduction premise. The registered Lang and composite Katz inputs are the only literature dependencies.

## Scope of partially checked numbered results

There are no partially checked numbered results at this checkpoint.

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
| [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus`](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The full integrality, divisibility, and size conclusions for the actual complex trace under the literal N_G condition, conditional on an explicitly supplied finiteness proof. This conditional helper is now used by the complete source-level theorem quadratic_projective_trace, which proves that finiteness from characteristic-zero smoothness. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_isHomogeneous`](QuaternaryQuadraticForms/HomogeneousForms.lean) | The coefficient-vector construction has the assigned degree of homogeneity, including when all coefficients vanish. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_coeff`](QuaternaryQuadraticForms/HomogeneousForms.lean) | Recover a specified coefficient from the constructed form. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_coeff_eq_zero_of_degree_ne`](QuaternaryQuadraticForms/HomogeneousForms.lean) | The constructed form has no coefficient outside its assigned degree. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_coeff_formula`](QuaternaryQuadraticForms/HomogeneousForms.lean) | The coefficient formula at an arbitrary exponent vector. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_coefficients`](QuaternaryQuadraticForms/HomogeneousForms.lean) | Every homogeneous polynomial is exactly the form built from its coefficients on the monomials of the assigned degree. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousForm_map`](QuaternaryQuadraticForms/HomogeneousForms.lean) | Forming the polynomial commutes with every homomorphism of coefficient semirings, including coefficient specialization and reduction modulo primes. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneousSystem_parameter_coefficients`](QuaternaryQuadraticForms/EliminationFamily.lean) | The coefficient polynomials of a homogeneous family reconstruct its specialization at every parameter point. | Checked locally |
| [`QuaternaryQuadraticForms.homogeneous_parameter_resultants`](QuaternaryQuadraticForms/EliminationFamily.lean) | For an actual polynomial-parameter family of homogeneous equations, internally substitute its coefficient polynomials into the registered generic resultant family. The resulting finite integer polynomial family is chosen before the field or parameter assignment and has exactly the same nonzero geometric-zero criterion. | Checked locally |
| [`QuaternaryQuadraticForms.rank_two_ne_iff_minors_zero`](QuaternaryQuadraticForms/RankMinors.lean) | Two rows fail to have rank two exactly when every two-by-two minor vanishes. The assertion also covers a zero row and an empty column set. | Checked locally |
| [`QuaternaryQuadraticForms.rank_two_iff_exists_minor_ne_zero`](QuaternaryQuadraticForms/RankMinors.lean) | Full rank is witnessed by one nonzero two-by-two minor. | Checked locally |
| [`QuaternaryQuadraticForms.card_badReductionIndex`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The system has eighteen entries; ordered repetitions add no zeros. | Checked locally |
| [`QuaternaryQuadraticForms.gradientMinor_homogeneous`](QuaternaryQuadraticForms/BadReductionSystem.lean) | A gradient minor of a quadratic and a degree-`n` homogeneous polynomial is homogeneous of degree `n`. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionSystem_homogeneous`](QuaternaryQuadraticForms/BadReductionSystem.lean) | Every entry of the literal system has its prescribed homogeneous degree, over the original coefficient ring. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionSystemDegree_pos`](QuaternaryQuadraticForms/BadReductionSystem.lean) | All prescribed degrees are positive when the manuscript's `n ≥ 2` hypothesis holds. | Checked locally |
| [`QuaternaryQuadraticForms.matrixQuadraticPolynomial_map_ring`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The matrix quadratic polynomial commutes with arbitrary coefficient homomorphisms, including reduction from the integers. | Checked locally |
| [`QuaternaryQuadraticForms.gradientMinor_map`](QuaternaryQuadraticForms/BadReductionSystem.lean) | Formal gradient minors commute with coefficient reduction and extension, with no assumption on the characteristic or on `n`. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionSystem_map`](QuaternaryQuadraticForms/BadReductionSystem.lean) | Mapping the literal system is the literal system of the mapped matrix and polynomial. | Checked locally |
| [`QuaternaryQuadraticForms.eval_badReductionSystem_map`](QuaternaryQuadraticForms/BadReductionSystem.lean) | Evaluation after coefficient specialization is the same as directly evaluating the original polynomial through that coefficient homomorphism. | Checked locally |
| [`QuaternaryQuadraticForms.eval_badReductionSystem_map_point`](QuaternaryQuadraticForms/BadReductionSystem.lean) | At an extended point, each specialized equation is the image of its value at the original point. | Checked locally |
| [`QuaternaryQuadraticForms.eval_gradientMinor`](QuaternaryQuadraticForms/BadReductionSystem.lean) | Evaluation of a formal gradient minor is the actual scalar minor of the two evaluated gradient rows. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionSystem_zero_iff`](QuaternaryQuadraticForms/BadReductionSystem.lean) | At any point over a field, the system vanishes exactly when both equations vanish and the two actual gradient rows fail to have rank two. | Checked locally |
| [`QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The nonzero common zeros of this explicit polynomial system are precisely the failures of the manuscript's projective rank condition. | Checked locally |
| [`QuaternaryQuadraticForms.exists_badReductionSystem_eval₂_zero_iff`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The same zero-locus statement after an arbitrary coefficient map to a field. This form applies directly to integral or universal coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff_not_goodReductionAt`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The two-step prime reduction and algebraic-closure extension is exactly evaluation of the original integral system through the composite coefficient map. | Checked locally |
| [`QuaternaryQuadraticForms.exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt`](QuaternaryQuadraticForms/BadReductionSystem.lean) | The prime-field specialization in the direct integer-cast form used by homogeneous elimination. | Checked locally |
| [`QuaternaryQuadraticForms.two_le_polynomialCoefficientHeight`](QuaternaryQuadraticForms/PolynomialHeight.lean) | The actual coefficient height is at least two. | Checked locally |
| [`QuaternaryQuadraticForms.natAbs_coeff_le_polynomialCoefficientHeight`](QuaternaryQuadraticForms/PolynomialHeight.lean) | Every coefficient, including those outside the support, is bounded by the actual coefficient height. | Checked locally |
| [`QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow`](QuaternaryQuadraticForms/PolynomialHeight.lean) | Evaluation is bounded by the coefficient sum times the height to the actual total degree. Only variables occurring in the polynomial need bounds. | Checked locally |
| [`QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow_of_forall`](QuaternaryQuadraticForms/PolynomialHeight.lean) | The same evaluation bound when all coordinates of the evaluation point are bounded by the chosen height. | Checked locally |
| [`QuaternaryQuadraticForms.finite_polynomial_family_eval_bound`](QuaternaryQuadraticForms/PolynomialHeight.lean) | Fixed positive constants work simultaneously for a finite family of integer polynomials, independently of the height and evaluation point. | Checked locally |
| [`QuaternaryQuadraticForms.finite_polynomial_family_eval_bound_of_height`](QuaternaryQuadraticForms/PolynomialHeight.lean) | A fixed finite family has a uniform bound in the actual coefficient height of any polynomial, for any evaluation tuple bounded by that height. | Checked locally |
| [`QuaternaryQuadraticForms.finite_polynomial_family_coeff_eval_bound`](QuaternaryQuadraticForms/PolynomialHeight.lean) | In particular, evaluating a fixed family on any indexed tuple of the coefficients of G has constants independent of G and of the coefficient indices. | Checked locally |
| [`QuaternaryQuadraticForms.genericDegreeForm_homogeneous`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | Homogeneity of the generic form is independent of its coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_homogeneous`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | Every equation in the generic system has its prescribed homogeneous degree in the four geometric variables. | Checked locally |
| [`QuaternaryQuadraticForms.genericQuadricMatrix_map_eval₂Hom`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | Specializing the parameters leaves the fixed quadratic matrix equal to its image under the chosen homomorphism from the integers. | Checked locally |
| [`QuaternaryQuadraticForms.genericDegreeForm_map_eval₂Hom`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | The generic form specializes to the form with exactly the chosen coefficient vector, over any commutative ring. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_map_eval₂Hom`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | Specialization commutes with construction of the full system. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_specialize`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | Inserting the actual coefficients of a homogeneous polynomial gives its literal bad-reduction system, with the fixed integral quadratic matrix. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_specialize_integral`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | The integral specialization uses ordinary integer evaluation at the literal coefficients of `G`. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_specialize_map`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | After any map from the integers, the parameter vector is the image of the original integer coefficient vector. This applies in particular to prime fields and their algebraic closures. | Checked locally |
| [`QuaternaryQuadraticForms.genericBadReductionSystem_specialize_intCast`](QuaternaryQuadraticForms/GenericQuadricFamily.lean) | The integer-cast specialization of the same fixed integral family. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_map_intCast_iff`](QuaternaryQuadraticForms/GeometricReduction.lean) | For integral equations, specialization to a field and then extension to its algebraic closure is the direct integer-cast evaluation. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_iff`](QuaternaryQuadraticForms/GeometricReduction.lean) | The geometric zero predicate for the specialized integral system is exactly failure of the two-gradient rank condition over the same algebraic closure. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_rat_iff`](QuaternaryQuadraticForms/GeometricReduction.lean) | The characteristic-zero system has a nonzero geometric zero exactly when the literal characteristic-zero smoothness hypothesis fails. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_zmod_iff`](QuaternaryQuadraticForms/GeometricReduction.lean) | The prime-field system has a nonzero geometric zero exactly when the manuscript's literal good-reduction condition fails at that prime. | Checked locally |
| [`QuaternaryQuadraticForms.badReduction_resultants_over_fields`](QuaternaryQuadraticForms/BadReductionResultants.lean) | A fixed integer family detects the actual common geometric zero condition after every field specialization of every integral form. | Checked locally |
| [`QuaternaryQuadraticForms.badReduction_resultant_family`](QuaternaryQuadraticForms/BadReductionResultants.lean) | The same fixed family has a nonzero integer value precisely under characteristic-zero smoothness, and every value is divisible by a prime precisely when the actual rank condition fails at that prime. | Checked locally |
| [`QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor`](QuaternaryQuadraticForms/BadReductionResultants.lean) | Characteristic-zero smoothness produces one actual nonzero integer divisible by every prime in the manuscript's bad-reduction set. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionPrimes_finite_of_smooth`](QuaternaryQuadraticForms/BadReductionResultants.lean) | The actual bad-prime set is finite under the manuscript's characteristic-zero smoothness hypothesis. | Checked locally |
| [`QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor_height_bound`](QuaternaryQuadraticForms/BadReductionHeight.lean) | Fixed constants bound a nonzero integer divisible by every actual bad prime. The constants depend on the fixed matrix and degree, and are chosen before the form `G` and its coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.polynomialBadPrimeModulus_height_bound`](QuaternaryQuadraticForms/BadReductionHeight.lean) | The actual modulus satisfies a uniform power bound in the actual coefficient height, for every proof of finiteness of its defining set. | Checked locally |
| [`QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound`](QuaternaryQuadraticForms/BadReductionHeight.lean) | Full Lemma 4.1(i): for fixed integral A and n >= 2, choose positive natural constants C,K before G; every homogeneous G satisfying the actual characteristic-zero rank condition has a finite literal bad-prime set and its literal N_G is at most K times the actual coefficient height to the power C. | Checked locally |
| [`QuaternaryQuadraticForms.quadratic_projective_trace_integer`](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean) | The complete divisibility and size conclusions of Lemma 5.9 directly for the actual integer projective trace, under characteristic-zero smoothness and exclusion of the literal N_G whose finiteness is proved internally. | Checked locally |
| [`QuaternaryQuadraticForms.quadratic_projective_trace`](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean) | Complete Lemma 5.9: the actual complex projective quadratic-character trace equals an integer a with p dividing a and \|a\| <= 4p. The literal N_G is defined using internally proved finiteness from characteristic-zero smoothness; no separate finiteness or good-reduction premise is assumed. | Checked locally |
| [`QuaternaryQuadraticForms.rowTripleMinor_eq_det`](QuaternaryQuadraticForms/RankThreeMinors.lean) | The polynomial expression is the determinant of the corresponding three-column matrix, including choices with repeated columns. | Checked locally |
| [`QuaternaryQuadraticForms.rowTripleMinor_map`](QuaternaryQuadraticForms/RankThreeMinors.lean) | Every coefficient homomorphism commutes with the literal minor. | Checked locally |
| [`QuaternaryQuadraticForms.rank_three_ne_iff_minors_zero`](QuaternaryQuadraticForms/RankThreeMinors.lean) | Three rows have rank different from three precisely when every ordered three-by-three column minor vanishes. | Checked locally |
| [`QuaternaryQuadraticForms.rank_three_iff_exists_minor_ne_zero`](QuaternaryQuadraticForms/RankThreeMinors.lean) | Full rank is witnessed by a nonzero ordered three-column minor. | Checked locally |
| [`QuaternaryQuadraticForms.planeEquationPolynomial_eq_planePolynomial`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | The ring-general equation agrees with the previously used field equation. | Checked locally |
| [`QuaternaryQuadraticForms.eval_planeEquationPolynomial`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Evaluation of the plane equation is the actual dot product. | Checked locally |
| [`QuaternaryQuadraticForms.planeEquationPolynomial_homogeneous`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | The plane equation retains homogeneous degree one even for zero normal. | Checked locally |
| [`QuaternaryQuadraticForms.planeEquationPolynomial_map`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Plane equations commute with every coefficient homomorphism. | Checked locally |
| [`QuaternaryQuadraticForms.gradientPlaneMinor_homogeneous`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Such a minor has degree `n` in the geometric variables. | Checked locally |
| [`QuaternaryQuadraticForms.gradientPlaneMinor_map`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | The minors commute with coefficient maps, including prime reduction. | Checked locally |
| [`QuaternaryQuadraticForms.eval_gradientPlaneMinor`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | The formal polynomial minor evaluates to the actual scalar row minor. | Checked locally |
| [`QuaternaryQuadraticForms.card_planeReductionIndex`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Ordered repetition changes neither the equations nor their finite nature. | Checked locally |
| [`QuaternaryQuadraticForms.planeReductionSystem_homogeneous`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Every entry has its positive prescribed homogeneous degree. | Checked locally |
| [`QuaternaryQuadraticForms.planeReductionSystemDegree_pos`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Positivity of all assigned degrees for homogeneous elimination. | Checked locally |
| [`QuaternaryQuadraticForms.planeReductionSystem_map`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Forming this entire system commutes with coefficient specialization. | Checked locally |
| [`QuaternaryQuadraticForms.eval_planeReductionSystem_map`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Evaluation after mapping equals evaluation through the coefficient map. | Checked locally |
| [`QuaternaryQuadraticForms.planeReductionSystem_zero_iff`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Vanishing of this system is the actual failure of rank three at a common zero of the quadratic, the form and the plane equation. | Checked locally |
| [`QuaternaryQuadraticForms.exists_planeReductionSystem_zero_iff`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Nonzero common zeros are precisely failures of the manuscript's literal plane-transversality condition. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_planeReductionSystem_iff`](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | The geometric zero condition is rank failure over the algebraic closure. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneDegreeForm_homogeneous`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | The form with joint indeterminate parameters is homogeneous of degree `n`. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneReductionSystem_homogeneous`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | Every equation in the second universal system has its assigned degree. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneQuadricMatrix_map_eval₂Hom`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | Evaluation of the joint parameters preserves the fixed matrix. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneDegreeForm_map_eval₂Hom`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | The generic form specializes to the form with the chosen literal coefficients. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneNormal_eval₂Hom`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | The generic normal specializes to the chosen four coordinates. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneReductionSystem_map_eval₂Hom`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | Coefficient specialization produces the entire literal plane system. | Checked locally |
| [`QuaternaryQuadraticForms.genericPlaneReductionSystem_specialize`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | Inserting the actual coefficients of `G` gives its actual second system. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_resultants_over_fields`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | A fixed integral family in `(g,u)` detects geometric nontransversality for every field and every homogeneous form of degree `n` over that field. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_resultant_family`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | The same fixed family detects the manuscript's actual geometric rank failure. | Checked locally |
| [`QuaternaryQuadraticForms.eval_specializePlaneResultant`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | Evaluation after partial specialization is the joint parameter evaluation. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_specialized_resultant_family`](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | One fixed family can equally be stated using polynomials in the plane normal after specialization of the coefficients of `G`. | Checked locally |
| [`QuaternaryQuadraticForms.hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed`](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean) | Over an algebraically closed field the geometric common-zero predicate is exactly the common-zero predicate in that field. | Checked locally |
| [`QuaternaryQuadraticForms.specializePlaneResultant_map`](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean) | Partial specialization of the form coefficients commutes with any coefficient homomorphism, including passage to an algebraic closure. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_resultants_over_algClosed_fields`](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean) | For an algebraically closed coefficient field, the fixed resultant family detects the literal rank condition over that same field. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_resultants_nonzero_of_transverse_witness`](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean) | A transverse plane over an algebraically closed field forces a nonzero evaluation of at least one member of the fixed resultant family. | Checked locally |
| [`QuaternaryQuadraticForms.rank_three_of_rank_two_of_tangent`](QuaternaryQuadraticForms/BertiniPlane.lean) | A linear functional nonzero on a common tangent vector is outside the span of two independent rows, so adjoining it gives rank three. | Checked locally |
| [`QuaternaryQuadraticForms.exists_transverse_plane_of_smooth_intersection`](QuaternaryQuadraticForms/BertiniPlane.lean) | The general Bertini input produces a plane satisfying the literal rank-three condition for a homogeneous quadratic and a degree-`n` form whose common nonzero zeros all satisfy the rank-two condition. | Checked locally |
| [`QuaternaryQuadraticForms.totalDegree_eval₂_le_of_degree_one`](QuaternaryQuadraticForms/ParameterSpecialization.lean) | Substitution of polynomials of degree at most one does not increase the total degree. Coefficients may be mapped to any commutative semiring. | Checked locally |
| [`QuaternaryQuadraticForms.totalDegree_specializePlaneResultant_le`](QuaternaryQuadraticForms/ExceptionalPlaneDegree.lean) | Specializing the coefficients of the form cannot increase the degree of a resultant polynomial in the remaining plane-normal variables. | Checked locally |
| [`QuaternaryQuadraticForms.exceptionalPlane_bounded_resultant_family`](QuaternaryQuadraticForms/ExceptionalPlaneDegree.lean) | The degree bound and integral family are chosen before the coefficient field and the degree-`n` form. Their simultaneous zeros detect the literal geometric failure of rank-three transversality. This does not yet assert that one specialized polynomial is nonzero; that needs a transverse plane. | Checked locally |
| [`QuaternaryQuadraticForms.exceptional_plane_polynomial_over_fields`](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean) | The exceptional polynomial over any field of odd characteristic with nonsingular quadratic reduction. The degree bound is chosen for the fixed integral matrix and degree before the coefficient field and form. | Checked locally |
| [`QuaternaryQuadraticForms.exceptional_plane_polynomial`](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean) | Full Lemma 4.1(ii): for fixed symmetric nonsingular integral A and n >= 2, choose E >= 1 before G,p; characteristic-zero smoothness and avoidance of the literal N_G give a nonzero polynomial D_p of total degree at most E, with D_p(0)=0. Its nonvanishing implies the literal adjugate dual-form condition and rank three of the actual gradients and normal at every nonzero geometric common zero. Finiteness defining N_G is proved internally by part (i). | Checked locally |
| [`QuaternaryQuadraticForms.plane_exists_nonzero_quadratic_value`](QuaternaryQuadraticForms/PlaneRestriction.lean) | Every nonzero hyperplane contains a vector at which the actual nonsingular symmetric quadratic form is nonzero; polarization and orthogonal dimensions supply the proof. | Checked locally |
| [`QuaternaryQuadraticForms.eval_planeRestrictionPolynomial`](QuaternaryQuadraticForms/PlaneRestriction.lean) | Evaluation of the actual ternary coordinate restriction agrees with the original four-variable quadratic form on the corresponding plane vector. | Checked locally |
| [`QuaternaryQuadraticForms.planeRestrictionPolynomial_homogeneous`](QuaternaryQuadraticForms/PlaneRestriction.lean) | The actual restriction along three linear plane coordinates is homogeneous of degree two. | Checked locally |
| [`QuaternaryQuadraticForms.planeRestrictionPolynomial_totalDegree_le`](QuaternaryQuadraticForms/PlaneRestriction.lean) | The actual ternary plane restriction has total degree at most two. | Checked locally |
| [`QuaternaryQuadraticForms.planeRestrictionPolynomial_ne_zero`](QuaternaryQuadraticForms/PlaneRestriction.lean) | The actual restricted polynomial is nonzero, proved from a nonzero evaluation witness without an invalid finite-field polynomial identity argument. | Checked locally |
| [`QuaternaryQuadraticForms.exists_plane_quadratic_restriction`](QuaternaryQuadraticForms/PlaneRestriction.lean) | Every nonzero plane admits three linear coordinates and a nonzero ternary polynomial of degree at most two with the literal quadratic evaluation identity. | Checked locally |
| [`QuaternaryQuadraticForms.ternary_polynomial_zero_card_le`](QuaternaryQuadraticForms/PolynomialGridCount.lean) | The actual affine zero set of a nonzero ternary polynomial of degree at most two over F_p has cardinality at most 2p^2, using the proved mathlib Schwartz-Zippel theorem. | Checked locally |
| [`QuaternaryQuadraticForms.planeSection_affine_card_eq`](QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | Exact cardinality of the actual affine quadratic-plane intersection: one zero vector plus p-1 vectors for each projective section point. | Checked locally |
| [`QuaternaryQuadraticForms.planeSection_affine_card_le`](QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | Every actual nonzero plane section of the nonsingular quaternary quadratic form has at most 2p^2 affine zeros, including singular sections. | Checked locally |
| [`QuaternaryQuadraticForms.planeSection_card_le`](QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | Every actual nonzero plane section has at most 2p+2 projective points, including tangent and singular sections; no dual-form nonvanishing is assumed. | Checked locally |
| [`QuaternaryQuadraticForms.projectiveSectionTrace_norm_le`](QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | The actual projective plane-section character sum has norm at most 2p+2 for every nonzero plane, using the proved cardinality and character norm bounds. | Checked locally |
| [`QuaternaryQuadraticForms.fourier_generic_constant_bound`](QuaternaryQuadraticForms/FourierBoundConstants.lean) | Elementary real inequality preserving the exact generic-frequency coefficient and reducing it to the manuscript constant 2n^2. | Checked locally |
| [`QuaternaryQuadraticForms.fourier_exceptional_constant_bound`](QuaternaryQuadraticForms/FourierBoundConstants.lean) | Elementary real inequality reducing 2p^2+(2n^2-4n+6)p to 2n^2 p^2 for n>=2 and p>=1. | Checked locally |
| [`QuaternaryQuadraticForms.fourier_zero_constant_bound`](QuaternaryQuadraticForms/FourierBoundConstants.lean) | Elementary real inequality reducing the zero-frequency factor (p-1)(2n^2-4n+4)p to 2n^2 p^2. | Checked locally |
| [`QuaternaryQuadraticForms.rpow_three_halves_eq_mul_sqrt`](QuaternaryQuadraticForms/FourierBoundConstants.lean) | The actual real power p^(3/2) equals p times sqrt(p) for p>=0. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_norm_le_section_and_trace`](QuaternaryQuadraticForms/FourierEstimates.lean) | Triangle inequality for the literal Fourier ray identity: norm C_p(u) is bounded by p times the actual section norm plus the actual global trace norm. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_zero_norm`](QuaternaryQuadraticForms/FourierEstimates.lean) | Exact zero-frequency norm with the real nonnegative factor p-1 and the actual projective trace. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_generic_bound`](QuaternaryQuadraticForms/FourierEstimates.lean) | The actual Fourier sum at a generic frequency satisfies the exact 2n^2 p sqrt(p) estimate under the literal geometric rank-two and rank-three conditions. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_zero_bound`](QuaternaryQuadraticForms/FourierEstimates.lean) | The actual zero-frequency Fourier sum satisfies the 2n^2 p^2 bound using the exact ray identity and the global Katz estimate. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_nonzero_bound`](QuaternaryQuadraticForms/FourierEstimates.lean) | The actual Fourier sum at every nonzero frequency satisfies 2n^2 p^2, including tangent and singular sections, using the actual section count and Katz estimate. | Checked locally |
| [`QuaternaryQuadraticForms.fourierSum_bound_prime_field`](QuaternaryQuadraticForms/FourierBound.lean) | Complete finite-field pointwise Fourier estimate with the actual exceptional-polynomial indicator, proved by the zero, exceptional, and generic frequency cases. | Checked locally |
| [`QuaternaryQuadraticForms.fourier_bound`](QuaternaryQuadraticForms/FourierBound.lean) | All five conclusions of Lemma 4.4 for integral coefficients and integral frequencies under literal characteristic-zero smoothness and p not dividing N_G, using the geometric properties of a supplied D_p. | Checked locally |
| [`QuaternaryQuadraticForms.uniform_polynomial_fourier_bound`](QuaternaryQuadraticForms/FourierTheorem.lean) | Complete Lemma 4.4 with E chosen before G,p and one nonzero bounded-degree D_p chosen before every allowed character and frequency, including all three weight properties, the exact Fourier bound, and the zero-frequency identity. | Checked locally |

The allowed dependencies are the standard logical foundations `propext`, `Classical.choice`, and `Quot.sound`. Individual exports may additionally use only the exact literature premises named in their ledger entry. Their actual Lean types and axiom dependencies are in the [verification report](certification/verification_report.json). 4 external Lean premises are registered separately from these proved exports; see [Trusted inputs](TRUSTED_INPUTS.md).

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
lake exe cache get Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.MvPolynomial.Degrees Mathlib.Algebra.MvPolynomial.Eval Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.Algebra.MvPolynomial.SchwartzZippel Mathlib.Algebra.MvPolynomial.Variables Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.Polynomial.Coeff Mathlib.Algebra.Polynomial.Homogenize Mathlib.Analysis.Complex.Basic Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Data.Fin.VecNotation Mathlib.Data.Finsupp.Weight Mathlib.Data.Fintype.BigOperators Mathlib.Data.Matrix.Mul Mathlib.Data.Nat.Factorization.Basic Mathlib.FieldTheory.ChevalleyWarning Mathlib.FieldTheory.Finite.Basic Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.FieldTheory.IsAlgClosed.Basic Mathlib.LinearAlgebra.Basis.VectorSpace Mathlib.LinearAlgebra.BilinearForm.Orthogonal Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.LinearAlgebra.FiniteDimensional.Lemmas Mathlib.LinearAlgebra.LinearIndependent.Basic Mathlib.LinearAlgebra.LinearIndependent.Lemmas Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.BilinearForm Mathlib.LinearAlgebra.Matrix.Dual Mathlib.LinearAlgebra.Matrix.Rank Mathlib.LinearAlgebra.Projectivization.Cardinality Mathlib.NumberTheory.DirichletCharacter.Bounds Mathlib.NumberTheory.LegendreSymbol.Basic Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic Mathlib.RingTheory.MvPolynomial.EulerIdentity Mathlib.RingTheory.MvPolynomial.Homogeneous Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.IntervalCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring
python3 scripts/verify_certificate.py
```

The verifier checks source identities, all 42 statement locations, the dependency graph, status accounting, locked toolchain and dependency checkouts, every local proof module, declaration kinds, actual types, and permitted axioms. The frozen definitions and uniformity in varying coefficients must be preserved in every later export.

## Next proof target

Complete Lemma 4.5 for the actual diagonal pair: prove characteristic-zero smoothness, characterize geometric bad reduction at p not dividing N_F by p dividing the product M of the six coefficient differences, and identify the existing modulus exactly as rad(|2αM|). Keep this target Pending until all three clauses and source correspondence are complete. The pencil character-sum evaluation in Lemma 4.6 is the subsequent target.
