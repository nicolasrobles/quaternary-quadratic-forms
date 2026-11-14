# Certification inventory

Frozen manuscript: v35, renamed without content changes for this repository.

**2 of 42 numbered results are certified.** 2 are partial, 0 are active numbered targets, and 38 are pending.

The current checkpoint certifies Lemma 2.5 relative to its exact cited Weil input and proves the complete projective-line Corollary 2.6. The charts, dehomogenization, degree calculation, and simple-root condition are checked deductions. The earlier integrality and divisibility clauses of Lemma 5.9 remain checked; its size bound remains pending. The weight properties, ray identity (4.5), and zero-frequency clause of Lemma 4.4 remain checked; that lemma's pointwise estimate remains pending. Both numbered lemmas remain Partial. The 33 auxiliary and supplementary groups are tracked separately; these are groups of assertions, not 33 additional numbered results.

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
| [Lemma 2.7](manuscript/quadratic_character_sums_github.tex#L951-L964) | Quadric character-sum bound (2n^2-4n+4)p under smooth branch divisor | Pending | Pending |

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
| [Lemma 4.2](manuscript/quadratic_character_sums_github.tex#L1712-L1724) | Uniform conic parametrization by binary quadratics over every extension field, with independent derivative vectors | Pending | Pending |
| [Lemma 4.3](manuscript/quadratic_character_sums_github.tex#L1756-L1765) | Transverse plane-section character-sum bound (2n-1) sqrt(p)+1 | Pending | Pending |
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
| [Lemma 5.9](manuscript/quadratic_character_sums_github.tex#L2686-L2690) | Quadratic local trace is integral, divisible by p, and bounded by4p | Partial | [`QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean); [`QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd`](QuaternaryQuadraticForms/QuadraticTrace.lean) |
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

## Scope of partially checked numbered results

### Lemma 4.4

[Statement correspondence review](certification/correspondence/fourier_rays.md)

Checked clauses:

- All three weight conditions in (3.1), with literal polynomial evaluation and multiplicative characters.
- The exact zero-frequency identity in (4.4).
- The complete intermediate ray identity (4.5), including integral coefficient and frequency reduction.

Remaining clauses:

- The coefficient-uniform pointwise estimate in (4.4), including the exceptional polynomial D_p and all generic and exceptional frequency cases.

The geometric bounds from Lemmas 2.7, 4.1 and 4.3, and the plane-section counting step, have not been imported as assumptions or certified by this checkpoint.

### Lemma 5.9

[Statement correspondence review](certification/correspondence/quadratic_trace.md)

Checked clauses:

- The projective quadratic-character trace a_p(G) is an integer, identified explicitly with the existing complex-valued trace.
- The odd prime p divides that actual integer trace, for both finite-field forms and reductions of the manuscript's integral coefficients.

Remaining clauses:

- The bound |a_p(G)| ≤ 4p, requiring the n=2 specialization of Lemma 2.7 and its geometric hypotheses.

The checked divisibility statement only needs an odd prime and a homogeneous quadratic G. Nonsingularity and smoothness are not assumed for this clause. The pending size bound and Lemma 2.7 have not been imported as replacement axioms.

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

The allowed dependencies are the standard logical foundations `propext`, `Classical.choice`, and `Quot.sound`. Individual exports may additionally use only the exact literature premises named in their ledger entry. Their actual Lean types and axiom dependencies are in the [verification report](certification/verification_report.json). 1 external Lean premise is registered separately from these proved exports; see [Trusted inputs](TRUSTED_INPUTS.md).

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
lake exe cache get Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar Mathlib.Data.Fintype.BigOperators Mathlib.LinearAlgebra.Projectivization.Cardinality Mathlib.Analysis.Complex.Basic Mathlib.NumberTheory.DirichletCharacter.Bounds Mathlib.RingTheory.MvPolynomial.Homogeneous Mathlib.Data.Matrix.Mul Mathlib.FieldTheory.ChevalleyWarning Mathlib.NumberTheory.LegendreSymbol.Basic Mathlib.Algebra.Polynomial.Homogenize Mathlib.Data.Fin.VecNotation Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring
python3 scripts/verify_certificate.py
```

The verifier checks source identities, all 42 statement locations, the dependency graph, status accounting, locked toolchain and dependency checkouts, every local proof module, declaration kinds, actual types, and permitted axioms. The frozen definitions and uniformity in varying coefficients must be preserved in every later export.

## Next proof target

Proceed to the finite-field estimate branch: register the precise Weil and Katz source interfaces and prove their manuscript-specific specializations. Corollary 2.6 is the first projective-line estimate in that branch. The Katz specialization is needed for the remaining size clause of Lemma 5.9 and for Lemma 4.4. Retain the checked exact identities and divisibility result as inputs; the internal geometric arguments remain proof obligations.
