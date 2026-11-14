# Source correspondence: the generic homogeneous resultant system

## Registered mathematical boundary

`QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants` in
`Trusted/Elimination.lean` represents the generic-coefficient statement of
Lang's theorem on resultant systems. The reference identifier is
`EXT.LANG_ELIMINATION`. The premise concerns arbitrary systems of
homogeneous forms of specified positive degrees. It does not assume a
result about the manuscript's gradients, bad primes, exceptional planes,
height bounds, or smooth reduction.

Let `ι` be a finite nonempty index type, let `N > 0`, and assign a positive
degree `d i` to each `i : ι`. The coefficient index is

```text
HomogeneousCoefficient N d := Σ i : ι, HomogeneousMonomial N (d i),
HomogeneousMonomial N e := {m : Fin N →₀ ℕ // m.degree = e}.
```

For a field `K` and a coefficient assignment
`w : HomogeneousCoefficient N d → K`, the family
`homogeneousSystem N d w` consists of the actual polynomials

\[
 f_i(X)=\sum_{|m|=d_i}w_{i,m}X^m.
\]

The trusted conclusion is the existence of a natural number `s` and
polynomials

```text
R : Fin s → MvPolynomial (HomogeneousCoefficient N d) ℤ
```

such that, for every field `K` and every assignment `w`,

\[
 \exists x\in\overline K^{\,N}\setminus\{0\},\quad
 f_i(x)=0\ \text{for all }i
 \quad\Longleftrightarrow\quad
 R_j(w)=0\ \text{for all }j.
\]

On the left, `HasNonzeroGeometricZero` quantifies over an actual nonzero
vector in `AlgebraicClosure K` and evaluates each polynomial after mapping
its coefficients along `algebraMap K (AlgebraicClosure K)`. On the right,
the expression is `MvPolynomial.eval₂ (Int.castRingHom K) w (R j) = 0`.
The polynomial family is chosen before the field and coefficient
assignment. It is therefore the same integer family in characteristic
zero and at every prime.

## Exact source and conventions

S. Lang, *Algebra*, revised third edition, Graduate Texts in Mathematics
211, Springer, New York, 2002,
[DOI 10.1007/978-1-4613-0041-0](https://link.springer.com/book/10.1007/978-1-4613-0041-0),
is reference `[La]` in the frozen manuscript.
The directly relevant statement is **Chapter IX, Theorem 4.1, printed
p. 402**. It supplies a finite family of integer polynomials in the
generic coefficients and the stated equivalence under specialization to
any field. The interface retains its existence and specialization
conclusion; it does not require or claim an implemented algorithm for
computing the resultant family.

The following surrounding locators fix the interpretation precisely:

| Locator | Role in the interface |
| --- | --- |
| IX, §2, printed pp. 386–388 | Homogeneous zero sets in projective space exclude the origin. Fields of every characteristic are viewed as algebras over `ℤ`, and coefficient specialization is by a ring homomorphism. |
| IX, Theorem 3.1 and its following remarks, printed p. 389 | Projective elimination also applies over `ℤ`; a nontrivial common zero in an extension can be taken in an algebraic closure of the coefficient field. |
| IX, §3, formulas (1)–(2) and Theorem 3.2, printed p. 390 | The generic variables index all monomials of each assigned degree. The coefficient assignments form the whole affine coefficient space. |
| IX, Theorem 4.1, printed p. 402 | The exact finite integer resultant-system statement used as the trusted input. |
| IX, §4, proof, printed pp. 404–405 | The output family can be empty, and systems in which specialized forms are zero are included. |

The use of a finite index type `ι` instead of a numbered list of forms is
only a reindexing. There is no change to the source's mathematical
quantifiers. Finiteness of the coefficient index follows from finitely
many exponent vectors of a fixed degree in finitely many variables.

## Edge cases and uniformity

The interface allows `s = 0`. Lang explicitly uses the empty resultant
family in the proof for one positive-degree form in two variables: such a
form always has a nontrivial zero over an algebraic closure. Requiring a
nonempty output family would unnecessarily alter that formulation.

The input degrees are positive assigned degrees of homogeneity. A
specialized form may be zero, and some monomial coefficients may vanish.
This is compatible with the whole affine coefficient space on p. 390 and
with the zero-form cases explicitly considered on p. 405. Consequently
the interface does not assume that every specialization has nonzero
coefficients or a nonzero polynomial of that total degree.

There is no restriction that the field characteristic avoid any of the
degrees. In particular, a derivative may vanish after reduction; the
resultant criterion still applies to the resulting literal system. There
is no denominator-clearing step or unmentioned finite set of excluded
primes in the trusted statement.

The nonzero-vector condition is essential. Every positive-degree
homogeneous system has the origin as an affine zero. The trusted statement
is the projective criterion, not an affine elimination criterion. It does
not identify the resultant equations with generators of the naive
contraction of the unsaturated homogeneous ideal to the coefficient ring.

## Algebra kept inside the certificate

[`HomogeneousForms.lean`](../../QuaternaryQuadraticForms/HomogeneousForms.lean)
defines the finite monomial index and the literal coefficient-vector sum.
It proves its homogeneity, its coefficient formula, reconstruction of any
homogeneous polynomial from its coefficients, and compatibility with every
homomorphism of coefficient semirings. In particular, choosing the
coefficients of an actual polynomial does not introduce a separate
assumption that the generic form represents it.

Polynomial-parameter substitution is kept outside the trusted premise.
For a family whose coefficients are polynomials in parameters, the
certificate must substitute those coefficient polynomials into the
universal `R j` and prove that evaluation commutes with specialization.
The same requirement applies to coefficient reduction modulo a prime.
The alternative general formulation directly for families in
`ℤ[Y][X]` is mathematically supported by Lang, but is not the trusted
interface used here.

For Lemma 4.1(i), the manuscript writes eight equations: `F`, the generic
form `G`, and the six two-by-two gradient minors indexed by unordered
pairs of distinct columns. The implementation in
[`BadReductionSystem.lean`](../../QuaternaryQuadraticForms/BadReductionSystem.lean)
uses eighteen equations, indexed by `Fin 2 ⊕ (Fin 4 × Fin 4)`: `F`, `G`,
and all sixteen ordered minors. For

\[
 M_{ij}=\partial_iF\,\partial_jG-\partial_jF\,\partial_iG,
\]

the four diagonal entries are zero and `M_{ji}=-M_{ij}`. The six additional
reverse-order entries therefore repeat the same vanishing conditions.
This preserves the exact common zero locus of the manuscript's eight
equations over every field, including characteristic two. Lang permits
these zero and repeated forms. The assigned degree is two for `F` and
`n` for each of the other seventeen entries, including the zero minors.

`rank_two_ne_iff_minors_zero` in
[`RankMinors.lean`](../../QuaternaryQuadraticForms/RankMinors.lean) proves
the equivalence for the two actual evaluated rows. The bad-system module
then proves the homogeneous degrees, identifies the common nonzero zeros
with failure of the rank-two condition, and proves the coefficient-map
identities, including the exact bridge to `¬ GoodReductionAt p A G`.
[`GenericQuadricFamily.lean`](../../QuaternaryQuadraticForms/GenericQuadricFamily.lean)
constructs the fixed matrix and generic degree-`n` form over the actual
parameter ring. Its specialization theorems identify the resulting
eighteen equations with those for the chosen polynomial, including after
reduction. These are internal proofs and are not consequences asserted by
the trusted declaration.

After substituting the coefficient polynomials into the resultant family,
characteristic-zero smoothness must select a nonzero integer value `z`
of one resultant polynomial. Bad reduction must then be proved to imply
that each bad prime divides that same `z`.

Neither the existence of this `z` for the manuscript's equations nor the
finiteness of its bad-reduction primes is asserted by the trusted input.
The finite bad-prime product, its comparison with `|z|`, and the uniform
bound for polynomial evaluation in terms of the coefficient height are
also internal deductions. The finite resultant family is fixed before the
coefficients of `G` are chosen; that is the uniformity needed for the
later constants depending only on `F` and `n`.

This record specifies source correspondence and the trust boundary.
Compilation results, declaration hashes, axiom reports, and execution
status are recorded separately.
