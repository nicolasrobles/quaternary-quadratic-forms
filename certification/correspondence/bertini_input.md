# Source correspondence: the general Bertini tangent interface

## Scope and declaration

The registered literature declaration is
`QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent` in
[`Trusted/Bertini.lean`](../../QuaternaryQuadraticForms/Trusted/Bertini.lean).
It is a composite coordinate form of Bertini and the general projective
Jacobian criterion. It is not a verbatim restatement of Hartshorne II.8.18.
The geometric coordinate interpretation and its sources below are
registered with the Bertini source as the two components
`EXT.HARTSHORNE_BERTINI` and `EXT.PROJECTIVE_JACOBIAN`.

The interface concerns any algebraically closed field `K`, any number `N`
of homogeneous coordinates, and any `c` equations with `c + 2 ≤ N`.
The polynomials `P_i` have positive assigned degrees `d_i`. At every nonzero
common zero, their actual formal-gradient matrix is assumed to have rank `c`.
The conclusion supplies `u ≠ 0` such that, at each nonzero common zero `x`
also satisfying `u · x = 0`, there exists a vector `v` with

\[
 \nabla P_i(x)\cdot v=0\quad\text{for every }i,
 \qquad u\cdot v\ne0.
\]

The declaration has no restriction on the characteristic and no condition
that the characteristic be prime to the degrees. It assumes neither that
the projective zero locus is irreducible nor that it is nonempty.

## Exact primary sources

| Component | Source and locator | Use in the interface |
|---|---|---|
| Bertini hyperplane theorem | R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Chapter II, Theorem 8.18 and its proof, printed pp. 179-180; [inspected book PDF](https://ebooks.karbust.me/Mathematics/Robin%20Hartshorne%20-%20Algebraic%20Geometry%20%281977%29%20%5B978-1-4757-3849-0%5D.pdf), PDF pp. 194-195 | For a nonsingular closed subvariety over an algebraically closed field, hyperplanes not containing it and with regular scheme-theoretic intersection form a dense open subset of the dual projective space. |
| Smooth-scheme formulation of Bertini | Stacks Project, [Lemma 33.47.3, tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6), with [Situation 33.47.2, tag 0FD4](https://stacks.math.columbia.edu/tag/0FD4) | Confirms the arbitrary-characteristic statement for smooth schemes and a generating linear system giving an immersion; its proof retains noncontainment of every component. |
| Jacobian criterion and dimension | Stacks Project, [Definition 10.137.5, tag 00T6](https://stacks.math.columbia.edu/tag/00T6), and [Lemma 10.137.6, tag 00T7](https://stacks.math.columbia.edu/tag/00T7), especially (1), (2), (7), and the dimension calculation in the proof | An invertible maximal Jacobian minor gives a standard smooth local presentation. With `N-1` affine coordinates and `c` equations, the local geometric dimension is `N-1-c`. |
| Closed points and geometric regularity | Stacks Project, [Theorem 10.34.1, tag 00FV](https://stacks.math.columbia.edu/tag/00FV), and [Lemma 10.140.5, tag 00TV](https://stacks.math.columbia.edu/tag/00TV) | Over the algebraically closed field, closed points are rational and regularity agrees with smoothness for the finite-type local algebras used here. |
| Tangent-space interpretation | Stacks Project, [Lemma 10.140.1, tag 00TR](https://stacks.math.columbia.edu/tag/00TR), and [Lemma 10.106.3, tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ); also the local calculation in Hartshorne II.8.18, p. 180 | Identifies cotangent classes and regular hypersurface sections with a nonzero differential on the tangent space. |
| Several smooth components | Stacks Project, [Lemma 28.9.4, tag 02IR](https://stacks.math.columbia.edu/tag/02IR), and [Lemma 28.7.6, tag 033M](https://stacks.math.columbia.edu/tag/033M) | A regular Noetherian scheme is a finite disjoint union of normal integral components. Here the components inherit smoothness, so Bertini can be applied to each. |

These are general geometric sources. The interface does not assert a
special result about a quadratic matrix, arithmetic reduction, or the
manuscript's exceptional polynomial. The single Lean premise's registry
entry explicitly identifies both the Bertini and the
projective-Jacobian/tangent components of this boundary.

## Derivation of the coordinate interface

Let `X` be the projective closed subscheme defined by the homogeneous
polynomials `P_i`. The following argument explains precisely the geometric
interpretation included in the registered premise.

### Smoothness and dimension

At a nonzero common zero `x`, choose a coordinate `x_j ≠ 0` and use the
corresponding affine projective chart. Euler's homogeneous identity gives

\[
 \sum_k x_k\,\partial_k P_i(x)=d_i P_i(x)=0.
\]

Consequently the `j`th column of the homogeneous Jacobian is a linear
combination of its other columns. Its rank `c` therefore remains `c`
after passage to the `N-1` affine chart coordinates. Some `c` by `c`
minor is nonzero. Localizing at that minor gives a standard smooth
presentation by the general Jacobian criterion cited above. Thus `X` is
smooth at that point, of dimension `N-1-c`. The same argument on all charts
and at all closed points gives a smooth projective scheme. The inequality
`c + 2 ≤ N` ensures that each nonempty component has positive dimension.

This argument uses the ideal generated by the given equations and its
local presentations. It does not assume that an arbitrary list of
equations generates a radical ideal, or identify set-theoretic smoothness
with scheme-theoretic smoothness without a Jacobian argument.

### Components and the hyperplane

The scheme `X` is Noetherian. Smoothness gives regular local rings, and
the cited component facts give finitely many disjoint smooth integral
components. Apply Hartshorne II.8.18 to each component. Their good
hyperplanes form finitely many dense open subsets of the same irreducible
dual projective space. Their intersection is nonempty and has a `K`-point.
Choose a nonzero coefficient vector `u` for such a hyperplane.

If `X` is empty, any nonzero vector `u` works; such a vector exists because
`N ≥ 2`. If `c = 0`, the same argument concerns the whole projective space.
Thus neither exceptional case requires an additional hypothesis.

### The common tangent vector

The affine-cone tangent space at a nonzero common zero is

\[
 T_x=\{v\in K^N:\nabla P_i(x)\cdot v=0\text{ for every }i\}.
\]

The projective tangent space is the quotient of this space by the radial
line `Kx`. Euler's identity puts `x` in `T_x`. When `u · x = 0`, the
linear functional `v ↦ u · v` descends to this quotient. The chosen
hyperplane meets the component regularly and does not contain it.
In a local projective chart its defining equation therefore has nonzero
class in the maximal ideal modulo its square. Its differential is
nonzero on the projective tangent space. Lift a tangent direction on which
it is nonzero to a vector `v` in `T_x`. This gives exactly the two asserted
conditions on `v`.

Noncontainment is essential in this interpretation. Merely requiring the
intersection scheme to be smooth would also allow a hyperplane containing
a smooth component, and would not imply the asserted nonzero differential.
The cited Bertini theorem and the argument above supply both properties.

No division by any `d_i` occurs. The use of Euler's identity is valid when
the characteristic divides a degree, since its right side is zero at a
common zero independently of that divisibility.

## What must remain internal in this manuscript

The source for the intended application is
[`quadratic_character_sums_github.tex`](../../manuscript/quadratic_character_sums_github.tex),
Lemma 4.1(ii), especially the geometric argument at lines 1670-1689.
The following steps are not conclusions of this literature premise:

1. Choose `K = AlgebraicClosure (ZMod p)`, `N = 4`, `c = 2`, and the actual
   coefficient extensions of the matrix quadratic polynomial and `G`.
2. Prove positive degrees and homogeneity, and derive the exact Jacobian
   rank-two hypothesis from the literal `GoodReductionAt` condition.
3. Deduce rank three of the rows `∇F(x), ∇G(x), u`. Indeed, pair a putative
   linear relation with the supplied `v` to force its `u` coefficient to
   vanish; the known rank-two condition then forces the other coefficients
   to vanish. This is an internal linear-algebra proof.
4. Identify rank failure with the actual three-by-three gradient minors
   and the nonzero common zeros of the second elimination system.
5. Apply the separately registered Lang resultants, obtain a nonzero
   specialization, and prove the resulting polynomial over `ZMod p` is
   not the zero polynomial. The hyperplane witness need only lie in the
   algebraic closure; no rational hyperplane over `ZMod p` is asserted.
6. Construct the literal `D_p`, prove `D_p(0)=0`, prove its dual-form and
   transversality implications, and bound its degree uniformly in `G,p`.

In particular the premise contains no integer `N_G`, bad-prime assertion,
coefficient-height bound, resultant polynomial, `D_p`, quantitative degree
bound, character sum, or pointwise Fourier estimate. It cannot by itself
certify Lemma 4.1(ii).

## Review conclusion

The stated general coordinate interface follows from the cited geometric
results with the explicit interpretation above. No additional
characteristic, degree-coprimality, irreducibility, or rational-hyperplane
hypothesis is needed. The manuscript-specific specialization and every
subsequent algebraic deduction are separate internal proofs, reviewed in
[bad_reduction.md](bad_reduction.md). This is a source review of an external
interface; its geometric sources have not been reproved in Lean. The
complete lemma also requires the internal proofs, inspected theorem types
and dependencies, and the repository verification gates.
