# Source correspondence: the Katz surface input

## Scope of the trusted statement

`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data` is a composite
literature interface. It combines Katz's cohomological theorem and trace
formula with the general adjunction and degree formulas for a smooth
projective hypersurface. It is not a verbatim quotation of one theorem,
and it does not assume Lemma 2.7, its quadric coefficient, or its scalar
character-sum bound.

The interface applies to arbitrary nonzero homogeneous polynomials
`F G : MvPolynomial (Fin 4) (ZMod p)` of positive degrees `m n`, respectively.
Its hypotheses are geometric irreducibility of `F`, the actual nonvanishing
gradient predicate `ProjectiveHypersurfaceSmooth` for `F`, and the actual
rank-two predicate `ProjectiveIntersectionTransverseRank` for `(F,G)`.
All three geometric conditions are imposed after mapping coefficients to
`AlgebraicClosure (ZMod p)`. The character is a nonprincipal
`MulChar (ZMod p) ℂ` whose `n`th power is principal.

For an integer polynomial `c` satisfying `SurfaceChernRelation m c`, the
conclusion is the existence of a natural number `r` and complex numbers
`λ : Fin r → ℂ` such that

\[
 r=m[T^2]\bigl(c(T)(1-nT+n^2T^2)\bigr),\qquad
 \operatorname{projectiveHypersurfaceTrace}(F,\psi,G)=\sum_i\lambda_i,
 \qquad |\lambda_i|=p.
\]

The first equality is an equality in the integers. The number of terms is
therefore nonnegative by the conclusion itself; no absolute value is
silently applied to the Chern expression. The sum is the actual finite sum
on the projective zero set of `F`, not a free variable representing a sum.

## Published inputs and exact locators

**Katz.** N. M. Katz, *Estimates for nonsingular multiplicative character
sums*, International Mathematics Research Notices **2002**, no. 7,
333–349, [DOI 10.1155/S1073792802106088](https://doi.org/10.1155/S1073792802106088).
The manuscript cites Theorem 8.1(1) and equation (5.3). The directly inspected
[author version](https://web.math.princeton.edu/~nmk/multp5.pdf) uses sequential
numbering: the corresponding statement is Theorem 18(1), printed p. 12;
the trace identity is on printed p. 5. Its hypotheses are a smooth,
geometrically connected projective variety, a transverse positive-degree
hypersurface section, and a nontrivial character annihilated by that degree.
It gives concentration in the middle cohomological degree, purity of that
weight, and dimension
\[
 (-1)^{\dim X}\int_X\frac{c(T_X)}{1+nL}.
\]
For a surface the trace sign is positive and purity gives complex absolute
value `p` for each Frobenius eigenvalue. The author version's Section 8,
printed p. 11, explicitly allows the section degree to be divisible by the
characteristic. Part (1) does not require the auxiliary hyperplane appearing
in part (2).

**General hypersurface intersection theory.** W. Fulton, *Intersection
Theory*, second edition, Springer, 1998,
[DOI 10.1007/978-1-4612-1700-8](https://doi.org/10.1007/978-1-4612-1700-8):
Examples 3.2.11–3.2.12, printed pp. 59–60, give the projective-space Euler
sequence and adjunction; Examples 2.5.1–2.5.2, printed p. 42, identify degree
with the top hyperplane intersection and give multiplication of degree
under a hypersurface section. Thus a degree-`m` smooth surface in projective
three-space satisfies
\[
 c(T_X)=\frac{(1+L)^4}{1+mL},\qquad \int_X L^2=m.
\]
These are arbitrary-field formulas: the book's conventions, printed p. 5,
allow an arbitrary base field. The indicated pages were checked in the
[searchable book text](https://djvu.online/file/8KbyCnh9POwWS).

Independent primary formulations of the ingredients are available in the
Stacks Project: [Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH) for the
Euler sequence, [Section 29.35, Lemma 29.35.17](https://stacks.math.columbia.edu/tag/01V4)
for the smooth conormal sequence, and
[Tag 02UF](https://stacks.math.columbia.edu/tag/02UF) for Whitney
multiplicativity. The coordinate interpretation also uses the usual local
Jacobian criterion, expressed by standard smooth presentations in
[Section 10.137](https://stacks.math.columbia.edu/tag/00T1), and the
hypersurface construction in
[Section 33.35.1](https://stacks.math.columbia.edu/tag/089X).

## Why the coordinate hypotheses suffice

The following is the mathematical interpretation of the general interface,
not an assertion that the repository formalizes schemes, Chern classes, or
étale cohomology.

A nonzero homogeneous irreducible polynomial of positive degree over the
algebraic closure defines a nonempty integral projective hypersurface of
dimension two in projective three-space. Irreducibility therefore supplies
geometric connectedness as well as reducedness. The gradient condition
supplies smoothness by the Jacobian criterion. It is essential that this
condition quantifies over geometric points, not only prime-field points.

At each common geometric zero, the two independent gradient rows say that
the restriction of `G` cuts the smooth surface transversely. In particular,
`G` cannot vanish identically on that surface: irreducibility would imply
`F` divides `G`, and differentiation on `F = 0` would make the rows
dependent. The positive-degree proper section is a divisor; its dimension
is one. Projective dimension theory also guarantees a common zero. Thus
no additional nonemptiness or codimension hypothesis is being discarded.
This includes no quadric-specific geometric deduction.

There is no need to assume `p ∤ m` or `p ∤ n`. The geometric predicates
exclude singular or nontransverse inseparable cases directly. Allowing
`n = 1` causes no inconsistency: the two character hypotheses then have no
simultaneous instance.

The condition `ψ ^ n = 1` makes the character value independent of a
nonzero rescaling of homogeneous coordinates. Extension of a nonprincipal
multiplicative character by zero makes the contribution of `G = 0` zero.
Consequently Katz's sum over the open complement is precisely the sum
over all projective points used here. A complex realization of the finite
order character and the Frobenius eigenvalues is part of the literature
interpretation of purity and the trace formula.

## What the certificate proves internally

`SurfaceChernRelation m c` imposes the adjunction relation only in degrees
zero, one and two. Higher coefficients of `c` are irrelevant. The
polynomial calculations determine these three coefficients and calculate
`surfaceSectionEulerCoefficient`; they are proved in `SurfaceChern.lean`.
The trusted statement does not take their explicit expanded values as
additional conclusions.

The quadric application separately establishes its defining polynomial,
homogeneity, nonvanishing, geometric irreducibility, and actual gradient
condition from the matrix hypotheses. It retains the manuscript's actual
transversality and character hypotheses. The equality between the general
projective trace and the matrix-quadric trace is proved in
`ProjectiveSurfaceTrace.lean`.

Finally, the substitution `m = 2`, verification of
`c = 1 + 2T + 2T²`, coefficient evaluation `2n² − 4n + 4`, and triangle
inequality are internal deductions. They must not be imported as literature
premises. The trusted boundary is exactly the general spectral statement
with the general geometric interpretation and intersection-theoretic
formulas disclosed above. It should be registered against both `EXT.KATZ`
and `EXT.HYPERSURFACE_CHERN`.
