# Source correspondence: the general Poisson input for Lemma 5.1

## Source and approved scope

The mapped source group `EXT.POISSON_R4` already permits the classical
Poisson formula for smooth compactly supported functions on four-dimensional
Euclidean space, including affine-lattice scaling and absolute convergence.
The source is D. R. Heath-Brown, *A new form of the circle method, and its
application to quadratic forms*, J. reine angew. Math. **481** (1996),
149–206, [DOI](https://doi.org/10.1515/crll.1996.481.149).
The [author manuscript](https://ora.ox.ac.uk/objects/uuid%3Abbd3c62f-f010-44b5-8be5-87e903fb0084/files/m7ec02df6e1b8303a66e7a6015ecb6044)
states the general n-dimensional formula in Section 3, proof of Theorem 2,
on author pages 19–20. It gives the negative Fourier sign and the positive
translation phase after the substitution x=b+qy.

The premise below registers only this standard analysis theorem and its
absolute-convergence clause for smooth compact support. It contains no
quadratic form, arithmetic weight, delta kernel, complete sum, counting
function, or manuscript asymptotic. In particular, the manuscript's
Lemma 5.1 is not accepted as an external input.

The pinned mathlib file `Mathlib/Analysis/Fourier/PoissonSummation.lean`
provides the one-dimensional theorem for functions from the reals to the
complex numbers. Its checked interfaces are not a four-dimensional affine
lattice theorem. The present registration uses the already approved general
four-dimensional literature input rather than claiming that interface exists.

## Exact mathematical statement

Let g: R^4 -> C be infinitely differentiable with compact support, and let
L>0. Write

\[
\widehat g(v)=\int_{\mathbb R^4}g(x)e^{-2\pi i\langle v,x\rangle}\,dx.
\]

Then the series of absolute values of `widehat g(u/L)` over integer u
converges. For every real vector z,

\[
\sum_{m\in\mathbb Z^4}g(z+Lm)
=L^{-4}\sum_{u\in\mathbb Z^4}
 e^{2\pi i\langle u/L,z\rangle}\widehat g(u/L).
\]

This is the classical affine-lattice Poisson formula. Smooth compactly
supported functions and their Fourier transforms have the decay required
for absolute convergence. The left lattice restriction has finite support;
its finiteness in the manuscript application is also proved internally.
The measure is canonical Euclidean Lebesgue measure. No additional Fourier
normalization or covolume convention is left implicit in the interface.

## Preregistered Lean interface

The complete type was elaborated as a local hypothesis, without introducing
an external declaration, before registration. Its exact elaborated type and
SHA-256 are stored in `certification/status.json`. The registered declaration
is `QuaternaryQuadraticForms.Trusted.poisson_four_dimensional`, in
`QuaternaryQuadraticForms/Trusted/Poisson.lean`.

```lean
∀ (g : RealVector4 → ℂ) (L : ℝ), IsSmoothWeight g → 0 < L →
  Summable (fun u : Fin 4 → ℤ =>
    ‖poissonFourierIntegral g (L⁻¹ • integerRealVector u)‖) ∧
  ∀ z : RealVector4,
    (∑' x : Fin 4 → ℤ, g (z + L • integerRealVector x)) =
      ((L : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((inner ℝ (L⁻¹ • integerRealVector u) z : ℝ) : ℂ)) *
        poissonFourierIntegral g (L⁻¹ • integerRealVector u)
```

`RealVector4`, `integerRealVector`, and `poissonFourierIntegral` are literal
Euclidean-space, coordinate-cast, and Bochner-integral definitions. The
smoothness order in `IsSmoothWeight` is infinity, not analytic regularity.

## Internal application obligations

The manuscript application must prove smoothness and compact support of its
actual test function; positivity of all scales; finite lattice and modulus
support; residue-class reindexing; equality of the exponential and ZMod
characters; the exact mixed complete sum; the B^4 integral substitution;
the identity B^4 Q^(-2) q^(-4)=B^2 q^(-3); and absolute convergence after the
finite arithmetic sums. These are internal proof obligations and are not
part of the registered premise. Source correspondence for the resulting
Lemma 5.1 is recorded separately after its complete proof is checked.
