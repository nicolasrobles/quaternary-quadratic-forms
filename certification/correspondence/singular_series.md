# Source correspondence: Lemma 3.9

## Scope and frozen source

This review covers every assertion of `lem:singseries`, Lemma 3.9:
ordered convergence of the actual complete-sum series restricted by
coprimality with `q`, its exact singular-series value, and its uniform
tail at every real cutoff at least one.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The manuscript and its PDF are unchanged.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | Symmetric nonsingular integral `A`, nonsquare determinant, actual `N_F=2|det A|`, and the original supplied character's Legendre values at good primes |
| `eq:singint`, `eq:SF`, lines 178–188 | Actual counting densities and the singular-series constant `L(1,chi)` times the corrected local-density product |
| `eq:Sdef`, lines 1029–1039 | Actual complete sums over residue units and four-coordinate residue vectors |
| `lem:crt`, `lem:gauss`, `lem:badprime` | Previously checked multiplicativity, good-prime-power calculation, and every-modulus complete-sum bound |
| `lem:conemod`, lines 1348–1408 | Previously checked cancellation of the actual modulus sums, specialized to zero frequency and gcd restriction one |
| `lem:density`, lines 1410–1444 | Actual local counting limits, absolute local series, good-prime formula, and corrected-product convergence |
| `lem:singseries`, lines 1446–1457 | Ordered convergence, `eq:seriesfactor`, and the uniform `eq:seriestail` |
| Lines 1459–1481 | Finite Abel summation, ordered boundary convergence, continuity, and the exact tail identity |
| Lines 1483–1513 | Absolute shifted series, Euler comparison, original-character L-values, and the limit at zero |

The complete source endpoint is `source_singular_series`. It includes
the manuscript's squarefree good-modulus hypotheses. Supporting
identities and estimates establish stronger versions without
squarefreeness. These stronger versions do not weaken the source
statement or change the underlying objects.

## Actual objects and conventions

| Manuscript object | Lean object |
| --- | --- |
| `S_c(0)` at positive modulus | Existing `unweightedCompleteSum c A 0`, through the previously proved totalization `unweightedCompleteSumValue` |
| Coefficient restricted by `(c,q)=1` | `coprimeCompleteSumValue q A c`, equal to the actual complete sum when `c.Coprime q`, and zero otherwise |
| Shifted summand | `singularSeriesTerm q A z c`, with denominator the complex embedding of the real power `(c:Real)^(4+z)` |
| Partial sum with real cutoff `X` | `singularSeriesPartialSum q A z X`, summed over `Finset.Icc 1 floor(X)` |
| Ordered value `D_q(z)` | `singularSeriesValue q A z`, defined as `limUnder atTop` of the real-cutoff partial sums |
| Actual shifted prime factor | `shiftedLocalDensity p A z`, the series of actual prime-power complete sums |
| Actual local density `sigma_p` | Existing `localQuadraticDensity p A`, defined from normalized zero counts in Lemma 3.8 |
| Original character Euler factor | `dirichletRealEulerFactor M chi p s = 1-chi(p)p^(-s)` |
| Source constant `S_F` | `singularSeriesConstant M chi A = chi.LFunction 1 * tprod(correctedLocalDensityFactor M chi A)` |
| Finite factor removed at `q` | `singularSeriesRemovalFactor q A`, the product of actual reciprocal densities over `singularSeriesPrimeDivisors q` |

The modulus-zero totalizations are proved to vanish. Zero is absent
from the source summation interval. At zero shift the denominator is
proved equal to the ordinary complex fourth power of the natural
modulus. The coprimality-masked coefficient sum is proved equal to the
existing `unweightedModulusSum q 1 A 0 X` from Lemma 3.7.

The boundary series is an ordered limit. Neither its definition nor
the final theorem asserts unconditional `Summable` or `HasSum` at
shift zero. `tsum` is used for the global complete-sum series only
after absolute convergence has been proved at a strictly positive
shift. The local prime-power series and the corrected Euler product
are absolutely convergent, including at zero, as separately proved.

The supplied character is retained at its original positive level
`M`. The source's primitive quadratic character is one such
character. The proof needs only its stated good-prime Legendre
values; no new assertion about its bad-prime values is imposed.
`NeZero M` expresses positivity of its natural-number modulus.

## Modules and public exports

All names are in the `QuaternaryQuadraticForms` namespace. The
milestone contains 82 public theorem exports in sixteen modules.
Concrete definitions are not counted as theorem exports or numbered
results. The live ledger records each actual export and its scope.

| Module | Theorem exports | Reviewed role |
| --- | ---: | --- |
| [SingularSeriesDefinitions.lean](../../QuaternaryQuadraticForms/SingularSeriesDefinitions.lean) | 4 | Actual masked coefficients, shifted terms, ordered partial sums and value; zero-term and source-sum bridges |
| [OrderedSeriesTail.lean](../../QuaternaryQuadraticForms/OrderedSeriesTail.lean) | 10 | General finite Abel formula, ordered convergence, exact tail identity, uniform tail estimate, and right continuity |
| [SingularSeriesConvergence.lean](../../QuaternaryQuadraticForms/SingularSeriesConvergence.lean) | 6 | Discharge of the analytic coefficient bound using actual Lemma 3.7, including uniform constant order |
| [ShiftedLocalDefinitions.lean](../../QuaternaryQuadraticForms/ShiftedLocalDefinitions.lean) | 4 | Actual prime-power coefficients and exact real-power normalization |
| [ShiftedLocalConvergence.lean](../../QuaternaryQuadraticForms/ShiftedLocalConvergence.lean) | 8 | All-prime absolute convergence, summable domination, right continuity and counting-density boundary value |
| [ShiftedLocalGoodPrime.lean](../../QuaternaryQuadraticForms/ShiftedLocalGoodPrime.lean) | 9 | Exact good-prime geometric series, original-character quotient, and numerator/denominator nonvanishing |
| [SourceDirichletCharacter.lean](../../QuaternaryQuadraticForms/SourceDirichletCharacter.lean) | 2 | Nonprincipality of the original supplied character, deduced from nonsquareness |
| [SingularEulerAbsolute.lean](../../QuaternaryQuadraticForms/SingularEulerAbsolute.lean) | 9 | Actual multiplicativity, positive-shift absolute summability and prime-power Euler product |
| [SingularEulerProduct.lean](../../QuaternaryQuadraticForms/SingularEulerProduct.lean) | 4 | Exact removal of factors at primes dividing `q` |
| [SingularEulerOrdered.lean](../../QuaternaryQuadraticForms/SingularEulerOrdered.lean) | 5 | Positive-shift agreement of ordered and absolute sums; literal real-cutoff finite tails |
| [SingularSeriesLFactors.lean](../../QuaternaryQuadraticForms/SingularSeriesLFactors.lean) | 7 | Original-character Euler factors, nonvanishing, continuity, and library L-function comparison |
| [SingularSeriesPrimeSets.lean](../../QuaternaryQuadraticForms/SingularSeriesPrimeSets.lean) | 1 | Exact finite prime-divisor set |
| [SingularSeriesConstant.lean](../../QuaternaryQuadraticForms/SingularSeriesConstant.lean) | 3 | Source constant, good-density nonvanishing, and justified finite removal product |
| [SingularSeriesEulerComparison.lean](../../QuaternaryQuadraticForms/SingularSeriesEulerComparison.lean) | 4 | Finite corrected Euler comparison and boundary continuity without inverting bad densities |
| [SingularSeriesBoundary.lean](../../QuaternaryQuadraticForms/SingularSeriesBoundary.lean) | 2 | Zero-shift corrected product and exact identity for the actual ordered series |
| [SingularSeriesTheorem.lean](../../QuaternaryQuadraticForms/SingularSeriesTheorem.lean) | 4 | Full convergence, both tail-limit formulations, and complete source theorem |

## Ordered convergence and the uniform tail

The general analytic lemma starts with an actual sequence `a` whose
zero coefficient vanishes and whose ordered coefficient sums satisfy

\[
|A(v)|\le K v^{3+\eta}\quad(v\ge1),\qquad 0<\eta\le\tfrac12.
\]

For every real exponent `s >= 4`, finite Abel summation gives

\[
P_s(X)=X^{-s}A(X)+s\int_1^X A(v)v^{-s-1}\,dv.
\]

The integration uses the step function with the literal natural
floor. Its local integrability and the improper-integral majorant
are proved. The boundary term tends to zero. The ordered partial
sums therefore converge to

\[
D(s)=s\int_1^\infty A(v)v^{-s-1}\,dv.
\]

Subtracting the finite identity yields the exact tail identity

\[
D(s)-P_s(X)
=s\int_X^\infty A(v)v^{-s-1}\,dv-X^{-s}A(X).
\]

The endpoint has a minus sign, and the lower integration endpoint is
the actual real cutoff, including integer cutoffs. Absolute values
give

\[
|D(s)-P_s(X)|
\le K\left(1+\frac{s}{s-3-\eta}\right)X^{3+\eta-s}
\le9KX^{-1+\eta}.
\]

The proof establishes the integral estimate and the elementary
uniform bound for every `s >= 4`. Dominated convergence, with
majorant `K v^(-2+eta)`, proves right continuity at `s=4`.

For the actual coefficient, Lemma 3.7 is specialized with `d=1`,
`e=q`, and `u=0`. The cone condition is proved for this zero vector.
Its already uniform constant supplies

\[
|T_q(v)|\le K_{A,\eta}q^\eta v^{3+\eta}.
\]

The final proof chooses `eta = min(epsilon, 1/2)` and
`C = 9 K_(A,eta)`. Since `q >= 1`, `X >= 1`, and `eta <= epsilon`,
the exponent weakening proves

\[
|D_q(z)-P_q(z,X)|
\le C_{A,\varepsilon}q^\varepsilon X^{-1+\varepsilon}
\quad(z\ge0,\ X\ge1).
\]

The source theorem quantifies in the following order:

1. Fixed `A`, symmetry, nonsingularity, nonsquareness, and `epsilon > 0`.
2. One positive real constant `C`.
3. Every positive supplied character level `M`, the character `chi`,
   and its good-prime Legendre agreement.
4. Every positive squarefree `q` coprime to `N_F`.
5. Every real cutoff `X >= 1`.

Thus the theorem type itself encodes the required dependence on
`F,epsilon` only. The supporting estimate is also uniform in all
nonnegative shifts. No coefficient-bound premise survives in the
actual-object endpoints.

The finite-tail bridge proves, for `1 <= X <= Y`,

\[
P_q(z,Y)-P_q(z,X)
=\sum_{\lfloor X\rfloor<c\le\lfloor Y\rfloor}
\operatorname{singularSeriesTerm}(q,A,z,c).
\]

Its interval membership is proved equivalent to `X < c <= Y`.
`tendsto_singularSeriesTail_Ioc` therefore identifies the source's
literal ordered tail, not only a formal difference of unrelated
values.

## The shifted Euler product and the original character

Lemma 3.3 bounds the actual coefficient by
`4 sqrt(|det A|) c^3`. Consequently the shifted summand is bounded
by a constant times `c^(-1-z)` for `z > 0`, proving absolute
summability. Actual CRT multiplicativity and coprimality of the
masked coefficients supply the hypotheses of mathlib's Euler-product
theorem. Its prime-power factors are exactly

\[
\begin{cases}1,&p\mid q,\\ \sigma_p(z),&p\nmid q.\end{cases}
\]

At every prime the shifted coefficient is the original local
coefficient multiplied by `p^(-kz)`. Its norm is no larger than the
original coefficient's norm for `z >= 0`. The established summable
local majorant proves continuity on the closed nonnegative half-line
and the equality `sigma_p(0)=sigma_p` with the actual counting
density, including bad primes and two.

At a good prime the exact geometric sum proves

\[
\sigma_p(z)=
\frac{1-\chi(p)p^{-2-z}}{1-\chi(p)p^{-1-z}}.
\]

Both numerator and denominator are proved nonzero for nonnegative
shifts. These facts, and the nonvanishing of good counting densities,
are conclusions rather than assumptions.

Nonsquareness of the determinant provides an actual positive good
integer with Jacobi value `-1`, using the already checked arithmetic
construction from Lemma 3.7. Multiplicativity and agreement at good
primes transfer this value to the original supplied character.
The principal character is either one or zero at any residue, so
the supplied character is proved nonprincipal. No nonprincipality
premise or replacement character is introduced.

## L-function input and the boundary comparison

The manuscript cites Montgomery–Vaughan, Section 4.3, for the
needed Dirichlet L-function facts. The mapped group
`EXT.MV_DIRICHLET_L` is realized by verified results of the pinned
official mathlib revision, not by a new external Lean premise:

- `DirichletCharacter.LSeries_eulerProduct_hasProd` for real part
  strictly greater than one;
- `DirichletCharacter.LFunction_eq_LSeries` in that same half-plane;
- `DirichletCharacter.differentiable_LFunction` for a nonprincipal
  character, supplying continuity at one;
- `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`, supplying
  nonvanishing at `2+z`.

The boundary value is `DirichletCharacter.LFunction chi 1`.
The library's naive unconditional `LSeries` is never substituted at
one. No external axiom is added for the citation, and the number of
registered literature premises remains four.

For clarity, the formal Euler comparison uses a finite correction
equivalent to the manuscript's separated good/bad-prime products.
Write `E_p(s)=1-chi(p)p^(-s)` and let `E` be the primes dividing
`q N_F`. Define the restricted corrected factor

\[
R_{q,p}(z)=
\begin{cases}
E_p(1+z),&p\mid q,\\
E_p(1+z)\sigma_p(z),&p\nmid q.
\end{cases}
\]

Outside `E` the good-prime formula gives `R_(q,p)(z)=E_p(2+z)`.
The inverse exponent-two L-value and a finite modification yield

\[
\prod_pR_{q,p}(z)
=L(2+z,\chi)^{-1}
\prod_{p\in E}\frac{R_{q,p}(z)}{E_p(2+z)}.
\]

Every denominator here is proved nonzero. The finite correction
contains no inverse bad density and no inverse whole singular-series
constant. A zero bad density is allowed: it makes the corresponding
replacement factor and product zero without invalidating the finite
modification theorem.

For `z > 0`, multiplying by the convergent exponent-one L-product
identifies the actual absolutely convergent series with `L(1+z,chi)`
times this correction. Every constituent of the finite correction is
right-continuous at zero, and `L(2,chi)` is nonzero. Thus the
comparison passes to the boundary without interchanging a limit
with an uncorrected infinite product there.

At zero, uniqueness of the convergent corrected product identifies
the correction as the original corrected density product times
`prod_(p|q) sigma_p^(-1)`. Here `q` is coprime to `N_F`, so only
proved nonzero good densities are removed. Original character values
and actual densities remain in every bad-prime factor.

Finally, both the actual ordered series and the L-function expression
have the same right limit. The filter `nhdsWithin (Ioi 0) 0` is
nontrivial; Lean's limit-uniqueness theorem requires and obtains its
`NeBot` instance. This proves the exact boundary identity

\[
\sum_{\substack{c\ge1\\(c,q)=1}}\frac{S_c(0)}{c^4}
=\mathfrak S_F\prod_{p\mid q}\sigma_p^{-1}.
\]

## Boundary cases and final audit

- Modulus one is included, with complete-sum coefficient one and
  an empty finite removal product.
- The excluded zero modulus is explicitly zero in the totalizations.
- Real cutoffs, including integral endpoints, are handled exactly.
- Every positive epsilon is covered by the internal smaller exponent.
- Nonsquareness includes negative determinants; the previously proved
  Jacobi witness handles the sign cases.
- Every prime is covered by local convergence, including two and all
  bad primes.
- Bad local densities may vanish. Only good factors dividing `q`
  are inverted.
- The original character, including its bad-prime values, is retained.
- No conditional series is rearranged as an unconditional sum at zero.
- No partial-sum bound, nonprincipality, local nonvanishing, finite
  bad-prime support, or boundary identity is left as a new premise.

Independent mathematical reviews checked the analytic half and the
Euler/boundary half, including the literal tail bridge and the final
constant order. The final source target builds under official Lean
4.24.0, pinned mathlib, `warningAsError=true`, and
`autoImplicit=false`. Actual theorem types and axiom lists are
inspected separately from source correspondence. Aggregate execution
and exact-commit GitHub evidence are recorded in
[CHECKPOINT.md](../../CHECKPOINT.md), so a targeted build is not
represented as an aggregate or remote verification run.

No assertion is made here about Lemmas 3.10–3.11, the global analytic
theorems, or the thirty-three separately tracked supplementary groups.
