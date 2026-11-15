# Source correspondence: Heath-Brown's delta construction and Lemma 2.1

## Scope and verification state

This record covers the implemented fixed construction in [HB], Theorem 1
and Section 3, its separately registered input `EXT.HB_DELTA`, and the
internal proofs completing `lem:delta`, Lemma 2.1. The endpoint is
`QuaternaryQuadraticForms.source_delta_symbol` in
[DeltaSymbolTheorem.lean](../../QuaternaryQuadraticForms/DeltaSymbolTheorem.lean).
Implementation, actual-interface inspection, and independent mathematical
correspondence reviews are complete. Full aggregate execution state and
the corresponding local and exact-commit GitHub evidence belong in
[CHECKPOINT.md](../../CHECKPOINT.md); this correspondence record does not
replace those execution checks.

The frozen manuscript is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
SHA-256 `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
Its lines 615–626 contain the numbered statement, lines 628–634 explain
the normalization restriction, and lines 636–637 state finiteness of the
outer sum. Neither the manuscript nor its PDF is changed by this milestone.

## Accepted primary source

D. R. Heath-Brown, *A new form of the circle method, and its application
to quadratic forms*, Journal für die reine und angewandte Mathematik
481 (1996), 149–206,
[DOI 10.1515/crll.1996.481.149](https://doi.org/10.1515/crll.1996.481.149).

The source text was checked in the
[author PDF at Oxford University Research Archive](https://ora.ox.ac.uk/objects/uuid%3Abbd3c62f-f010-44b5-8be5-87e903fb0084/files/m7ec02df6e1b8303a66e7a6015ecb6044).
The page numbers below are the author PDF's own page numbers; they are not
assertions about the journal scan's pagination. The indexed primary PDF
text was available for inspection. Direct binary download and screenshot
requests returned HTTP 403, so no claim of visual inspection is made.

| Author-PDF location | Accepted content |
| --- | --- |
| Theorem 1, p. 3 | Delta identity and kernel properties |
| Section 2, (2.1), p. 14 | The fixed exponential bump |
| Section 2, (2.4), p. 15 | Its integral normalization |
| Section 3, (3.1)–(3.3), p. 17 | Fixed shifted weight, Poisson estimate, normalization |
| Section 3, p. 18 | Divisor pairing, additive orthogonality, and kernel formula |
| Section 3, p. 19 | Size and joint smoothness by locally finite sums |

## Actual constructed objects

All functions below are definitions, not additional uninterpreted
constants. The fixed real functions are

\[
w_0(t)=
\begin{cases}
\exp\bigl(-(1-t^2)^{-1}\bigr),&|t|<1,\\
0,&|t|\ge1,
\end{cases}
\qquad
c_0=\int_{\mathbb R}w_0(t)\,dt,
\qquad
\omega(t)=\frac4{c_0}w_0(4t-3).
\]

Define

\[
S(Q)=\sum_{r\ge1}\omega(r/Q),\qquad
h(x,y)=\sum_{j\ge1}
\frac{\omega(xj)-\omega(|y|/(xj))}{xj},\qquad
c(Q)=\frac{Q}{S(Q)}.
\]

The actual positive summation indices have type `PNat` (`ℕ+`).
Real division makes these definitions total in Lean; assertions about the
kernel are restricted to `x>0`, and normalization will only be used where
`S(Q)>0` has been proved. In particular a total value assigned to `c(2)`
by division by zero carries no normalized delta identity.

Write `e(t)=exp(2*pi*i*t)` and define the actual complex expression

\[
T(Q,n)=\sum_{q\ge1}\ \sum_{a\bmod q}^{*}
e(an/q)\,h(q/Q,n/Q^2).
\]

The star means precisely the residue units. The implementation uses the
existing `integralRamanujanSum`, with its standard additive character on
`ZMod q`. The internal unit-sum and exponential-sum bridges identify this
with the literal source phase. The modulus-one term is included. No
generic formal sum is substituted for the actual residue sum.

| Source object | Implemented definition |
| --- | --- |
| `w_0` | `heathBrownBaseBump` |
| `c_0` | `heathBrownBumpMass`, the actual real Bochner integral |
| `omega` | `heathBrownBump` |
| `S(Q)` | `heathBrownSamplingSum Q`, a `tsum` over `PNat` |
| `h(x,y)` | `heathBrownDeltaKernel (x,y)`, the fixed positive-index series |
| `c(Q)` | `heathBrownNormalization Q` |
| One positive-modulus term | `deltaSymbolTerm h Q n c` |
| Integer upper bound | `deltaSymbolCutoff Q n` |
| Finite positive-modulus range | `deltaSymbolModuli Q n` |

The first seven definitions are in
[DeltaSymbolDefinitions.lean](../../QuaternaryQuadraticForms/DeltaSymbolDefinitions.lean).
The two cutoff definitions are in
[DeltaSymbolSupport.lean](../../QuaternaryQuadraticForms/DeltaSymbolSupport.lean).
The generic normalization module separately defines `bumpSamplingSum`;
its specialization to `heathBrownBump` is definitionally the source
sampling sum, with the positive-index casts made explicit.

## Exact mathematical payload of the single trusted input

The single accepted declaration is
`QuaternaryQuadraticForms.Trusted.heathBrown_delta_data` in
[Trusted/HeathBrown.lean](../../QuaternaryQuadraticForms/Trusted/HeathBrown.lean).
It is a conjunction of the following statements about the definitions
above. It supplies no manuscript-specific matrix, quadratic form, Fourier
weight, or counting conclusion.

1. The function `omega` is continuous on `Real`, is nonnegative
   everywhere, is strictly positive on `(1/2,1)`, and is zero outside
   that open interval, including both endpoints.
2. The actual two-variable function `h` is infinitely differentiable
   on the open set `{(x,y) : 0<x}`. The implemented property is
   `ContDiffOn ℝ ∞ heathBrownDeltaKernel {z | 0 < z.1}` with
   `open scoped ContDiff`. No regularity at `x=0` is asserted.
   In the pinned library the order is
   `WithTop ENat`: the scoped `∞` means smoothness, whereas the outer
   `top` means analyticity. The interface uses smoothness only.
3. There is an absolute constant `B>0`, chosen before `x,y`, such that
   `abs(h(x,y)) <= B/x` whenever `x>0`.
4. If `x>0` and `max(1,2*abs(y)) < x`, then `h(x,y)=0`.
5. For every real `Q>1` and every integer `n`, the unnormalized identity
   is
   \[
   T(Q,n)=Q\,S(Q)\,\mathbf 1_{n=0}.
   \]
   Real factors on the right are cast to `Complex` when necessary.
6. For every natural number `N>=2`, there is a constant `A_N>0`, chosen
   before the real parameter `Q`, such that
   \[
   |S(Q)-Q|\le A_N\frac{Q}{Q^N}\qquad(Q>1).
   \]

The smoothness and positivity clauses are properties of the source's
fixed bump and kernel. They do not select a new kernel for each `Q` or
`n`. The raw error constant is independent of `Q,n`; the size constant
is independent of `Q,n,x,y`. Continuity of `omega` is a weakening of
its smoothness in the source.

The accepted-input entry in
[status.json](../status.json) records the declaration's exact inspected
Lean type, declaration kind, and type hash. The verifier checks that
record separately from proved exports and enforces the allowed axiom
dependencies. The corresponding source record in
[reference_inputs.json](../reference_inputs.json) points to this review
and to the source locators above. The kernel retains its actual
construction, so later cited integral estimates concern this same
function, rather than an independently chosen existential witness.

## Why the unnormalized identity is valid, including at Q=2

This identity is the source's Section 3 calculation before division by
the normalization. It is not an assumption of the manuscript's final
normalized lemma.

For fixed `Q>1`, let

\[
D_Q(n)=\sum_{r\mid n,\ r\ge1}
\left\{\omega(r/Q)-\omega\left(\frac{|n|}{rQ}\right)\right\}.
\]

For `n!=0`, pairing divisors of `abs(n)` sends `r` to `abs(n)/r`, so
`D_Q(n)=0`. For `n=0`, the second weight is zero and every positive
integer divides zero; the weight support nevertheless makes the sum
finite, giving `D_Q(0)=S(Q)`.

Additive orthogonality replaces the divisor indicator by the unrestricted
residue sum divided by `r`. Grouping each fraction into lowest terms,
with `r=q*j`, and using the displayed definition of `h`, gives

\[
D_Q(n)=Q^{-1}T(Q,n).
\]

All rearrangements here are finite for fixed `Q,n`, because the two
weight terms restrict the positive integer `r` to bounded intervals.
No division by `S(Q)` or nonvanishing hypothesis is used. Consequently
`T(Q,n)=Q*S(Q)*1_(n=0)` remains valid at `Q=2`.

At `Q=2`, every `omega(r/2)` is zero: `r=1,2` give the support
endpoints and `r>=3` lies outside the support. Thus `S(2)=0`, and the
unnormalized identity asserts that `T(2,n)=0`. It does not assert a
normalized delta formula at this parameter.

Theorem 1 is printed with the range `Q>1`. The structural interface
retains the unnormalized calculation valid throughout that range,
and the manuscript wrapper normalizes only in its own safe range
`Q>=3`. It does not import the printed positive-normalizer claim at
the exceptional value `Q=2`.

## Why the raw sampling estimate is uniform for Q>1

The Poisson paragraph on source p. 17 explicitly works with `Q>1`.
For the fixed Fourier transform
`omega_hat(t)=integral omega(u)*e(-t*u) du`, its calculation gives

\[
S(Q)-Q=Q\sum_{m\ne0}\widehat\omega(Qm).
\]

Integrating by parts `N` times bounds each nonzero term uniformly by
`C_N*Q*(Q*abs(m))^(-N)`. For `N>=2`, the sum over nonzero `m`
converges, giving the asserted bound `A_N*Q/Q^N` with `A_N`
independent of `Q`. Increasing a nonnegative bound produces `A_N>0`.
This is the uniform estimate in the source proof before (3.3).

This reasoning is distinct from taking an eventual asymptotic estimate
for `c(Q)` and declaring it uniform on an arbitrary parameter set.

## Internal proofs for the manuscript range

The following manuscript deductions are proved in the project and are
not included in the trusted input.

### Positivity and uniform lower bound

For `Q>=3`, choose an integer `r` nearest `3Q/4`. Then `r>0` and

\[
\frac7{12}\le\frac rQ\le\frac{11}{12}.
\]

The displayed compact interval lies inside `(1/2,1)`. Continuity and
strict positivity of the fixed `omega` give one `m>0` such that
`omega(t)>=m` throughout this interval. Nonnegativity of all summands,
together with finiteness of the positive-index support, yields
`S(Q)>=omega(r/Q)>=m`. The choice of `m` precedes `Q`.

This also proves the ordinary normalization admissibility condition:
there is a positive integer strictly between `Q/2` and `Q`. A simpler
floor argument gives this condition for all `Q>2`, but does not alone
supply the uniform lower bound used here.

### Rapid normalization and exact delta identity

For each natural `j>=1`, apply the raw estimate with `N=j+1`. Since
`S(Q)>=m`, field algebra and positivity give

\[
|c(Q)-1|=\frac{|Q-S(Q)|}{S(Q)}
\le\frac{A_{j+1}}m Q^{-j}\qquad(Q\ge3).
\]

The natural-order helper is `heathBrownNormalization_error_bound`.
The final endpoint retains the stronger literal real-order reading of
the source: `heathBrownNormalization_error_bound_real` proves, for
every real `j>=1`,

\[
\exists C_j>0\ \forall Q\ge3,\qquad
|c(Q)-1|\le C_jQ^{-j}.
\]

This corollary chooses the natural ceiling of `j`, applies the natural
helper, and uses monotonicity of real powers for `Q>=1`. The resulting
constant is chosen after `j` and before `Q,n`; no new literature input
is used for real orders.

Dividing the unnormalized identity by `Q*S(Q)` yields exactly the
manuscript's factor `c(Q)/Q^2`, with positivity of both denominators
proved first. The same fixed `h` works simultaneously for every allowed
`Q` and `n`.

### Finiteness, residue conventions, and source assembly

The support clause implies that the outer term is zero whenever

\[
q>\max\left(Q,\frac{2|n|}{Q}\right).
\]

`deltaSymbol_modulus_bound_eq_max` proves that this displayed maximum
equals the scaled support expression used by `deltaSymbolCutoff`.
The cutoff is its natural floor, and `mem_deltaSymbolModuli` identifies
membership with the precise positive-integer inequality. The remaining
support proofs establish that every term outside this finite set is
zero, and derive finite support, summability, absolute summability, a
`HasSum` statement, and equivalent finite-sum presentations. These
results hold for every positive real `Q` and every kernel satisfying
the support condition, without using the Heath-Brown premise.

The phase bridge uses each unit's canonical residue representative and
the actual complex exponential; at modulus one the unit sum consists
of its single trivial phase. Thus it preserves negative and zero
integer `n` and includes the first positive modulus.

The endpoint `source_delta_symbol` recovers all of lines 615–626:
one common smooth kernel and one normalization function, positivity
for every real `Q>=3`, the identity for every integer `n`, rapid error
for every real `j>=1`, and the global kernel size and support.
It also includes finite support of the actual outer summand, proving
the consequence in lines 636–637. The explicit finite identity is
additionally available as `heathBrown_delta_finite_identity`.

## Complete module and theorem-interface mapping

All theorem names in this table are in namespace
`QuaternaryQuadraticForms`. The five modules introduce 29 proved
theorem interfaces and one separately registered literature axiom.
Definitions are not counted as theorem exports. The complete
registration and inspected types are recorded in `status.json`.

| Module | Theorem interfaces | Exact interfaces and role |
| --- | ---: | --- |
| [DeltaSymbolDefinitions.lean](../../QuaternaryQuadraticForms/DeltaSymbolDefinitions.lean) | 0 | Seven actual source definitions listed above; no axiom |
| [Trusted/HeathBrown.lean](../../QuaternaryQuadraticForms/Trusted/HeathBrown.lean) | 0 | The single axiom `Trusted.heathBrown_delta_data`; its nine top-level conjuncts express the six mathematical groups specified above |
| [DeltaSymbolNormalization.lean](../../QuaternaryQuadraticForms/DeltaSymbolNormalization.lean) | 4 | `bumpSamplingSum_finite_support`, `bumpSamplingSum_summable`, `bumpSamplingSum_uniform_pos`, `bumpNormalization_error_bound`: generic sampling support, the compact-interval lower bound, and natural-order normalization |
| [DeltaSymbolSupport.lean](../../QuaternaryQuadraticForms/DeltaSymbolSupport.lean) | 16 | Literal phases, exact cutoff, finite support, convergence, and reindexing; listed completely below |
| [DeltaSymbolTheorem.lean](../../QuaternaryQuadraticForms/DeltaSymbolTheorem.lean) | 9 | Specialization to the fixed source definitions, positive normalization, natural and real decay, both identities, and the complete source endpoint; listed completely below |

The 16 support interfaces are grouped by their precise role:

| Role | Interfaces |
| --- | --- |
| Literal phases and modulus one | `deltaSymbolTerm_eq_unit_sum`, `deltaSymbolTerm_eq_exponential_sum`, `deltaSymbolTerm_modulus_one` |
| Support inequalities and finite-set membership | `deltaSymbolKernel_eq_zero_of_modulus_bound`, `deltaSymbolTerm_eq_zero_of_modulus_bound`, `deltaSymbol_modulus_bound_eq_max`, `mem_deltaSymbolModuli`, `deltaSymbolTerm_eq_zero_of_not_mem` |
| Finite support and actual series value | `deltaSymbolTerm_finite_support`, `deltaSymbolTerm_summable`, `deltaSymbolTerm_norm_summable`, `deltaSymbolTerm_hasSum`, `deltaSymbolTerm_tsum_eq_sum` |
| Equivalent finite presentations | `deltaSymbolModuli_sum_eq_sum_range`, `deltaSymbolTerm_tsum_eq_sum_range`, `deltaSymbolTerm_tsum_eq_unit_sum` |

The nine final specialization interfaces are:

| Role | Interfaces |
| --- | --- |
| Kernel properties and positive normalizer | `heathBrownDeltaKernel_properties`, `heathBrownSamplingSum_uniform_pos`, `heathBrownSamplingSum_pos`, `heathBrownNormalization_pos` |
| Natural and real decay orders | `heathBrownNormalization_error_bound`, `heathBrownNormalization_error_bound_real` |
| Exact identities and complete numbered result | `heathBrown_delta_identity`, `heathBrown_delta_finite_identity`, `source_delta_symbol` |

The normalization and support modules use only the ordinary foundations
and the pinned mathlib. The nine source-specialization interfaces use
the one registered Heath-Brown input. No earlier literature premise is
needed for this milestone. The external declaration is never counted
as a proved supporting export.

## Restriction that must remain visible

For `2<Q<3`, the only nonzero normalization summand is `omega(2/Q)`.
As `Q` decreases to `2`, it tends to zero, and `Q/S(Q)` diverges.
Thus even excluding the single inadmissible value `Q=2` does not
justify a bound `abs(c(Q)-1)<=C_j*Q^(-j)` uniformly over every
admissible `Q>1`. The raw sampling estimate has no such denominator
problem. The internal restriction `Q>=3` is essential for the stated
uniform normalization estimate.

## Review and execution boundary

The implemented definitions, registered source type, both generic proof
modules, the real-order extension, and the final endpoint have been
reviewed against the literal manuscript and the cited source. Independent
reviews checked the uniform denominator, absence of a strengthened
hypothesis, integer and real exponent quantifiers, positive-modulus
conventions, literal phases, cutoff identity, and the distinction
between smoothness and analyticity. The real-order target was rebuilt
successfully after its addition.

The aggregate verifier separately checks every registered theorem's
actual kind, full type and axiom list, the external input's type hash,
the frozen source, and the complete project. Its execution state and
any successful reports, together with the exact published commit,
are tracked in `CHECKPOINT.md`.
This record makes no whole-paper certification claim and adds no
trusted mathematical scope beyond the six source groups above.
