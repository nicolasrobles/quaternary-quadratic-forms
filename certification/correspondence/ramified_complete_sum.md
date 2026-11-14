# Source correspondence: Lemma 3.4

## Scope and frozen source

This review concerns the full assertion of `lem:ramified`, Lemma 3.4:

$$
\mathcal S_{p,p^k}(u)
=\chi(p)^{k+1}p^{2k+1}
\,\xi_p(\operatorname{adj}(A)u)
\,R_{p^{k+1}}(F^*(u))
\qquad(p\nmid N,\ k\ge1).
$$

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | The nonsingular symmetric integral matrix, `F(x)=xᵀAx`, `α=det A`, `N_F=2|α|`, and `χ(p)=(α/p)` away from `N_F` |
| Notation, lines 561–572 | The positive additive character and sums over reduced residue classes |
| `eq:dualform`, lines 816–818 | The actual adjugate dual value `F*(u)=uᵀ adj(A)u` |
| Section 3, lines 997–1025 | The condition `rad(N_F)∣N`, the supplied local functions, scalar invariance, and the additional weight and Fourier-bound hypotheses |
| `eq:Snewdef`, lines 1029–1038 | The actual mixed sum, its modulus `qc`, and its cone condition modulo `q` |
| `eq:ramanujan`, lines 1043–1045 | The actual Ramanujan sum over units |
| `lem:ramified`, `eq:ramified`, lines 1184–1190 | The complete shared-prime formula |
| `eq:Uj`, lines 1193–1220 | The weighted unit sum and its stationary-residue evaluation |
| Lines 1222–1231 | The actual unit-digit decomposition and the identity `𝒰_(k+1)=p·𝒮_(p,p^k)` |

There is one assertion in the lemma. The formula for `𝒰_j` is a proved
intermediate assertion, not a replacement for the displayed mixed-sum
conclusion. Both formulas are present, and the final source theorem
uses the existing mixed sum and the original supplied local function.

## Modules and reviewed exports

| Module | Public theorem exports | Reviewed role |
| --- | ---: | --- |
| [WeightedGaussSums.lean](../../QuaternaryQuadraticForms/WeightedGaussSums.lean) | 3 | Literal weighted inner and outer sums, with exact constant-weight specializations |
| [WeightedGaussStationaryPhase.lean](../../QuaternaryQuadraticForms/WeightedGaussStationaryPhase.lean) | 2 | Actual vector digits, the gradient phase, and four-coordinate orthogonality |
| [WeightedGaussExtraction.lean](../../QuaternaryQuadraticForms/WeightedGaussExtraction.lean) | 3 | Adjugate multiplication and extraction of the scalar-invariant weight |
| [PrimePowerUnitDigits.lean](../../QuaternaryQuadraticForms/PrimePowerUnitDigits.lean) | 2 | An actual bijection of unit digits and its exact canonical integer representatives |
| [RamifiedUnitLift.lean](../../QuaternaryQuadraticForms/RamifiedUnitLift.lean) | 2 | Scalar orthogonality imposing precisely the mixed-sum cone condition |
| [WeightedCompleteSum.lean](../../QuaternaryQuadraticForms/WeightedCompleteSum.lean) | 3 | Summing the proved extraction and evaluating the source `𝒰_j` |
| [SourceGoodPrime.lean](../../QuaternaryQuadraticForms/SourceGoodPrime.lean) | 1 | Deriving the actual quadratic good-prime condition from the source radical hypothesis |
| [RamifiedCompleteSum.lean](../../QuaternaryQuadraticForms/RamifiedCompleteSum.lean) | 2 | The complete shared-prime identity and its original-family source wrapper |

These are eighteen public theorem exports in eight modules. The new
definitions `weightedIntegralGaussSum`, `primeWeightedCompleteSum`, and
`residueUnitDigitsEquiv` are actual finite-sum objects or an actual
equivalence; they are not additional numbered results.

## Actual sums, weights, and phases

The existing
[CompleteSums.lean](../../QuaternaryQuadraticForms/CompleteSums.lean)
defines `mixedCompleteSum ξ q c A u` by summing over
`a : (ZMod c)ˣ` and `x : Fin 4 → ZMod (q*c)`. On the canonical integer
representatives, its summand is

```lean
if (q : ℤ) ∣ integralQuadraticValue A x then
  compositeWeight ξ q x * ZMod.stdAddChar
    ((a * integralQuadraticValue A x + dotProduct u x : ℤ) : ZMod (q * c))
else 0
```

Thus its cone condition and additive phase are exactly those in
`eq:Snewdef`. The existing lift-independence theorems prove that this
definition is independent of the representatives used. The source
prime-product weight `compositeWeight` satisfies
`compositeWeight_prime`: at a prime `p`, the product equals the supplied
local function `ξ p` on the reduction of the integer vector.

The new inner sum is literally

```lean
weightedIntegralGaussSum p n ξ A a u :=
  ∑ x : Fin 4 → ZMod n,
    ξ (fun i => (residueLift n x i : ZMod p)) *
      ZMod.stdAddChar
        ((a * integralQuadraticValue A (residueLift n x) +
          dotProduct u (residueLift n x) : ℤ) : ZMod n)
```

The definition `primeWeightedCompleteSum p n ξ A u` sums this inner
expression over the actual group `(ZMod n)ˣ`, using each unit's
canonical integer representative as `a`. At `n=p^j`, it is precisely
the source `𝒰_j(u)`.

`weightedIntegralGaussSum_one` identifies the constant-weight inner
sum with `integralQuadraticGaussSum`.
`unweightedCompleteSum_eq_sum_integralQuadraticGaussSum` identifies the
sum of these literal inner expressions with the existing `S_n(u)`.
`primeWeightedCompleteSum_one` gives the corresponding exact outer
constant-weight specialization. These identities retain the same
matrix, integral frequency, and positive standard-character phase.

The existing `integralRamanujanSum n t` is the actual unit sum

$$
\sum_{a\in(\mathbb Z/n\mathbb Z)^\times}e_n(at).
$$

Its argument in every terminal formula is the actual integer
`dotProduct u (A.adjugate.mulVec u)`. The weight argument is the actual
vector `reduceFrequency p (A.adjugate.mulVec u)`, where
`reduceFrequency p v` is definitionally `fun i => (v i : ZMod p)`.
There is no replacement dual form, abstract character value, or
unspecified weighted sum.

## Vector digits and stationary orthogonality

`weightedGauss_digit_phase` first works at a general modulus `m*p`
with positive `m,p` and `p∣m`. The existing proved
`residueDigitsVectorEquiv` and `sum_residueLift_digits` give an actual
bijection of four-coordinate residues

$$
x=y+mz,\qquad y\bmod m,\quad z\bmod p,
$$

with equality of the canonical integer representatives coordinate by
coordinate. No CRT coprimality assumption is used.

Symmetry gives the exact integral quadratic expansion. Since `p∣m`,
the quadratic term `a m² F(z)` is divisible by `mp`. Reducing the
expanded phase therefore gives

$$
e_{mp}\bigl(aF(y+mz)+u\cdot(y+mz)\bigr)
=e_{mp}\bigl(aF(y)+u\cdot y\bigr)
\,e_p\bigl((2aAy+u)\cdot z\bigr).
$$

The proof retains the factor `2` from polarization and the positive
sign of the linear frequency. Since `p∣m`, reducing `y+mz` modulo `p`
also gives exactly the reduction of `y`, so its weight is unchanged.

`weightedIntegralGaussSum_stationary_expansion` applies the existing
proved `stdAddChar_residue_vector_orthogonality` to the final vector
digit. The resulting scalar is

$$
\sum_{z\bmod p}e_p\bigl((2aAy+u)\cdot z\bigr)
=\begin{cases}
p^4,&2aAy+u\equiv0\pmod p,\\
0,&\text{otherwise}.
\end{cases}
$$

Accordingly the exported expansion is a literal sum over `y : Fin 4
→ ZMod m`, with the original phase and weight and this explicit
stationary indicator. The digit expansion and orthogonality require
neither primality nor nonsingularity. For the source, `m=p^(j−1)` and
`j≥2` supply `p∣m`; this is exactly the source inequality `2j−2≥j`.

## Extracting the adjugate weight

In `stationary_weight_eq_adjugate`, put `B=reduceQuadraticMatrix p A`.
The hypothesis `p∤N_F`, with the actual definition
`quadraticBadPrimeModulus A = 2*A.det.natAbs`, gives `p≠2` and
`B.det≠0`. The scalar hypothesis `p∤a` gives `(a : ZMod p)≠0`.

The stationary condition is the actual vector equation

$$
(2a)By+u=0\quad\text{over }\mathbb F_p.
$$

Applying `B.adjugate.mulVec` on the left and using the proved matrix
identity `B.adjugate * B = B.det • 1` gives

$$
\operatorname{adj}(B)u=-(2a\det B)y.
$$

The coefficient `-(2a det B)` is proved nonzero from the three
nonvanishing factors. Scalar invariance consequently gives
`ξ(y)=ξ(adj(B)u)`. This is equivalent to the source's formulation
`y=-(2aα)⁻¹ adj(A)u`; the formal proof avoids introducing an inverse
because the already proved nonzero scalar relation suffices.

The coefficient-reduction lemmas prove that this vector is exactly
the reduction of `A.adjugate.mulVec u`, using the existing actual
adjugate reduction theorem. The proof does not substitute an unrelated
inverse matrix or transpose.

`weightedIntegralGaussSum_mul_extract` compares the stationary
expansion for `ξ` with the same expansion for constant weight one.
At a stationary residue it substitutes the proved weight identity;
at every other residue both summands vanish. This proves the literal
inner identity

$$
\sum_{x\bmod mp}\xi_p(x)e_{mp}(aF(x)+u\cdot x)
=\xi_p(\operatorname{adj}(A)u)
\sum_{x\bmod mp}e_{mp}(aF(x)+u\cdot x).
$$

`weightedIntegralGaussSum_prime_power_extract` specializes it to
every `j≥2`. No formula for the weighted sum is assumed. In
particular, scalar invariance applies also when the stationary vector
is zero; neither zero frequency nor a zero weight requires division
by a weight value.

## Evaluation of the actual weighted unit sum

`primeWeightedCompleteSum_of_gauss_factor` is a finite-sum composition
helper: if every actual inner sum has a common factor `C`, that factor
can be moved outside the actual unit sum. Its premise is completely
discharged in `primeWeightedCompleteSum_prime_power_factor` using the
proved inner extraction.

For an actual unit modulo `p^j`, its canonical integer representative
is proved not divisible by `p`. This uses the unit's coprimality with
`p^j` and the fact that `p∣p^j` for `j≥1`; the available hypothesis
`j≥2` is sufficient. No arbitrary or asserted coprime lift is used.

The resulting theorem identifies `𝒰_j` with
`ξ_p(adj(A)u) * S_(p^j)(u)`. Applying the previously proved exact
Lemma 3.2(ii), `unweightedCompleteSum_prime_power`, gives
`primeWeightedCompleteSum_prime_power`:

$$
\mathcal U_j(u)
=(\operatorname{legendreSym}(p,\det A))^j p^{2j}
\,\xi_p(\operatorname{adj}(A)u)
\,R_{p^j}(F^*(u)),\qquad j\ge2.
$$

This is `eq:Uj`, with the source identification
`χ(p)=(det A/p)` at the proved good prime. The Ramanujan phase and its
modulus are inherited from the checked Gauss evaluation, including
its actual unit reindexing. A weighted extraction hypothesis, a Gauss
value hypothesis, or a separate assumed evaluation does not remain in
the public `𝒰_j` endpoint.

## Unit digits, the cone condition, and the factor p

The second digit argument concerns the scalar unit parameter. In
`PrimePowerUnitDigits.lean`, `residueUnitDigitsEquiv c p hpc` is an
actual equivalence

$$
(\mathbb Z/c\mathbb Z)^\times\times\mathbb Z/p\mathbb Z
\;\simeq\;(\mathbb Z/(pc)\mathbb Z)^\times
\qquad(p\mid c).
$$

It is constructed by restricting the existing residue-digit
equivalence to the coprime subtypes and transporting through
`ZMod.unitsEquivCoprime`. The coprimality proof verifies both
directions: `a+c t` is coprime to `pc` exactly when `a` is coprime to
`c`, because `p∣c`. No CRT statement for coprime moduli is used here.

`residueUnitDigitsEquiv_val` proves the exact canonical value
`a.val + c*t.val`, not merely a congruence. The public
`sum_units_residueLift_digits` therefore reindexes the literal outer
unit sum with precisely the integer representatives used in
`mixedCompleteSum`. The explicit ring equivalence for `c*p=p*c`
preserves these canonical values.

`RamifiedUnitLift.lean` separates the phase for the scalar digit:

$$
e_{pc}\bigl((a+ct)F(x)+u\cdot x\bigr)
=e_{pc}\bigl(aF(x)+u\cdot x\bigr)e_p(tF(x)).
$$

Primitive-standard-character orthogonality gives

$$
\sum_{t\bmod p}e_p(tF(x))
=\begin{cases}
p,&p\mid F(x),\\
0,&\text{otherwise}.
\end{cases}
$$

The selected condition is exactly
`(p : ℤ) ∣ integralQuadraticValue A (residueLift (p*c) x)`.
After `compositeWeight_prime`, the remaining summand is definitionally
the existing mixed summand at `q=p`. Consequently
`primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum` proves

$$
\operatorname{primeWeightedCompleteSum}(p,pc,\xi_p,A,u)
=p\,\mathcal S_{p,c}(u).
$$

This bridge needs only primality and `p∣c`; the matrix, frequency, and
weight family are arbitrary. It has no symmetry, nonsingularity,
scalar-invariance, or oddness hypothesis.
`primeWeightedCompleteSum_prime_power_lift` takes `c=p^k`, with `k≥1`,
and rewrites `p*p^k=p^(k+1)`. It gives exactly the source identity
`𝒰_(k+1)=p·𝒮_(p,p^k)`.

The two orthogonality factors serve different sums: the four vector
digits contribute `p⁴` in the stationary expansion, whereas this
single scalar unit digit contributes `p`. The bridge contains exactly
one factor `p`.

## Source hypotheses and terminal statement

The core theorem `ramified_complete_sum` combines the two proved
identities at `j=k+1`. Since `p` is prime, `(p : ℂ)≠0`; cancelling
this scalar gives the claimed mixed-sum value. The exponent identity
`2*(k+1)=(2*k+1)+1` gives exactly `p^(2*k+1)`. Nothing is cancelled
from the weight, the Ramanujan sum, or a Gauss sum, all of which may
vanish.

`source_not_dvd_quadraticBadPrimeModulus` derives the core good-prime
hypothesis from the source's actual radical condition. The existing
`primeRadical M` is the product of the distinct prime divisors of `M`,
and `prime_dvd_primeRadical_iff` states the prime-divisibility
equivalence for `M≠0`. Here `A.det≠0` proves `N_F≠0`, so a prime
dividing `N_F` would divide its radical and therefore `N`, contrary to
`hpN`.

The nonzero determinant cannot be omitted from this source bridge:
at zero, the repository's prime-factor convention gives
`primeRadical 0=1`, so radical divisibility alone would not imply the
good-prime conclusion. The proof uses the source's standing
nonsingularity explicitly. The separate source assumption `N≥1` need
not be repeated because `p∤N` already rules out `N=0`.

The final source theorem is
`QuaternaryQuadraticForms.source_ramified_complete_sum`:

```lean
theorem source_ramified_complete_sum
    (N p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hpN : ¬ p ∣ N)
    (ξ : ∀ q : ℕ, q.Prime → ¬ q ∣ N → (Fin 4 → ZMod q) → ℂ)
    (hξ : ∀ r : ZMod p, r ≠ 0 → ∀ y : Fin 4 → ZMod p,
      ξ p Fact.out hpN (r • y) = ξ p Fact.out hpN y)
    (u : Fin 4 → ℤ) :
    mixedCompleteSum (extendPrimeWeights N ξ) p (p ^ k) A u =
      (legendreSym p A.det : ℂ) ^ (k + 1) * (p : ℂ) ^ (2 * k + 1) *
        ξ p Fact.out hpN (reduceFrequency p (A.adjugate.mulVec u)) *
          integralRamanujanSum (p ^ (k + 1))
            (dotProduct u (A.adjugate.mulVec u))
```

The family is supplied only at primes not dividing `N`, exactly as in
Section 3. The existing `extendPrimeWeights` gives a total index type
for the composite-weight definition, and `extendPrimeWeights_apply`
proves agreement with the original supplied function at this `p`.
The terminal right-hand side explicitly uses that original function.
No value or invariance property at an excluded prime is assumed.

| Source assumption or boundary case | Treatment in the checked endpoint |
| --- | --- |
| Prime `p∤N` | The exact prime instance and `hpN`; these also give `(p,N)=1`. Since `p` is prime, the modulus `q=p` is automatically squarefree. |
| `rad(N_F)∣N` | The repository's existing actual radical of `2*A.det.natAbs`, with no replacement modulus. |
| Symmetry and integer nonsingularity | Exactly `A.transpose=A` and `A.det≠0`; the former supplies polarization and the latter makes the radical implication valid. |
| `k≥1` | Exactly `hk : 1≤k`. At `k=1`, the vector argument has `j=2`, so the quadratic-error divisibility holds with equality in `2j−2≥j`. |
| `k=0` | Excluded as in the source. The general weighted extraction need not hold at `j=1`, and `𝒮_(p,1)=C_p` is a different sum. |
| Every integral frequency | The unchanged `u : Fin 4 → ℤ`, including zero, frequencies divisible by `p`, and frequencies with zero dual value. |
| Nonzero-scalar invariance | Required only for the supplied local function at this prime; the Section 3 family hypothesis specializes to it. |
| `ξ_p(0)=0` and `|ξ_p|≤1` | Unused by the identity. Scalar invariance already applies to the zero vector, and no weight value is divided out. Omitting these hypotheses strengthens the result. |
| `D_p`, `E`, `K`, and `eq:Cstrata` | Unused; the proof does not use a Fourier estimate or an exceptional-locus premise. |
| Global nonsquareness of `det A` | Unused by the local identity. The displayed character value is the source's prescribed Legendre value at a good prime. |
| The prime two | Excluded by the derived `p∤2|det A|`; no independent oddness assumption is added. |

## Inspected dependencies and review conclusion

The combined actual type and `#print axioms` inspection completed
successfully for all eighteen public theorem exports. The printed
types of both terminal theorems are precisely the formulas described
above. Every new export has exactly

```text
Classical.choice
Quot.sound
propext
```

No registered literature premise occurs in these dependencies. The
finite equivalences, character orthogonality, matrix adjugate
identities, and earlier Gauss evaluations are proved in the pinned
mathlib or the repository. The common-factor helper is instantiated
with the proved stationary extraction; the actual unit lift is also
proved. No source-internal estimate, weighted evaluation, unit-digit
identity, or good-prime implication survives as an unproved premise
in the final source theorem.

All eight modules passed strict compilation with the pinned Lean
4.24.0 toolchain. The targeted root library build completed
successfully with 3,166 jobs, and the eighteen-export inspection
exited successfully. Independent review of the definitions, proofs,
and printed types finds the entire source assertion present with
its exact moduli, phase, adjugate arguments, scalar factors, and
source family. No mathematical gap or additional source hypothesis
was found.

This completed correspondence review supports Certified
classification of Lemma 3.4 when the full repository verification
gates pass. At the time this review was frozen, the strict builds and
type/dependency inspection were complete; the full aggregate gate and
the subsequent exact-commit CI gate were still pending. The live
ledger, verification report, and execution checkpoint record the
eventual checked hashes and publication evidence.

The milestone adds eighteen exports, eight modules, and this review,
giving 571 registered exports, 128 proof modules, and 155 inspected
inputs at integration. The numbered-result scope is 14 Certified,
0 Partial, 0 Active, and 28 Pending; the 33 auxiliary Pending groups
remain separate. The four registered literature premises, twenty
mapped reference groups, and nine pinned dependency revisions are
unchanged. The earlier Section 4, CRT, Gauss, and uniform-bound scope
is preserved.

The next full target is Lemma 3.5, which remains Pending. Its scope
includes both `eq:goodglobal` under `(c,N_F)=1` and `eq:coneratio` on
the dual cone for every `c≥1`, including arbitrary factors supported
on the bad primes. The present milestone proves neither global
assembly clause. In particular, the later bad-factor argument must
multiply by the existing `S_(c₁)(u)` and cannot assume it is nonzero.
