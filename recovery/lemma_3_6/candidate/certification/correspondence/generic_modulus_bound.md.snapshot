# Source correspondence: Lemma 3.6

## Source and complete scope

This review concerns the full assertion of `lem:genericmod`, equation
`eq:genericmod`. For a fixed symmetric nonsingular integral matrix `A`
and every positive real `ε`, the source asserts a constant depending
only on `F(x)=xᵀAx` and `ε` such that

$$
\sum_{\substack{1\le c\le X\\(c,q)=d}}
\frac{|\mathcal S_{q,c}(u)|}{c^3}
\le C_{F,\varepsilon}|C_e(u)|d^2
\mathbf 1_{d\mid F^*(u)}(X|F^*(u)|)^\varepsilon,
\qquad q=de.
$$

Here `q` is squarefree, `(q,N)=1`, `F*(u)≠0`, and `X≥1`.
The standing local assumptions include `rad(N_F)∣N`, the original
prime functions, their scalar invariance, and their norm bound.
The formal endpoint
`QuaternaryQuadraticForms.source_generic_modulus_bound` has exactly
the displayed conclusion for the actual source sums. Its constant
is chosen before all varying moduli, local functions, frequencies,
and cutoffs.

The frozen source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | The symmetric nonsingular integral matrix, `F(x)=xᵀAx`, `α=det A`, and `N_F=2|α|` |
| Notation, lines 561–578 | Positive additive characters, reduced residues, divisor and prime counts, the indicator, and positive `ε` |
| `eq:dualform`, lines 816–818 | The actual integer dual value `F*(u)=uᵀadj(A)u` |
| `sec:local`, lines 997–1025 | The radical condition, original local functions, scalar invariance, norm bound, and additional hypotheses not used by this estimate |
| `eq:Cdef`, lines 1006–1012 | The original prime-product weight and actual constrained Fourier sum |
| `eq:Sdef`, `eq:Snewdef`, lines 1029–1039 | The actual unweighted and mixed complete sums and their modulus-one specializations |
| `eq:ramanujan`, lines 1043–1045 | The actual Ramanujan unit sum and the source's separate divisor-sum expression |
| `lem:badprime`, lines 1156–1177 | The exact uniform bound `4√|α| c³` for the actual unweighted sum |
| `eq:q1q2`, lines 1234–1238 | The gcd and quotient defining the shared and complementary factors |
| `lem:goodglobal`, lines 1240–1279 | The previously checked good-modulus evaluation and bad/good factorization |
| `sec:moduli`, lines 1282–1290 | Fixed factorization `q=de`, actual gcd restriction, and counting the bad-prime factor |
| `lem:genericmod`, `eq:genericmod`, lines 1292–1300 | The complete assertion of Lemma 3.6 |
| Lines 1302–1314 | Removing the bad-prime factor and taking norms in the good-modulus formula |
| `eq:ramsplit`, lines 1315–1329 | The source's local-series organization and its divisibility support |
| Lines 1330–1342 | The source's divisor/harmonic estimate and absorption into a positive power |

The proof retains the first part of the source argument and uses a
stronger finite gcd estimate for the remaining summation. It gives
one factor `τ(|m|)` in the intermediate bound, where `m=F*(u)`,
instead of the source proof's two. This proves the same complete
assertion. It does not change the frozen manuscript or claim that
every intermediate identity in the source's alternative local-series
calculation has been newly formalized.

## Modules and the thirty-nine theorem exports

All names below belong to the `QuaternaryQuadraticForms` namespace.
The table lists all thirty-nine new public theorem exports in twelve
modules. These exports support one additional numbered manuscript
result, Lemma 3.6; they are not thirty-nine numbered results.

| Module | Exports | Declarations and reviewed role |
| --- | ---: | --- |
| [RamanujanPrimePower.lean](../../QuaternaryQuadraticForms/RamanujanPrimePower.lean) | 4 | `integralRamanujanSum_prime_eq`; `integralRamanujanSum_mul_modulus_eq_zero`; `integralRamanujanSum_mul_modulus_mul`; `integralRamanujanSum_prime_power_eq`: exact evaluations and recurrence of the literal unit sums |
| [RamanujanGcdBound.lean](../../QuaternaryQuadraticForms/RamanujanGcdBound.lean) | 6 | `integralRamanujanSum_prime_power_norm_le_gcd`; `integralRamanujanSum_norm_le_gcd`; `integralRamanujanSum_mul_norm_le`; `integralRamanujanSum_eq_zero_of_prime_sq_dvd`; `integralRamanujanSum_shared_eq_zero`; `integralRamanujanSum_shared_norm_le`: actual gcd bounds and the exact shared-factor divisibility support |
| [GcdHarmonicBound.lean](../../QuaternaryQuadraticForms/GcdHarmonicBound.lean) | 3 | `sum_divisor_multiples_div_le_harmonic`; `sum_gcd_div_le_divisor_card_mul_harmonic`; `sum_gcd_div_le_divisor_card_mul_log`: finite positive-divisor and harmonic estimates |
| [PrimeSupportCount.lean](../../QuaternaryQuadraticForms/PrimeSupportCount.lean) | 4 | `mem_primeSupportModuliUpTo`; `primeSupportModuliUpTo_card_le`; `primeSupportModuliUpTo_card_le_log`; `primeSupportModuliUpTo_card_le_log_normalized`: counting the actual positive bad-supported moduli by their factorization vectors |
| [DivisorPowerBound.lean](../../QuaternaryQuadraticForms/DivisorPowerBound.lean) | 1 | `divisors_card_le_rpow`: a positive divisor-bound constant uniform in every positive integer |
| [LogPowerBound.lean](../../QuaternaryQuadraticForms/LogPowerBound.lean) | 1 | `one_add_log_pow_le_rpow`: a positive logarithmic-power constant uniform for all real `X≥1` |
| [FactorizationSumBound.lean](../../QuaternaryQuadraticForms/FactorizationSumBound.lean) | 1 | `sum_le_product_of_factorization`: a finite-factor-pair injection and nonnegative sum comparison |
| [ModulusNormSum.lean](../../QuaternaryQuadraticForms/ModulusNormSum.lean) | 5 | `mem_gcdModuliUpTo`; `normalizedMixedCompleteSum_of_neZero`; `normalizedMixedCompleteSum_nonneg`; `modulusNormSum_nonneg`; `modulusNormSum_eq_zero_of_vanishing`: the literal positive-modulus sum, normalization, and summation of actual vanishing |
| [MixedSumNormBounds.lean](../../QuaternaryQuadraticForms/MixedSumNormBounds.lean) | 6 | `globalQuadraticChar_norm_le`; `compositeWeight_norm_le`; `primeWeightsNorm_le_extend`; `mixedCompleteSum_good_modulus_norm_le`; `mixedCompleteSum_eq_bad_mul_good`; `mixedCompleteSum_div_cube_le_of_prime_split`: norm bounds and actual CRT with the bad factor retained |
| [MixedSumGcdBound.lean](../../QuaternaryQuadraticForms/MixedSumGcdBound.lean) | 4 | `mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd`; `mixedCompleteSum_eq_zero_of_gcd_not_dvd`; `mixedCompleteSum_div_cube_le_gcd_of_prime_split`; `mixedCompleteSum_div_cube_le_gcd_indicator_of_prime_split`: actual mixed-sum support and normalized arithmetic estimates |
| [GenericModulusBound.lean](../../QuaternaryQuadraticForms/GenericModulusBound.lean) | 2 | `modulusNormSum_eq_zero_of_not_dvd`; `modulusNormSum_le_divisor_log`: vanishing of the whole sum and the unconditional actual finite-sum divisor/logarithm bound |
| [GenericModulusTheorem.lean](../../QuaternaryQuadraticForms/GenericModulusTheorem.lean) | 2 | `modulusNormSum_le_rpow`; `source_generic_modulus_bound`: the uniform power bound and its original-source-family endpoint |

The new definitions `primeSupportModuliUpTo`, `gcdModuliUpTo`,
`normalizedMixedCompleteSum`, and `modulusNormSum` are concrete
finite sets and sums. They are not additional numbered assertions.
The first thirty-seven exports include reusable supporting results;
the final two give the full estimate for a total local family and
for the original supplied source family, respectively.

## Actual objects, normalization, and finite cutoff

The previously established definitions of the complete sums and
Ramanujan sums are unchanged.

| Source object | Lean object and interpretation |
| --- | --- |
| `F(x)` | `integralQuadraticValue A x = dotProduct x (A.mulVec x)` |
| `F*(u)` | `dotProduct u (A.adjugate.mulVec u)` as an integer |
| `N_F` | `quadraticBadPrimeModulus A = 2*A.det.natAbs` |
| `𝒮_(q,c)(u)` | `mixedCompleteSum ξ q c A u`, with actual units modulo `c`, vectors modulo `q*c`, and the congruence `q∣F(x)` |
| `S_b(u)` | `unweightedCompleteSum b A u`, with the same original integral form and frequency |
| `C_e(u)` | `constrainedFourierSum ξ e A u`, the actual constrained Fourier sum |
| `R_n(m)` | `integralRamanujanSum n m`, over the actual group `(ZMod n)ˣ` |
| `τ(|m|)` | `m.natAbs.divisors.card`, counting positive natural divisors |
| `ω(N_F)` | `(quadraticBadPrimeModulus A).primeFactors.card` |
| `1_(d∣m)` | The real-valued expression `if (d : ℤ) ∣ m then 1 else 0` |
| Left side of Lemma 3.6 | `modulusNormSum ξ q d A u X` |

The summation set is literally

```lean
gcdModuliUpTo q d T :=
  (Finset.Icc 1 T).filter (fun c => Nat.gcd c q = d)
```

At `T=⌊X⌋₊` and `X≥1`, its positive natural indices are exactly
the source's positive integer moduli `c≤X` satisfying `(c,q)=d`.
`mem_gcdModuliUpTo` retains positivity, the cutoff, and the gcd
condition. The local evaluations use `gcd(q,c)`; the assembly
explicitly uses `Nat.gcd_comm` to identify it with `d`.

`normalizedMixedCompleteSum` equals
`‖mixedCompleteSum ξ q c A u‖/(c : ℝ)^3` at every positive `c`.
It is extended by zero only at `c=0`, to provide a total summand;
zero does not occur in the finite set. The actual complex norm is
used, and there is no change to the phase, the integer quadratic
form, the modulus, or the frequency. In particular, no matrix
Hessian or factor of two is substituted for the source's `A`.

## Exact Ramanujan arithmetic and divisibility support

The unit-digit bijection for `p∣c` writes every unit modulo `pc`
uniquely as a unit lift modulo `c` plus `c` times a residue modulo
`p`. Additive orthogonality in that digit gives

$$
R_{pc}(m)=0\quad\text{if }p\nmid m,
\qquad R_{pc}(pm)=pR_c(m).
$$

These two recurrence statements require positive `p,c` and `p∣c`;
they do not require primality. At a prime, the already proved
complete additive-character sum minus its zero term gives the
values `p−1` and `−1`. Induction on the positive exponent then
proves the exact formula

$$
R_{p^{k+1}}(m)=
\begin{cases}
p^k(p-1),&p^{k+1}\mid m,\\
-p^k,&p^k\mid m\text{ and }p^{k+1}\nmid m,\\
0,&p^k\nmid m.
\end{cases}
$$

The formula includes `p=2`, arbitrary signed integer frequencies,
and `m=0`; it avoids imposing a valuation convention at zero.
It implies the prime-power norm bound. Induction over coprime
prime-power factors uses the previously checked multiplicativity
of the actual Ramanujan sum and the proved multiplicativity of
`gcd(n,|m|)` in the modulus to obtain

$$
|R_n(m)|\le\gcd(n,|m|)\qquad(n\ge1).
$$

The additional arithmetic divisibility
`gcd(dc,|m|) ∣ d*gcd(c,|m|)` and positivity yield

$$
|R_{dc}(m)|\le d\gcd(c,|m|).
$$

For the support condition, if `p²∣n` and `p∤m`, write `n=p²t`
and apply the repeated-factor orthogonality at `p*(p*t)`. Thus the
actual sum vanishes. If `d` is squarefree and `d∣c`, each prime
of `d` occurs at least twice in `dc`. Nonvanishing of `R_(dc)(m)`
therefore forces every prime of `d` to divide `m`, and squarefreeness
forces `d∣m`. The proof obtains this last implication through the
equality `d=gcd(d,m.natAbs)`, proved by the prime-divisor
characterization of squarefree naturals.

These are deductions about the actual unit sums, not assumed local
values or abstract multiplicative functions. The separate
`aux:ramanujan` obligation asserting the complete divisor-sum
identity `R_n(m)=∑_(h∣(n,m))h μ(n/h)` remains separate and Pending.
The present proof does not need that full identity, its literature
input, the infinite local sums in `eq:ramsplit`, or their product
evaluation. No claim of completing those separate obligations is
made here.

## The actual bad/good split and pointwise normalized estimate

For each positive `c`, the previously proved
`exists_modulus_prime_split` constructs positive `b,g` such that

$$
c=bg,\qquad (b,g)=1,\qquad (g,N_F)=1,
\qquad p\mid b\Longrightarrow p\mid N_F
\quad(p\text{ prime}).
$$

From `(q,N_F)=1`, the prime-support argument proves `(q,b)=1`
and `gcd(q,c)=gcd(q,g)`. The full CRT blocks `b` and `qg` are
therefore coprime. Applying the actual mixed-sum CRT identity and
the modulus-one specialization gives

$$
\mathcal S_{q,c}(u)=S_b(u)\mathcal S_{q,g}(u).
$$

This is a product identity, including zero values of `S_b(u)`;
that factor is never divided out. The previously checked Lemma
3.3 bounds its norm by `4√|det A| b³`. Taking norms in the actual
good-modulus formula at `g` bounds the remaining factor by

$$
|C_e(u)|\,d g^2\,|R_{dg}(m)|,
\qquad d=\gcd(q,g),\quad e=q/d.
$$

The actual Jacobi coefficient has norm at most one, and the actual
prime-product weight has norm at most one by multiplying the local
norm bounds. These estimates do not need a supplied Dirichlet
character or a nonvanishing character value.

Since `q` is squarefree, its divisor `d` is squarefree, and by its
definition `d∣g`. The new Ramanujan statements therefore give
the actual vanishing outside `d∣m` and, in all cases, the bound

$$
\frac{|\mathcal S_{q,c}(u)|}{c^3}
\le 4\sqrt{|\det A|}\,|C_e(u)|\,d^2
\frac{\gcd(g,|m|)}{g}.
$$

The normalization uses `c=bg`, positive real `b,g,c`, and ordinary
field algebra. It cancels only positive modulus powers. No sum,
weight, Fourier coefficient, or arithmetic indicator is cancelled.
`mixedCompleteSum_eq_zero_of_gcd_not_dvd` proves the vanishing
for every positive `c`, including arbitrary bad-prime factors.
Its proof does not need a local norm bound.

## Finite aggregation and the stronger divisor bound

The proof of `modulusNormSum_le_divisor_log` supplies every premise
of the generic finite-sum helper using the given arithmetic objects.
For each index in the actual gcd-restricted set it chooses a proved
split `c=b*g`. Positivity and divisibility show both `b≤c` and
`g≤c`, so both factors are at most `⌊X⌋₊`. The pair map is injective:
equal pairs have equal products, and those products are the original
indices. Uniqueness of the choice of split is not assumed or needed.

The image lies in the Cartesian product of the actual positive
bad-supported moduli up to the cutoff and the entire positive
interval `1≤g≤⌊X⌋₊`. Nonnegativity permits enlargement to that
product. The Fourier coefficient is constant across this sum:
the gcd restriction identifies the shared factor with the fixed `d`,
and `q=d*e` with `d>0` proves `q/d=e`.

For `M=|m|>0`, the actual gcd is one of the positive divisors of `M`
that divide `g`. Consequently

$$
\frac{\gcd(g,M)}g
\le\sum_{h\mid M}\mathbf 1_{h\mid g}\frac hg.
$$

For each positive `h`, division by `h` injects its positive multiples
in `1≤g≤T` into `1≤j≤T`, and `h/g=1/(g/h)`. Finite sum interchange
therefore yields the proved bound

$$
\sum_{1\le g\le T}\frac{\gcd(g,M)}g
\le\tau(M)H_T.
$$

The pinned library's proved harmonic estimate gives
`H_(floor X)≤1+log X` for every real `X≥1`.

For the first factor, the actual prime factorization vector of each
positive bad-supported `b≤T` is zero outside `N_F.primeFactors`.
For every supported prime `p≥2`, its exponent is at most `Nat.log 2 T`,
because `2^v≤p^v≤b≤T`. Unique factorization makes the vector encoding
injective. Counting the finite box gives

$$
\#\{b\le X:\operatorname{supp}(b)\subseteq\operatorname{supp}(N_F)\}
\le\left(1+\frac{\log X}{\log 2}\right)^r
\le\left(1+\frac1{\log 2}\right)^r(1+\log X)^r,
\quad r=\omega(N_F).
$$

The factors `b=1` and the real cutoff `X=1` are included. The
count is at the fixed `N_F`, not at the varying source `N`.

Combining the two finite estimates proves, for every allowed `m≠0`,

$$
\sum_{\substack{c\le X\\(c,q)=d}}
\frac{|\mathcal S_{q,c}(u)|}{c^3}
\le B_A|C_e(u)|d^2\tau(|m|)(1+\log X)^{r+1},
\qquad
B_A=4\sqrt{|\det A|}\left(1+\frac1{\log 2}\right)^r.
$$

Separately, `modulusNormSum_eq_zero_of_not_dvd` proves that the whole
left side is zero if `d∤m`. The final theorem combines these actual
results by cases to retain the exact source indicator.

## Uniform constants and the exact source endpoint

`divisors_card_le_rpow ε hε` proves

$$
\exists D_\varepsilon>0\ \forall M\ge1,
\qquad\tau(M)\le D_\varepsilon M^\varepsilon.
$$

Its proof uses the actual divisor-count factorization. Large primes
have `p^ε≥2`, so `v+1≤2^v≤p^(εv)`. Only finitely many small primes
require correction factors; Bernoulli's inequality bounds those
uniformly in their exponents. The resulting constant is chosen
before the integer `M`. No divisor growth estimate is assumed.

`one_add_log_pow_le_rpow (r+1) ε hε` proves

$$
\exists L_{r+1,\varepsilon}>0\ \forall X\ge1,
\qquad(1+\log X)^{r+1}\le L_{r+1,\varepsilon}X^\varepsilon.
$$

The zero-exponent boundary is treated explicitly in the generic
lemma. At a positive exponent it takes `δ=ε/k`, applies the proved
inequality `log X≤X^δ/δ`, raises a nonnegative bound to the integral
power `k`, and proves `δk=ε`. The constant is chosen before `X`.

Thus the final proof may take

$$
C_{A,\varepsilon}=B_A D_\varepsilon L_{r+1,\varepsilon}>0.
$$

It uses separate `ε` powers in the two independent variables and
the exact real identity
`X^ε * |m|^ε = (X*|m|)^ε` for their nonnegative bases. No doubling
of the requested exponent occurs. This constant depends only on
the fixed `A` and `ε`; in particular, it does not depend on `N`,
the weight family, `q,d,e,u`, or `X`.

The source endpoint has the following complete type:

```lean
theorem source_generic_modulus_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ)
        (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
        (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
        Squarefree q → q = d * e → q.Coprime N →
        primeRadical (quadraticBadPrimeModulus A) ∣ N →
        (∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
          ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y) →
        (∀ p (hp : p.Prime) (hN : ¬p ∣ N),
          ∀ x : Fin 4 → ZMod p, ‖ξ p hp hN x‖ ≤ 1) →
        ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) ≠ 0 →
        ∀ (X : ℝ), 1 ≤ X →
          modulusNormSum (extendPrimeWeights N ξ) q d A u X ≤
            C * ‖constrainedFourierSum (extendPrimeWeights N ξ) e A u‖ * (d : ℝ) ^ 2 *
              (if (d : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) then 1 else 0) *
                (X * |((dotProduct u (A.adjugate.mulVec u) : ℤ) : ℝ)|) ^ ε
```

The existential constant precedes all varying data and all their
hypotheses. This order is part of the theorem, not merely a prose
interpretation of a pointwise bound. The matrix, adjugate, actual
sums, exact gcd summation condition, original local family, integer
divisibility indicator, real absolute value, and arbitrary real
cutoff remain visible in the statement or its concrete definitions.

The earlier source radical bridge derives `(q,N_F)=1` from
`(q,N)=1`, `rad(N_F)∣N`, and integer nonsingularity. The original
weight invariance and norm hypotheses supply precisely the
properties used by the total-family core theorem. Since `q=d*e`,
every prime of `e` also divides `q` and lies outside `N`. The
previously proved agreement of `extendPrimeWeights` with the
original supplied functions therefore applies in both sums.
No arbitrary excluded-prime value enters the source expression.
The conversions `Int.cast_natAbs` and `Int.cast_abs` change the
internal natural absolute value into the source's real `|m|`.

## Source assumptions and boundary cases

| Assumption or boundary | Treatment in the complete theorem |
| --- | --- |
| Symmetric nonsingular integral `4×4` matrix | Exactly `A.transpose=A` and `A.det≠0`; no good reduction of every modulus is assumed. |
| Positive `q=d*e` and squarefree `q` | Natural factors with `NeZero` instances, `q=d*e`, and `Squarefree q`. Positivity of the source factors is included. Squarefreeness of the shared gcd and all needed coprimalities are derived. |
| `(q,N)=1` and `rad(N_F)∣N` | Explicit source hypotheses; the already proved bridge supplies `(q,N_F)=1`. |
| Original local functions | Supplied only at primes outside `N`; invariance and norm at most one are explicit. |
| `F*(u)≠0` | The actual integer dual value is nonzero; this makes its natural absolute value positive for the divisor estimate. |
| Negative dual value | All local formulas accept integer `m`; `Int.natCast_dvd` exactly relates divisibility to `m.natAbs`. The source endpoint restores real absolute value. |
| `q=1` | The factorization forces `d=e=1`. The original empty prime product is one, and the previously checked `C_1(u)=1` applies. |
| `d=1` | The indicator is one for every integer `m`; no prime divisor of `d` is required. |
| `X=1` | The finite set contains only `c=1` when `d=1` and is empty otherwise. The harmonic and prime-support bounds include this endpoint. |
| `C_e(u)=0` | No proof divides by the Fourier sum; the pointwise bound forces actual vanishing of every nonnegative summand. |
| Bad primes and `p=2` | All bad-prime powers remain in `b` and use the uniform complete-sum bound. The standalone exact Ramanujan arithmetic includes the prime two. |
| Positive real `ε` | The theorem covers every `ε>0`, with its constant independent of both real `X` and integer `m`. |
| `ξ_p(0)=0`, polynomial strata, `E,K` | Unused by this absolute-value estimate. Omitting them strengthens the result and retains every source instance. |
| Nonsquare `α` and the source Dirichlet character | Unused here; they are needed for other source conclusions involving cancellation. No character construction or conductor bound is assumed. |
| `N≥1` | Not needed by the proof. The source's positive `N` is included; it is not incorrectly inferred from coprimality. |

The proof excludes only the dual-cone case from the claimed modulus
estimate, exactly as the source does. It does not establish the
cancellation statement of Lemma 3.7, which remains the next separate
numbered obligation.

## Dependency inspection and review conclusion

The mathematical and source-correspondence review found no gap in
the complete proof or mismatch with the assertion of Lemma 3.6.
The exact source normalization, nonzero dual condition, shared-factor
indicator, full modulus range, and constant quantifiers are present.
The stronger finite gcd route proves the entire stated estimate;
it does not rely on assuming the missing result as a numerical
premise.

The twelve new modules passed strict compilation with the pinned
Lean 4.24.0 toolchain. The final targeted build completed successfully
with 3,158 jobs. The combined default-format `#check` and `#print axioms`
inspection exited successfully and printed all thirty-nine actual
types and all thirty-nine dependency lists. Its declaration set was
compared with the complete public theorem set in the twelve modules,
and both actual final endpoint types were read. Every new export has
exactly

```text
Classical.choice
Quot.sound
propext
```

No registered literature premise, new axiom, placeholder, or unchecked
evaluation occurs in these dependencies. The arithmetic, exact unit
sums, finite injections, harmonic bound, and real-power inequalities
are proved in the pinned library or repository. No unproved
Ramanujan evaluation, CRT identity, prime-support decomposition,
divisor estimate, logarithmic estimate, or modulus-sum bound survives
as an extra premise in the source endpoint.

This completed correspondence review supports Certified classification
of the full Lemma 3.6 when the repository verification gates pass. At
the time the review was frozen, strict compilation, the targeted build,
and the complete type/dependency inspection had passed. The full
aggregate verifier and subsequent exact-proof-commit CI gate were
still pending. This review does not claim either execution outcome.

The package adds thirty-nine public theorem exports, twelve proof
modules, and this correspondence review to the preceding Lemma 3.5
scope. After registration, the expected scope is 637 exports, 151
proof modules, and 180 inspected inputs. Completion of the full
verification gates permits the single numbered-result transition to
16 Certified, 0 Partial, 0 Active, and 26 Pending. The thirty-three
auxiliary and supplementary Pending groups, four registered
literature premises, twenty mapped reference groups, and nine pinned
dependency revisions remain separate. In particular, the full
Ramanujan divisor-definition agreement is not silently included in
this milestone. Whole-manuscript certification remains false.

The live ledger, verification report, and execution checkpoint record
the actual registration, aggregate outcome, checked proof commit,
and subsequent exact-commit CI evidence. Historical Lemma 3.5
verification at 598 exports and 139 modules is not execution evidence
for these new files.
