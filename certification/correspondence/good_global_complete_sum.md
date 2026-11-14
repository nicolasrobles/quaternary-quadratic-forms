# Lemma 3.5: complete global formula and dual-cone identity

## Source and scope

This review covers both assertions of `lem:goodglobal`. With the
manuscript's actual factors

$$
d=q_1=\gcd(q,c),\qquad e=q_2=q/d,
$$

the first assertion, under `(c,N_F)=1`, is

$$
\mathcal S_{q,c}(u)
=C_e(u)\,d c^2\chi(dc)\,
\xi_d(\operatorname{adj}(A)u)\,R_{dc}(F^*(u)).
$$

The second assertion, under `F*(u)=0`, is the identity

$$
\mathcal S_{q,c}(u)
=C_e(u)\,d^2\chi(d)\,
\xi_d(\operatorname{adj}(A)u)\,S_c(u)
$$

for every positive `c`, including moduli with arbitrary bad-prime
factors. Both assertions are proved together in
`QuaternaryQuadraticForms.source_good_global_complete_sum`. The
second assertion is a product identity and includes vanishing values
of `S_c(u)`.

The frozen source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | Symmetric nonsingular integral `A`, `F(x)=xᵀAx`, `α=det A`, `N_F=2|α|`, and the supplied character's stated good-prime values |
| Notation, lines 561–572 | The positive additive character and sums over reduced residue classes |
| `eq:dualform`, lines 816–818 | The actual dual value `F*(u)=uᵀ adj(A)u` |
| `sec:local`, lines 997–1025 | `rad(N_F)∣N`, the original prime functions, scalar invariance, and the additional weight and Fourier-bound hypotheses |
| `eq:Cdef`, lines 1006–1012 | The original prime-product weight and the actual constrained Fourier sum |
| `eq:Sdef`, `eq:Snewdef`, lines 1029–1039 | The actual unweighted and mixed complete sums, including their modulus-one specializations |
| `eq:ramanujan`, lines 1043–1045 | The actual Ramanujan unit sum |
| `eq:q1q2`, lines 1234–1238 | The literal gcd and quotient defining the two source factors |
| `lem:goodglobal`, `eq:goodglobal`, `eq:coneratio`, lines 1240–1252 | Both assertions of Lemma 3.5 |
| Lines 1254–1268 | Prime-power assembly of the good-modulus formula |
| Lines 1270–1279 | The totient specialization and extension across the bad-prime factor |

The proof uses the previously checked complete versions of Lemmas
3.1, 3.2, and 3.4. The actual Ramanujan multiplicativity, character
agreement, arithmetic factorizations, and global assembly are proved
in the present modules; none is a premise standing in for part of
Lemma 3.5.

## Modules, declarations, and inspected types

All declaration names in the following table are in the
`QuaternaryQuadraticForms` namespace. Their actual printed types and
axiom lists were inspected, including the hypotheses of the three
source endpoints.

| Module | Public theorem exports and reviewed role |
| --- | --- |
| [SquarefreeGcdFactors.lean](../../QuaternaryQuadraticForms/SquarefreeGcdFactors.lean) | `squarefree_gcd_factors`: the actual gcd/quotient package; `gcd_mul_blocks_coprime`: coprimality of the full CRT blocks; `squarefree_shared_gcd_factors`: the shared-support split of a squarefree divisor; `squarefree_dvd_prime_pow_eq_one_or_prime`: the two possible squarefree divisors of a prime power |
| [ModulusPrimeSplit.lean](../../QuaternaryQuadraticForms/ModulusPrimeSplit.lean) | `exists_modulus_prime_split`: an actual positive bad/good decomposition; `coprime_of_prime_dvd_support`: coprimality from prime support; `gcd_eq_good_part_of_prime_support`: preservation of the actual gcd after removing the bad factor |
| [RamanujanMultiplicativity.lean](../../QuaternaryQuadraticForms/RamanujanMultiplicativity.lean) | `integralRamanujanSum_mul`: multiplicativity of the actual unit sum; `integralRamanujanSum_zero`: its exact totient value at zero; `totient_mul_of_dvd`: `φ(dc)=d φ(c)` when `d∣c` |
| [GlobalQuadraticCharacter.lean](../../QuaternaryQuadraticForms/GlobalQuadraticCharacter.lean) | `globalQuadraticChar_one`, `globalQuadraticChar_mul`, `globalQuadraticChar_prime`, `globalQuadraticChar_prime_power`, `globalQuadraticChar_sq`: actual Jacobi-symbol identities; `monoidHom_eq_globalQuadraticChar`: determination by good-prime values; `globalQuadraticChar_eq_dirichletCharacter`: proved agreement with the supplied Dirichlet character at good positive moduli |
| [GoodUnweightedCompleteSum.lean](../../QuaternaryQuadraticForms/GoodUnweightedCompleteSum.lean) | `unweightedCompleteSum_good_modulus`: the actual `S_c(u)` formula at every good positive modulus and every integral frequency |
| [SourceGoodModulus.lean](../../QuaternaryQuadraticForms/SourceGoodModulus.lean) | `source_coprime_quadraticBadPrimeModulus`: the source radical condition implies `(q,N_F)=1` from `(q,N)=1` |
| [SourceCompositeWeights.lean](../../QuaternaryQuadraticForms/SourceCompositeWeights.lean) | `compositeWeight_extend_eq_source`: equality with the literal product of original supplied prime functions |
| [SharedSupportCompleteSum.lean](../../QuaternaryQuadraticForms/SharedSupportCompleteSum.lean) | `mixedCompleteSum_shared_support`: the exact good-modulus formula for squarefree `q∣c` |
| [GoodGlobalCompleteSum.lean](../../QuaternaryQuadraticForms/GoodGlobalCompleteSum.lean) | `mixedCompleteSum_good_modulus`: the full good-modulus formula with the actual gcd and quotient |
| [ConeCompleteSum.lean](../../QuaternaryQuadraticForms/ConeCompleteSum.lean) | `mixedCompleteSum_good_modulus_dual_cone`: specialization at good `c`; `mixedCompleteSum_dual_cone`: the complete identity at every positive `c` |
| [GoodGlobalTheorem.lean](../../QuaternaryQuadraticForms/GoodGlobalTheorem.lean) | `source_mixedCompleteSum_good_modulus`, `source_mixedCompleteSum_dual_cone`, `source_good_global_complete_sum`: the two original-character/original-weight clauses and their conjunction |

These are twenty-seven public theorem exports in eleven modules.
The new definitions `globalQuadraticChar` and `sourceCompositeWeight`
are concrete mathematical objects, not additional numbered results.
Private induction statements are proved within the corresponding
modules and do not add hypotheses to the exported endpoints.

## Actual objects and the source character

The sums retain the existing definitions in
[CompleteSums.lean](../../QuaternaryQuadraticForms/CompleteSums.lean)
and [RamanujanSums.lean](../../QuaternaryQuadraticForms/RamanujanSums.lean).

| Manuscript object | Lean object and interpretation |
| --- | --- |
| `F(x)` | `integralQuadraticValue A x`, the actual integral matrix polynomial |
| `F*(u)` | `dotProduct u (A.adjugate.mulVec u)` |
| `N_F` | `quadraticBadPrimeModulus A = 2*A.det.natAbs` |
| `𝒮_(q,c)(u)` | `mixedCompleteSum ξ q c A u`, over actual units modulo `c` and vectors modulo `q*c`, with the condition `q∣F(x)` |
| `S_c(u)` | `unweightedCompleteSum c A u`, over actual units and vectors modulo `c` |
| `C_e(u)` | `constrainedFourierSum ξ e A u`, over actual vectors modulo `e` satisfying `e∣F(x)` |
| `R_n(t)` | `integralRamanujanSum n t`, the actual sum of `ZMod.stdAddChar(a*t)` over `(ZMod n)ˣ` |
| `ξ_d(adj(A)u)` | The literal product `sourceCompositeWeight N ξ d hdN (A.adjugate.mulVec u)` in the source endpoints |
| `χ(n)` | The original supplied `χ : DirichletCharacter ℂ M`, evaluated at `(n : ZMod M)` in the source endpoints |

The mixed sum uses canonical integer representatives, the positive
standard additive character, and the exact cone condition modulo
`q`. The earlier lift-independence results justify its source
interpretation. This milestone changes none of these definitions or
conventions. The same integral frequency `u` is retained throughout
the CRT and prime-power arguments.

For internal assembly the new concrete coefficient is

```lean
def globalQuadraticChar (α : ℤ) (n : ℕ) : ℂ := (jacobiSym α n : ℂ)
```

Its prime value is the actual `legendreSym p α`; its prime-power
value is that symbol raised to `k`, including `k=0`. Multiplicativity
comes from the proved mathlib Jacobi-symbol identity. The square-one
export requires `n.Coprime α.natAbs`; it is not used to divide by a
character value in the cone argument.

The source supplies a primitive quadratic Dirichlet character and
explicitly states its Legendre values at every prime outside `N_F`.
The formal source endpoints take an actual
`χ : DirichletCharacter ℂ M` together with exactly that prime-value
property:

```lean
∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
  χ (p : ZMod M) = (legendreSym p A.det : ℂ)
```

`monoidHom_eq_globalQuadraticChar` proves, by induction over primes,
that an actual multiplicative map with these values agrees with the
Jacobi coefficient at every positive argument coprime to
`2*α.natAbs`. `globalQuadraticChar_eq_dirichletCharacter` applies it
to the composition of the supplied character's monoid homomorphism
with the natural-number cast into `ZMod M`. Thus composite agreement
is proved from multiplicativity and the source's stated prime
values; agreement at composite arguments is not assumed.

In the first clause the required argument is `dc`. It is good because
`d∣c` and `c` is good. In the all-modulus cone clause the required
argument is only `d`; it is good because `d∣q` and the source radical
condition proves that `q` is good. No agreement at zero, bad, or even
arguments is asserted for the internal Jacobi coefficient. In
particular, the all-modulus theorem does not evaluate `χ(c)` when `c`
has bad-prime factors.

This is a specialization theorem for the original supplied source
character. It does not construct the character attached to
`ℚ(√α)`, prove its primitivity, or identify its conductor. Those
properties are unnecessary for Lemma 3.5 once the actual character
and its source-stated good-prime values are supplied. The standing
nonsquareness of `α` is likewise unused by these identities.

## The seven arithmetic helpers

The formal proof uses actual gcds and quotients, with no assumed
factorization. `squarefree_gcd_factors q c hq hc` proves

$$
de=q,\qquad d>0,\quad e>0,\qquad
d,e\text{ squarefree},\qquad (e,dc)=1,\qquad d\mid c.
$$

Here `hq : Squarefree q` and `hc : c≠0`; the factors are literally
`q.gcd c` and `q / q.gcd c`. The coprimality is the full condition
needed to split the mixed-sum moduli, rather than merely `(d,e)=1`.
The sum modules use local `NeZero` instances derived from the core
gcd and quotient positivity theorems, so the exported formulas keep
the literal factors. No new global instance or alternative factor
definition is needed.

For coprime `m,n` and squarefree `q∣m*n`,
`squarefree_shared_gcd_factors` proves

$$
\gcd(q,m)\gcd(q,n)=q,
$$

with both gcds squarefree and dividing their respective moduli.
`gcd_mul_blocks_coprime` proves

$$
\bigl(\gcd(q,m)m,\ \gcd(q,n)n\bigr)=1.
$$

This latter theorem needs only `(m,n)=1`; it has no squarefreeness
hypothesis. The actual full blocks are therefore eligible for the
previously proved mixed-sum CRT theorem. At a prime power,
`squarefree_dvd_prime_pow_eq_one_or_prime` proves `q=1 ∨ q=p` from
`Squarefree q`, primality of `p`, and `q∣p^k`. It also includes the
exponent-zero case, where only `q=1` can occur.

For the second source clause, `exists_modulus_prime_split c N hc`
constructs positive `b,g` such that

$$
c=bg,\qquad (b,g)=1,\qquad (g,N)=1,
\qquad p\mid b\Longrightarrow p\mid N
\quad\text{for every prime }p.
$$

The construction uses `Nat.recOnPosPrimePosCoprime`. At a prime power
the entire factor goes into `b` if its prime divides `N`, and into
`g` otherwise; at a coprime product the factors are multiplied and
their cross-coprimality is proved from divisibility. This supplies
the actual source decomposition at `N=N_F`; it is not a theorem
conditional on an unspecified bad/good split.

`coprime_of_prime_dvd_support` derives `(q,b)=1` from `(q,N)=1` and
that prime-support condition. Finally,
`gcd_eq_good_part_of_prime_support` proves
`gcd(q,c)=gcd(q,g)` from `c=b*g` and the same hypotheses. These
generic arithmetic statements include `c=1` and the boundary
conventions `N=0` or `N=1`; their application here uses the actual
nonzero source `N_F`.

## Ramanujan sums, totients, and the unweighted formula

`integralRamanujanSum_mul` proves

$$
R_{mn}(t)=R_m(t)R_n(t),\qquad (m,n)=1,
$$

for the literal unit sums and every integer `t`. It reindexes by the
actual `scaledChineseRemainderUnits` equivalence. The corresponding
residue has value `n*a.val+m*b.val`, so the positive standard
character separates into the two characters with the same argument
`t`. This is a proved bijection of reduced residue classes, not a
multiplicativity axiom. Both moduli may equal one.

`integralRamanujanSum_zero` evaluates the sum by the actual
cardinality of `(ZMod n)ˣ`, giving `(Nat.totient n : ℂ)`. The unique
unit of `ZMod 1` contributes one, as required by `R_1(0)=φ(1)=1`.
`totient_mul_of_dvd d c h` proves `φ(dc)=d φ(c)` whenever `d∣c`.
It includes zero cases; in the nonzero case its cancellation is
only by the proved positive integer `φ(d)`. No complete sum or
character value is cancelled.

`unweightedCompleteSum_good_modulus` proves

$$
S_c(u)=\operatorname{globalQuadraticChar}(\det A,c)\,
c^2 R_c(F^*(u))
$$

for every positive `c` coprime to `N_F`. The proof uses
`Nat.recOnPosPrimePosCoprime`: the prime-power case is the completed
Lemma 3.2(ii), the case `c=1` uses the actual modulus-one values, and
the product case uses the previously proved `S_c` CRT identity and
the new actual Ramanujan and Jacobi multiplicativity. The matrix is
the given symmetric integral matrix and `u` is unrestricted. There
is no remaining prime-power evaluation hypothesis in this export.

## Assembly at good moduli

The intermediate `mixedCompleteSum_shared_support` treats squarefree
`q∣c`. Its conclusion is

$$
\mathcal S_{q,c}(u)
=q c^2\operatorname{globalQuadraticChar}(\det A,qc)\,
\xi_q(\operatorname{adj}(A)u)\,R_{qc}(F^*(u)).
$$

Its induction is again on the actual positive modulus `c` through
coprime prime-power blocks. At `c=p^k` with `k≥1`, the squarefree
divisor theorem reduces `q` to `1` or `p`. The first case is the
unweighted formula; the second is the completed shared-prime
Lemma 3.4. In that case `q*c=p^(k+1)` and
`p^(2*k+1)=p*(p^k)^2`, giving precisely the required scalar and
Ramanujan modulus. The good-prime hypothesis follows from `p∣c`
and `(c,N_F)=1`.

At a coprime product `c=m*n`, the proof splits `q` into the actual
gcds with `m,n`. Their product is proved to be `q`; their full blocks
are proved coprime. The existing mixed-sum CRT theorem, the actual
prime-product weight identity, and the Ramanujan and character
multiplicativity then combine the two induction conclusions. The
integer identity

$$
q(mn)=(\gcd(q,m)m)(\gcd(q,n)n)
$$

provides the exact final Ramanujan modulus. Scalar invariance
restricts to each gcd factor by divisibility of its prime factors.
The induction base `c=1` forces `q=1` and uses the exact source sum
at modulus one. Consequently no `k=0` case of the ramified theorem
is invoked.

`mixedCompleteSum_good_modulus` now uses `d=gcd(q,c)` and `e=q/d`.
The proved coprimality `(e,dc)=1` permits the actual CRT split into
the blocks `(e,1)` and `(d,c)`. The first factor is exactly
`mixedCompleteSum_one_right`, hence `C_e(u)`; the second is the
shared-support theorem because `d∣c`. The resulting product is the
entire first source formula with the internal Jacobi coefficient.
Every modulus and factor in the conclusion is the literal gcd or
quotient from `eq:q1q2`.

This core good-modulus theorem needs no additional hypothesis that
all primes of `q` are good: primes present only in `e` stay inside
the unevaluated actual `C_e`. The source wrapper supplies the
original weights at those primes through `(q,N)=1`. This weakening
of the source assumptions does not change its conclusion.

## The dual cone and arbitrary bad-prime factors

For good `c`, `mixedCompleteSum_good_modulus_dual_cone` substitutes
the actual integer equality `F*(u)=0` into the good-modulus and
unweighted formulas. It uses

$$
R_{dc}(0)=\varphi(dc)=d\varphi(c),\qquad
R_c(0)=\varphi(c),\qquad
\operatorname{globalQuadraticChar}(\det A,dc)
=\operatorname{globalQuadraticChar}(\det A,d)
\operatorname{globalQuadraticChar}(\det A,c).
$$

Ring rearrangement gives the cone coefficient `d²` multiplying the
actual `S_c(u)`. The proof divides by neither `S_c(u)` nor the
character, weight, or Ramanujan value.

For arbitrary positive `c`, `mixedCompleteSum_dual_cone` applies the
constructed decomposition `c=b*g` at `N=N_F`. From `(q,N_F)=1` it
derives `(q,b)=1`, and hence coprimality of the full CRT blocks
`1*b` and `q*g`. The two existing exact CRT identities give

$$
\mathcal S_{q,c}(u)=S_b(u)\mathcal S_{q,g}(u),\qquad
S_c(u)=S_b(u)S_g(u).
$$

The proved gcd equality identifies the factors `d,e` for `c` with
those for `g`. The good-modulus cone identity applies at `g`, and
multiplication by `S_b(u)` finishes the argument. Its possible
vanishing is fully retained. No Gauss evaluation at bad primes, no
character agreement at bad moduli, and no nonvanishing hypothesis
is used. This is the entire second assertion of Lemma 3.5, including
all bad-prime factors.

## Original weights and the source hypotheses

The source family has exactly the dependent type

```lean
ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ
```

The new `sourceCompositeWeight` is the literal product over
`p : q.primeFactors`, evaluating each supplied function on
`fun i => (x i : ZMod p)`. The primality and `p∤N` proofs are
obtained from membership and `(q,N)=1`. The theorem
`compositeWeight_extend_eq_source` proves equality with the
total-family representation `compositeWeight (extendPrimeWeights
N ξ) q x` already used in the complete sums.

In the source endpoints, the right-hand weight at `d` explicitly
uses this original product. The two sums written with
`extendPrimeWeights` also use precisely the original source
functions: `d∣q` and `e=q/d∣q` give `(d,N)=(e,N)=1`, and the existing
`compositeWeight_extend` identity applies to each summand. In
particular, `constrainedFourierSum (extendPrimeWeights N ξ) e A u`
is the actual source `C_e(u)`. No arbitrary value at a prime dividing
`N` enters either sum. The existing
`primeWeightsInvariant_extend` theorem supplies the core scalar
invariance from the stated invariance of the original family.

`source_coprime_quadraticBadPrimeModulus` derives `(q,N_F)=1`
from `(q,N)=1`, `A.det≠0`, and the exact hypothesis
`primeRadical (quadraticBadPrimeModulus A) ∣ N`. If a prime divided
both `q` and `N_F`, the already proved source good-prime bridge
would contradict its exclusion from `N`. Integer nonsingularity is
used here: `primeRadical 0=1` under the repository convention, so
the radical condition by itself would not exclude prime divisors
of `N_F=0`.

| Source assumption or boundary | Treatment in the checked statements |
| --- | --- |
| Positive integer `q,c` | Natural moduli with `[NeZero q]` and `[NeZero c]`; this covers every source integer modulus at least one. |
| Squarefree `q` | Exactly `Squarefree q`; all gcd-factor squarefreeness and CRT hypotheses are derived. |
| `(q,N)=1` and `rad(N_F)∣N` | Exactly `q.Coprime N` and the repository's actual `primeRadical`; the latter and nonsingularity are used for the all-modulus source clause. |
| Symmetric nonsingular matrix | Exactly `A.transpose=A` and `A.det≠0` in the final conjunction. The standalone good-modulus source clause is stronger and does not need the determinant/radical hypotheses. |
| `N≥1` | Unused, and not asserted to follow from `(q,N)=1`. The allowed extra case `N=0` forces `q=1`, so all source-weight products are empty and the identities remain valid. |
| Supplied Dirichlet character | The actual `DirichletCharacter` and the source-stated good-prime Legendre values; agreement at the needed composite arguments is proved. Primitivity, a specified conductor, and nonsquareness of `det A` are unused. |
| Scalar invariance | The exact nonzero-scalar invariance of each supplied function; the proof uses its restriction to primes dividing `q`. |
| `ξ_p(0)=0`, `|ξ_p|≤1` | Unused by these identities; no weight value is cancelled. |
| `D_p`, `E`, `K`, `eq:Cstrata` | Unused; the present conclusion is an exact identity and uses no Fourier-bound premise. |
| `q=1`, `c=1`, `d=1`, or `e=1` | Included through actual modulus-one sums, the single unit of `ZMod 1`, and empty prime products. |
| Prime-power exponent | The ramified branch uses only `k≥1`; `k=0` is handled by the modulus-one base. The character prime-power helper itself includes every `k≥0`. |
| Frequency | Every `u : Fin 4 → ℤ` in the first clause; the second has only the literal condition `dotProduct u (A.adjugate.mulVec u)=0`, with no nonzero-frequency assumption. |
| Vanishing sums | Included. Neither the good-modulus nor the bad-factor cone argument cancels a complete sum or character value. |

## Full source endpoint

The inspected type of the final theorem is the following conjunction.
The local nonzero instances for its displayed gcd and quotient are
proved as described above.

```lean
theorem source_good_global_complete_sum (N M : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (χ : DirichletCharacter ℂ M)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
    (u : Fin 4 → ℤ) :
    (c.Coprime (quadraticBadPrimeModulus A) →
      mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
        constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
          (q.gcd c : ℂ) * (c : ℂ) ^ 2 * χ ((q.gcd c * c : ℕ) : ZMod M) *
            sourceCompositeWeight N ξ (q.gcd c)
              (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
                integralRamanujanSum (q.gcd c * c)
                  (dotProduct u (A.adjugate.mulVec u))) ∧
    (dotProduct u (A.adjugate.mulVec u) = 0 →
      mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
        constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
          (q.gcd c : ℂ) ^ 2 * χ ((q.gcd c : ℕ) : ZMod M) *
            sourceCompositeWeight N ξ (q.gcd c)
              (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
                unweightedCompleteSum c A u)
```

The first implication is supplied by
`source_mixedCompleteSum_good_modulus`; the second by
`source_mixedCompleteSum_dual_cone`. The printed conjunction contains
both source clauses with their distinct hypotheses. In particular,
the second implication has no good-modulus restriction on `c`.
The matrix, adjugate, dual value, original character, original
weights, and literal gcd/quotient remain visible in the type.

## Dependency inspection and review conclusion

The combined actual type and `#print axioms` inspection exited
successfully for all twenty-seven public theorem exports. Exactly
twenty-six have the standard foundation list

```text
Classical.choice
Quot.sound
propext
```

The remaining theorem, `gcd_mul_blocks_coprime`, depends only on
`propext`. This is the actual inspected distinction; it is not
inferred from a proposed dependency list. No registered literature
premise, new axiom, placeholder, or unchecked evaluation occurs in
these dependencies. The arithmetic, finite equivalences, Jacobi
identities, prime-power evaluations, and CRT identities are proved
in the pinned mathlib or the repository.

All eleven new modules passed strict compilation with the pinned
Lean 4.24.0 toolchain. The targeted root library build passed with
3,180 jobs. Independent review of the source, definitions, proof
chain, and actual printed types found both source assertions in
full. The original character's good-prime values and the original
weight invariance are explicit standing source data. No assumed
composite-character agreement, modulus decomposition, CRT formula,
Ramanujan multiplicativity, Gauss evaluation, or cone specialization
survives as an additional source-internal premise of the final
theorem.

This completed correspondence review supports Certified
classification of the full Lemma 3.5 when the repository
verification gates pass. At the time this review was frozen, strict
compilation, the targeted root build, and actual type/dependency
inspection had passed; the full aggregate verifier and subsequent
exact-proof-commit CI gate were still pending. The execution
checkpoint and verification report record the later outcomes and
the exact checked hashes. Earlier Lemma 3.4 execution evidence
covers its historical scope of 571 exports, 128 modules, and 155
inspected inputs; it is not verification evidence for these new
proof files.

The milestone adds twenty-seven public theorem exports, eleven
proof modules, and this correspondence review. At integration the
scope is 598 registered exports, 139 proof modules, and 167 inspected
inputs, with 15 Certified, 0 Partial, 0 Active, and 27 Pending
numbered results. The 33 auxiliary Pending groups, four registered
literature premises, twenty mapped reference groups, and nine
pinned dependency revisions remain separate and unchanged. Earlier
Section 4, CRT, Gauss, uniform-bound, and shared-prime scope is
preserved. Whole-manuscript certification remains false.

The next full target is Lemma 3.6, `lem:genericmod`: statement
lines 1292–1300 and proof lines 1302–1342. It remains Pending. Its
complete scope includes the actual sum over positive `c≤X` with
`gcd(c,q)=q₁`, the condition `F*(u)≠0`, the exact factor
`q₁²·1_(q₁∣F*(u))`, and the bound with a constant depending only on
`F` and `ε`, uniformly in the other source parameters. No part of
that analytic bound is claimed by this review.
