# Source correspondence: Lemma 3.1

## Scope and frozen source

This review covers both assertions of `lem:crt`, Lemma 3.1: the Chinese
remainder factorization of the actual mixed complete sum and its invariance
under multiplication of the integral frequency by a scalar coprime to the
full modulus. It also checks the source definitions, representative
independence, modulus-one specializations, and the two immediate
factorization consequences following the proof.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Content |
| --- | --- |
| `eq:forms`, lines 157–164 | The integral quadratic form `F(x) = xᵀAx` and the standing assumptions on `A` |
| Line 564 | The positive additive phase `e_c(z) = exp(2πiz/c)` |
| `eq:weightproperties`, lines 997–1005 | Functions supplied only at primes not dividing `N`, with scalar invariance and additional hypotheses for later estimates |
| Lines 1006–1009 | Reduction of integral vectors, the actual prime-product weight `ξ_q`, and `ξ_1 = 1` |
| `eq:Cdef`, lines 1010–1013 | The constrained Fourier sum `C_q(u)` |
| `eq:Cstrata`, lines 1014–1025 | Further size hypotheses, unused in Lemma 3.1 |
| `eq:Sdef`, `eq:Snewdef`, lines 1029–1039 | The two complete sums, lift independence, and the cases `q = 1` and `c = 1` |
| `lem:crt`, `eq:crt`, lines 1048–1056 | The two conclusions of Lemma 3.1 |
| Lines 1058–1080 | Scaled vector and unit CRT coordinates, the cone and weight factorizations, and the two phase factors |
| Lines 1082–1087 | The inverse-scalar change of variables proving frequency invariance |
| Lines 1089–1090 | The prime-product formula for `C_q` and multiplicativity of `S_c` |

The Ramanujan-sum formula at lines 1043–1046 and the prime-power Gauss
formula beginning with Lemma 3.2 at line 1092 are distinct statements.
Neither is assumed in this deduction or certified by this review.

## Modules and review boundary

| Module | Public exports | Reviewed role |
| --- | ---: | --- |
| [CRTCharacters.lean](../../QuaternaryQuadraticForms/CRTCharacters.lean) | 3 | The actual standard additive characters at product moduli and at modulus one |
| [CRTArithmetic.lean](../../QuaternaryQuadraticForms/CRTArithmetic.lean) | 8 | The source's scaled CRT bijections on residue classes, units, and vectors |
| [CompleteSumAlgebra.lean](../../QuaternaryQuadraticForms/CompleteSumAlgebra.lean) | 9 | Integral quadratic values, their formal-polynomial identification, coordinate lifts, and reduction identities |
| [CompositeWeights.lean](../../QuaternaryQuadraticForms/CompositeWeights.lean) | 16 | The literal product of local functions, periodicity, coprime factorization, and scalar invariance |
| [MixedPhase.lean](../../QuaternaryQuadraticForms/MixedPhase.lean) | 4 | Lift independence and the exact two-factor source phase congruence |
| [CompleteSums.lean](../../QuaternaryQuadraticForms/CompleteSums.lean) | 3 | The actual finite-sum definitions and independence of all integer representatives |
| [CompleteSumCRT.lean](../../QuaternaryQuadraticForms/CompleteSumCRT.lean) | 2 | Factorization of the actual mixed summand and complete finite sum |
| [CompleteSumInvariance.lean](../../QuaternaryQuadraticForms/CompleteSumInvariance.lean) | 3 | The inverse-scalar summand identity and frequency invariance under the exact integer gcd condition |
| [CompleteSumSpecializations.lean](../../QuaternaryQuadraticForms/CompleteSumSpecializations.lean) | 8 | Modulus-one values, the actual prime-field cone sum, and its existing integral Fourier-sum specialization |
| [CompleteSumFactorization.lean](../../QuaternaryQuadraticForms/CompleteSumFactorization.lean) | 3 | The two multiplicativity identities and the squarefree prime-product corollary |
| [SourceWeights.lean](../../QuaternaryQuadraticForms/SourceWeights.lean) | 3 | Exact treatment of the family supplied only at primes not dividing `N` |
| [CompleteSumTheorem.lean](../../QuaternaryQuadraticForms/CompleteSumTheorem.lean) | 4 | Both source conclusions, separately and in a single bundled theorem |

The twelve modules contain 66 new public theorem exports. Definitions and
private helper lemmas are not additional numbered results or additional
public theorem exports. All twelve modules have passed strict compilation
in the pinned Lean/mathlib environment. The actual types and axiom lists
of all 66 exports have also been inspected successfully. This record is
the completed source-correspondence review; the aggregate repository gate
is a separate requirement for Certified classification.

## Actual objects and representative independence

`Fin 4` represents the four coordinates, with the order-preserving
relabeling from `0,1,2,3` to the manuscript's `1,2,3,4`. The data `A` and
`u` are an actual integer matrix and an actual integral frequency. The
definition

```lean
integralQuadraticValue A x := dotProduct x (A.mulVec x)
```

is exactly `F(x) = xᵀAx`. The theorem
`integralQuadraticValue_eq_eval` identifies it with evaluation of the
existing formal polynomial `matrixQuadraticPolynomial A`. Thus the new
local-sum definitions use the same form as the previously checked
geometric and Fourier definitions.

`matrixQuadraticValue_map` proves compatibility with a coefficient ring
homomorphism, including reduction into every `ZMod n`.
`matrixQuadraticValue_mul` and `integralQuadraticValue_mul` prove the
literal quadratic homogeneity `F(t x) = t² F(x)`. These facts use no
symmetry, determinant, characteristic, or invertibility assumption. The
integral congruence and divisibility lemmas are proved from the coefficient
map, so the constraint remains the original congruence `q ∣ F(x)`.

For a positive modulus `n`, `residueLift n x` is the vector of canonical
integer representatives `((x i).val : ℤ)`. `residueLift_cast` proves that
reduction recovers `x`, including at modulus one. The canonical choice is
used to define the sums, and its irrelevance is proved separately.

The additive character is mathlib's actual `ZMod.stdAddChar`. Its proved
identity `ZMod.stdAddChar_coe` is

$$
\operatorname{stdAddChar}_n(z\bmod n)
  =\exp(2\pi i z/n),
$$

which has the sign and normalization in the source. The product-modulus
lemmas establish

$$
e_{mn}(nz)=e_m(z),\qquad
e_{mn}(na+mb)=e_m(a)e_n(b)
$$

for all positive `m,n`, without needing their coprimality. They do not
introduce an arbitrary character or a character-factorization premise.

With the prime-product weight described below, the mixed sum is the
literal finite sum

$$
\mathcal S_{q,c}(u)
 =\sum_{a\in(\mathbb Z/c\mathbb Z)^\times}
   \sum_{x\in(\mathbb Z/qc\mathbb Z)^4}
   \mathbf 1_{q\mid F(\widetilde x)}\,
   \xi_q(\widetilde x)\,
   e_{qc}\bigl(\widetilde a F(\widetilde x)+u\cdot\widetilde x\bigr).
$$

Here `mixedIntegerSummand` uses an `if` with value zero outside the cone,
and `mixedCompleteSum` sums it over the actual unit and vector types. The
zero branch is exactly the source restriction on the summation set. No
factor of `q`, cardinality normalization, lifted unrestricted parameter
sum, or different quadratic constraint is substituted for this object.
The definitions of `unweightedCompleteSum` and `constrainedFourierSum`
likewise match `S_c` and `C_q` directly.

The source assertion that the phase is well defined in `a mod c` requires
the cone condition. If `b-a=c\ell` and `F(x)=qk`, then

$$
(bF(x)+u\cdot x)-(aF(x)+u\cdot x)=qc\,k\ell.
$$

`mixedPhase_intCast_lift_independent` proves precisely the corresponding
equality in `ZMod (q*c)`, and `mixedPhase_lift_independent` applies the
actual standard character. Neither assumes `(q,c)=1`.
`mixedIntegerSummand_a_congr` extends this equality to the complete
summand: off the cone both sides are zero.

`mixedIntegerSummand_x_congr` proves invariance under changing all vector
representatives modulo `qc`. Reduction modulo `q` preserves the cone;
reduction to each prime dividing `q` preserves the weight; the actual
quadratic and dot-product maps preserve the phase modulo `qc`.
`mixedIntegerSummand_congr` combines the two independent choices. Thus the
CRT proof can use arbitrary integer lifts of its explicit coordinates
without presuming that a scaled sum is itself the canonical lift.

## Generic weights and the exact good-prime family

`compositeWeight ξ q x` is defined as

$$
\prod_{p\in q.\mathrm{primeFactors}}
     \xi_p(x\bmod p).
$$

The finite set contains each distinct prime divisor once. This agrees
with the source weight for every positive squarefree `q` and gives a
useful extension to other positive moduli. `compositeWeight_one` proves
the empty product is the constant function one. At a prime,
`compositeWeight_prime` and `compositeWeight_mod_prime` recover exactly
the supplied local function.

The family in the elementary helpers is total in its natural-number
index only to simplify dependent types. The product never evaluates a
nonprime index. `PrimeWeightsInvariant ξ q` asks only for

```lean
∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
  ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y
```

and imposes no property on other indices. The proofs of periodicity,
factorization, and scalar invariance use the literal local functions;
they do not replace them by multiplicative characters, projective class
functions with an assumed sum formula, or abstract numerical quantities.

The final source wrapper removes even the convenience of supplying a
total family. Its data are exactly of type

```lean
ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ
```

so a function is supplied only for a prime not dividing `N`.
`extendPrimeWeights N ξ` agrees with that function there and is defined
to be zero elsewhere. This extension introduces no hypothesis on an
excluded prime. Under `q.Coprime N`, every prime divisor of `q` belongs to
the original domain. `primeWeightsInvariant_extend` obtains exactly the
local invariance needed by the generic theorem.

Crucially, `compositeWeight_extend` proves equality with the product of
the original dependent family itself, indexed by the subtype
`p : q.primeFactors` with primality and nondivisibility proved for each
factor. Thus the extension in the final theorem denotes precisely the
source `ξ_q`. The same bridge applies to both factors of a CRT
decomposition, since `(q₁q₂,N)=1` implies `(q₁,N)=(q₂,N)=1`.

The source's zero value and bound `|ξ_p(x)| ≤ 1`, the polynomials `D_p`,
their degree bounds, and the stratified Fourier estimate are unused in
this identity proof. They are not assumed by the Lean endpoints. The
only weight hypothesis used is the source scalar invariance, at the
source primes. This permits all source instances, including the later
quadratic-character and general multiplicative-character weights.

## Both CRT changes of variables and the exact phase

Write `n₁=q₁c₁` and `n₂=q₂c₂`. The source hypothesis is

```lean
(q₁ * c₁).Coprime (q₂ * c₂)
```

and every modulus is a natural number with a `NeZero` instance. These
instances express positivity for the natural moduli and include one.
No condition `(q,c)=1` is added. In particular `q_i` and `c_i` may have
common prime factors within the same CRT block.

`scaledChineseRemainder` is built from mathlib's proved CRT equivalence,
composed with multiplication by the appropriate coprime units on each
component. Its integer-lift formula is exactly

$$
(x_1,x_2)\longmapsto n_2x_1+n_1x_2\pmod{n_1n_2}.
$$

`scaledChineseRemainderVector` applies this equivalence coordinatewise.
The use of a ring equivalence for the identity
`n₁n₂=(q₁q₂)(c₁c₂)` changes only the spelling of the modulus. The proved
lift formula verifies that the integer coordinates in the phase
calculation are the coordinates of this actual bijection.

Independently, `scaledChineseRemainderUnits` is an equivalence

$$
(\mathbb Z/c_1\mathbb Z)^\times
 \times(\mathbb Z/c_2\mathbb Z)^\times
 \simeq (\mathbb Z/c_1c_2\mathbb Z)^\times,
$$

whose underlying residue is exactly

$$
a=c_2a_1+c_1a_2\pmod{c_1c_2}.
$$

This is a bijection of the reduced-residue summation sets, not merely
an equivalence on all residue classes or an unproved unit condition.
The required `(c₁,c₂)=1` is deduced from the displayed source hypothesis.

For the scaled vector `x=n₂x₁+n₁x₂`, reduction modulo `q₁` gives
`x=n₂x₁`, and reduction modulo `q₂` gives `x=n₁x₂`. The complementary
scalars are units modulo the respective cone moduli. Quadratic
homogeneity and cancellation of these units prove

$$
q_1q_2\mid F(x)
 \quad\Longleftrightarrow\quad
q_1\mid F(x_1)\ \text{and}\ q_2\mid F(x_2).
$$

Combining the two divisibilities uses the deduced `(q₁,q₂)=1`. It does
not rely on squarefreeness or nonsingularity. Disjoint prime supports and
local scalar invariance similarly prove

$$
\xi_{q_1q_2}(x)=\xi_{q_1}(x_1)\xi_{q_2}(x_2).
$$

The exact quadratic expansion used in `MixedPhase.lean` is

$$
F(rx+sy)=r^2F(x)+s^2F(y)
  +rs\bigl(x^{\mathsf T}Ay+y^{\mathsf T}Ax\bigr).
$$

The cross term has the factor `n₁n₂`. More subtly, the terms containing
the opposite unit parameter require the two cone conditions. For
example,

$$
c_1a_2 n_2^2 F(x_1)
 =n_1n_2\,a_2n_2\bigl(F(x_1)/q_1\bigr),
$$

which is an integer multiple of the full modulus because `q₁ ∣ F(x₁)`;
the second such term is treated symmetrically. The formal proof uses
divisibility witnesses and polynomial identities, so it does not divide
inside a residue ring or assume an inverse of `q_i` there.

`mixedPhase_crt_intCast` proves the resulting exact phase congruence for
arbitrary integer representatives. `mixedPhase_crt` then proves

$$
e_{n_1n_2}\bigl((c_2a_1+c_1a_2)F(x)+u\cdot x\bigr)
 =e_{n_1}\bigl(c_2n_2a_1F(x_1)+u\cdot x_1\bigr)
  e_{n_2}\bigl(c_1n_1a_2F(x_2)+u\cdot x_2\bigr).
$$

Both factors and both positive linear phases agree with source line
1076. The polynomial phase identity itself needs the cone conditions,
not coprimality; coprimality enters the actual reindexings.

`mixedIntegerSummand_crt` combines the weight, cone, and phase identities.
If either local cone condition fails, the corresponding factor and the
global summand are zero. This verifies the full summand identity,
including the excluded vectors.

The local unit parameters still carry the exact multipliers

$$
c_2n_2=q_2c_2^2,\qquad c_1n_1=q_1c_1^2.
$$

The proof derives that they are coprime to `c₁` and `c₂`, respectively,
from `(n₁,n₂)=1`. Multiplication by the resulting units permutes each
actual local unit group. `mixedCompleteSum_scaled_unit`, a private
proved helper, removes the multipliers using these permutations and
the already proved lift independence. Reindexing both finite sums by
their equivalences and distributing their products then gives the public
`mixedCompleteSum_crt`:

$$
\mathcal S_{q_1q_2,c_1c_2}(u)
 =\mathcal S_{q_1,c_1}(u)\mathcal S_{q_2,c_2}(u).
$$

The argument preserves the frequency `u` in both final factors; there
is no remaining inverse-modulus scalar in a frequency argument.

## Unit-frequency invariance under the literal integer condition

The public endpoint `mixedCompleteSum_unit_frequency` has the exact
source scalar hypothesis

```lean
(t : ℤ)
(ht : t.gcd ((q * c : ℕ) : ℤ) = 1)
```

and concludes

```lean
mixedCompleteSum ξ q c A (fun i => t * u i) =
  mixedCompleteSum ξ q c A u
```

The equivalence between this integer gcd condition and the residue
being a unit is supplied by proved mathlib lemmas. This covers negative
integers and does not assume `t ≠ 0` in `ℤ`.

For an inverse representative `s` with `ts=1 mod qc`, the proved
`mixedIntegerSummand_inverse_scale` is the exact source substitution

$$
(a,x)\longmapsto(t^2a,sx)
$$

inside the summand with frequency `tu`. The weight is unchanged by the
unit action at every prime dividing `q`. The cone condition is preserved
because `F(sx)=s²F(x)` and `s²` is a unit modulo `q`. The phase calculation
is

$$
(t^2a)F(sx)+(tu)\cdot(sx)
 =(ts)^2aF(x)+(ts)u\cdot x
 \equiv aF(x)+u\cdot x\pmod{qc}.
$$

`mixedCompleteSum_isUnit_frequency` realizes these substitutions as
permutations of `(ZMod c)ˣ` and `Fin 4 → ZMod (q*c)`. The former uses
the square of the reduced unit; the latter uses multiplication by its
inverse in each coordinate. The canonical-lift discrepancies are
discharged by `mixedIntegerSummand_congr`, and the sums are reindexed by
the actual equivalences. Thus invariance is proved for the literal sum,
with no abstract invariance premise on the complete sum itself.

## Modulus one and definition bridges

At modulus one `ZMod 1` is the one-element ring. Its unique element is
also its unique unit; a sum over `(ZMod 1)ˣ` therefore has one term, not
zero terms. `stdAddChar_modulus_one` is the constant character one, the
cone congruence modulo one is automatic, and the prime-product weight
is one.

The following public identities are proved directly from the definitions.

| Export | Exact source identity |
| --- | --- |
| `mixedCompleteSum_one_left` | `𝒮_{1,c}(u) = S_c(u)` |
| `mixedCompleteSum_one_right` | `𝒮_{q,1}(u) = C_q(u)` |
| `unweightedCompleteSum_one` | `S_1(u) = 1` |
| `constrainedFourierSum_one` | `C_1(u) = 1` |
| `mixedCompleteSum_one_one` | `𝒮_{1,1}(u) = 1` |

No local zero-value assumption is used to replace the empty product by
zero. The unit formulation of frequency invariance also correctly covers
`qc=1`, for which every integer, including `t=0`, has gcd one with the
modulus. No nonzero-residue test is used in place of the unit condition
at a composite modulus or at one.

`constrainedFourierSum_prime` identifies the actual prime specialization
with

$$
\sum_{\substack{x\in\mathbb F_p^4\\
 x^{\mathsf T}(A\bmod p)x=0}}
 \xi_p(x)e_p((u\bmod p)\cdot x).
$$

The proof reduces the integral matrix and vector through the proved maps,
uses `p ∣ F(\widetilde x)` if and only if the reduced form is zero, and
identifies the prime weight with the supplied local function. The zero
vector is part of the source cone; if the local source weight vanishes
there, its contribution vanishes by that value rather than by altering
the summation set.

For an arbitrary `MulChar (ZMod p) ℂ` and arbitrary integral polynomial
`G`, `constrainedFourierSum_eq_integralFourierSum` identifies the
specialization `ξ_p(x)=ψ(G mod p evaluated at x)` with the existing
`integralFourierSum p A ψ G u`. The further export
`constrainedFourierSum_polynomial_character` makes this choice of family
literal in its statement. These definition bridges impose no
nonprincipality, character-order, homogeneity, smoothness, or degree
hypothesis. Such hypotheses belong to separate estimates and are not
needed to identify the objects.

## The immediate factorization consequences

`unweightedCompleteSum_mul` applies the mixed CRT identity at
`q₁=q₂=1` and the first specialization above to prove multiplicativity
of the literal `S_c(u)` for arbitrary coprime positive `c₁,c₂`.

`constrainedFourierSum_mul` applies the same identity at `c₁=c₂=1`
and proves multiplicativity of the actual `C_q(u)` under local scalar
invariance. `constrainedFourierSum_primeFactors` then proves the source
formula

$$
C_q(u)=\prod_{p\mid q}C_p(u)
$$

for positive squarefree `q`. Its product is over `p : q.primeFactors`,
so each factor is an actual prime sum with positivity supplied by the
proved primality of its index. The proof uses the actual factorization
`q=∏_{p∣q}p` for squarefree `q`, an induction over the finite prime set,
and the preceding proved multiplicativity on coprime factors. This is
where squarefreeness is needed; it is not omitted from this corollary.
The empty product agrees with `C_1(u)=1`.

For the source-domain family, `primeWeightsInvariant_extend` supplies
the required hypothesis and `compositeWeight_extend` identifies every
factor. The corollaries at lines 1089–1090 are therefore included without
assuming any local function or property at a prime dividing `N`.

## Exact terminal source statement and hypothesis audit

The complete source endpoint is
`QuaternaryQuadraticForms.source_complete_sum_crt` in
`CompleteSumTheorem.lean`. Its data and hypotheses are

```lean
(N : ℕ)
(ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
(q₁ q₂ c₁ c₂ : ℕ)
[NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
(A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
(hqN : (q₁ * q₂).Coprime N)
(hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
(hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
  ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
```

Its first conjunct is the factorization of the actual
`mixedCompleteSum (extendPrimeWeights N ξ)` at `(q₁q₂,c₁c₂)`. Its
second conjunct quantifies over every integer `t` with
`t.gcd ((q₁q₂c₁c₂ : ℕ) : ℤ)=1` and states the source invariance for
the same mixed sum. The data `A,u,ξ` are unchanged between the two
conclusions and between the local factors.

`source_mixedCompleteSum_crt` exports the first clause separately.
`source_mixedCompleteSum_unit_frequency` exports the second for arbitrary
positive `q,c`, without needing to supply a CRT factorization of them.
`complete_sum_crt` bundles both clauses for the total family and its
local `PrimeWeightsInvariant` hypothesis. All four actual types were
inspected after strict compilation.

| Source assumption or convention | Treatment in the final statements |
| --- | --- |
| Positive integral moduli | Positive natural moduli are represented by `NeZero`; every source modulus is included. |
| `q=q'q''`, `c=c'c''` | Products appear literally in the theorem, avoiding any extra equality assumptions. |
| `(q'c',q''c'')=1` | Exactly the displayed block coprimality; the derived cross-coprimalities are proved internally. |
| `(q,N)=1` and weights supplied only for `p∤N` | Exact source-family type, `hqN`, and the proved extension/product bridge. |
| `t∈ℤ` with `(t,qc)=1` | Exact integer gcd condition, including negative scalars and the modulus-one case. |
| `q` squarefree | Unused for the two main identities, which are proved for a broader prime-product definition; retained for the stated prime-product corollary. |
| Symmetry, nonsingularity, and nonsquare determinant of `A` | Unused: the actual quadratic identities and residue changes hold for every integral matrix. All source matrices are included. |
| `N≥1`, `rad(N_F)∣N` | The positive source `N` is represented by a natural number. No lower bound or bad-prime condition is needed by the identity proof. |
| Zero-value and norm bounds for `ξ_p`, and all `D_p,E,K` data | Unused in the identity proof and therefore omitted; scalar invariance remains exactly where needed. |
| No restriction on `c` apart from positivity | Preserved: `c` can be even, contain primes dividing `N`, and share primes with `q`. |

Omitting these unused assumptions strengthens the identity statements and
does not exclude a manuscript instance. In particular, the proof does
not assume `(q,c)=1`, good reduction at the primes of `c`, a field
structure on a composite residue ring, or invertibility of the quadratic
matrix.

## Inspected dependencies and review conclusion

The actual `#check` and `#print axioms` inspection completed successfully
for all 66 new public exports. Sixty-five have exactly

```text
Classical.choice
Quot.sound
propext
```

The remaining export, `residueLift_cast`, has exactly `Quot.sound` and
`propext`. In particular, all four terminal wrapper exports, both main
sum identities, the two factorization consequences, and the definition
bridges have no literature-premise dependency.

The Chinese remainder equivalences, finite-sum reindexings, standard
additive-character identities, and arithmetic facts are proved in the
pinned mathlib or in the new modules. No external input, internal
manuscript lemma, or omitted deduction was introduced as an axiom. The
four previously registered literature premises are unchanged and none
occurs in the actual dependencies of these new exports. Imports of
modules that contain other verified results do not alter this observed
dependency statement.

All twelve modules passed strict compilation with the pinned
`leanprover/lean4:v4.24.0`, pinned dependency revisions,
`autoImplicit=false`, and `warningAsError=true`. The independent review
of the definitions, proofs, and printed terminal types finds both source
clauses present, all source instances covered, and no mathematical gap.
It specifically checks the two different CRT bijections, both local
phase multipliers, the cone-dependent lift independence, the source-only
prime domain, and the degenerate modulus-one conventions.

This completed source-correspondence review supports Certified
classification of Lemma 3.1 once the full repository verification gates
pass. At the time this review was frozen, the module builds and actual
export inspection were complete and the aggregate gate was still
pending. The live ledger, verification report, and execution checkpoint
record the eventual checked scope, hashes, dependency checks, and exact
commit/run evidence. The intended added scope is 66 public exports in
twelve modules plus this review; the surrounding Gauss-sum, analytic,
and other pending manuscript obligations remain separate.
