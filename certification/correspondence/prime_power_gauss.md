# Source correspondence: Lemma 3.2

## Scope and frozen source

This review concerns all three assertions of `lem:gauss`, Lemma 3.2:
the shifted quaternary Gauss evaluation at a good prime power, the
formula for the manuscript's actual unweighted complete sum, and the
cardinality of its actual projective quadric. The pure Gauss recurrence
and affine point count are supporting deductions, not additional
numbered results.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | The integral symmetric matrix, `F(x)=xᵀAx`, `α=det A`, `N_F=2|α|`, and the identification `χ(p)=(α/p)` at good primes |
| Line 564 | The positive additive character `e_n(z)=exp(2πiz/n)` |
| `eq:dualform`, lines 814–818 | The actual adjugate dual form `F*(u)=uᵀadj(A)u` |
| `eq:Sdef`, lines 1029–1035 | The actual sum `S_c(u)` over unit parameters and residue vectors |
| `eq:ramanujan`, lines 1043–1046 | The definition of `R_n(t)` as the unit sum of the standard additive character |
| `lem:gauss`, `eq:gauss`, `eq:unram`, lines 1092–1108 | All three conclusions of Lemma 3.2 |
| Lines 1110–1118 | Square completion and the pure Gauss value |
| Lines 1119–1125 | Residue digits, additive orthogonality, the two-step recurrence, and `V_0=1` |
| Lines 1125–1138 | General-matrix diagonalization, the determinant square, and the prime base case |
| Lines 1140–1142 | Summation over units and permutation by the negative reciprocal coefficient |
| Lines 1144–1152 | The affine count, removal of the origin, and the projective count |

The Möbius expansion of the Ramanujan sum in `eq:ramanujan` is a
separate cited identity. Lemma 3.2 uses the defining unit sum, which is
the object formalized here. The bad-prime estimate beginning with
Lemma 3.3 and the shared-prime mixed sum in Lemma 3.4 are distinct
obligations.

## Modules and review boundary

| Module | Public exports | Reviewed role |
| --- | ---: | --- |
| `QuadraticGaussSums.lean` | 0 | Definitions of the actual residue and integral Gauss sums |
| `IntegralGaussSums.lean` | 6 | Integer lifts, zero coefficients, modulus one, and the existing complete-sum bridge |
| `PrimePowerUnits.lean` | 4 | Deriving actual prime-power units from the source good-prime conditions |
| `MatrixSquareCompletion.lean` | 1 | The precise adjugate square-completion identity over a commutative ring |
| `QuadraticGaussShift.lean` | 3 | Translation of the actual residue sum and the literal modular inverse |
| `IntegralGaussShift.lean` | 3 | Reduction of the dual form and integral square completion at good prime powers |
| `GeneralPrimeGauss.lean` | 2 | Arbitrary-matrix prime base case and the zero scalar |
| `PrimePowerResidues.lean` | 5 | Actual non-coprime digit bijections and finite-sum reindexings |
| `PrimePowerGaussRecurrence.lean` | 7 | Exact digit phase, vector orthogonality, and the two-step recurrence |
| `PrimePowerGauss.lean` | 3 | Closed pure and shifted prime-power formulas and the unit-parameter pure value |
| `RamanujanSums.lean` | 8 | Actual Ramanujan sums, modulus-one values, and unit/inverse reindexings |
| `GaussRamanujan.lean` | 3 | Exact reciprocal phase sum and conditional proof-composition helpers |
| `UnramifiedCompleteSum.lean` | 1 | The full Ramanujan formula with the pure value proved internally |
| `QuadricCounting.lean` | 2 | The affine character average and the actual projective-ray count |
| `QuadricPointCount.lean` | 5 | Exact affine/projective counts, integer forms, and the integral source endpoint |
| `PrimePowerGaussTheorem.lean` | 1 | A single theorem containing every source clause |

These sixteen modules contain 54 new public theorem exports. Definitions
and private helper lemmas are compiled, but are not counted as additional
public exports or numbered manuscript results. The existing scalar Gauss,
prime-character, coefficient-reduction, complete-sum, and projective-ray
interfaces are reused in their already checked scopes.

## Objects and coefficient reduction

`Fin 4` supplies the four coordinates. The source's integer matrix and
frequency are represented by `Matrix (Fin 4) (Fin 4) ℤ` and `Fin 4 → ℤ`.
The existing `integralQuadraticValue A x` is literally
`dotProduct x (A.mulVec x)`, and its proved polynomial bridge identifies
this with evaluation of `matrixQuadraticPolynomial A`.

[QuadraticGaussSums.lean](../../QuaternaryQuadraticForms/QuadraticGaussSums.lean)
defines

```lean
quadraticGaussSum n A a u :=
  ∑ x : Fin 4 → ZMod n,
    ZMod.stdAddChar (a * dotProduct x (A.mulVec x) + dotProduct u x)
```

for a positive natural modulus, represented by `[NeZero n]`.
`integralQuadraticGaussSum` reduces the actual integer `A,a,u` into this
same sum. It does not introduce an abstract Gauss-sum function or change
the number of variables. The additive character is the existing
`ZMod.stdAddChar`, whose integer-value formula is the source's positive
phase `exp(2πiz/n)`.

[IntegralGaussSums.lean](../../QuaternaryQuadraticForms/IntegralGaussSums.lean)
proves the literal representative formula

$$
\sum_{x\bmod n}
e_n\bigl(aF(\widetilde x)+u\cdot\widetilde x\bigr)
$$

for `integralQuadraticGaussSum n A a u`. Its coordinate lifts are the
already justified `residueLift`; coefficient reduction commutes with the
quadratic value and with the linear pairing. The module also proves
that `unweightedCompleteSum n A u` is exactly the sum of these Gauss
sums over `(ZMod n)ˣ`. Thus the formula for `S_{p^k}` concerns the
complete sum defined and checked with Lemma 3.1.

`quadraticGaussSum_zero` gives `n^4` at zero quadratic and linear
coefficients. The modulus-one Gauss sum is one for every matrix,
scalar, and frequency. At `n=1`, both the residue ring and its vector
space have a single element, and the standard character has value one.
This is the exact base value needed for the recurrence.

## Good primes, the source character, and modular inverses

The existing definition

```lean
quadraticBadPrimeModulus A := 2 * A.det.natAbs
```

is exactly the source's positive modulus `N_F=2|det A|`.
`reduceQuadraticMatrix n A` is the entrywise integer coefficient map.
The previously proved good-prime lemmas derive `p≠2`, nonsingularity
of the reduced matrix, and symmetry of its reduction from the displayed
source data. Reduction also commutes with the actual adjugate.

[PrimePowerUnits.lean](../../QuaternaryQuadraticForms/PrimePowerUnits.lean)
proves that an integer not divisible by the prime is a unit modulo
every `p^k`, using prime coprimality and its preservation under powers.
The source condition `p ∤ N_F` gives `p ∤ det A` and makes both two and
the determinant units at every prime power. Combined with `p ∤ a`, it
makes `4a det A` a unit. No field structure is assumed on `ZMod (p^k)`.

The existing `complexQuadraticChar p` is the complex cast of the actual
integer-valued prime-field quadratic character. Its integral-value
identity is

```lean
complexQuadraticChar p (a : ZMod p) = (legendreSym p a : ℂ).
```

The new integral endpoints therefore use `legendreSym p A.det` for
`χ(p)`. This agrees with the source's explicit good-prime identification
at lines 165–167. The local lemma needs only these prime values and their
powers. It does not require or claim a separate construction of the
global primitive Dirichlet character, its conductor, or an `L`-function.

## The prime base case for an arbitrary matrix

[GeneralPrimeGauss.lean](../../QuaternaryQuadraticForms/GeneralPrimeGauss.lean)
proves the exact prime-field formula for every symmetric matrix with
nonzero determinant. An orthogonal basis is produced by mathlib's
proved symmetric-bilinear-form theorem when two is invertible. Its
indexing is transported to `Fin 4` using the proved dimension of the
actual four-coordinate space.

If `P` is the actual change-of-basis matrix and `d_i` are the diagonal
coefficients, the proof establishes both

$$
F(Px)=\sum_{i=1}^{4}d_i x_i^2,
\qquad
\prod_{i=1}^{4}d_i=(\det P)^2\det A.
$$

The matrix `P` is invertible because it is the matrix of a basis
change. Nonsingularity of `A` consequently proves that every `d_i` is
nonzero. These conclusions are proved from the actual basis and matrix;
neither a diagonalization nor a determinant-square relation is left as
a hypothesis of the public endpoint.

The finite sum is reindexed by that basis equivalence and separated
into four one-dimensional sums. The previously checked scalar formula
gives `χ_p(a d_i) τ_p` for each factor. The product contains `χ_p(a)^4=1`,
the nonzero square `det(P)^2`, and `τ_p^4=p^2`. Hence

$$
V_1(a)=\chi_p(\det A)p^2\qquad(a\ne0\bmod p).
$$

`quadraticGaussSum_prime_zero_frequency` is the resulting public
general-matrix theorem. `quadraticGaussSum_prime_all_scalars` also
retains the zero scalar, where the sum is `p^4`; that term is required
by the affine counting argument.

The scalar Gauss facts were already proved using official mathlib
results. Their use here adds no literature axiom for the cited
Montgomery–Vaughan Gauss-sum identities and makes no choice of a complex
square root of `p`.

## Actual digits and the two-step recurrence

[PrimePowerResidues.lean](../../QuaternaryQuadraticForms/PrimePowerResidues.lean)
constructs the actual bijection

$$
(r,s)\longmapsto \widetilde r+m\widetilde s\pmod{mn}
$$

from `ZMod m × ZMod n` to `ZMod (m*n)`. It uses the proved finite digit
bijection and the equivalences with `Fin`, and proves that the displayed
integer is the canonical representative. No coprimality of `m,n` is
needed. Applying the bijection coordinatewise gives exact finite-sum
identities on integer lifts.

Applying it twice gives

$$
x=r+p(w+mz),\qquad
r,z\in(\mathbb Z/p\mathbb Z)^4,\quad
w\in(\mathbb Z/m\mathbb Z)^4,
$$

as a bijection onto the vectors modulo `p*(m*p)`. Here `m` is any
positive integer, including one and integers divisible by `p`.

[PrimePowerGaussRecurrence.lean](../../QuaternaryQuadraticForms/PrimePowerGaussRecurrence.lean)
checks, for the actual symmetric integral matrix, the congruence

$$
aF(r+p(w+mz))
\equiv aF(r+pw)+pm\,(2a\,r^{\mathsf T}Az)
\pmod{p^2m}.
$$

The discarded difference is the integer multiple

$$
p^2m\,a\bigl(2w^{\mathsf T}Az+mF(z)\bigr).
$$

This calculation is proved before passing to the standard character.
It yields exactly

$$
e_{p^2m}\bigl(aF(r+p(w+mz))\bigr)
=e_{p^2m}\bigl(aF(r+pw)\bigr)
 e_p\bigl(2a\,r^{\mathsf T}Az\bigr).
$$

`stdAddChar_vector_orthogonality` proves the four-coordinate character
sum by separating it into the four actual one-coordinate sums.
`matrix_bilinear_character_sum` then uses nonsingularity modulo `p`
and nonvanishing of `2a` to prove

$$
\sum_{z\in\mathbb F_p^4} e_p(2a\,r^{\mathsf T}Az)
=\begin{cases}p^4&r=0,\\0&r\ne0.\end{cases}
$$

Thus the low digit is forced to zero. At that digit, quadratic
homogeneity and the exact standard-character cancellation give

$$
e_{p^2m}(aF(pw))=e_m(aF(w)).
$$

Summing the remaining middle digit proves the stronger actual identity

$$
\sum_{x\bmod p^2m}e_{p^2m}(aF(x))
=p^4\sum_{w\bmod m}e_m(aF(w))
$$

for arbitrary positive `m` under the good-prime and scalar conditions
at `p`. Taking `m=p^k` gives
`integralQuadraticGaussSum_primePower_recurrence`:

$$
V_{k+2}(a)=p^4V_k(a),\qquad k\ge0.
$$

All digit ranges, the selecting zero vector, and the factors `p^4` and
`p^2` in this argument are literal. The proof does not use coprime CRT
to decompose powers of one prime. The specialization `k=0` keeps the
middle modulus `p^0=1`, so the recurrence reaches the proved `V_0=1`.

## Square completion and the exact adjugate phase

[MatrixSquareCompletion.lean](../../QuaternaryQuadraticForms/MatrixSquareCompletion.lean)
works over an arbitrary commutative ring. For an actual inverse `b`
satisfying `(4a det A)b=1`, it proves

$$
\begin{aligned}
&aF\bigl(x-2b\,\operatorname{adj}(A)u\bigr)
 +u\cdot\bigl(x-2b\,\operatorname{adj}(A)u\bigr)\\
&\hspace{2em}=aF(x)-b\,u^{\mathsf T}\operatorname{adj}(A)u.
\end{aligned}
$$

The argument uses symmetry of `A`, the actual identity
`A adj(A)=(det A)I`, and bilinearity. Since `(2a det A)(2b)=1`, its
translation is the source's inverse-`2aα` translation. The concluding
phase has exactly the required inverse of `4aα` and the required
minus sign.

[QuadraticGaussShift.lean](../../QuaternaryQuadraticForms/QuadraticGaussShift.lean)
implements the translation as an equivalence of all residue vectors.
Its final inverse is the literal `ZMod` inverse, with its unit property
proved before use. The character of the constant phase factors out of
the actual finite sum.

[IntegralGaussShift.lean](../../QuaternaryQuadraticForms/IntegralGaussShift.lean)
proves that reduction of

```lean
dotProduct u (A.adjugate.mulVec u)
```

is precisely the quadratic value of the reduced adjugate at the reduced
frequency. This is the source `F*(u)`, with the original integer matrix
and arbitrary integral frequency. Its prime-power shift theorem obtains
all unit hypotheses from `p ∤ N_F` and `p ∤ a`.

## Closed Gauss values and the Ramanujan factor

[PrimePowerGauss.lean](../../QuaternaryQuadraticForms/PrimePowerGauss.lean)
uses two-step induction with the proved bases `k=0,1` and the actual
recurrence. At a good prime the actual character value has square one,
so the recurrence yields

$$
V_k(a)=\chi(p)^k p^{2k}.
$$

The shifted endpoint combines this closed pure value with the proved
integral square completion. It therefore has precisely

$$
\sum_{x\bmod p^k}e_{p^k}(aF(x)+u\cdot x)
=\chi(p)^k p^{2k}
e_{p^k}\bigl(-\overline{4a\alpha}\,F^*(u)\bigr).
$$

The coefficient is independent of the unit scalar `a`, as required in
the summation for part (ii). The integral formula is valid for arbitrary
negative or positive `a,u` subject only to the stated scalar
nondivisibility and good-prime conditions. No condition `u≠0` or
`F*(u)≠0` is introduced. The pure and shifted formulas are also proved
at the internal base exponent zero; the source instances have `k≥1`.

For the actual unit group modulo `p^k`, the theorem
`quadraticGaussSum_prime_power_units_pure` assumes `1≤k` and proves
the same pure value for every unit. A unit modulo `p^k` maps to a unit
modulo `p`, so its canonical integer lift is not divisible by `p`.
The positive-exponent hypothesis is present at exactly this step:
the unique unit modulo one has canonical lift zero and does not justify
that nondivisibility argument.

[RamanujanSums.lean](../../QuaternaryQuadraticForms/RamanujanSums.lean)
defines `residueRamanujanSum` as the actual unit sum
`∑ a : (ZMod n)ˣ, stdAddChar (a*m)` and `integralRamanujanSum` by
reduction of the integer frequency. The lift formula matches the first
expression in `eq:ramanujan`; the prime specialization is the previously
checked `primeRamanujan`. The unique unit at modulus one contributes
one, including at zero frequency.

Multiplication by a unit, inversion, and multiplication by minus one
are implemented as actual permutations of the unit group. In particular,
for every unit `r`, the negative reciprocal phase satisfies

$$
\sum_{a\bmod n}^{*}e_n\bigl(-(ra)^{-1}t\bigr)=R_n(t).
$$

[GaussRamanujan.lean](../../QuaternaryQuadraticForms/GaussRamanujan.lean)
applies this identity with `r=4 det A` and
`t=uᵀadj(A)u`. Its assembly helpers display an explicit constant-pure-
Gauss hypothesis `hK`; this is a proof-composition interface, not a
registered premise or a source assertion accepted without proof. The
final prime-power formula supplies this hypothesis by the proved
unit pure evaluation above.

[UnramifiedCompleteSum.lean](../../QuaternaryQuadraticForms/UnramifiedCompleteSum.lean)
performs that substitution for every actual unit, obtaining

$$
S_{p^k}(u)=\chi(p)^k p^{2k}R_{p^k}(F^*(u)),\qquad k\ge1.
$$

The unit conditions on two and the determinant are derived from the
source good-prime condition. The pure coefficient is obtained from
`quadraticGaussSum_prime_power_units_pure`. No scalar value, constancy
condition, Gauss formula, or reciprocal-permutation assertion remains
as a hypothesis in `unweightedCompleteSum_prime_power`.

## The actual affine and projective point counts

[QuadricCounting.lean](../../QuaternaryQuadraticForms/QuadricCounting.lean)
defines `affineQuadricPoints A` as the finite set of the actual vectors
`x : Fin 4 → ZMod p` with `quadraticValue A x=0`, including the origin.
Additive orthogonality gives the exact equality

$$
p\,\#\{x\in\mathbb F_p^4:F(x)=0\}
=\sum_{a\in\mathbb F_p}V_1(a).
$$

The zero scalar contributes `p^4`. The other `p-1` scalars have the
proved common value `χ(p)p^2`. Therefore the affine count is

$$
p^3+\chi(p)(p^2-p).
$$

The projective object is the existing `projectiveQuadric A`: the finite
subset of the actual projectivization of the four-coordinate vector
space whose representative has quadratic value zero. Its membership
condition is independent of the representative. The already checked
projective-ray bijection partitions all nonzero vectors into one
projective point and one nonzero scalar. Applied to the cone indicator,
it proves

$$
\#\{x:F(x)=0\}=1+(p-1)\#\mathcal Q(\mathbb F_p).
$$

The origin contributes exactly one; each projective point contributes
exactly `p-1` nonzero vectors. Cancelling the nonzero integer `p-1`
then gives

$$
\#\mathcal Q(\mathbb F_p)=p^2+(1+\chi(p))p+1.
$$

[QuadricPointCount.lean](../../QuaternaryQuadraticForms/QuadricPointCount.lean)
exports the affine and projective equalities as integer equalities as
well as their complex casts. The final integral projective statement is
about `(projectiveQuadric (reduceQuadraticMatrix p A)).card` itself,
with coefficient `legendreSym p A.det`. No geometric point-count formula
or unspecified cardinality is assumed.

## Exact terminal statement and hypothesis audit

The complete source endpoint is
`QuaternaryQuadraticForms.prime_power_gauss` in
[PrimePowerGaussTheorem.lean](../../QuaternaryQuadraticForms/PrimePowerGaussTheorem.lean).
Its data and hypotheses are exactly

```lean
(p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
(A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
(hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ℤ)
```

Its first conjunct quantifies over every integer `a` not divisible by
`p` and states the shifted formula. Its second conjunct states the
formula for `unweightedCompleteSum (p^k) A u` with the actual
`integralRamanujanSum`. Its third conjunct is the actual integer
cardinality of `projectiveQuadric (reduceQuadraticMatrix p A)`.
The data `A,p,k,u` are unchanged between the conclusions, and the
scalar `a` is quantified only inside part (i).

| Source conclusion | Complete source export |
| --- | --- |
| Part (i), shifted Gauss evaluation | `integralQuadraticGaussSum_prime_power` |
| Part (ii), unweighted complete sum | `unweightedCompleteSum_prime_power` |
| Part (iii), projective quadric count | `integral_projectiveQuadric_card` |
| All three clauses together | `prime_power_gauss` |

| Source assumption or convention | Treatment in the final statements |
| --- | --- |
| Prime `p` | Exactly `[Fact p.Prime]`; no extra congruence class of `p` is imposed. |
| `k≥1` | Exactly `1≤k` in the bundled theorem and complete-sum theorem. The internal pure/shifted formulas also include `k=0`. |
| Integral symmetric `4×4` matrix | Exactly the source matrix type and transpose equality. The prime base case diagonalizes this actual matrix internally. |
| `α=det A` | `A.det` throughout, with the determinant map proved under coefficient reduction. |
| `N_F=2|α|` and `p∤N_F` | Exactly `quadraticBadPrimeModulus A=2*A.det.natAbs` and its nondivisibility condition. No condition involving the additional character-weight bad primes is imposed. |
| Integer `a` with `p∤a` | Universally quantified in part (i), with literal integer divisibility; negative integers are included. |
| Arbitrary integral `u` | The original four-coordinate frequency is retained, including `u=0` and `F*(u)=0`. |
| `χ(p)` | The actual Legendre symbol `legendreSym p A.det`, matching the source's explicit good-prime definition. |
| The inverse modulo `p^k` | The actual `ZMod` inverse of the reduction of `4*a*A.det`; its unit condition is proved from the source hypotheses. |
| `F*(u)` | Literally `dotProduct u (A.adjugate.mulVec u)`, with its coefficient-reduction identity proved. |
| Reduced-residue sum in `S_{p^k}` | The actual group `(ZMod (p^k))ˣ`, connected to the previously checked definition of `unweightedCompleteSum`. |
| `R_n(t)` | Its defining unit sum with the positive standard additive character; no Möbius expansion is needed or assumed for this lemma. |
| Points of `P³(F_p)` on the quadric | The existing actual four-dimensional projectivization and its quadratic-zero finite subset. The endpoint is an equality of integer cardinalities. |
| Global nonsingularity of the integer matrix | Redundant at each allowed prime: if `det A=0`, then `N_F=0` and every prime divides it. Reduced nonsingularity and prime-power invertibility are derived internally. |
| Global nonsquareness of `det A` | Unused by these local identities, which hold for either determinant square class. All source instances are included. |

The omission of unused or redundant global hypotheses strengthens the
local formulas without excluding any source instance. There is no
assumed diagonalization, pure Gauss evaluation, digit recurrence,
constant-over-units hypothesis, Ramanujan reindexing, or point-count
formula in the terminal theorem. These are all proved deductions on
the actual arithmetic objects.

## Inspected dependencies and review conclusion

The actual `#check` and `#print axioms` inspection completed successfully
for all 54 new public exports. Every one has exactly

```text
Classical.choice
Quot.sound
propext
```

In particular, the three individual source endpoints and the bundled
`prime_power_gauss` have no literature-premise dependency. The observed
terminal types agree with the formulas and hypothesis audit above.

The orthogonal-basis theorem, scalar Gauss identities, residue digits,
finite-sum reindexings, standard-character orthogonality, adjugate
identities, and projective-ray correspondence are proved in the pinned
mathlib or the repository. No external input, internal manuscript lemma,
or omitted deduction was introduced as an axiom. The four previously
registered literature premises are unchanged, and none occurs in the
actual dependencies of these new exports. Imports of modules containing
other verified results do not alter this observed dependency statement.

All sixteen modules passed strict compilation with the pinned
`leanprover/lean4:v4.24.0`, pinned dependency revisions,
`autoImplicit=false`, and `warningAsError=true`. The independent review
of the definitions, proofs, and printed terminal types finds all three
source clauses present, all source instances covered, and no
mathematical gap. It specifically checks the arbitrary symmetric
matrix at the prime base case, the actual digit bijections and `p^4`
recurrence factor, the internal exponent-zero base, the literal
negative inverse adjugate phase, the actual unit sum and reciprocal
permutation, and the genuine projective cardinality.

This completed source-correspondence review supports Certified
classification of Lemma 3.2 once the full repository verification gates
pass. At the time this review was frozen, the module builds and actual
export inspection were complete and the aggregate gate was still
pending. The live ledger, verification report, and execution checkpoint
record the eventual checked scope, hashes, dependency checks, and exact
commit/run evidence. The added scope is 54 public exports in sixteen
modules plus this review. The bad-prime bound, shared-prime mixed sum,
global analytic arguments, and other pending manuscript obligations
remain separate.
