# Source correspondence: Lemma 3.7

## Source and complete scope

This review concerns the full assertion of `lem:conemod`, equation
`eq:conemod`. For a fixed symmetric nonsingular integral matrix `A`
whose determinant is not a square, and every positive real `ε`, the
source asserts one constant depending only on the form and `ε` such
that

$$
\left|\sum_{\substack{1\le c\le X\\(c,q)=d}}S_c(u)\right|
\le C_{F,\varepsilon}X^3(Xq)^\varepsilon,
\qquad q=de,
$$

when `q` is squarefree, `(q,N_F)=1`, `F*(u)=0`, and `X≥1`.
The norm is taken after the complex sum over the moduli. The claimed
cancellation would not follow by summing absolute values of all
individual good-modulus terms.

The formal source endpoint is
`QuaternaryQuadraticForms.source_cone_modulus_bound`. It concerns the
actual unweighted complete sums and the literal gcd restriction. Its
positive constant is chosen before all varying moduli, their factors,
frequencies, and real cutoffs. Its core theorem also proves the estimate
without the source's squarefreeness hypothesis. The source wrapper
retains that hypothesis explicitly.

The frozen manuscript is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | Symmetric nonsingular integral `A`, `α=det A`, `N_F=2|α|`, the standing nonsquare assumption, and the primitive source character's good-prime values |
| Notation, lines 561–578 | Positive additive characters, reduced residues, divisor and prime counts, and positive `ε` |
| `eq:dualform`, lines 816–818 | The actual integer dual value `F*(u)=uᵀadj(A)u` |
| `eq:Sdef`, lines 1029–1039 | The actual unweighted complete sum and its relation to the mixed sums |
| `eq:ramanujan`, lines 1043–1045 | The actual Ramanujan sum over units |
| `lem:crt`, lines 1048–1090 | Complete-sum multiplicativity, including the unweighted specialization |
| `lem:gauss`, `eq:unram`, lines 1092–1105 | The actual unramified prime-power evaluation |
| `lem:badprime`, lines 1156–1177 | The uniform bound `|S_c(u)|≤4√|α|c³` |
| `eq:q1q2`, lines 1234–1238 | The shared gcd and complementary factor |
| `sec:moduli`, lines 1282–1290 | Fixed factorization `q=de`, the actual gcd restriction, and counting bad-supported factors |
| Lines 1344–1346 | Cancellation from the nonsquareness of `α` |
| `lem:conemod`, `eq:conemod`, lines 1348–1354 | The complete assertion of Lemma 3.7 |
| `eq:chicube`, lines 1357–1362 | Periodic cancellation and cubic weighted partial sums |
| `eq:chicoprime`, lines 1363–1370 | Möbius detection of coprimality and cubic cancellation |
| Lines 1372–1387 | The good-modulus totient evaluation and the exact relative totient rearrangement |
| `eq:conegood`, lines 1388–1392 | The resulting good-modulus harmonic bound |
| Lines 1394–1404 | Exact bad/good factorization, bad-supported counting, and positive-power absorption |

The formal argument follows the source's cancellation, Möbius,
totient, and bad/good factorization route. It constructs an auxiliary
character of period `4|α|` from the actual Jacobi coefficient rather
than requiring a supplied primitive character and its conductor. The
auxiliary character vanishes outside the good indices, which permits
a divisor-count loss `τ(e)` in place of the source's
`2^ω(eN_F)`. These are valid changes inside a constant depending on
the fixed form and the prescribed exponent. No assertion about the
primitive conductor or the quadratic number field is silently assumed.

## Fourteen modules and forty theorem exports

All declarations below belong to the `QuaternaryQuadraticForms`
namespace. These are forty supporting theorem exports for one
additional numbered manuscript result.

| Module | Exports | Declarations and reviewed role |
| --- | ---: | --- |
| [PeriodicSumBound.lean](../../QuaternaryQuadraticForms/PeriodicSumBound.lean) | 1 | `periodic_sum_range_norm_le`: a uniform bound for every initial partial sum of a bounded zero-mean periodic sequence |
| [CharacterCubicBound.lean](../../QuaternaryQuadraticForms/CharacterCubicBound.lean) | 2 | `periodic_cubic_sum_norm_le`; `periodic_cubic_sum_floor_norm_le`: exact finite summation by parts and natural/real cubic cutoffs |
| [QuadraticCharacterPeriod.lean](../../QuaternaryQuadraticForms/QuadraticCharacterPeriod.lean) | 10 | `goodQuadraticChar_one`; `goodQuadraticChar_zero`; `goodQuadraticChar_of_coprime`; `goodQuadraticChar_of_not_coprime`; `goodQuadraticChar_mul`; `goodQuadraticChar_norm_le_one`; `goodQuadraticChar_coprime_four_iff`; `goodQuadraticChar_mod`; `goodQuadraticChar_periodic`; `goodQuadraticDirichletChar_natCast`: the actual good Jacobi coefficient, complete multiplicativity, its period, and an actual Dirichlet-character realization |
| [QuadraticJacobiWitness.lean](../../QuaternaryQuadraticForms/QuadraticJacobiWitness.lean) | 1 | `exists_jacobiSym_neg_one_mod_eight_of_squarefree`: a genuine negative Jacobi numerator, obtained from a quadratic nonresidue and CRT |
| [QuadraticCharacterNonprincipal.lean](../../QuaternaryQuadraticForms/QuadraticCharacterNonprincipal.lean) | 3 | `exists_good_jacobiSym_neg_one`; `goodQuadraticDirichletChar_ne_one`; `goodQuadraticChar_sum_period_eq_zero`: nonsquareness of the original integer yields nonprincipality and actual zero period sum |
| [CoprimeCubicBound.lean](../../QuaternaryQuadraticForms/CoprimeCubicBound.lean) | 5 | `sum_Icc_dvd_eq_sum_div`; `coprime_indicator_eq_moebius_sum`; `sum_coprime_eq_sum_moebius_multiples`; `moebius_complex_norm_le_one`; `coprime_cubic_sum_norm_le`: exact Möbius detection, positive-multiple reindexing, and the divisor-count cancellation bound |
| [TotientDivisorExpansion.lean](../../QuaternaryQuadraticForms/TotientDivisorExpansion.lean) | 2 | `totient_eq_sum_moebius`; `totient_mul_eq_sum_moebius`: ordinary and relative expansions of the actual Euler totient |
| [DivisorSumReindex.lean](../../QuaternaryQuadraticForms/DivisorSumReindex.lean) | 3 | `sum_Icc_divisors_eq_sum_mul`; `sum_gcdModuliUpTo_eq_sum_coprime`; `sum_coprime_divisors_eq_sum_mul`: exact finite divisor and gcd rearrangements with positive quotient cutoffs |
| [ConeTotientReindex.lean](../../QuaternaryQuadraticForms/ConeTotientReindex.lean) | 1 | `sum_gcd_totient_eq_moebius`: the literal gcd-restricted totient sum as the source's double sum |
| [TotientCancellationBound.lean](../../QuaternaryQuadraticForms/TotientCancellationBound.lean) | 2 | `sum_gcd_totient_norm_le_harmonic`; `sum_gcd_totient_floor_norm_le_log`: cubic cancellation yields one divisor count and one harmonic factor |
| [ModulusSumFactorization.lean](../../QuaternaryQuadraticForms/ModulusSumFactorization.lean) | 4 | `modulus_prime_split_unique`; `sum_gcdModuli_eq_sum_prime_split`; `unweightedCompleteSumValue_of_neZero`; `unweightedModulusSum_prime_split`: a genuine finite bad/good bijection and exact CRT of the complex modulus sum |
| [ConeModulusFormula.lean](../../QuaternaryQuadraticForms/ConeModulusFormula.lean) | 2 | `unweightedCompleteSum_on_dual_cone`; `good_modulus_sum_eq_quadratic_totient`: the actual complete sums equal the twisted totient summands on the dual cone |
| [ConeModulusBound.lean](../../QuaternaryQuadraticForms/ConeModulusBound.lean) | 2 | `good_modulus_sum_norm_le_harmonic`; `unweightedModulusSum_le_divisor_log`: actual good-modulus cancellation and the full bad/good divisor/logarithm bound |
| [ConeModulusTheorem.lean](../../QuaternaryQuadraticForms/ConeModulusTheorem.lean) | 2 | `unweightedModulusSum_le_rpow`; `source_cone_modulus_bound`: the uniform core estimate and complete source endpoint |

The new definitions `goodQuadraticChar`, `goodQuadraticCharHom`,
`goodQuadraticDirichletChar`, `unweightedCompleteSumValue`, and
`unweightedModulusSum` are concrete arithmetic functions, characters,
and finite sums. They are not additional numbered assertions or
external inputs.

## Actual objects and order of summation

The existing integral quadratic form, dual value, complete sums, and
Ramanujan sums are unchanged.

| Source object | Lean object and meaning |
| --- | --- |
| `F(x)` | `integralQuadraticValue A x = dotProduct x (A.mulVec x)` |
| `F*(u)` | `dotProduct u (A.adjugate.mulVec u)` as an integer |
| `α`, `|α|`, `N_F` | `A.det`, `A.det.natAbs`, and `quadraticBadPrimeModulus A = 2*A.det.natAbs` |
| `S_c(u)` | `unweightedCompleteSum c A u`, over the actual units modulo `c` and vectors modulo `c` |
| `R_c(0)` | `integralRamanujanSum c 0`, which equals the actual `Nat.totient c` |
| Good quadratic coefficient | `globalQuadraticChar A.det c`, the actual Jacobi symbol cast to `ℂ` |
| Auxiliary periodic coefficient `ψ(c)` | `goodQuadraticChar A.det c`, the same value when `(c,N_F)=1` and zero otherwise |
| `τ(e)` | `e.divisors.card`, the number of positive divisors |
| `ω(N_F)` | `(quadraticBadPrimeModulus A).primeFactors.card` |
| Complex sum in Lemma 3.7 | `unweightedModulusSum q d A u X` |

The summation set is the existing exact finite set

```lean
gcdModuliUpTo q d T :=
  (Finset.Icc 1 T).filter (fun c => Nat.gcd c q = d)
```

The new total summand agrees with `unweightedCompleteSum` whenever
`c≠0` and is defined to be zero at zero solely to make a function on
all natural numbers. Zero never occurs in the summation set. At
`T=⌊X⌋₊`, the positive natural indices are exactly the positive
integer moduli `c≤X` in the source. The final left side is the complex
norm of this finite sum, with no normalization by `c³` and no local
weight `ξ` or Fourier factor `C_e(u)`.

In the bad/good decomposition the complete sum over each good factor
is evaluated and bounded before taking a triangle inequality over
the bad factors. This retains precisely the cancellation needed in
the source.

## The nonsquare assumption proves actual nonprincipality

Set `a=|α|` and `P=4a`. The proof defines

$$
\psi(n)=\begin{cases}
\left(\frac{\alpha}{n}\right),&(n,2a)=1,\\
0,&(n,2a)\ne1,
\end{cases}
$$

using the actual library Jacobi symbol, cast to `ℂ`. The value at one
is one and the value at zero is zero. Jacobi multiplicativity and
the multiplicative coprimality predicate give complete
multiplicativity on all natural numbers. The Jacobi trichotomy gives
`|ψ(n)|≤1` without a separate boundedness premise.

For good indices the denominator is odd, so the proved Jacobi
periodicity theorem applies modulo `4a`. Coprimality with `2a` is
equivalent to coprimality with `4a` and is preserved by reduction
modulo `4a`. The zero extension consequently has period `P` on all
natural numbers, not just the good ones. For `α≠0`, applying this
function to the natural representative of a residue class constructs
an actual `DirichletCharacter ℂ P`. Multiplication of representatives
is justified using reduction modulo `P`; nonunits map to zero. Its
values on natural casts equal `ψ` exactly.

Nonprincipality is proved from `¬IsSquare α`. There is no extra
assumption that this constructed character is nonprincipal or that
its period sum cancels. The arithmetic proof proceeds as follows.

1. Write `|α|=b²s` with positive `b,s` and squarefree `s`, using the
   proved natural squarefree decomposition.
2. If `s` has an odd prime divisor `p`, squarefreeness gives
   `s=p t` with `(p,t)=1`. A genuine quadratic nonresidue modulo `p`
   is combined by CRT with the residue one modulo `8t`. This gives
   `n≡1 mod8` and `Jacobi(n|s)=-1`. Jacobi nonvanishing supplies
   `(n,s)=1`.
3. Quadratic reciprocity, including the power of two in `s`, gives
   `Jacobi(s|n)=Jacobi(n|s)` when `n≡1 mod8`. The supplementary
   law for `-1` gives the same negative value for `-s`. If a
   squarefree `s` is neither one nor two, the existence of an odd
   prime divisor is itself proved.
4. The remaining squarefree part `s=2` uses the explicit modulus
   five, where both `Jacobi(2|5)` and `Jacobi(-2|5)` are `-1`.
   If `s=1`, the positive sign would make `α` an integer square and
   contradict the hypothesis. For the negative sign, modulus three
   gives `Jacobi(-1|3)=-1`.
5. The witness at the squarefree part is lifted to a unit modulo
   `4|α|` through the proved surjectivity of the unit reduction map.
   Thus it remains coprime to every prime in the original square
   factor as well. Reduction preserves the squarefree character
   value; the numerator square factor has Jacobi value one at this
   lifted good index. The result is an actual `N` with
   `(N,2|α|)=1` and `Jacobi(α|N)=-1`.

Since `α≠0`, the good-modulus condition here excludes `N=0`.

The constructed Dirichlet character therefore takes the value `-1`
on a unit, while the principal character takes the value one there.
This proves it is not principal. The proved finite character-sum
identity then gives zero sum over all residues. The actual
`ZMod P`/`Fin P` equivalence identifies this with

$$
\sum_{0\le n<P}\psi(n)=0.
$$

This construction handles negative determinants, repeated prime
factors, and the prime two. It does not conflate nonsquareness of
`α` with nonsquareness of `|α|`: a negative square determinant is
handled by the explicit negative-sign branch. The period depends
only on `α`, so replacing the source conductor by this period is
legitimate inside the form-dependent constant.

## Periodic cancellation and exact Möbius detection

For a complex sequence with positive period `P`, zero sum over one
period, and termwise norm at most one, complete periods can be
removed from every initial partial sum. A remaining interval shorter
than `P` has norm at most `P`. The proof is a finite induction and
includes the empty prefix.

Finite summation by parts with the weights `n³` then gives

$$
\left|\sum_{1\le n\le T}f(n)n^3\right|\le2PT^3.
$$

The boundary term is at most `PT³`; the nonnegative successive
differences telescope to another `PT³`. The proof does not assume
`f(0)=0`, because the cubic weight at zero vanishes. A separate real
cutoff theorem applies for every `Z≥0`, including cutoffs below one.
Applying these results to `ψ` gives a fixed cubic constant `B=2P`.

For an arbitrary positive integer `M`, the actual Möbius divisor sum
detects coprimality:

$$
\mathbf1_{(n,M)=1}=\sum_{h\mid M,\ h\mid n}\mu(h).
$$

The proof derives this identity from the actual arithmetic-function
Möbius/zeta identity and the divisors of `gcd(n,M)`. It then exactly
reindexes positive multiples `n=h k`, with the natural quotient
cutoff `T/h`. Complete multiplicativity and `|f(h)|≤1`, together
with the proved bound `|μ(h)|≤1`, give

$$
\left|\sum_{\substack{1\le n\le T\\(n,M)=1}}f(n)n^3\right|
\le B\tau(M)T^3.
$$

There are no approximated cutoffs in this step:
`h·⌊T/h⌋≤T` bounds the cubic scale, including empty quotient
intervals. The loss is a bound by all positive divisors of `M`.
The source counts only the squarefree divisors with nonzero Möbius
value; the larger divisor count is sufficient for the final
arbitrarily small positive power.

## The actual relative totient identity and good-modulus sum

At every positive good modulus, the previously checked actual
unramified evaluation and CRT give

$$
S_c(u)=\operatorname{Jacobi}(\alpha\mid c)c^2R_c(F^*(u)).
$$

On the integral dual cone, `F*(u)=0`, the actual unit sum `R_c(0)`
is `φ(c)`. Thus the sum over good moduli equals the sum of
`ψ(c)c²φ(c)` over all indices in the same gcd-restricted set;
the other terms vanish by the definition of `ψ`.

The relative totient identity is proved for every positive `d` and
every natural `n`:

$$
\varphi(dn)=\varphi(d)
\sum_{\substack{h\mid n\\(h,d)=1}}\mu(h)\frac nh.
$$

Here `n/h` is an exact integer quotient in each divisor term. The
proof first derives the ordinary totient expansion by actual Möbius
inversion, then splits `n` into the part supported on primes of `d`
and the coprime part. The actual totient prime-factor product gives
the supported-factor contribution. This establishes the source's
formula rather than taking it as an extra arithmetic assumption.
The identity also handles `n=0` separately; summation indices are
positive.

For `q=de`, the equality
`gcd(dn,de)=d·gcd(n,e)` proves that the exact condition `(c,q)=d`
is equivalent to `c=dn` with `(n,e)=1`. This does not require that
`d` and `e` be coprime. Finite divisor reindexing then gives, for a
completely multiplicative `f`,

$$
\begin{aligned}
\sum_{\substack{1\le c\le T\\(c,q)=d}}f(c)c^2\varphi(c)
={}&f(d)d^2\varphi(d)
\sum_{\substack{1\le h\le T/d\\(h,q)=1}}
\mu(h)f(h)h^2
\sum_{\substack{1\le k\le T/(dh)\\(k,e)=1}}f(k)k^3.
\end{aligned}
$$

All ranges are finite positive ranges with their exact natural
quotients. The reindexing retains both coprimality restrictions.
Using `φ(d)≤d`, the preceding coprime cubic bound with `M=e`, and
`dh·⌊T/(dh)⌋≤T`, each outer term has norm at most
`B τ(e)T³/h`. Enlarging the nonnegative harmonic range yields

$$
\left|\sum_{\substack{1\le c\le T\\(c,q)=d\\(c,N_F)=1}}S_c(u)\right|
\le2P\tau(e)T^3H_T.
$$

This is the precise good-modulus bound used in the assembly. The
source applies coprimality detection to `eN_F`; here bad indices
already have zero coefficient, so `M=e` suffices. In particular no
unproved cancellation of the original character restricted to an
arbitrary subset has been assumed.

## Exact bad/good summation and the explicit intermediate constant

Every positive modulus has a unique factorization `c=b g` in which
all prime factors of `b` divide `N_F` and `(g,N_F)=1`. The new proof
establishes uniqueness from the cross-coprimalities and mutual
divisibility. It then uses a finite bijection between the original
moduli and their pairs `(b,g)`. Since `(q,N_F)=1`, the gcd condition
is exactly `(g,q)=d` and the upper bound is the natural quotient
`g≤⌊X⌋₊/b`.

Actual complete-sum CRT gives the identity

$$
\sum_{\substack{1\le c\le X\\(c,q)=d}}S_c(u)
=\sum_{\substack{b\le X\\p\mid b\Rightarrow p\mid N_F}}
S_b(u)
\sum_{\substack{g\le\lfloor X\rfloor/b\\(g,q)=d\\(g,N_F)=1}}S_g(u).
$$

The inner complex sum remains intact. Its harmonic bound combines
with the previously checked uniform bad-prime estimate
`|S_b(u)|≤4√a b³`. The exact inequality
`b·⌊⌊X⌋₊/b⌋≤⌊X⌋₊≤X` cancels the cubic growth of `b`.
Monotonicity of the harmonic sum and its bound at the real cutoff
give `H_(⌊X⌋₊/b)≤1+log X`.

Writing `r=ω(N_F)` and `P=4a`, the established prime-support count is
bounded by
`(1+1/log2)^r(1+log X)^r`. Thus the actual complete modulus sum
satisfies

$$
\left|\sum_{\substack{1\le c\le X\\(c,q)=d}}S_c(u)\right|
\le K_A\tau(e)X^3(1+\log X)^{r+1},
$$

where the explicit positive form-dependent constant is

$$
K_A=4\sqrt a\,(2P)\left(1+\frac1{\log2}\right)^r.
$$

The finite count, its logarithmic bound, and the uniform bad-prime
estimate are previously checked repository results. The use of
their exact objects and hypotheses is visible in the new assembly.

## Uniform quantifier order and positive-power absorption

For every `ε>0`, the existing proved divisor bound supplies `D_ε>0`
uniformly over every positive integer. Since `e∣q`, actual divisor
inclusion gives

$$
\tau(e)\le\tau(q)\le D_\varepsilon q^\varepsilon.
$$

The existing logarithmic-power bound supplies `L_(r+1,ε)>0`, uniformly
for all `X≥1`, with

$$
(1+\log X)^{r+1}\le L_{r+1,\varepsilon}X^\varepsilon.
$$

The constant is chosen as
`C=K_A D_ε L_(r+1,ε)`. Positivity follows from `a>0`, `P>0`, and
`log2>0`. It has no dependence on `q,d,e,u,X`. The two different
variables contribute `q^ε` and `X^ε`, which combine by the proved
real-power multiplication rule into `(Xq)^ε`.

The final source theorem has the order

```text
fixed A, A.transpose=A, A.det≠0, ¬IsSquare A.det, ε>0
  ∃ C>0
    ∀ positive q,d,e,
      Squarefree q → q=d*e → q.Coprime (2*|det A|) →
      ∀ integral u, uᵀadj(A)u=0 →
      ∀ real X≥1,
        ‖unweightedModulusSum q d A u X‖ ≤ C*X³*(X*q)^ε.
```

The constant therefore has exactly the uniformity asserted by the
source's `≪_(F,ε)`. Natural `NeZero` instances express positivity of
the source's integer moduli and factors. The core theorem omits
`Squarefree q`; the source wrapper includes it, with no change to
the constant or summand.

## Assumptions and boundary cases

| Assumption or boundary | Treatment |
| --- | --- |
| Symmetric nonsingular integral `4×4` matrix | Exactly `A.transpose=A` and `A.det≠0`; these support the actual local evaluations and uniform complete-sum bound. |
| Nonsquare determinant | Explicit `¬IsSquare A.det`; actual nonprincipality and period cancellation are proved from it. |
| Negative determinant | The sign is retained through Jacobi supplementary laws; negative squares are included in the nonsquare branch. |
| Prime two or repeated determinant factors | The coefficient vanishes at even indices; reciprocity handles the power of two, and unit lifting handles primes in numerator square factors. |
| `(q,N_F)=1` | Exactly the source hypothesis. The stronger `(q,N)=1` is not inserted. |
| Squarefree `q=de` | Retained in the source wrapper. The finite gcd and relative-totient identities prove the stronger core without it. |
| `q=1` | The positive factorization forces `d=e=1`; divisor count one and all empty products have their actual values. |
| `d=1` or `e=1` | The gcd/coprimality reindexing and Möbius identity apply directly; `M=1` has the single positive divisor one. |
| `u=0` | Allowed: the source requires only the actual dual value to vanish. No frequency nonzero assumption is introduced. |
| `X=1` | The only possible modulus is one, present exactly when `d=1`; harmonic and logarithmic bounds include this endpoint. |
| `d>X` or a divided cutoff below one | The corresponding positive interval is empty. Natural quotient/floor identities preserve this exactly. |
| Modulus one | The actual complete sum and actual totient at one agree with the existing local definitions. |
| Real cutoff | `⌊X⌋₊` gives the exact positive-modulus range for every real `X≥1`; no integrality of `X` is assumed. |
| Positive real `ε` | Both absorption constants are selected for the same arbitrary positive exponent before varying arithmetic parameters. |
| Local functions, `N`, `E,K`, polynomial strata | Absent from this unweighted source assertion and unnecessary in the formal theorem. |
| A supplied primitive character or conductor | Unnecessary: the auxiliary actual good-modulus character, its nonprincipality, and its period sum are proved. No field-character identification is added as a premise. |

The theorem concerns the dual-cone case exactly. It does not replace
the separate off-cone estimate of Lemma 3.6 or claim the later
singular-series, weighted-average, or global analytic results.

## Dependency inspection and review conclusion

The independent mathematical and source-correspondence review found
no gap in the complete chain or mismatch with the assertion of
Lemma 3.7. The original arithmetic objects, zero dual condition,
literal gcd restriction, norm after the complex sum, full positive
modulus range, and constant quantifiers are all retained.
Nonprincipality, periodic cancellation, Möbius detection, the
relative totient identity, finite reindexing, and power absorption
do not survive as unproved premises in the source endpoint.

All fourteen new modules passed strict compilation with the pinned
Lean 4.24.0 toolchain. The final targeted build completed successfully
with 3,151 jobs. The combined default-format `#check` and
`#print axioms` inspection exited successfully, printing all forty
actual theorem types and forty dependency lists. The inspected
declaration set was independently compared with the complete public
theorem set in the fourteen frozen source files and agreed exactly.
All fourteen frozen source hashes were independently rechecked, and
the full actual types of both final endpoints were read.

The final unified inspection log contained 18,176 bytes, with SHA-256
`0648140a5459788ece973aed370292063c4661603f0fa15ed5be4cc371f77fbf`.
Thirty-nine exports have exactly the standard logical foundations
`Classical.choice`, `Quot.sound`, and `propext`. The remaining export,
`goodQuadraticChar_coprime_four_iff`, has exactly `[propext]`.
These actual lists are retained without adding unused allowances.
Both complete endpoint dependency lists are the standard triplet.
There are no new axioms, registered literature premises, placeholders,
or unchecked evaluation dependencies in the new exports.

At the time this review was frozen, strict compilation, the targeted
build, and the complete actual type/dependency inspection had passed.
The full aggregate verifier and subsequent exact-proof-commit CI
were still separate pending gates. This review does not claim those
execution outcomes.

This correspondence review supports the single numbered-result
promotion of complete Lemma 3.7 when the repository verification
gates pass. The fourteen new modules and forty exports add this
review to the preceding complete Lemma 3.6 scope. After registration,
the expected scope is 677 theorem exports, 165 proof modules, and
195 inspected inputs, with 17 Certified, 0 Partial, 0 Active, and
25 Pending numbered results. The thirty-three auxiliary and
supplementary groups, four registered literature premises, twenty
mapped reference groups, and nine pinned dependency revisions remain
separate and unchanged. The broader auxiliary Ramanujan-definition
agreement remains Pending. Whole-manuscript certification remains
false.

Strict compilation, a targeted build, source review, the full local
aggregate verifier, and exact-proof-commit GitHub CI are distinct
checks. The live ledger, verification report, and execution checkpoint
record the actual registration and execution outcomes. Historical
Lemma 3.6 evidence at 637 exports and 151 modules is not execution
evidence for the new files.
