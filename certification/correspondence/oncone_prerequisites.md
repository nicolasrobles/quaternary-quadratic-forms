# Dual-cone counting and the modulus partial-summation estimate

## Exact scope

This batch covers the auxiliary obligation `aux:conecount` and three
supporting exports for the proof of Lemma 5.3. The supplied modules are
`DualConeCounting.lean` (118 lines, one public theorem) and
`ConeFrequencyAbel.lean` (162 lines, three public theorems).

The weighted count is equation `eq:conecount`, at lines 814–824 of
`manuscript/quadratic_character_sums_github.tex`. The analytic calculation
is the partial-summation step in the proof of Lemma 5.3. The source SHA-256
remains `e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a`.

The reciprocal-norm count is a complete auxiliary result. The modulus
estimate is supporting progress only: the mixed-sum factorization,
Fourier factors, Poisson normalization, and final summation for Lemma 5.3
remain subsequent assembly work. No numbered result is promoted by this
batch, and Lemma 5.3 remains Pending.

## The actual dual cone and its weighted count

`dualConeFrequencies A U` is exactly the set of nonzero integral vectors
in the Euclidean ball of radius `U` satisfying
`u^T adj(A) u = 0`. Thus its reciprocals are the manuscript's
`1/norm(u)`, with no change of norm or primitive-vector restriction.

The export `source_dual_cone_count` takes a symmetric nonsingular integral
matrix with nonsquare determinant. It forms `S = adj(A)` over the rationals
and proves `det(S) = det(A)^3`. If that cube were a rational square,
division of its square root by the nonzero `det(A)` would make `det(A)`
a rational square. The proved rational-to-integer square equivalence
contradicts the source hypothesis. Certified Lemma 2.3 therefore applies
to this actual rational adjugate form.

The private finite-set argument uses the maximum radius `M` and splits
at `M/2`. Given subcounts at most `D T^2`, the outer reciprocal sum is at
most `2 D M`; induction gives the same bound for the inner set. If
`M/2 < 1`, that set is empty because a nonzero integral vector has
Euclidean norm at least one. This proves the bound `4 D U`, including
empty sets and the endpoint `U = 1`.

The quadric-counting constant `K` is chosen before the radius. For fixed
`U >= 1`, its subcounts satisfy

\[
 N(T)\le K T^{2+\varepsilon}\le K U^\varepsilon T^2
 \qquad(1\le T\le U).
\]

Taking `D = K U^epsilon` in the finite argument gives

\[
 \sum_{\substack{0<\lVert u\rVert\le U\\F^*(u)=0}}
 \frac1{\lVert u\rVert}
 \le 4K U^{1+\varepsilon}.
\]

The final constant `4K` depends only on the form and positive exponent,
and precedes every real `U >= 1`. This is every clause of `aux:conecount`.

## Cancellation, endpoints and Abel summation

`cone_modulus_abel_bound` uses the actual complex partial sum of the
unweighted complete sums `S_c(u)` in a fixed gcd class. Its norm is taken
after that summation. The coefficient at zero is explicitly zero, giving
the correct lower boundary in the Abel identity. The upper boundary
vanishes by the hypothesis `f(X) = 0`.

The sum runs over positive integers up to `floor(X)`. If `X` is integral,
its extra endpoint term vanishes by `f(X) = 0`; otherwise this is already
the strict cutoff `c < X`. The case `X = 1` is included.

The derivative is measurable and bounded on the finite interval, which
supplies the integrability required by the Abel identity. With the stated
partial-sum and derivative bounds, the resulting integrand has norm at
most `L K t^(eta-1)`. Since `eta > 0`, integration gives
`L K (X^eta-1)/eta <= L K X^eta/eta`.

## The derivative and source specialization

For `phi(t) = t^(-4) I(t/Q)`, the export
`coneIntegralWeight_derivative` uses the exact chain rule:

\[
 \phi'(t)=t^{-4}Q^{-1}I'(t/Q)-4t^{-5}I(t/Q).
\]

The estimate `|I(t/Q)|+(t/Q)|I'(t/Q)| <= L t` then gives
`|phi'(t)| <= 4L/t^4`. In the source application the actual complex
delta integral is differentiated with `v = u/sqrt(q)` fixed.

`DeltaIntegralBounds.onCone_modulus_sum` combines the already checked
scaled-integral estimate and Lemma 3.7, sets `X = r_0 Q`, and uses the
actual endpoint cutoff. Its conclusion is the inner modulus bound

\[
 \left|\sum_{\substack{c\le r_0Q\\(c,q)=d}} S_c(u)\phi(c)\right|
 \le C\frac{q}{B\lVert u\rVert}B^{3\eta}(Bq)^\eta.
\]

The constant can be taken as `4 J K r_0^eta/eta`, before every individual
weight, positive squarefree factorization, scale `B`, and nonzero cone
frequency. The analytic bounds and endpoint cutoff are explicit hypotheses
supplied by the certified predecessors. The final mixed-sum factors and
the Poisson prefactor are not part of this conclusion.

## Audit and execution evidence

Independent reviews approved the weighted count and all three analytic
exports, with no required fatal, serious, moderate, or light correction.
All four supplied theorem records list only `Classical.choice`,
`Quot.sound`, and `propext`. No literature premise is added.

The [extracted package evidence](../local/oncone_prerequisites_package_evidence.json)
preserves both source hashes and all four theorem records. The focused
check `python3 scripts/verify_oncone_prerequisites.py` verifies exact supplied
bytes, strict compilation, declaration kinds, actual theorem types and
axiom sets, the loaded project axiom registry, and pinned dependencies.
This review and the relevant predecessor reviews are included in the
execution report's input hashes. The checked commit, successful run,
preserved report and acceptance decision appear in [CHECKPOINT.md](../../CHECKPOINT.md).
