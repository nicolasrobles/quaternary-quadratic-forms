# Weil input and Lemma 2.5

## Accepted source

N. M. Katz, *Estimates for nonsingular multiplicative character sums*,
International Mathematics Research Notices 2002, no. 7, 333–349,
[DOI 10.1155/S1073792802106088](https://doi.org/10.1155/S1073792802106088),
equation (1.2), is reference [K] in the frozen manuscript.

The corresponding statement was checked in the
[author version dated April 19, 2001](https://web.math.princeton.edu/~nmk/multp5.pdf),
Section 1, page 1, the multiplicative-character bound immediately following
the discussion of the additive-character bound. The displays in this author
version are unnumbered. Its statement concerns a finite field of cardinality
q, a nontrivial complex multiplicative character extended by zero, and a
degree-d polynomial with d distinct zeros in an overfield, where d is positive.
The bound is (d−1)√q. Unlike the preceding additive-character statement,
this multiplicative statement has no restriction that d be prime to the
characteristic. The stronger purity discussion following the estimate is
not an assumption needed for the estimate.

The frozen manuscript also cites [IK, Theorem 11.23]. The present interface
uses [K] alone; no second literature premise or perfect-power reduction is
needed.

## Exact formal interface

[Trusted/Weil.lean](../../QuaternaryQuadraticForms/Trusted/Weil.lean) declares
`QuaternaryQuadraticForms.Trusted.weil_simple_roots` as the one external
premise associated with `EXT.WEIL`. It specializes the cited finite field to
the actual prime field `ZMod p` and has these hypotheses:

- `Fact p.Prime`;
- `ψ : MulChar (ZMod p) ℂ` and `ψ ≠ 1`;
- `f : Polynomial (ZMod p)` and `0 < f.natDegree`;
- `Fintype.card (f.rootSet (AlgebraicClosure (ZMod p))) = f.natDegree`.

Its conclusion is the norm bound for the literal sum of `ψ (f.eval z)` over
`z : ZMod p`, with right side `((f.natDegree : ℝ) - 1) * Real.sqrt p`.
The subtraction is real subtraction, not truncated natural subtraction.

The character type extends characters by zero, including the principal
character. Thus `ψ ≠ 1` is precisely nonprincipality in this setting.
The root set records distinct roots rather than multiplicities. Positive
degree excludes the zero polynomial, for which `natDegree` is zero. An
algebraic closure is an overfield of the kind used in [K].

The registry records the declaration's exact inspected Lean type and its
hash. The verifier checks its kind as an axiom and permits its use only by
exports whose axiom allowance names this declaration explicitly. It is kept
separate from proved exports and appears by name in their inspected axiom
dependencies.

## Manuscript correspondence

The frozen statement `lem:weil`, Lemma 2.5, is implemented as
`QuaternaryQuadraticForms.weil_bound` in
[WeilBound.lean](../../QuaternaryQuadraticForms/WeilBound.lean). The explicit
parameter m is linked to the actual polynomial degree and to the number of
distinct geometric roots. This is a source-relative certification of the
cited statement, not a new proof of the Weil estimate.

`weil_bound_of_separable` uses the proved root-count equivalence in
[GeometricRoots.lean](../../QuaternaryQuadraticForms/GeometricRoots.lean).
That equivalence comes from the pinned official mathlib, not from another
external premise.

Corollary 2.6 is a separate deduction. Its chart decomposition, polynomial
dehomogenization, degree calculation, simple-root condition, and contribution
at infinity are not included in the trusted input.
