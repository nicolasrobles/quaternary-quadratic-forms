# Source correspondence: local delta integrals (Lemma 2.2)

## Scope and current state

The frozen manuscript's Lemma 2.2 is `lem:integrals`, lines 667–688,
with proof at lines 690–753. The current task is its complete formalization.
The statements below have been checked against the primary sources and
registered before introducing their Lean premises. Internal proof assembly and independent source correspondence review are
complete. Aggregate verification and its exact publication evidence are
recorded separately in CHECKPOINT.md.

The manuscript SHA-256 remains
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

## Primary analytic source

D. R. Heath-Brown, *A new form of the circle method, and its application to
quadratic forms*, J. reine angew. Math. 481 (1996), 149–206,
[DOI](https://doi.org/10.1515/crll.1996.481.149),
[author manuscript](https://ora.ox.ac.uk/objects/uuid%3Abbd3c62f-f010-44b5-8be5-87e903fb0084/files/m7ec02df6e1b8303a66e7a6015ecb6044).

The indexed primary text was inspected; direct binary retrieval is blocked
by HTTP 403. Page numbers here refer to the author manuscript.

| Declaration | Exact source location | Imported content |
| --- | --- | --- |
| `heathBrown_weight_localization` | §2 Lemma 2, p.16; §6 Lemma 12 and its construction, pp.30–31 | A common positive scale, interval radius, and first-derivative lower bound; each actual localized weight is away from the zero set or satisfies the source local geometry after a signed permutation |
| `heathBrown_singular_graph` | Theorem 3, pp.6–7; §6 Lemma 11, pp.28–29 | Thin-slab convergence to the integrable graph-coordinate expression for a consistent selector of the source interval roots |
| `heathBrown_zero_approximation` | §7 Lemma 13, pp.32–33 | Uniform rapid approximation to the thin-slab singular integral on each fixed bounded positive r-range |
| `heathBrown_integral_reduction` | §7 Lemma 14 and proof, pp.33–34 | Actual fixed-frequency differentiability and separate modified weight/amplitude witnesses for value and derivative estimates |
| `heathBrown_oscillatory_bounds` | §7 Lemmas 15 and 18, pp.34–36; §8 Lemma 22, pp.39–40 | Bounds for the actual auxiliary integral; the last requires a uniform lower bound on the actual Hessian determinant |

The interfaces are the four-dimensional quadratic case of these analytic
arguments. They use real coefficient matrices. Although the surrounding
arithmetic problem starts with integral coefficients, the inspected proofs
of §§6–8 use only real differential and integral estimates; no arithmetic
property of the coefficients enters. This real-coefficient formulation is
documented explicitly, rather than attributed as a verbatim matrix-quantified
statement in the source. The matrix is fixed before every estimate constant.

## Quantitative definitions and quantifier audit

`HBWeightControl B D w` contains actual smoothness, compact support, a
Euclidean support-radius bound B, and the literal iterated coordinate partial
bounds D(k). The support bound implies the source cube-radius bound. Norms in
the analytic estimates can be taken Euclidean: in fixed dimension four,
changing the source vector-norm convention changes only the permitted common
constants. No maximum norm is identified definitionally with a Euclidean norm.

`HBC0Geometry F a lam w` records precisely the positive first derivative on
every source interval and the unique root in that interval. It assumes no
global graph. The root selector in `HBGraphSelector` must actually lie in
every prescribed interval. The explicit quadratic positive-root chart and
its consistency are internal deductions.

Every D(k), amplitude bound K(j,N), geometric lower bound, and bounded upper
r-range is fixed before the individual weight, amplitude, r, and frequency.
Localization chooses delta before both W and the center y. The construction
in Lemma 12 chooses delta from common parameters, which is stronger than an
unusable collection of unrelated per-weight choices.

The H-envelope is `(r / max r |t|)^N` for r>0. At t=0 it is one, as intended
by the source analytic minimum convention; Lean's division by zero is never
used to replace that convention.

Lemma 14 may choose different witnesses for the value and derivative. Their
derivative and amplitude bounds are common; their supports remain in the
original support. The derivative is of `r ↦ deltaIntegral F w r v` with
the original v fixed. Differentiability is included, not inferred from a
bound on Lean's total derivative.

The source inputs are restricted to 0<r≤R with fixed R. Extension beyond the
common actual kernel cutoff is internal. The epsilon scaling and combination
of the two separate estimates are internal real-algebra proofs. The Hessian
is defined by actual derivatives; its equality to 2A and determinant lower
bound for symmetric nonsingular A are proved internally.

## Surface normalization is a separate geometric source

Heath-Brown identifies his singular integral with a graph-coordinate
integral. His cited theorem does not itself supply the normalized Hausdorff
surface measure used by the manuscript. The independent general graph area
formula is registered under `EXT.SIMON_GRAPH_AREA`; see
[surface_area_formula.md](surface_area_formula.md).

The following deductions remain internal: the actual gradient 2Ax; its
uniform positive annular lower bound; the explicit positive-root graph;
the graph area/gradient ratio; identification of the two singular integrals;
orthogonal transport; the finite common choice of constants; and the actual
localized weight and frequency substitutions.

## Subsequent work

The requested return to `aux:Sxi` and `aux:Sxibound` has now been implemented
and reviewed; see the separate main-coefficient record. No further proof
target is claimed by this milestone. Absolute convergence for arbitrary
weights meeting the cone vertex remains the separately tracked
`aux:singint_absolute` obligation.

## Implemented manuscript deductions

The complete endpoint is
[source_delta_integrals](../../QuaternaryQuadraticForms/DeltaIntegralTheorem.lean).
It uses the actual integral coefficient matrix embedded into the reals.
A stronger real symmetric nonsingular matrix theorem is exported as well;
the nonsquare-determinant condition from the global paper is unnecessary
for this analytic lemma.

| Manuscript clause | Checked implementation |
| --- | --- |
| One delta and cutoff before every W,y | `source_delta_integrals`, with uniform annular gradient and derivative sequences selected internally |
| Actual theta and W_y, mass and reconstruction | `AnalyticWeightBump`, `AnalyticWeightPieces`, `AnalyticWeightDerivativeBounds` |
| Cutoff at every r≥r0 and every frequency | `deltaIntegral_uniform_cutoff`; an extra strict margin proves local vanishing and the actual derivative |
| Nonvanishing alternative | `localizedWeight_alternative`; the estimated family is exactly the pieces whose closed support meets F=0 |
| Zero-frequency approximation | `DeltaIntegralBounds.zero_error`, with the actual surface integral as its value functional |
| Zero-frequency derivative | `DeltaIntegralBounds.zero_derivative`, with the original frequency fixed |
| Rapid nonzero-frequency decay | `DeltaIntegralBounds.rapid`, for every natural j≥1 |
| Combined epsilon decay | `DeltaIntegralBounds.decay`, for 0<epsilon<1/2 and nonzero frequency |
| Derivative existence | `DeltaIntegralBounds.differentiable` at every positive r and every fixed frequency |
| Absolute convergence where sigma is used | Explicit `IntegrableOn` conclusion in both complete endpoints |

The final `DeltaIntegralBounds` is a proposition with all constants
quantified before the weight, scale and frequency. It applies on the
entire positive real scale set. It is not a bundle of unrelated
per-weight estimates.

The larger finite family of 384 signed coordinate permutations contains
every change used in the source construction. Every map is an actual
Euclidean linear isometry. The pullback matrix, determinant preservation,
full gradient norm, volume, surface measure, integral and r-derivative
transport are internal proofs. A finite sum of positive constants gives
one common constant before selecting any piece.

For the zero-frequency approximation above the cutoff R, the internal
proof uses the already established error bound at R, where I_R(0)=0,
and monotonicity of R^j≤r^j. This is a valid internal extension of the
source bounded-r estimate and does not add a literature assumption.

The positive-root chart handles both zero and nonzero leading coefficient.
Its exact characterization uses the positive distinguished gradient
coordinate. C0 interval geometry proves consistency of the actual roots;
the graph is never assumed globally for the entire cone. Differentiating
the actual graph equation gives the full gradient/area-factor identity.

This analytic work contributes 155 public theorem exports in 24 modules.
The independent audit reviewed the primary source interfaces, measure
normalization, all quantifier orders, branch selection, fixed-frequency
derivatives, finite uniformity, cutoff boundary, and integral-matrix
specialization. No correspondence defect was found. The subsequent
coefficient continuation has its own
[review record](main_coefficient.md) and uses no analytic source premise.


