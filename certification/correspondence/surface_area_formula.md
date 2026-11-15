# Source correspondence: the general graph area formula

## Independent accepted source

Leon Simon, *Introduction to Geometric Measure Theory*, author text,
copyright 2017/2018,
[primary PDF](https://math.stanford.edu/~lms/ntu-gmt-text.pdf).

The downloaded primary PDF has 1,234,390 bytes and SHA-256
`ba7fd4a53bf0f1d0ac54aec50bb72c4bba196b8e784d65cd0a7fd85131a3bf03`.
The normalization and area-theorem locations were inspected both in indexed
text and in rendered pages.

| Location | Content |
| --- | --- |
| Ch.1 §2, equations 2.1–2.2, printed p.11 | Normalized Hausdorff measure, with the unit-ball volume divided by the diameter factor |
| Ch.2 §3, Theorem 3.3, printed p.57 | Area formula for locally Lipschitz maps, including the injective case |
| Ch.2 §3, Remark 3.4(2), printed p.58 | Nonnegative weighted area formula |
| Ch.2 §3, Example 3.5(2),(3), printed pp.60–61 | Agreement with submanifold volume and the scalar graph factor sqrt(1+|Dphi|²) |

## Exact trusted scope

`Trusted.simon_graph_area` is the general measure identity for a C1 scalar
graph over an open subset of Euclidean three-space, embedded in Euclidean
four-space. The graph function is also globally measurable; only its
restriction to the open domain must be C1. The identity identifies the
restriction of normalized Hausdorff measure to the graph with the pushforward
of Lebesgue measure weighted by the actual graph area factor.

This source input mentions no quadratic form, weight, delta kernel,
Heath-Brown limit, or manuscript singular integral. Those specializations
are internal.

Mathlib's Hausdorff measure is the unnormalized diameter-power convention.
`euclideanSurfaceMeasure` is therefore defined using the exact factor
`volume (ball (0 : RealVector3) 1) / 2^3`. There is no unproved numerical
normalization or redefinition of the manuscript's singular integral.

The complex-valued integral transformation and integrability equivalence
are proved from the measure identity with mathlib's map and density APIs.
Orthogonal invariance is also proved internally from mathlib's Hausdorff
isometry theorem; it is not part of this literature premise.

## Verification state

The exact proposition was elaborated without axioms and its type recorded
before introduction of the premise. Registration and source review precede
aggregate verification of any manuscript conclusion.

