import QuaternaryQuadraticForms.TransversePullback
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Literature input: Bertini in homogeneous polynomial coordinates

This is a composite geometric interface for an arbitrary finite homogeneous
system in an arbitrary projective dimension. Hartshorne, II.8.18, pp. 179-180,
supplies the regular hyperplane section. The standard projective Jacobian
interpretation, local dimension, and tangent-space identification are also
part of this literature boundary, with exact primary-source locators in
`certification/correspondence/bertini_input.md`.

The conclusion says that a hyperplane functional is nonzero on some common
tangent vector at each intersection point. Rank increase, the matrix-quadric
specialization, geometric field extension, elimination, nonzero resultant
specialization, and the exceptional polynomial and its degree are separate
internal deductions. This declaration asserts none of those conclusions.
-/

noncomputable section

open QuaternaryQuadraticForms

axiom QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent
    (K : Type*) [Field K] [IsAlgClosed K]
    (N c : ℕ) (hcodim : c + 2 ≤ N)
    (P : Fin c → MvPolynomial (Fin N) K) (d : Fin c → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhomogeneous : ∀ i, (P i).IsHomogeneous (d i))
    (hjacobian : ∀ x : Fin N → K, x ≠ 0 →
      (∀ i, MvPolynomial.eval x (P i) = 0) →
        Matrix.rank (fun i => polynomialGradient (P i) x) = c) :
    ∃ u : Fin N → K, u ≠ 0 ∧
      ∀ x : Fin N → K, x ≠ 0 →
        (∀ i, MvPolynomial.eval x (P i) = 0) → dotProduct u x = 0 →
          ∃ v : Fin N → K,
            (∀ i, dotProduct (polynomialGradient (P i) x) v = 0) ∧
              dotProduct u v ≠ 0
