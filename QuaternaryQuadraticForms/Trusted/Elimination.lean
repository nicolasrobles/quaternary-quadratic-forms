import QuaternaryQuadraticForms.EliminationData

/-!
# Registered literature input: homogeneous resultant systems

Lang, Algebra, revised third edition, Chapter IX, Theorem 4.1, p. 402.
The generic coefficient family is fixed before any field or coefficient
specialization. Projective zeros are interpreted over the algebraic closure,
as in the remarks after Theorem 3.1, p. 389. See the registered correspondence
record for zero specialized forms and the possibly empty output family.

Polynomial-parameter substitutions and all deductions about the manuscript's
gradient equations, bad primes, and coefficient heights are proved elsewhere.
-/

noncomputable section

open QuaternaryQuadraticForms

axiom QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants
    (N : ℕ) (hN : 0 < N) (ι : Type) [Fintype ι] [Nonempty ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (HomogeneousCoefficient N d) ℤ),
      ∀ (K : Type) [Field K] (w : HomogeneousCoefficient N d → K),
        HasNonzeroGeometricZero (homogeneousSystem N d w) ↔
          ∀ j, MvPolynomial.eval₂ (Int.castRingHom K) w (R j) = 0
