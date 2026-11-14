import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite algebra for the ray decomposition

This file proves only the finite weighted-sum identity used after the
additive-character sum along each ray has been evaluated in equation (4.5)
of the frozen manuscript. It does not identify the finite-field Fourier
sum with this expression and does not certify Lemma 4.4.
-/

open scoped BigOperators

namespace QuaternaryQuadraticForms

universe u v

/-- Algebraic assembly of the two values of a nonzero-ray sum.
The predicate identifies the rays contained in the hyperplane. -/
theorem weighted_ray_sum
    {ι : Type u} {R : Type v} [CommRing R]
    (s : Finset ι) (weight : ι → R) (hit : ι → Prop)
    [DecidablePred hit] (p : R) :
    (∑ i ∈ s, weight i * (if hit i then p - 1 else -1)) =
      p * (∑ i ∈ s.filter hit, weight i) - ∑ i ∈ s, weight i := by
  classical
  calc
    (∑ i ∈ s, weight i * (if hit i then p - 1 else -1)) =
        ∑ i ∈ s, (p * (if hit i then weight i else 0) - weight i) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : hit i
      · simp only [if_pos h]
        ring
      · simp [h]
    _ = p * (∑ i ∈ s, if hit i then weight i else 0) -
        ∑ i ∈ s, weight i := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = p * (∑ i ∈ s.filter hit, weight i) - ∑ i ∈ s, weight i := by
      rw [Finset.sum_filter]

end QuaternaryQuadraticForms

