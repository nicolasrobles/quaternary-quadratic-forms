import QuaternaryQuadraticForms.EuclideanIntegerBox
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The integer zeros counted in Lemma 2.3

The coefficient matrix has rational entries, while the counted vectors
are actual integer vectors in the source Euclidean ball. The finite
representation is identified with the literal set before its cardinality
is used. A separate helper transports a proved box estimate through an
injective integer linear map with a fixed coordinate bound.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The rational quadratic form evaluated at an integer vector. -/
def rationalIntegerQuadricValue (S : Matrix (Fin 4) (Fin 4) ℚ)
    (z : Fin 4 → ℤ) : ℚ :=
  dotProduct (fun i => (z i : ℚ)) (S.mulVec (fun i => (z i : ℚ)))

/-- The literal set of integer zeros in the manuscript's Euclidean ball. -/
def sourceQuadricZeroSet (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ) :
    Set (Fin 4 → ℤ) :=
  {z | integerEuclideanNorm z ≤ U ∧ rationalIntegerQuadricValue S z = 0}

/-- A finite representation of the same source set. -/
def integerQuadricZeros (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ) :
    Finset (Fin 4 → ℤ) := by
  classical
  exact (integerEuclideanBall U).filter fun z => rationalIntegerQuadricValue S z = 0

/-- Membership removes the finite coordinate-box representation. -/
theorem mem_integerQuadricZeros (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ)
    (z : Fin 4 → ℤ) :
    z ∈ integerQuadricZeros S U ↔
      integerEuclideanNorm z ≤ U ∧ rationalIntegerQuadricValue S z = 0 := by
  classical
  simp only [integerQuadricZeros, Finset.mem_filter, mem_integerEuclideanBall]

/-- The represented set is exactly the source's set of integer zeros. -/
theorem sourceQuadricZeroSet_eq (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ) :
    sourceQuadricZeroSet S U = (integerQuadricZeros S U : Set (Fin 4 → ℤ)) := by
  ext z
  exact (mem_integerQuadricZeros S U z).symm

/-- Finiteness holds for every real radius, before any estimate is applied. -/
theorem sourceQuadricZeroSet_finite (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ) :
    (sourceQuadricZeroSet S U).Finite := by
  rw [sourceQuadricZeroSet_eq]
  exact Finset.finite_toSet _

/-- The source set cardinality is the actual finite-solution count. -/
theorem sourceQuadricZeroSet_ncard (S : Matrix (Fin 4) (Fin 4) ℚ) (U : ℝ) :
    (sourceQuadricZeroSet S U).ncard = (integerQuadricZeros S U).card := by
  rw [sourceQuadricZeroSet_eq, Set.ncard_coe_finset]

/-- An anisotropic rational form has at most the origin among its integer zeros. -/
theorem integerQuadricZeros_card_le_one
    (S : Matrix (Fin 4) (Fin 4) ℚ)
    (haniso : ∀ x : Fin 4 → ℚ, dotProduct x (S.mulVec x) = 0 → x = 0)
    (U : ℝ) : (integerQuadricZeros S U).card ≤ 1 := by
  classical
  have hsub : integerQuadricZeros S U ⊆ {0} := by
    intro z hz
    have hq := haniso (fun i => (z i : ℚ)) (mem_integerQuadricZeros S U z |>.mp hz).2
    have hz0 : z = 0 := by
      funext i
      have hi := congrFun hq i
      change (z i : ℚ) = 0 at hi
      exact_mod_cast hi
    simp only [Finset.mem_singleton]
    exact hz0
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

/-- An injective integer linear map transports a uniform model count back
to the actual Euclidean zero set, with a constant independent of the radius. -/
theorem integerQuadricZeros_bound_of_lattice_model
    (S : Matrix (Fin 4) (Fin 4) ℚ) (ε : ℝ)
    (L : Matrix (Fin 4) (Fin 4) ℤ) (hL : Function.Injective L.mulVec)
    (D : ℝ) (hD : 1 ≤ D)
    (hcoord : ∀ z : Fin 4 → ℤ, ∀ i,
      |((L.mulVec z) i : ℝ)| ≤ D * integerEuclideanNorm z)
    (P : (Fin 4 → ℤ) → Prop)
    (hmap : ∀ z, rationalIntegerQuadricValue S z = 0 → P (L.mulVec z))
    (C : ℝ) (hC : 0 < C)
    (hcount : ∀ V : ℝ, 1 ≤ V → ∀ s : Finset (Fin 4 → ℤ),
      (∀ z ∈ s, (∀ i, |(z i : ℝ)| ≤ V) ∧ P z) →
      (s.card : ℝ) ≤ C * V ^ (2 + ε)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ U : ℝ, 1 ≤ U →
      ((integerQuadricZeros S U).card : ℝ) ≤ C' * U ^ (2 + ε) := by
  classical
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨C * D ^ (2 + ε), mul_pos hC (Real.rpow_pos_of_pos hDpos _), ?_⟩
  intro U hU
  have hV : 1 ≤ D * U := calc
    1 ≤ D := hD
    _ = D * 1 := (mul_one D).symm
    _ ≤ D * U := mul_le_mul_of_nonneg_left hU hDpos.le
  let s := (integerQuadricZeros S U).image L.mulVec
  have hs : ∀ y ∈ s, (∀ i, |(y i : ℝ)| ≤ D * U) ∧ P y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hzU, hzF⟩ := (mem_integerQuadricZeros S U z).mp hz
    refine ⟨fun i => (hcoord z i).trans ?_, hmap z hzF⟩
    exact mul_le_mul_of_nonneg_left hzU hDpos.le
  have hb := hcount (D * U) hV s hs
  have hc : s.card = (integerQuadricZeros S U).card :=
    Finset.card_image_of_injective _ hL
  rw [hc] at hb
  calc
    ((integerQuadricZeros S U).card : ℝ) ≤ C * (D * U) ^ (2 + ε) := hb
    _ = (C * D ^ (2 + ε)) * U ^ (2 + ε) := by
      rw [Real.mul_rpow hDpos.le (zero_le_one.trans hU)]
      ring

end QuaternaryQuadraticForms
