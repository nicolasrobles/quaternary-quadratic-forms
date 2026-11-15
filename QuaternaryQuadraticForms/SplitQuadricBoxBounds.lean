import QuaternaryQuadraticForms.SplitQuadricFibers

/-!
# Elementary box estimates for a split quaternary form
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- An integral coordinate with real absolute value at most `U` lies in the floor interval. -/
theorem splitQuadric_mem_interval {z : ℤ} {U : ℝ} (hz : |(z : ℝ)| ≤ U) :
    z ∈ Finset.Icc (-⌊U⌋) ⌊U⌋ := by
  have hz' := abs_le.mp hz
  have hneg : -z ≤ ⌊U⌋ := Int.le_floor.mpr (by push_cast; linarith)
  exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hz'.2⟩

/-- A positive coefficient controlling the integral binary form. -/
def splitQuadricCoefficient (a b c : ℤ) : ℝ :=
  |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + 1

/-- The coefficient is strictly positive, including when every coefficient vanishes. -/
theorem splitQuadricCoefficient_pos (a b c : ℤ) :
    0 < splitQuadricCoefficient a b c := by
  dsimp [splitQuadricCoefficient]
  positivity

/-- The binary value in a coordinate box has size at most a fixed multiple of `U²`. -/
theorem splitQuadric_binaryValue_natAbs_le (a b c x y : ℤ) (U : ℝ) (hU : 0 ≤ U)
    (hx : |(x : ℝ)| ≤ U) (hy : |(y : ℝ)| ≤ U) :
    ((splitQuadricBinaryValue a b c x y).natAbs : ℝ) ≤
      splitQuadricCoefficient a b c * U ^ (2 : ℕ) := by
  have hx2 : |(x : ℝ)| ^ (2 : ℕ) ≤ U ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : |(y : ℝ)| ^ (2 : ℕ) ≤ U ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hxy : |(x : ℝ)| * |(y : ℝ)| ≤ U ^ (2 : ℕ) := by
    nlinarith [mul_le_mul hx hy (abs_nonneg (y : ℝ)) hU]
  calc
    _ = |(a : ℝ) * (x : ℝ) ^ (2 : ℕ) + (b : ℝ) * (x : ℝ) * (y : ℝ) +
        (c : ℝ) * (y : ℝ) ^ (2 : ℕ)| := by simp [splitQuadricBinaryValue]
    _ ≤ |(a : ℝ) * (x : ℝ) ^ (2 : ℕ) + (b : ℝ) * (x : ℝ) * (y : ℝ)| +
        |(c : ℝ) * (y : ℝ) ^ (2 : ℕ)| := abs_add_le _ _
    _ ≤ (|(a : ℝ)| * |(x : ℝ)| ^ (2 : ℕ) + |(b : ℝ)| * |(x : ℝ)| * |(y : ℝ)|) +
        |(c : ℝ)| * |(y : ℝ)| ^ (2 : ℕ) := by
      simpa only [abs_mul, abs_pow] using
        add_le_add_right (abs_add_le ((a : ℝ) * (x : ℝ) ^ (2 : ℕ))
          ((b : ℝ) * (x : ℝ) * (y : ℝ))) |(c : ℝ) * (y : ℝ) ^ (2 : ℕ)|
    _ ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * U ^ (2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_left hx2 (abs_nonneg (a : ℝ)),
        mul_le_mul_of_nonneg_left hxy (abs_nonneg (b : ℝ)),
        mul_le_mul_of_nonneg_left hy2 (abs_nonneg (c : ℝ))]
    _ ≤ _ := by dsimp [splitQuadricCoefficient]; nlinarith [sq_nonneg U]

/-- The zero binary fibre consists of two coordinate axes. -/
theorem splitQuadric_zero_fiber_card_le (k : ℤ) (hk : k ≠ 0)
    (U : ℝ) (hU : 1 ≤ U) (s : Finset (Fin 4 → ℤ))
    (hbox : ∀ z ∈ s, ∀ i, |(z i : ℝ)| ≤ U)
    (htail : ∀ z ∈ s, z 2 = 0 ∧ z 3 = 0)
    (heq : ∀ z ∈ s, k * z 0 * z 1 = 0) :
    (s.card : ℝ) ≤ 6 * U := by
  classical
  let I : Finset ℤ := Finset.Icc (-⌊U⌋) ⌊U⌋
  let A : Finset (Fin 4 → ℤ) := I.image (fun t => ![t, 0, 0, 0])
  let B : Finset (Fin 4 → ℤ) := I.image (fun t => ![0, t, 0, 0])
  have hsub : s ⊆ A ∪ B := by
    intro z hz
    have hprod : z 0 = 0 ∨ z 1 = 0 := by
      have h := heq z hz
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl ((mul_eq_zero.mp h).resolve_left hk)
      · exact Or.inr h
    obtain ⟨h2, h3⟩ := htail z hz
    rcases hprod with h0 | h1
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨z 1, splitQuadric_mem_interval (hbox z hz 1), ?_⟩
      funext i
      fin_cases i <;> simp [h0, h2, h3]
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨z 0, splitQuadric_mem_interval (hbox z hz 0), ?_⟩
      funext i
      fin_cases i <;> simp [h1, h2, h3]
  have hcard : s.card ≤ 2 * I.card := by
    calc
      _ ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le _ _
      _ ≤ I.card + I.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = _ := by omega
  have hcast : (s.card : ℝ) ≤ 2 * (I.card : ℝ) := by exact_mod_cast hcard
  have hI := integerEuclideanInterval_card_le_three_mul U hU
  change (I.card : ℝ) ≤ 3 * U at hI
  linarith

end QuaternaryQuadraticForms
