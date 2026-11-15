import QuaternaryQuadraticForms.SplitQuadricBoxBounds

/-!
# Counting integral zeros of a split quaternary form

The anisotropic binary part leaves only two axes at binary value zero. Every
other binary fibre is bounded by the divisor estimate. The result has a generic
finite-set interface so rational changes of coordinates can be handled outside
this counting argument.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The divisor estimate is uniform over every nonzero binary value in the box. -/
theorem splitQuadric_nonzero_fibers_uniform (a b c : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ U : ℝ, 1 ≤ U → ∀ x y : ℤ,
      |(x : ℝ)| ≤ U → |(y : ℝ)| ≤ U →
      splitQuadricBinaryValue a b c x y ≠ 0 →
      (2 : ℝ) * ((splitQuadricBinaryValue a b c x y).natAbs.divisors.card : ℝ) ≤
        D * U ^ ε := by
  obtain ⟨B, hB, hdiv⟩ := divisors_card_le_rpow (ε / 2) (by positivity)
  let A := splitQuadricCoefficient a b c
  have hA : 0 < A := splitQuadricCoefficient_pos a b c
  refine ⟨2 * B * A ^ (ε / 2), by positivity, ?_⟩
  intro U hU x y hx hy hn
  have hU0 : 0 ≤ U := by linarith
  have hsize := splitQuadric_binaryValue_natAbs_le a b c x y U hU0 hx hy
  change ((splitQuadricBinaryValue a b c x y).natAbs : ℝ) ≤ A * U ^ 2 at hsize
  have hpower : (A * U ^ 2) ^ (ε / 2) = A ^ (ε / 2) * U ^ ε := by
    rw [Real.mul_rpow hA.le (sq_nonneg U), ← Real.rpow_natCast_mul hU0]
    congr 1
    congr 1
    ring
  calc
    _ ≤ 2 * (B * ((splitQuadricBinaryValue a b c x y).natAbs : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (hdiv _ (Int.natAbs_pos.mpr hn)) (by norm_num)
    _ ≤ 2 * (B * (A * U ^ 2) ^ (ε / 2)) := by
      gcongr
    _ = _ := by rw [hpower]; ring

/-- Summing the divisor estimate over the two free binary coordinates. -/
theorem splitQuadric_nonzero_box_card_le (k a b c : ℤ) (hk : k ≠ 0)
    (ε D : ℝ) (hD : 0 ≤ D) (U : ℝ) (hU : 1 ≤ U)
    (hdiv : ∀ x y : ℤ, |(x : ℝ)| ≤ U → |(y : ℝ)| ≤ U →
      splitQuadricBinaryValue a b c x y ≠ 0 →
      (2 : ℝ) * ((splitQuadricBinaryValue a b c x y).natAbs.divisors.card : ℝ) ≤
        D * U ^ ε)
    (s : Finset (Fin 4 → ℤ))
    (hbox : ∀ z ∈ s, ∀ i, |(z i : ℝ)| ≤ U)
    (hne : ∀ z ∈ s, splitQuadricBinaryValue a b c (z 2) (z 3) ≠ 0)
    (heq : ∀ z ∈ s,
      k * z 0 * z 1 + a * z 2 ^ 2 + b * z 2 * z 3 + c * z 3 ^ 2 = 0) :
    (s.card : ℝ) ≤ 9 * D * U ^ (2 + ε) := by
  classical
  let I : Finset ℤ := Finset.Icc (-⌊U⌋) ⌊U⌋
  let f : (Fin 4 → ℤ) → ℤ × ℤ := fun z => (z 2, z 3)
  have hmaps : (s : Set (Fin 4 → ℤ)).MapsTo f
      ((I ×ˢ I : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro z hz
    change (z 2, z 3) ∈ I ×ˢ I
    exact Finset.mem_product.mpr
      ⟨splitQuadric_mem_interval (hbox z hz 2), splitQuadric_mem_interval (hbox z hz 3)⟩
  have hfiber (p : ℤ × ℤ) :
      ((s.filter (fun z => f z = p)).card : ℝ) ≤ D * U ^ ε := by
    let t := s.filter (fun z => f z = p)
    by_cases ht : t.Nonempty
    · obtain ⟨z, hz⟩ := ht
      obtain ⟨hzs, hzp⟩ := Finset.mem_filter.mp hz
      have h2 : z 2 = p.1 := congrArg Prod.fst hzp
      have h3 : z 3 = p.2 := congrArg Prod.snd hzp
      have hn : splitQuadricBinaryValue a b c p.1 p.2 ≠ 0 := by
        rw [← h2, ← h3]
        exact hne z hzs
      have hc := splitQuadric_nonzero_fiber_card_le k a b c hk t p.1 p.2 hn
        (by
          intro w hw
          have hp := (Finset.mem_filter.mp hw).2
          exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩)
        (by intro w hw; exact heq w (Finset.mem_filter.mp hw).1)
      have hcr : (t.card : ℝ) ≤
          2 * ((splitQuadricBinaryValue a b c p.1 p.2).natAbs.divisors.card : ℝ) := by
        exact_mod_cast hc
      exact hcr.trans (hdiv p.1 p.2 (by rw [← h2]; exact hbox z hzs 2)
        (by rw [← h3]; exact hbox z hzs 3) hn)
    · have hzero : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      change (t.card : ℝ) ≤ _
      rw [hzero]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hI := integerEuclideanInterval_card_le_three_mul U hU
  change (I.card : ℝ) ≤ 3 * U at hI
  have hUpos : 0 < U := by linarith
  calc
    (s.card : ℝ) = ∑ p ∈ I ×ˢ I, ((s.filter (fun z => f z = p)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _p ∈ I ×ˢ I, D * U ^ ε := Finset.sum_le_sum (fun p _ => hfiber p)
    _ = (I.card : ℝ) ^ 2 * (D * U ^ ε) := by
      simp [Finset.card_product, pow_two, Nat.cast_mul]
    _ ≤ (3 * U) ^ 2 * (D * U ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hI 2
    _ = 9 * D * U ^ (2 + ε) := by
      rw [Real.rpow_add hUpos, Real.rpow_two]
      ring

/-- Integral zeros of a split form with anisotropic binary part satisfy the
`U^(2+ε)` estimate, uniformly over all finite subsets of its coordinate box. -/
theorem splitQuadric_box_bound (k a b c : ℤ) (hk : k ≠ 0)
    (haniso : ∀ x y : ℤ, a * x ^ 2 + b * x * y + c * y ^ 2 = 0 → x = 0 ∧ y = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ s : Finset (Fin 4 → ℤ),
      (∀ z ∈ s, (∀ i, |(z i : ℝ)| ≤ U) ∧
        k * z 0 * z 1 + a * z 2 ^ 2 + b * z 2 * z 3 + c * z 3 ^ 2 = 0) →
      (s.card : ℝ) ≤ C * U ^ (2 + ε) := by
  classical
  obtain ⟨D, hD, hdiv⟩ := splitQuadric_nonzero_fibers_uniform a b c ε hε
  refine ⟨6 + 9 * D, by positivity, ?_⟩
  intro U hU s hs
  let s₀ := s.filter (fun z => splitQuadricBinaryValue a b c (z 2) (z 3) = 0)
  let s₁ := s.filter (fun z => splitQuadricBinaryValue a b c (z 2) (z 3) ≠ 0)
  have hzero : (s₀.card : ℝ) ≤ 6 * U := by
    apply splitQuadric_zero_fiber_card_le k hk U hU s₀
    · intro z hz
      exact (hs z (Finset.mem_filter.mp hz).1).1
    · intro z hz
      exact haniso (z 2) (z 3) (Finset.mem_filter.mp hz).2
    · intro z hz
      have hz0 := (Finset.mem_filter.mp hz).2
      have heq := (hs z (Finset.mem_filter.mp hz).1).2
      dsimp [splitQuadricBinaryValue] at hz0
      linarith
  have hnonzero : (s₁.card : ℝ) ≤ 9 * D * U ^ (2 + ε) := by
    apply splitQuadric_nonzero_box_card_le k a b c hk ε D hD.le U hU (hdiv U hU) s₁
    · intro z hz
      exact (hs z (Finset.mem_filter.mp hz).1).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      exact (hs z (Finset.mem_filter.mp hz).1).2
  have hcard : (s.card : ℝ) = (s₀.card : ℝ) + (s₁.card : ℝ) := by
    exact_mod_cast (Finset.filter_card_add_filter_neg_card_eq_card
      (s := s) (fun z => splitQuadricBinaryValue a b c (z 2) (z 3) = 0)).symm
  have hup : U ≤ U ^ (2 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU (show (1 : ℝ) ≤ 2 + ε by linarith)
  rw [hcard]
  nlinarith

end QuaternaryQuadraticForms
