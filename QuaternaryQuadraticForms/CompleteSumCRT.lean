import QuaternaryQuadraticForms.CompleteSums
import QuaternaryQuadraticForms.CRTArithmetic

/-!
# Chinese remainder factorization of the literal mixed complete sum

The scaled CRT coordinates are those in the manuscript.  The cone
constraint and the prime-product weight both split in these coordinates.
The phase has the source factors `c₂ n₂` and `c₁ n₁`, which are removed
by bijections of the two local unit groups.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem primeWeightsInvariant_of_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) [NeZero n] (hqn : q ∣ n) (hξ : PrimeWeightsInvariant ξ n) :
    PrimeWeightsInvariant ξ q := by
  intro p hp
  exact hξ p (Nat.primeFactors_mono hqn (NeZero.ne n) hp)

private theorem scaled_vector_congr_left
    (q₁ q₂ c₁ c₂ : ℕ) (x₁ x₂ : Fin 4 → ℤ) (i : Fin 4) :
    ((((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) i : ZMod q₁) =
      ((((q₂ * c₂ : ℕ) : ℤ) • x₁) i : ZMod q₁) := by
  simp [Pi.add_apply, Pi.smul_apply]

private theorem scaled_vector_congr_right
    (q₁ q₂ c₁ c₂ : ℕ) (x₁ x₂ : Fin 4 → ℤ) (i : Fin 4) :
    ((((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) i : ZMod q₂) =
      ((((q₁ * c₁ : ℕ) : ℤ) • x₂) i : ZMod q₂) := by
  simp [Pi.add_apply, Pi.smul_apply]

private theorem compositeWeight_crt_scaled
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : PrimeWeightsInvariant ξ (q₁ * q₂)) (x₁ x₂ : Fin 4 → ℤ) :
    compositeWeight ξ (q₁ * q₂)
        (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) =
      compositeWeight ξ q₁ x₁ * compositeWeight ξ q₂ x₂ := by
  have hqq : q₁.Coprime q₂ := hcoprime.of_dvd
    (dvd_mul_right q₁ c₁) (dvd_mul_right q₂ c₂)
  have hξ₁ := primeWeightsInvariant_of_dvd ξ q₁ (q₁ * q₂) (dvd_mul_right q₁ q₂) hξ
  have hξ₂ := primeWeightsInvariant_of_dvd ξ q₂ (q₁ * q₂) (dvd_mul_left q₂ q₁) hξ
  rw [compositeWeight_mul ξ q₁ q₂ hqq]
  rw [compositeWeight_congr ξ q₁ _ _ (scaled_vector_congr_left q₁ q₂ c₁ c₂ x₁ x₂),
    compositeWeight_congr ξ q₂ _ _ (scaled_vector_congr_right q₁ q₂ c₁ c₂ x₁ x₂)]
  have hscale₁ : compositeWeight ξ q₁ (((q₂ * c₂ : ℕ) : ℤ) • x₁) =
      compositeWeight ξ q₁ x₁ := by
    apply compositeWeight_smul ξ q₁ _ x₁ hξ₁
    simpa only [Int.natAbs_natCast] using
      hcoprime.symm.of_dvd_right (dvd_mul_right q₁ c₁)
  have hscale₂ : compositeWeight ξ q₂ (((q₁ * c₁ : ℕ) : ℤ) • x₂) =
      compositeWeight ξ q₂ x₂ := by
    apply compositeWeight_smul ξ q₂ _ x₂ hξ₂
    simpa only [Int.natAbs_natCast] using
      hcoprime.of_dvd_right (dvd_mul_right q₂ c₂)
  rw [hscale₁, hscale₂]

private theorem integralQuadraticValue_dvd_smul_iff
    (q n : ℕ) (hcoprime : n.Coprime q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℤ) :
    ((q : ℤ) ∣ integralQuadraticValue A ((n : ℤ) • x)) ↔
      (q : ℤ) ∣ integralQuadraticValue A x := by
  change ((q : ℤ) ∣ integralQuadraticValue A (fun i => (n : ℤ) * x i)) ↔ _
  rw [integralQuadraticValue_mul]
  have hcop : IsCoprime (q : ℤ) ((n : ℤ) ^ 2) := hcoprime.symm.isCoprime.pow_right
  exact ⟨hcop.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩

private theorem integralQuadraticValue_crt_cone
    (q₁ q₂ c₁ c₂ : ℕ)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x₁ x₂ : Fin 4 → ℤ) :
    (((q₁ * q₂ : ℕ) : ℤ) ∣ integralQuadraticValue A
      (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂)) ↔
      (q₁ : ℤ) ∣ integralQuadraticValue A x₁ ∧
      (q₂ : ℤ) ∣ integralQuadraticValue A x₂ := by
  have hqq : q₁.Coprime q₂ := hcoprime.of_dvd
    (dvd_mul_right q₁ c₁) (dvd_mul_right q₂ c₂)
  have hfirst := (integralQuadraticValue_dvd_congr q₁ A _ _
    (scaled_vector_congr_left q₁ q₂ c₁ c₂ x₁ x₂)).trans
    (integralQuadraticValue_dvd_smul_iff q₁ (q₂ * c₂)
      (hcoprime.symm.of_dvd_right (dvd_mul_right q₁ c₁)) A x₁)
  have hsecond := (integralQuadraticValue_dvd_congr q₂ A _ _
    (scaled_vector_congr_right q₁ q₂ c₁ c₂ x₁ x₂)).trans
    (integralQuadraticValue_dvd_smul_iff q₂ (q₁ * c₁)
      (hcoprime.of_dvd_right (dvd_mul_right q₂ c₂)) A x₂)
  rw [← hfirst, ← hsecond, Nat.cast_mul]
  constructor
  · intro h
    exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩
  · rintro ⟨h₁, h₂⟩
    exact hqq.isCoprime.mul_dvd h₁ h₂

/-- The source mixed summand factors in the actual scaled CRT coordinates.
The local unit parameters still carry the source factors `c₂ n₂` and `c₁ n₁`. -/
theorem mixedIntegerSummand_crt
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u x₁ x₂ : Fin 4 → ℤ) (a₁ a₂ : ℤ)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : PrimeWeightsInvariant ξ (q₁ * q₂)) :
    mixedIntegerSummand ξ (q₁ * q₂) (c₁ * c₂) A u
        ((c₂ : ℤ) * a₁ + (c₁ : ℤ) * a₂)
        (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) =
      mixedIntegerSummand ξ q₁ c₁ A u (((c₂ * (q₂ * c₂) : ℕ) : ℤ) * a₁) x₁ *
      mixedIntegerSummand ξ q₂ c₂ A u (((c₁ * (q₁ * c₁) : ℕ) : ℤ) * a₂) x₂ := by
  have hcone := integralQuadraticValue_crt_cone q₁ q₂ c₁ c₂ hcoprime A x₁ x₂
  have hweight := compositeWeight_crt_scaled ξ q₁ q₂ c₁ c₂ hcoprime hξ x₁ x₂
  by_cases hF₁ : (q₁ : ℤ) ∣ integralQuadraticValue A x₁
  · by_cases hF₂ : (q₂ : ℤ) ∣ integralQuadraticValue A x₂
    · have hF := hcone.mpr ⟨hF₁, hF₂⟩
      have hmod : (q₁ * q₂) * (c₁ * c₂) = (q₁ * c₁) * (q₂ * c₂) := by ring
      have hchar (z : ℤ) :
          ZMod.stdAddChar (N := (q₁ * q₂) * (c₁ * c₂))
              (z : ZMod ((q₁ * q₂) * (c₁ * c₂))) =
            ZMod.stdAddChar (N := (q₁ * c₁) * (q₂ * c₂))
              (z : ZMod ((q₁ * c₁) * (q₂ * c₂))) := by
        rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, hmod]
      have hphase : ZMod.stdAddChar (N := (q₁ * q₂) * (c₁ * c₂))
          ((((c₂ : ℤ) * a₁ + (c₁ : ℤ) * a₂) * integralQuadraticValue A
              (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) +
            dotProduct u (((q₂ * c₂ : ℕ) : ℤ) • x₁ +
              ((q₁ * c₁ : ℕ) : ℤ) • x₂) : ℤ) :
            ZMod ((q₁ * q₂) * (c₁ * c₂))) =
          ZMod.stdAddChar (N := q₁ * c₁)
            (((((c₂ * (q₂ * c₂) : ℕ) : ℤ) * a₁) * integralQuadraticValue A x₁ +
              dotProduct u x₁ : ℤ) : ZMod (q₁ * c₁)) *
          ZMod.stdAddChar (N := q₂ * c₂)
            (((((c₁ * (q₁ * c₁) : ℕ) : ℤ) * a₂) * integralQuadraticValue A x₂ +
              dotProduct u x₂ : ℤ) : ZMod (q₂ * c₂)) := by
        rw [hchar]
        simpa only [integralQuadraticValue, Nat.cast_mul] using
          mixedPhase_crt q₁ q₂ c₁ c₂ A x₁ x₂ u a₁ a₂ hF₁ hF₂
      simp only [mixedIntegerSummand, if_pos hF, if_pos hF₁, if_pos hF₂, hweight, hphase]
      ring
    · have hF : ¬ ((q₁ * q₂ : ℕ) : ℤ) ∣ integralQuadraticValue A
          (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) :=
        fun h => hF₂ (hcone.mp h).2
      simp only [mixedIntegerSummand, if_neg hF, if_pos hF₁, if_neg hF₂, mul_zero]
  · have hF : ¬ ((q₁ * q₂ : ℕ) : ℤ) ∣ integralQuadraticValue A
        (((q₂ * c₂ : ℕ) : ℤ) • x₁ + ((q₁ * c₁ : ℕ) : ℤ) • x₂) :=
      fun h => hF₁ (hcone.mp h).1
    simp only [mixedIntegerSummand, if_neg hF, if_neg hF₁, zero_mul]

private def mixedCRTVector (q₁ q₂ c₁ c₂ : ℕ)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂)) :
    (Fin 4 → ZMod (q₁ * c₁)) × (Fin 4 → ZMod (q₂ * c₂)) ≃
      (Fin 4 → ZMod ((q₁ * q₂) * (c₁ * c₂))) :=
  (scaledChineseRemainderVector (Fin 4) (q₁ * c₁) (q₂ * c₂) hcoprime).trans
    (Equiv.piCongrRight fun _ =>
      (ZMod.ringEquivCongr (show (q₁ * c₁) * (q₂ * c₂) =
        (q₁ * q₂) * (c₁ * c₂) by ring)).toEquiv)

private theorem mixedCRTVector_lift
    (q₁ q₂ c₁ c₂ : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (x₁ : Fin 4 → ZMod (q₁ * c₁)) (x₂ : Fin 4 → ZMod (q₂ * c₂)) (i : Fin 4) :
    (residueLift ((q₁ * q₂) * (c₁ * c₂))
        (mixedCRTVector q₁ q₂ c₁ c₂ hcoprime (x₁, x₂)) i :
      ZMod ((q₁ * q₂) * (c₁ * c₂))) =
      ((((q₂ * c₂ : ℕ) : ℤ) • residueLift (q₁ * c₁) x₁ +
        ((q₁ * c₁ : ℕ) : ℤ) • residueLift (q₂ * c₂) x₂) i :
      ZMod ((q₁ * q₂) * (c₁ * c₂))) := by
  rw [residueLift_cast]
  change ZMod.ringEquivCongr _
    (scaledChineseRemainder (q₁ * c₁) (q₂ * c₂) hcoprime (x₁ i, x₂ i)) =
      ((((q₂ * c₂ : ℕ) : ℤ) * residueLift (q₁ * c₁) x₁ i +
        ((q₁ * c₁ : ℕ) : ℤ) * residueLift (q₂ * c₂) x₂ i : ℤ) :
        ZMod ((q₁ * q₂) * (c₁ * c₂)))
  rw [← residueLift_cast (q₁ * c₁) x₁ i, ← residueLift_cast (q₂ * c₂) x₂ i,
    scaledChineseRemainder_intCast, ZMod.ringEquivCongr_intCast]

private theorem scaledCRTUnits_lift
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hcoprime : c₁.Coprime c₂)
    (a₁ : (ZMod c₁)ˣ) (a₂ : (ZMod c₂)ˣ) :
    (((scaledChineseRemainderUnits c₁ c₂ hcoprime (a₁, a₂) :
        ZMod (c₁ * c₂)).val : ℤ) : ZMod (c₁ * c₂)) =
      (((c₂ : ℤ) * ((a₁ : ZMod c₁).val : ℤ) +
        (c₁ : ℤ) * ((a₂ : ZMod c₂).val : ℤ) : ℤ) : ZMod (c₁ * c₂)) := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
    scaledChineseRemainderUnits_apply c₁ c₂ hcoprime a₁ a₂

private theorem mixedCompleteSum_scaled_unit
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (r : ℕ) (hr : r.Coprime c) :
    (∑ a : (ZMod c)ˣ, ∑ x : Fin 4 → ZMod (q * c),
      mixedIntegerSummand ξ q c A u ((r : ℤ) * ((a : ZMod c).val : ℤ))
        (residueLift (q * c) x)) = mixedCompleteSum ξ q c A u := by
  let v := ZMod.unitOfCoprime r hr
  calc
    _ = ∑ a : (ZMod c)ˣ, ∑ x : Fin 4 → ZMod (q * c),
        mixedIntegerSummand ξ q c A u (((v * a : (ZMod c)ˣ) : ZMod c).val : ℤ)
          (residueLift (q * c) x) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      apply mixedIntegerSummand_a_congr ξ q c A u (residueLift (q * c) x)
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
        Units.val_mul, v, ZMod.coe_unitOfCoprime]
    _ = mixedCompleteSum ξ q c A u := by
      exact Equiv.sum_comp (Equiv.mulLeft v) (fun a : (ZMod c)ˣ =>
        ∑ x : Fin 4 → ZMod (q * c),
          mixedIntegerSummand ξ q c A u ((a : ZMod c).val : ℤ)
            (residueLift (q * c) x))

/-- Full CRT multiplicativity of the actual mixed complete sum.
Only scalar invariance at primes dividing `q₁*q₂` is assumed. -/
theorem mixedCompleteSum_crt
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ c₁ c₂ : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (hcoprime : (q₁ * c₁).Coprime (q₂ * c₂))
    (hξ : PrimeWeightsInvariant ξ (q₁ * q₂)) :
    mixedCompleteSum ξ (q₁ * q₂) (c₁ * c₂) A u =
      mixedCompleteSum ξ q₁ c₁ A u * mixedCompleteSum ξ q₂ c₂ A u := by
  have hcc : c₁.Coprime c₂ := hcoprime.of_dvd
    (dvd_mul_left c₁ q₁) (dvd_mul_left c₂ q₂)
  have hr₁ : (c₂ * (q₂ * c₂)).Coprime c₁ := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcc.symm, hcoprime.symm.of_dvd_right (dvd_mul_left c₁ q₁)⟩
  have hr₂ : (c₁ * (q₁ * c₁)).Coprime c₂ := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcc, hcoprime.of_dvd_right (dvd_mul_left c₂ q₂)⟩
  let eA := scaledChineseRemainderUnits c₁ c₂ hcc
  let eX := mixedCRTVector q₁ q₂ c₁ c₂ hcoprime
  let H (a : (ZMod (c₁ * c₂))ˣ) (x : Fin 4 → ZMod ((q₁ * q₂) * (c₁ * c₂))) :=
    mixedIntegerSummand ξ (q₁ * q₂) (c₁ * c₂) A u ((a : ZMod (c₁ * c₂)).val : ℤ)
      (residueLift ((q₁ * q₂) * (c₁ * c₂)) x)
  let K₁ (a : (ZMod c₁)ˣ) (x : Fin 4 → ZMod (q₁ * c₁)) :=
    mixedIntegerSummand ξ q₁ c₁ A u
      (((c₂ * (q₂ * c₂) : ℕ) : ℤ) * ((a : ZMod c₁).val : ℤ))
      (residueLift (q₁ * c₁) x)
  let K₂ (a : (ZMod c₂)ˣ) (x : Fin 4 → ZMod (q₂ * c₂)) :=
    mixedIntegerSummand ξ q₂ c₂ A u
      (((c₁ * (q₁ * c₁) : ℕ) : ℤ) * ((a : ZMod c₂).val : ℤ))
      (residueLift (q₂ * c₂) x)
  have hterm (a₁ : (ZMod c₁)ˣ) (a₂ : (ZMod c₂)ˣ)
      (x₁ : Fin 4 → ZMod (q₁ * c₁)) (x₂ : Fin 4 → ZMod (q₂ * c₂)) :
      H (eA (a₁, a₂)) (eX (x₁, x₂)) = K₁ a₁ x₁ * K₂ a₂ x₂ := by
    apply (mixedIntegerSummand_congr ξ (q₁ * q₂) (c₁ * c₂) A u
      (((eA (a₁, a₂) : (ZMod (c₁ * c₂))ˣ) : ZMod (c₁ * c₂)).val : ℤ)
      ((c₂ : ℤ) * ((a₁ : ZMod c₁).val : ℤ) +
        (c₁ : ℤ) * ((a₂ : ZMod c₂).val : ℤ))
      (residueLift ((q₁ * q₂) * (c₁ * c₂)) (eX (x₁, x₂)))
      (((q₂ * c₂ : ℕ) : ℤ) • residueLift (q₁ * c₁) x₁ +
        ((q₁ * c₁ : ℕ) : ℤ) • residueLift (q₂ * c₂) x₂)
      (scaledCRTUnits_lift c₁ c₂ hcc a₁ a₂)
      (mixedCRTVector_lift q₁ q₂ c₁ c₂ hcoprime x₁ x₂)).trans
    exact mixedIntegerSummand_crt ξ q₁ q₂ c₁ c₂ A u
      (residueLift (q₁ * c₁) x₁) (residueLift (q₂ * c₂) x₂)
      ((a₁ : ZMod c₁).val : ℤ) ((a₂ : ZMod c₂).val : ℤ) hcoprime hξ
  calc
    mixedCompleteSum ξ (q₁ * q₂) (c₁ * c₂) A u =
        ∑ a : (ZMod c₁)ˣ × (ZMod c₂)ˣ,
          ∑ x : (Fin 4 → ZMod (q₁ * c₁)) × (Fin 4 → ZMod (q₂ * c₂)),
            H (eA a) (eX x) := by
      change (∑ a, ∑ x, H a x) = _
      rw [← eA.sum_comp (fun a => ∑ x, H a x)]
      apply Finset.sum_congr rfl
      intro a _
      exact (eX.sum_comp (fun x => H (eA a) x)).symm
    _ = (∑ a : (ZMod c₁)ˣ, ∑ x : Fin 4 → ZMod (q₁ * c₁), K₁ a x) *
        (∑ a : (ZMod c₂)ˣ, ∑ x : Fin 4 → ZMod (q₂ * c₂), K₂ a x) := by
      simp only [Fintype.sum_prod_type]
      simp_rw [hterm, ← Finset.sum_mul_sum]
    _ = mixedCompleteSum ξ q₁ c₁ A u * mixedCompleteSum ξ q₂ c₂ A u := by
      exact congrArg₂ (fun z w : ℂ => z * w)
        (mixedCompleteSum_scaled_unit ξ q₁ c₁ A u (c₂ * (q₂ * c₂)) hr₁)
        (mixedCompleteSum_scaled_unit ξ q₂ c₂ A u (c₁ * (q₁ * c₁)) hr₂)

end QuaternaryQuadraticForms
