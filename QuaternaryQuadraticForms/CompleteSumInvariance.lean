import QuaternaryQuadraticForms.CompleteSums
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Unit-frequency invariance of the actual mixed complete sum

The changes of variables are the source changes `x ↦ t⁻¹ x` and
`a ↦ t² a`, made as bijections of the actual residue vector and unit sets.
No nonzero integer assumption is used, so modulus one is included.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Inverse scalar representatives give the exact source change of variables
in the complete-sum summand. -/
theorem mixedIntegerSummand_inverse_scale
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u x : Fin 4 → ℤ)
    (a t s : ℤ) (hξ : PrimeWeightsInvariant ξ q)
    (hts : ((t * s : ℤ) : ZMod (q * c)) = 1) :
    mixedIntegerSummand ξ q c A (fun i => t * u i) (t ^ 2 * a)
        (fun i => s * x i) =
      mixedIntegerSummand ξ q c A u a x := by
  have htsq : (t : ZMod q) * (s : ZMod q) = 1 := by
    have h := congrArg (ZMod.castHom (dvd_mul_right q c) (ZMod q)) hts
    simpa only [map_intCast, map_one, map_mul, Int.cast_mul] using h
  have hsunit : IsUnit (s : ZMod q) := by
    refine ⟨⟨(s : ZMod q), (t : ZMod q), ?_, htsq⟩, rfl⟩
    simpa only [mul_comm] using htsq
  have hdiv : ((q : ℤ) ∣ integralQuadraticValue A (fun i => s * x i)) ↔
      (q : ℤ) ∣ integralQuadraticValue A x := by
    rw [integralQuadraticValue_mul,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact (hsunit.pow 2).mul_right_eq_zero
  have hw := compositeWeight_smul_of_isUnit ξ q s x hξ hsunit
  have hd : dotProduct (fun i => t * u i) (fun i => s * x i) =
      (t * s) * dotProduct u x := by
    change dotProduct (t • u) (s • x) = _
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hphase :
      (((t ^ 2 * a) * integralQuadraticValue A (fun i => s * x i) +
        dotProduct (fun i => t * u i) (fun i => s * x i) : ℤ) : ZMod (q * c)) =
      ((a * integralQuadraticValue A x + dotProduct u x : ℤ) : ZMod (q * c)) := by
    rw [integralQuadraticValue_mul, hd]
    have ht : (t : ZMod (q * c)) * (s : ZMod (q * c)) = 1 := by
      simpa only [Int.cast_mul] using hts
    push_cast
    calc
      _ = ((t : ZMod (q * c)) * (s : ZMod (q * c))) ^ 2 *
          (a : ZMod (q * c)) * (integralQuadraticValue A x : ZMod (q * c)) +
          ((t : ZMod (q * c)) * (s : ZMod (q * c))) *
            ((dotProduct u x : ℤ) : ZMod (q * c)) := by ring
      _ = _ := by rw [ht]; simp
  unfold mixedIntegerSummand
  by_cases hx : (q : ℤ) ∣ integralQuadraticValue A x
  · simp only [if_pos hx, if_pos (hdiv.mpr hx), hw, hphase]
  · simp only [if_neg hx, if_neg (fun h => hx (hdiv.mp h))]

/-- Invariance under any integer scalar that is a unit modulo `q*c`.
The proof uses bijections of the literal unit and vector summation sets. -/
theorem mixedCompleteSum_isUnit_frequency
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (t : ℤ)
    (hξ : PrimeWeightsInvariant ξ q) (ht : IsUnit (t : ZMod (q * c))) :
    mixedCompleteSum ξ q c A (fun i => t * u i) = mixedCompleteSum ξ q c A u := by
  classical
  let v : (ZMod (q * c))ˣ := ht.unit
  have hv : (v : ZMod (q * c)) = (t : ZMod (q * c)) := ht.unit_spec
  let s : ℤ := ((v⁻¹ : (ZMod (q * c))ˣ) : ZMod (q * c)).val
  have hs : (s : ZMod (q * c)) = ((v⁻¹ : (ZMod (q * c))ˣ) : ZMod (q * c)) := by
    simp only [s, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hts : ((t * s : ℤ) : ZMod (q * c)) = 1 := by
    rw [Int.cast_mul, hs, ← hv]
    exact v.val_inv
  let vc : (ZMod c)ˣ := Units.map
    (ZMod.castHom (dvd_mul_left c q) (ZMod c)).toMonoidHom v
  have hvc : (vc : ZMod c) = (t : ZMod c) := by
    change ZMod.castHom (dvd_mul_left c q) (ZMod c) (v : ZMod (q * c)) = _
    rw [hv, map_intCast]
  let ea : Equiv.Perm (ZMod c)ˣ := Equiv.mulLeft (vc ^ 2)
  let ex : Equiv.Perm (Fin 4 → ZMod (q * c)) :=
    Equiv.piCongrRight (fun _ => (v⁻¹).mulLeft)
  have ha (a : (ZMod c)ˣ) :
      (((((ea a : (ZMod c)ˣ) : ZMod c).val : ℕ) : ℤ) : ZMod c) =
        ((t ^ 2 * (((a : ZMod c).val : ℕ) : ℤ) : ℤ) : ZMod c) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul, Int.cast_pow]
    change ((vc ^ 2 * a : (ZMod c)ˣ) : ZMod c) = _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hvc]
  have hx (x : Fin 4 → ZMod (q * c)) (i : Fin 4) :
      (residueLift (q * c) (ex x) i : ZMod (q * c)) =
        ((s * residueLift (q * c) x i : ℤ) : ZMod (q * c)) := by
    rw [residueLift_cast, Int.cast_mul, residueLift_cast, hs]
    rfl
  unfold mixedCompleteSum
  calc
    _ = ∑ a : (ZMod c)ˣ, ∑ x : Fin 4 → ZMod (q * c),
        mixedIntegerSummand ξ q c A (fun i => t * u i)
          (((((ea a : (ZMod c)ˣ) : ZMod c).val : ℕ) : ℤ))
          (residueLift (q * c) (ex x)) := by
      symm
      let f (a : (ZMod c)ˣ) (x : Fin 4 → ZMod (q * c)) : ℂ :=
        mixedIntegerSummand ξ q c A (fun i => t * u i)
          (((a : ZMod c).val : ℕ) : ℤ) (residueLift (q * c) x)
      exact Fintype.sum_equiv ea (fun a => ∑ x, f (ea a) (ex x))
        (fun a => ∑ x, f a x) (fun a => Equiv.sum_comp ex (fun x => f (ea a) x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      rw [mixedIntegerSummand_congr ξ q c A (fun i => t * u i)
        _ (t ^ 2 * (((a : ZMod c).val : ℕ) : ℤ))
        _ (fun i => s * residueLift (q * c) x i) (ha a) (hx x)]
      exact mixedIntegerSummand_inverse_scale ξ q c A u (residueLift (q * c) x)
        (((a : ZMod c).val : ℕ) : ℤ) t s hξ hts

/-- The second assertion of Lemma 3.1, under the literal integer gcd condition. -/
theorem mixedCompleteSum_unit_frequency
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) (t : ℤ)
    (hξ : PrimeWeightsInvariant ξ q) (ht : t.gcd ((q * c : ℕ) : ℤ) = 1) :
    mixedCompleteSum ξ q c A (fun i => t * u i) = mixedCompleteSum ξ q c A u := by
  apply mixedCompleteSum_isUnit_frequency ξ q c A u t hξ
  exact (ZMod.coe_int_isUnit_iff_isCoprime t (q * c)).mpr
    (Int.isCoprime_iff_gcd_eq_one.mpr ht).symm

end QuaternaryQuadraticForms
