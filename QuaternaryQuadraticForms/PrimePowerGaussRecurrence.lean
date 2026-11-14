import QuaternaryQuadraticForms.PrimePowerResidues
import QuaternaryQuadraticForms.IntegralGaussSums
import QuaternaryQuadraticForms.FourierOrthogonality

/-!
# The prime-power quadratic Gauss recurrence

Actual residue digits and additive orthogonality prove the recurrence for
the integral matrix quadratic form. The middle modulus can be any positive
integer; taking it to be `p^k` gives the source recurrence, including `k=0`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Orthogonality of the standard character in all four coordinates. -/
theorem stdAddChar_vector_orthogonality (p : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod p) :
    (∑ z : Fin 4 → ZMod p, ZMod.stdAddChar (dotProduct c z)) =
      if c = 0 then (p : ℂ) ^ 4 else 0 := by
  classical
  have hsum :
      (∑ z : Fin 4 → ZMod p, ZMod.stdAddChar (dotProduct c z)) =
        ∏ i : Fin 4, (if c i = 0 then (p : ℂ) else 0) := by
    simp_rw [dotProduct, stdAddChar_sum]
    rw [← Fintype.prod_sum (fun (i : Fin 4) (z : ZMod p) => ZMod.stdAddChar (c i * z))]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [mul_comm] using stdAddChar_orthogonality p (c i)
  rw [hsum]
  by_cases hc : c = 0
  · subst c
    simp
  · rw [if_neg hc]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    change c i ≠ 0 at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Nonsingularity makes the bilinear digit sum select precisely the zero vector. -/
theorem matrix_bilinear_character_sum (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (a : ZMod p)
    (hdet : A.det ≠ 0) (h2 : (2 : ZMod p) ≠ 0) (ha : a ≠ 0)
    (r : Fin 4 → ZMod p) :
    (∑ z : Fin 4 → ZMod p,
      ZMod.stdAddChar (2 * a * dotProduct r (A.mulVec z))) =
      if r = 0 then (p : ℂ) ^ 4 else 0 := by
  let c : Fin 4 → ZMod p := (2 * a) • Matrix.vecMul r A
  have hphase (z : Fin 4 → ZMod p) :
      2 * a * dotProduct r (A.mulVec z) = dotProduct c z := by
    rw [Matrix.dotProduct_mulVec]
    exact (smul_dotProduct (2 * a) (Matrix.vecMul r A) z).symm
  simp_rw [hphase]
  rw [stdAddChar_vector_orthogonality]
  have hc : c = 0 ↔ r = 0 := by
    constructor
    · intro hc
      apply Matrix.eq_zero_of_vecMul_eq_zero hdet
      funext i
      have hi : (2 * a) * Matrix.vecMul r A i = 0 := by
        simpa only [c, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hc i
      exact (mul_eq_zero.mp hi).resolve_left (mul_ne_zero h2 ha)
    · intro hr
      subst r
      simp [c]
  simp only [hc]

private theorem integralPureGauss_eq_lift (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) :
    integralQuadraticGaussSum n A a 0 =
      ∑ x : Fin 4 → ZMod n,
        ZMod.stdAddChar ((a * integralQuadraticValue A (residueLift n x) : ℤ) : ZMod n) := by
  simpa only [zero_dotProduct, add_zero] using
    integralQuadraticGaussSum_eq_lift_sum n A a 0

private theorem integralQuadraticValue_add_symmetric
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (x y : Fin 4 → ℤ) :
    integralQuadraticValue A (x + y) = integralQuadraticValue A x +
      2 * dotProduct x (A.mulVec y) + integralQuadraticValue A y := by
  have hcross : dotProduct y (A.mulVec x) = dotProduct x (A.mulVec y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  simp only [integralQuadraticValue, Matrix.mulVec_add, add_dotProduct,
    dotProduct_add]
  rw [hcross]
  ring

/-- The three-digit quadratic phase retains exactly its linear outer-digit term. -/
theorem primeSquare_digit_phase_intCast (p m : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (r w z : Fin 4 → ℤ) :
    ((a * integralQuadraticValue A
      (fun i => r i + (p : ℤ) * (w i + (m : ℤ) * z i)) : ℤ) : ZMod (p * (m * p))) =
      ((a * integralQuadraticValue A (fun i => r i + (p : ℤ) * w i) +
        ((m : ℤ) * p) * (2 * a * dotProduct r (A.mulVec z)) : ℤ) : ZMod (p * (m * p))) := by
  have hvec : (fun i => r i + (p : ℤ) * (w i + (m : ℤ) * z i)) =
      (r + (p : ℤ) • w) + ((p : ℤ) * m) • z := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbase : (fun i => r i + (p : ℤ) * w i) = r + (p : ℤ) • w := rfl
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨-(a * (2 * dotProduct w (A.mulVec z) + (m : ℤ) * integralQuadraticValue A z)), ?_⟩
  rw [hvec, hbase,
    integralQuadraticValue_add_symmetric A hA (r + (p : ℤ) • w) (((p : ℤ) * m) • z)]
  rw [show integralQuadraticValue A (((p : ℤ) * m) • z) =
      ((p : ℤ) * m) ^ 2 * integralQuadraticValue A z from
        integralQuadraticValue_mul A ((p : ℤ) * m) z]
  simp only [Matrix.mulVec_smul, dotProduct_smul, add_dotProduct,
    smul_dotProduct, smul_eq_mul, Nat.cast_mul]
  ring

/-- The actual standard character splits into a middle phase and a prime-field digit phase. -/
theorem primeSquare_digit_phase (p m : ℕ) [NeZero p] [NeZero m]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (r w z : Fin 4 → ℤ) :
    ZMod.stdAddChar (N := p * (m * p))
      ((a * integralQuadraticValue A
        (fun i => r i + (p : ℤ) * (w i + (m : ℤ) * z i)) : ℤ) : ZMod (p * (m * p))) =
      ZMod.stdAddChar (N := p * (m * p))
        ((a * integralQuadraticValue A (fun i => r i + (p : ℤ) * w i) : ℤ) : ZMod (p * (m * p))) *
      ZMod.stdAddChar (N := p)
        ((2 * a * dotProduct r (A.mulVec z) : ℤ) : ZMod p) := by
  rw [primeSquare_digit_phase_intCast p m A hA a r w z,
    Int.cast_add, AddChar.map_add_eq_mul]
  congr 1
  simpa only [Nat.cast_mul] using stdAddChar_mul_modulus p (m * p)
    (2 * a * dotProduct r (A.mulVec z))

/-- The outer digit vanishes by orthogonality unless the low digit is zero. -/
theorem primeSquare_digit_orthogonality (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ)
    (hdet : ¬(p : ℤ) ∣ A.det) (ha : ¬(p : ℤ) ∣ a) (r : Fin 4 → ZMod p) :
    (∑ z : Fin 4 → ZMod p,
      ZMod.stdAddChar (N := p)
        ((2 * a * dotProduct (residueLift p r) (A.mulVec (residueLift p z)) : ℤ) : ZMod p)) =
      if r = 0 then (p : ℂ) ^ 4 else 0 := by
  have hdet' : (A.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    intro hz
    have hcast : (A.det : ZMod p) = 0 :=
      ((Int.castRingHom (ZMod p)).map_det A).trans hz
    exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast)
  have ha' : (a : ZMod p) ≠ 0 :=
    fun hz => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
  have hphase (z : Fin 4 → ZMod p) :
      ((2 * a * dotProduct (residueLift p r) (A.mulVec (residueLift p z)) : ℤ) : ZMod p) =
        2 * (a : ZMod p) * dotProduct r ((A.map (Int.castRingHom (ZMod p))).mulVec z) := by
    simp [dotProduct, Matrix.mulVec, residueLift]
  simp_rw [hphase]
  exact matrix_bilinear_character_sum p _ (a : ZMod p) hdet' h2 ha' r

private theorem primeSquare_zero_digit_phase (p m : ℕ) [NeZero p] [NeZero m]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (w : Fin 4 → ℤ) :
    ZMod.stdAddChar (N := p * (m * p))
      ((a * integralQuadraticValue A (fun i => (p : ℤ) * w i) : ℤ) : ZMod (p * (m * p))) =
      ZMod.stdAddChar (N := m) ((a * integralQuadraticValue A w : ℤ) : ZMod m) := by
  rw [integralQuadraticValue_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp

/-- Removing two good-prime factors gives the actual quadratic Gauss recurrence.
The middle modulus is arbitrary and positive, and may itself be divisible by `p`. -/
theorem integralQuadraticGaussSum_primeSquare_mul (p m : ℕ)
    [Fact p.Prime] [NeZero m] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (a : ℤ)
    (hdet : ¬(p : ℤ) ∣ A.det) (ha : ¬(p : ℤ) ∣ a) :
    integralQuadraticGaussSum (p * (m * p)) A a 0 =
      (p : ℂ) ^ 4 * integralQuadraticGaussSum m A a 0 := by
  classical
  rw [integralPureGauss_eq_lift,
    sum_residueLift_three_digits p m (fun x => ZMod.stdAddChar (N := p * (m * p))
      ((a * integralQuadraticValue A x : ℤ) : ZMod (p * (m * p))))]
  simp_rw [primeSquare_digit_phase p m A hA a, ← Finset.mul_sum,
    primeSquare_digit_orthogonality p hp A a hdet ha]
  rw [Finset.sum_eq_single (0 : Fin 4 → ZMod p)]
  · rw [integralPureGauss_eq_lift, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hz : residueLift p (0 : Fin 4 → ZMod p) = 0 := by
      funext i
      simp [residueLift]
    rw [hz]
    simp only [Pi.zero_apply, zero_add, ite_true]
    rw [primeSquare_zero_digit_phase p m A a]
    ring
  · intro r _ hr
    simp [hr]
  · simp

private theorem integralGauss_congr_modulus (m n : ℕ) [NeZero m] [NeZero n]
    (h : m = n) (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) :
    integralQuadraticGaussSum m A a u = integralQuadraticGaussSum n A a u := by
  subst n
  rfl

/-- The manuscript's recurrence `V_(k+2)=p^4 V_k`, including the base modulus `p^0=1`. -/
theorem integralQuadraticGaussSum_primePower_recurrence (p k : ℕ)
    [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (a : ℤ)
    (hdet : ¬(p : ℤ) ∣ A.det) (ha : ¬(p : ℤ) ∣ a) :
    integralQuadraticGaussSum (p ^ (k + 2)) A a 0 =
      (p : ℂ) ^ 4 * integralQuadraticGaussSum (p ^ k) A a 0 := by
  have hmod : p ^ (k + 2) = p * (p ^ k * p) := by
    rw [pow_add, pow_two]
    ring
  exact (integralGauss_congr_modulus _ _ hmod A a 0).trans
    (integralQuadraticGaussSum_primeSquare_mul p (p ^ k) hp A hA a hdet ha)

end QuaternaryQuadraticForms
