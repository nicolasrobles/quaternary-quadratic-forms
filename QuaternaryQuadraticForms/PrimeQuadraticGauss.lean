import QuaternaryQuadraticForms.QuadraticCharacter
import QuaternaryQuadraticForms.FiniteCharacters
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Prime-field quadratic Gauss identities

The Gauss sum uses the actual complex quadratic character and standard
additive character. Mathlib's proved Gauss-sum identities give its square
and nonvanishing. Counting square roots and translating the finite sum
then give the complete one-dimensional quadratic exponential sum used in
the proof of Lemma 4.6, including a zero quadratic coefficient.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The manuscript's quadratic Gauss sum over the prime field. -/
def primeQuadraticGauss (p : ℕ) [Fact p.Prime] : ℂ :=
  gaussSum (complexQuadraticChar p) (ZMod.stdAddChar (N := p))

/-- The literal one-dimensional quadratic exponential sum. -/
def primeQuadraticExponentialSum (p : ℕ) [Fact p.Prime]
    (c w : ZMod p) : ℂ :=
  ∑ y : ZMod p, ZMod.stdAddChar (c * y ^ 2 + w * y)

/-- A nonzero argument has quadratic-character square equal to one. -/
theorem complexQuadraticChar_sq_apply (p : ℕ) [Fact p.Prime]
    (x : ZMod p) (hx : x ≠ 0) : complexQuadraticChar p x ^ 2 = 1 := by
  change (quadraticChar (ZMod p) x : ℂ) ^ 2 = 1
  exact_mod_cast quadraticChar_sq_one hx

/-- The actual quadratic Gauss sum is nonzero at every odd prime. -/
theorem primeQuadraticGauss_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeQuadraticGauss p ≠ 0 := by
  apply gaussSum_ne_zero_of_nontrivial
    (R := ZMod p) (R' := ℂ) _ (complexQuadraticChar_ne_one p hp)
    (ZMod.isPrimitive_stdAddChar p)
  simpa only [ZMod.card, Nat.cast_ne_zero] using (Fact.out : p.Prime).ne_zero

/-- The square identity for the actual quadratic Gauss sum. -/
theorem primeQuadraticGauss_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeQuadraticGauss p ^ 2 = complexQuadraticChar p (-1) * (p : ℂ) := by
  simpa only [primeQuadraticGauss, ZMod.card] using
    gaussSum_sq (complexQuadraticChar_ne_one p hp)
      (complexQuadraticChar_isQuadratic p) (ZMod.isPrimitive_stdAddChar p)

/-- The fourth power is `p²`, with no choice of a square root of `p`. -/
theorem primeQuadraticGauss_fourth (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    primeQuadraticGauss p ^ 4 = (p : ℂ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, primeQuadraticGauss_sq p hp,
    mul_pow, complexQuadraticChar_sq_apply p (-1) (neg_ne_zero.mpr one_ne_zero), one_mul]

/-- Quadratic Gauss inversion at every frequency, including zero. -/
theorem primeQuadraticGauss_inversion (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (m : ZMod p) :
    (∑ s : ZMod p, complexQuadraticChar p s * ZMod.stdAddChar (s * m)) =
      complexQuadraticChar p m * primeQuadraticGauss p := by
  by_cases hm : m = 0
  · subst m
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, zero_mul]
    exact MulChar.sum_eq_zero_of_ne_one (complexQuadraticChar_ne_one p hp)
  · have hshift := gaussSum_mulShift (complexQuadraticChar p)
      (ZMod.stdAddChar (N := p)) (Units.mk0 m hm)
    have hidentity :
        complexQuadraticChar p m *
          (∑ s : ZMod p, complexQuadraticChar p s * ZMod.stdAddChar (s * m)) =
        primeQuadraticGauss p := by
      simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0,
        primeQuadraticGauss, mul_comm] using hshift
    calc
      (∑ s : ZMod p, complexQuadraticChar p s * ZMod.stdAddChar (s * m)) =
          (complexQuadraticChar p m * complexQuadraticChar p m) *
            (∑ s : ZMod p, complexQuadraticChar p s * ZMod.stdAddChar (s * m)) := by
        rw [← pow_two, complexQuadraticChar_sq_apply p m hm, one_mul]
      _ = complexQuadraticChar p m * primeQuadraticGauss p := by
        rw [mul_assoc, hidentity]

/-- Removing the zero term gives the same inversion identity over units. -/
theorem primeQuadraticGauss_units_inversion (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (m : ZMod p) :
    (∑ s : (ZMod p)ˣ,
      complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar ((s : ZMod p) * m)) =
      complexQuadraticChar p m * primeQuadraticGauss p := by
  classical
  have hsplit :
      (∑ s : ZMod p, complexQuadraticChar p s * ZMod.stdAddChar (s * m)) =
        ∑ s : (ZMod p)ˣ,
          complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar ((s : ZMod p) * m) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun s : ZMod p => complexQuadraticChar p s * ZMod.stdAddChar (s * m)) 0]
    simp only [MulChar.map_zero, zero_mul, zero_add]
    exact (Equiv.sum_comp unitsEquivNeZero
      (fun s : {s : ZMod p // s ≠ 0} =>
        complexQuadraticChar p s.val * ZMod.stdAddChar (s.val * m))).symm
  rw [← hsplit]
  exact primeQuadraticGauss_inversion p hp m

/-- Inversion permutes the nonzero scalars and leaves the quadratic
character unchanged, giving the reciprocal phase used in the pencil sum. -/
theorem primeQuadraticGauss_units_div_inversion (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (m : ZMod p) :
    (∑ s : (ZMod p)ˣ,
      complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar (m / (s : ZMod p))) =
      complexQuadraticChar p m * primeQuadraticGauss p := by
  have hchar (x : ZMod p) :
      complexQuadraticChar p x⁻¹ = complexQuadraticChar p x := by
    rw [← MulChar.inv_apply', (complexQuadraticChar_isQuadratic p).inv]
  calc
    (∑ s : (ZMod p)ˣ,
        complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar (m / (s : ZMod p))) =
      ∑ s : (ZMod p)ˣ,
        complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar ((s : ZMod p) * m) := by
      simpa only [Equiv.inv_apply, Units.val_inv_eq_inv_val, hchar,
        div_eq_mul_inv, mul_comm] using
        Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
          (fun s : (ZMod p)ˣ =>
            complexQuadraticChar p (s : ZMod p) * ZMod.stdAddChar ((s : ZMod p) * m))
    _ = complexQuadraticChar p m * primeQuadraticGauss p :=
      primeQuadraticGauss_units_inversion p hp m

/-- The zero-quadratic-coefficient case is exact additive orthogonality. -/
theorem primeQuadraticExponentialSum_zero (p : ℕ) [Fact p.Prime]
    (w : ZMod p) :
    primeQuadraticExponentialSum p 0 w = if w = 0 then (p : ℂ) else 0 := by
  unfold primeQuadraticExponentialSum
  simp only [zero_mul, zero_add]
  simpa only [mul_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift w (ZMod.isPrimitive_stdAddChar p)

/-- Counting the square roots of each field element gives the exact
unshifted quadratic exponential sum for a nonzero quadratic coefficient. -/
theorem primeQuadraticExponentialSum_unshifted (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (c : ZMod p) (hc : c ≠ 0) :
    (∑ y : ZMod p, ZMod.stdAddChar (c * y ^ 2)) =
      complexQuadraticChar p c * primeQuadraticGauss p := by
  classical
  have hroots (t : ZMod p) :
      ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = t)).card : ℂ) =
        complexQuadraticChar p t + 1 := by
    have hcount :
        ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = t)).card : ℤ) =
          quadraticChar (ZMod p) t + 1 := by
      simpa only [Set.toFinset_setOf] using
        quadraticChar_card_sqrts ((ZMod.ringChar_zmod_n p).substr hp) t
    change ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = t)).card : ℂ) =
      (quadraticChar (ZMod p) t : ℂ) + 1
    exact_mod_cast hcount
  have hlinear : (∑ t : ZMod p, ZMod.stdAddChar (c * t)) = 0 := by
    simpa only [mul_comm, if_neg hc, Nat.cast_zero] using
      AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar p)
  have hinversion :
      (∑ t : ZMod p, complexQuadraticChar p t * ZMod.stdAddChar (c * t)) =
        complexQuadraticChar p c * primeQuadraticGauss p := by
    simpa only [mul_comm] using primeQuadraticGauss_inversion p hp c
  calc
    (∑ y : ZMod p, ZMod.stdAddChar (c * y ^ 2)) =
        ∑ t : ZMod p,
          ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = t)).card : ℂ) *
            ZMod.stdAddChar (c * t) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_fiberwise' (Finset.univ : Finset (ZMod p))
          (fun y : ZMod p => y ^ 2) (fun t => ZMod.stdAddChar (c * t))).symm
    _ = ∑ t : ZMod p,
        (complexQuadraticChar p t + 1) * ZMod.stdAddChar (c * t) := by
      simp_rw [hroots]
    _ = (∑ t : ZMod p, complexQuadraticChar p t * ZMod.stdAddChar (c * t)) +
        ∑ t : ZMod p, ZMod.stdAddChar (c * t) := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
    _ = complexQuadraticChar p c * primeQuadraticGauss p := by
      rw [hinversion, hlinear, add_zero]

/-- Completing the square in the actual finite sum gives the exact formula
for every nonzero quadratic coefficient and every linear coefficient. -/
theorem primeQuadraticExponentialSum_of_ne_zero (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (c w : ZMod p) (hc : c ≠ 0) :
    primeQuadraticExponentialSum p c w =
      complexQuadraticChar p c * primeQuadraticGauss p *
        ZMod.stdAddChar (-(w ^ 2) / (4 * c)) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp)
  have h4 : (4 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have hshift (y : ZMod p) :
      c * y ^ 2 + w * y =
        c * (y + w / (2 * c)) ^ 2 + (-(w ^ 2) / (4 * c)) := by
    field_simp [h2, h4, hc]
    ring
  calc
    primeQuadraticExponentialSum p c w =
        ∑ y : ZMod p,
          ZMod.stdAddChar (c * (y + w / (2 * c)) ^ 2 + (-(w ^ 2) / (4 * c))) := by
      unfold primeQuadraticExponentialSum
      apply Finset.sum_congr rfl
      intro y _
      rw [hshift]
    _ = (∑ y : ZMod p, ZMod.stdAddChar (c * (y + w / (2 * c)) ^ 2)) *
        ZMod.stdAddChar (-(w ^ 2) / (4 * c)) := by
      simp_rw [AddChar.map_add_eq_mul]
      rw [Finset.sum_mul]
    _ = (∑ y : ZMod p, ZMod.stdAddChar (c * y ^ 2)) *
        ZMod.stdAddChar (-(w ^ 2) / (4 * c)) := by
      congr 1
      exact Equiv.sum_comp (Equiv.addRight (w / (2 * c)))
        (fun y : ZMod p => ZMod.stdAddChar (c * y ^ 2))
    _ = complexQuadraticChar p c * primeQuadraticGauss p *
        ZMod.stdAddChar (-(w ^ 2) / (4 * c)) := by
      rw [primeQuadraticExponentialSum_unshifted p hp c hc]

end QuaternaryQuadraticForms
