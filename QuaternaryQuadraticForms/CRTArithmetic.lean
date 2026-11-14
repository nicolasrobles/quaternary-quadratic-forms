import QuaternaryQuadraticForms.CRTCharacters
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod

/-!
# The source's scaled Chinese remainder coordinates

The manuscript uses `x = n x₁ + m x₂` rather than inverse-coefficient
coordinates. Multiplication by the coprime factors in the two component
rings converts mathlib's Chinese remainder equivalence into this actual
bijection, both on residues and on units. The character identities and
the formulas for positive moduli include modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual CRT bijection in the manuscript's scaled coordinates. -/
def scaledChineseRemainder (m n : ℕ) (h : m.Coprime n) :
    ZMod m × ZMod n ≃ ZMod (m * n) :=
  ((ZMod.unitOfCoprime n h.symm).mulLeft.prodCongr
    (ZMod.unitOfCoprime m h).mulLeft).trans (ZMod.chineseRemainder h).symm.toEquiv

private theorem chineseRemainder_fst (m n : ℕ) (h : m.Coprime n)
    (z : ZMod (m * n)) :
    (ZMod.chineseRemainder h z).1 =
      ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) z := by
  change (ZMod.cast z : ZMod m × ZMod n).1 = (ZMod.cast z : ZMod m)
  exact Prod.fst_zmod_cast z

private theorem chineseRemainder_snd (m n : ℕ) (h : m.Coprime n)
    (z : ZMod (m * n)) :
    (ZMod.chineseRemainder h z).2 =
      ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) z := by
  change (ZMod.cast z : ZMod m × ZMod n).2 = (ZMod.cast z : ZMod n)
  exact Prod.snd_zmod_cast z

private theorem chineseRemainder_scaled (m n : ℕ) (h : m.Coprime n)
    (x : ZMod m) (y : ZMod n) :
    ZMod.chineseRemainder h (scaledChineseRemainder m n h (x, y)) =
      ((n : ZMod m) * x, (m : ZMod n) * y) := by
  simp [scaledChineseRemainder]

/-- The first reduction of the source CRT coordinates. -/
theorem scaledChineseRemainder_fst (m n : ℕ) (h : m.Coprime n)
    (x : ZMod m) (y : ZMod n) :
    ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)
        (scaledChineseRemainder m n h (x, y)) = (n : ZMod m) * x := by
  rw [← chineseRemainder_fst m n h, chineseRemainder_scaled]

/-- The second reduction of the source CRT coordinates. -/
theorem scaledChineseRemainder_snd (m n : ℕ) (h : m.Coprime n)
    (x : ZMod m) (y : ZMod n) :
    ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)
        (scaledChineseRemainder m n h (x, y)) = (m : ZMod n) * y := by
  rw [← chineseRemainder_snd m n h, chineseRemainder_scaled]

/-- Integer representatives give exactly `n a + m b` modulo the product. -/
theorem scaledChineseRemainder_intCast (m n : ℕ) (h : m.Coprime n) (a b : ℤ) :
    scaledChineseRemainder m n h ((a : ZMod m), (b : ZMod n)) =
      (((n : ℤ) * a + (m : ℤ) * b : ℤ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [chineseRemainder_scaled]
  apply Prod.ext
  · rw [chineseRemainder_fst]
    simp
  · rw [chineseRemainder_snd]
    simp

/-- Canonical representatives realize the source's literal scaled sum. -/
theorem scaledChineseRemainder_apply (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod m) (y : ZMod n) :
    scaledChineseRemainder m n h (x, y) =
      (n : ZMod (m * n)) * (x.val : ZMod (m * n)) +
        (m : ZMod (m * n)) * (y.val : ZMod (m * n)) := by
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] using
    scaledChineseRemainder_intCast m n h (x.val : ℤ) (y.val : ℤ)

/-- The source's corresponding bijection on reduced residue classes. -/
def scaledChineseRemainderUnits (m n : ℕ) (h : m.Coprime n) :
    (ZMod m)ˣ × (ZMod n)ˣ ≃ (ZMod (m * n))ˣ :=
  ((Equiv.mulLeft (ZMod.unitOfCoprime n h.symm)).prodCongr
    (Equiv.mulLeft (ZMod.unitOfCoprime m h))).trans
      (MulEquiv.prodUnits.symm.toEquiv.trans
        (Units.mapEquiv (ZMod.chineseRemainder h).symm.toMulEquiv).toEquiv)

/-- The units bijection has exactly the same underlying residue as the
source's scaled CRT bijection. -/
theorem scaledChineseRemainderUnits_coe (m n : ℕ) (h : m.Coprime n)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    ((scaledChineseRemainderUnits m n h (a, b) : (ZMod (m * n))ˣ) :
        ZMod (m * n)) =
      scaledChineseRemainder m n h ((a : ZMod m), (b : ZMod n)) := by
  rfl

/-- Explicit integer-lift formula for the reduced-residue CRT bijection. -/
theorem scaledChineseRemainderUnits_apply (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    ((scaledChineseRemainderUnits m n h (a, b) : (ZMod (m * n))ˣ) :
        ZMod (m * n)) =
      (n : ZMod (m * n)) * ((a : ZMod m).val : ZMod (m * n)) +
        (m : ZMod (m * n)) * ((b : ZMod n).val : ZMod (m * n)) := by
  rw [scaledChineseRemainderUnits_coe, scaledChineseRemainder_apply]

/-- Coordinatewise CRT, suitable in particular for the four source coordinates. -/
def scaledChineseRemainderVector (ι : Type*) (m n : ℕ) (h : m.Coprime n) :
    (ι → ZMod m) × (ι → ZMod n) ≃ (ι → ZMod (m * n)) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ => ZMod m) (fun _ => ZMod n)).symm.trans
    (Equiv.piCongrRight fun _ => scaledChineseRemainder m n h)

/-- The vector bijection is the actual scalar bijection in each coordinate. -/
theorem scaledChineseRemainderVector_apply (ι : Type*) (m n : ℕ) (h : m.Coprime n)
    (x : ι → ZMod m) (y : ι → ZMod n) (i : ι) :
    scaledChineseRemainderVector ι m n h (x, y) i =
      scaledChineseRemainder m n h (x i, y i) := rfl

/-- The standard additive character factors in the actual scaled CRT coordinates. -/
theorem stdAddChar_scaledChineseRemainder (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod m) (y : ZMod n) :
    ZMod.stdAddChar (N := m * n) (scaledChineseRemainder m n h (x, y)) =
      ZMod.stdAddChar x * ZMod.stdAddChar y := by
  rw [scaledChineseRemainder_apply]
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] using stdAddChar_crt_split m n (x.val : ℤ) (y.val : ℤ)

end QuaternaryQuadraticForms
