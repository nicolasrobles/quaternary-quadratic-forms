import QuaternaryQuadraticForms.GlobalQuadraticCharacter

/-!
# A periodic character realizing the actual good Jacobi coefficient

We set the coefficient to zero outside the integers coprime to `2 * |α|`.
Jacobi periodicity then supplies period `4 * |α|`, and the same function
defines a Dirichlet character at that level when `α ≠ 0`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual Jacobi coefficient, restricted to good moduli. -/
def goodQuadraticChar (α : ℤ) (n : ℕ) : ℂ :=
  if n.Coprime (2 * α.natAbs) then globalQuadraticChar α n else 0

@[simp]
theorem goodQuadraticChar_one (α : ℤ) : goodQuadraticChar α 1 = 1 := by
  simp [goodQuadraticChar]

@[simp]
theorem goodQuadraticChar_zero (α : ℤ) : goodQuadraticChar α 0 = 0 := by
  have h : 2 * α.natAbs ≠ 1 := by omega
  simp [goodQuadraticChar, h]

theorem goodQuadraticChar_of_coprime (α : ℤ) (n : ℕ)
    (hn : n.Coprime (2 * α.natAbs)) :
    goodQuadraticChar α n = globalQuadraticChar α n := by
  simp [goodQuadraticChar, hn]

theorem goodQuadraticChar_of_not_coprime (α : ℤ) (n : ℕ)
    (hn : ¬n.Coprime (2 * α.natAbs)) : goodQuadraticChar α n = 0 := by
  simp [goodQuadraticChar, hn]

theorem goodQuadraticChar_mul (α : ℤ) (m n : ℕ) :
    goodQuadraticChar α (m * n) = goodQuadraticChar α m * goodQuadraticChar α n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  simp only [goodQuadraticChar, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all [globalQuadraticChar_mul]

/-- A monoid homomorphism on all natural numbers, including zero. -/
def goodQuadraticCharHom (α : ℤ) : ℕ →* ℂ where
  toFun := goodQuadraticChar α
  map_one' := goodQuadraticChar_one α
  map_mul' := goodQuadraticChar_mul α

theorem goodQuadraticChar_norm_le_one (α : ℤ) (n : ℕ) :
    ‖goodQuadraticChar α n‖ ≤ 1 := by
  unfold goodQuadraticChar
  split_ifs
  · rcases jacobiSym.trichotomy α n with h | h | h <;>
      simp [globalQuadraticChar, h]
  · simp

theorem goodQuadraticChar_coprime_four_iff (α : ℤ) (n : ℕ) :
    n.Coprime (4 * α.natAbs) ↔ n.Coprime (2 * α.natAbs) := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  have h4 : (4 : ℕ) = 2 ^ 2 := by decide
  rw [h4, Nat.coprime_pow_right_iff (by decide)]

theorem goodQuadraticChar_mod (α : ℤ) (n : ℕ) :
    goodQuadraticChar α (n % (4 * α.natAbs)) = goodQuadraticChar α n := by
  have hc : (n % (4 * α.natAbs)).Coprime (2 * α.natAbs) ↔
      n.Coprime (2 * α.natAbs) := by
    rw [← goodQuadraticChar_coprime_four_iff, ← goodQuadraticChar_coprime_four_iff]
    change Nat.gcd (n % (4 * α.natAbs)) (4 * α.natAbs) = 1 ↔
      Nat.gcd n (4 * α.natAbs) = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm (4 * α.natAbs) n]
  by_cases hn : n.Coprime (2 * α.natAbs)
  · rw [goodQuadraticChar_of_coprime _ _ (hc.mpr hn), goodQuadraticChar_of_coprime _ _ hn]
    exact congrArg (fun z : ℤ => (z : ℂ))
      (jacobiSym.mod_right α ((Nat.coprime_mul_iff_right.mp hn).1.odd_of_right)).symm
  · simp [goodQuadraticChar, hn, hc]

theorem goodQuadraticChar_periodic (α : ℤ) :
    Function.Periodic (goodQuadraticChar α) (4 * α.natAbs) := by
  intro n
  rw [← goodQuadraticChar_mod α (n + 4 * α.natAbs)]
  simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, goodQuadraticChar_mod]

/-- The same good-modulus coefficient as an actual Dirichlet character. -/
def goodQuadraticDirichletChar (α : ℤ) (hα : α ≠ 0) :
    DirichletCharacter ℂ (4 * α.natAbs) where
  toFun z := goodQuadraticChar α z.val
  map_one' := by
    rw [ZMod.val_one_eq_one_mod, goodQuadraticChar_mod, goodQuadraticChar_one]
  map_mul' a b := by
    rw [ZMod.val_mul, goodQuadraticChar_mod, goodQuadraticChar_mul]
  map_nonunit' a ha := by
    apply goodQuadraticChar_of_not_coprime
    intro h
    apply ha
    haveI : NeZero (4 * α.natAbs) := ⟨mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hα)⟩
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.isUnit_iff_coprime _ _).mpr ((goodQuadraticChar_coprime_four_iff α _).mpr h)

@[simp]
theorem goodQuadraticDirichletChar_natCast (α : ℤ) (hα : α ≠ 0) (n : ℕ) :
    goodQuadraticDirichletChar α hα (n : ZMod (4 * α.natAbs)) =
      goodQuadraticChar α n := by
  haveI : NeZero (4 * α.natAbs) := ⟨mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hα)⟩
  change goodQuadraticChar α (n : ZMod (4 * α.natAbs)).val = _
  rw [ZMod.val_natCast, goodQuadraticChar_mod]

end QuaternaryQuadraticForms
