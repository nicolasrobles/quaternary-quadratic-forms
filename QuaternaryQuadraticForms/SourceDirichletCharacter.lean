import QuaternaryQuadraticForms.GlobalQuadraticCharacter
import QuaternaryQuadraticForms.QuadraticCharacterNonprincipal

/-!
# Nonprincipality of the original source character

The character supplied in the manuscript is retained at its original level.
Its stipulated values at good primes, together with nonsquareness of the
determinant, produce an actual value `-1`.  Thus nonprincipality is a proved
consequence of the source assumptions, including when the supplied level has
additional bad primes.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The original supplied character takes the value `-1` at a positive good
modulus; no assertion about its values at bad primes is required. -/
theorem sourceDirichletCharacter_exists_neg_one
    (α : ℤ) (hα : α ≠ 0) (hns : ¬IsSquare α)
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ 2 * α.natAbs →
      χ (p : ZMod M) = (legendreSym p α : ℂ)) :
    ∃ n : ℕ, n ≠ 0 ∧ n.Coprime (2 * α.natAbs) ∧ χ (n : ZMod M) = -1 := by
  obtain ⟨n, hn, hjn⟩ := exists_good_jacobiSym_neg_one α hα hns
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    simp only [Nat.coprime_zero_left] at hn
    have hpos := Int.natAbs_pos.mpr hα
    omega
  letI : NeZero n := ⟨hn0⟩
  refine ⟨n, hn0, hn, ?_⟩
  have he := globalQuadraticChar_eq_dirichletCharacter α M χ hχ n hn
  simpa only [globalQuadraticChar, hjn, Int.cast_neg, Int.cast_one] using he.symm

/-- Nonsquareness proves nonprincipality of the original source character,
rather than assuming it as an additional premise. -/
theorem sourceDirichletCharacter_ne_one
    (α : ℤ) (hα : α ≠ 0) (hns : ¬IsSquare α)
    (M : ℕ) (χ : DirichletCharacter ℂ M)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ 2 * α.natAbs →
      χ (p : ZMod M) = (legendreSym p α : ℂ)) : χ ≠ 1 := by
  obtain ⟨n, _, _, hn⟩ := sourceDirichletCharacter_exists_neg_one α hα hns M χ hχ
  intro h
  rw [h] at hn
  by_cases hu : IsUnit (n : ZMod M)
  · rw [MulChar.one_apply hu] at hn
    norm_num at hn
  · rw [MulChar.map_nonunit _ hu] at hn
    norm_num at hn

end QuaternaryQuadraticForms
