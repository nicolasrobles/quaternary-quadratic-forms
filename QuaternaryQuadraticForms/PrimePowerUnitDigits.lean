import QuaternaryQuadraticForms.PrimePowerResidues

/-!
# Unit digits when one modulus divides the other

The canonical low digit of a unit modulo `p * c` is a unit modulo `c`.
If `p ∣ c`, every high digit is then allowed. This is a restriction of the
actual residue-digit bijection, with no coprimality assumption on the moduli.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private def commutedResidueDigitsEquiv (c p : ℕ) [NeZero c] [NeZero p] :
    ZMod c × ZMod p ≃ ZMod (p * c) :=
  (residueDigitsEquiv c p).trans
    (ZMod.ringEquivCongr (Nat.mul_comm c p)).toEquiv

private theorem commutedResidueDigitsEquiv_val
    (c p : ℕ) [NeZero c] [NeZero p] (r : ZMod c) (t : ZMod p) :
    (commutedResidueDigitsEquiv c p (r, t)).val = r.val + c * t.val := by
  simp only [commutedResidueDigitsEquiv, Equiv.trans_apply,
    RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    ZMod.ringEquivCongr_val, residueDigitsEquiv_val]

private theorem unitDigits_coprime_iff
    (c p : ℕ) [NeZero c] [NeZero p] (hpc : p ∣ c)
    (r : ZMod c) (t : ZMod p) :
    Nat.Coprime (commutedResidueDigitsEquiv c p (r, t)).val (p * c) ↔
      Nat.Coprime r.val c := by
  rw [commutedResidueDigitsEquiv_val, Nat.coprime_mul_iff_right]
  constructor
  · intro h
    exact (Nat.coprime_add_mul_left_left r.val c t.val).mp h.2
  · intro h
    have hc := (Nat.coprime_add_mul_left_left r.val c t.val).mpr h
    exact ⟨hc.of_dvd_right hpc, hc⟩

/-- The actual unit digit bijection `(a,t) ↦ a + c*t` modulo `p*c`,
valid whenever the positive modulus `p` divides `c`. -/
def residueUnitDigitsEquiv (c p : ℕ) [NeZero c] [NeZero p] (hpc : p ∣ c) :
    (ZMod c)ˣ × ZMod p ≃ (ZMod (p * c))ˣ :=
  (Equiv.prodCongr (ZMod.unitsEquivCoprime (n := c)) (Equiv.refl (ZMod p))).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
      (((commutedResidueDigitsEquiv c p).subtypeEquiv
        (fun rt => (unitDigits_coprime_iff c p hpc rt.1 rt.2).symm)).trans
        (ZMod.unitsEquivCoprime (n := p * c)).symm))

/-- The unit bijection preserves the literal canonical low and high digits. -/
theorem residueUnitDigitsEquiv_val
    (c p : ℕ) [NeZero c] [NeZero p] (hpc : p ∣ c)
    (a : (ZMod c)ˣ) (t : ZMod p) :
    ((residueUnitDigitsEquiv c p hpc (a, t) : ZMod (p * c))).val =
      (a : ZMod c).val + c * t.val := by
  change (((commutedResidueDigitsEquiv c p ((a : ZMod c), t)).val :
    ZMod (p * c))).val = _
  rw [ZMod.natCast_zmod_val, commutedResidueDigitsEquiv_val]

/-- Reindexing an actual unit sum by its canonical digits. -/
theorem sum_units_residueLift_digits
    (c p : ℕ) [NeZero c] [NeZero p] (hpc : p ∣ c) (f : ℤ → ℂ) :
    (∑ b : (ZMod (p * c))ˣ, f (((b : ZMod (p * c)).val : ℕ) : ℤ)) =
      ∑ a : (ZMod c)ˣ, ∑ t : ZMod p,
        f ((((a : ZMod c).val : ℕ) : ℤ) + (c : ℤ) * (t.val : ℤ)) := by
  classical
  calc
    _ = ∑ rt : (ZMod c)ˣ × ZMod p,
        f ((((residueUnitDigitsEquiv c p hpc rt : ZMod (p * c))).val : ℕ) : ℤ) :=
      (Equiv.sum_comp (residueUnitDigitsEquiv c p hpc) _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro t _
      rw [residueUnitDigitsEquiv_val]
      push_cast
      rfl

end QuaternaryQuadraticForms
