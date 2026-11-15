import QuaternaryQuadraticForms.PrimePowerResidues
import Mathlib.Data.Nat.Prime.Basic

/-!
# Splitting actual prime-power scalar residues

The nonunits modulo `p^(k+1)` are precisely the multiples of `p` obtained
from residues modulo `p^k`. The proof constructs both parts using actual
canonical residue digits, and includes `k=0`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private def scalarDigits (p k : ℕ) [NeZero p] :
    ZMod p × ZMod (p ^ k) ≃ ZMod (p ^ k * p) :=
  (residueDigitsEquiv p (p ^ k)).trans
    (ZMod.ringEquivCongr (Nat.mul_comm p (p ^ k))).toEquiv

private theorem scalarDigits_val (p k : ℕ) [NeZero p]
    (r : ZMod p) (s : ZMod (p ^ k)) :
    (scalarDigits p k (r, s)).val = r.val + p * s.val := by
  simp only [scalarDigits, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, ZMod.ringEquivCongr_val, residueDigitsEquiv_val]

private theorem scalarDigits_coprime (p k : ℕ) [NeZero p]
    (r : ZMod p) (s : ZMod (p ^ k)) :
    Nat.Coprime (scalarDigits p k (r, s)).val (p ^ k * p) ↔
      Nat.Coprime r.val p := by
  rw [scalarDigits_val, ← pow_succ,
    Nat.coprime_pow_right_iff (Nat.succ_pos k), Nat.coprime_add_mul_left_left]

private def scalarUnitDigits (p k : ℕ) [NeZero p] :
    (ZMod p)ˣ × ZMod (p ^ k) ≃ (ZMod (p ^ k * p))ˣ :=
  (Equiv.prodCongr (ZMod.unitsEquivCoprime (n := p))
    (Equiv.refl (ZMod (p ^ k)))).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
      (((scalarDigits p k).subtypeEquiv
        (fun rs => (scalarDigits_coprime p k rs.1 rs.2).symm)).trans
        (ZMod.unitsEquivCoprime (n := p ^ k * p)).symm))

private theorem scalarUnitDigits_coe (p k : ℕ) [NeZero p]
    (a : (ZMod p)ˣ) (s : ZMod (p ^ k)) :
    (scalarUnitDigits p k (a, s) : ZMod (p ^ k * p)) =
      scalarDigits p k ((a : ZMod p), s) := by
  change (((scalarDigits p k ((a : ZMod p), s)).val : ℕ) : ZMod (p ^ k * p)) = _
  exact ZMod.natCast_zmod_val _

/-- Every scalar residue is either an actual unit or a unique multiple of `p`
lifted from the preceding power. This exact sum partition also holds at `k=0`. -/
theorem sum_primePower_scalars (p k : ℕ) [Fact p.Prime]
    (f : ZMod (p ^ k * p) → ℂ) :
    (∑ a : ZMod (p ^ k * p), f a) =
      (∑ a : (ZMod (p ^ k * p))ˣ, f (a : ZMod (p ^ k * p))) +
        ∑ b : ZMod (p ^ k), f ((p : ZMod (p ^ k * p)) * b.val) := by
  classical
  have hu :
      (∑ a : (ZMod (p ^ k * p))ˣ, f (a : ZMod (p ^ k * p))) =
        ∑ a : (ZMod p)ˣ, ∑ b : ZMod (p ^ k),
          f (scalarDigits p k ((a : ZMod p), b)) := by
    rw [← Equiv.sum_comp (scalarUnitDigits p k)
      (fun a : (ZMod (p ^ k * p))ˣ => f (a : ZMod (p ^ k * p))),
      Fintype.sum_prod_type]
    simp only [scalarUnitDigits_coe]
  have hz (b : ZMod (p ^ k)) :
      scalarDigits p k (0, b) = (p : ZMod (p ^ k * p)) * b.val := by
    rw [← ZMod.natCast_zmod_val (scalarDigits p k (0, b)), scalarDigits_val]
    simp
  calc
    _ = ∑ r : ZMod p, ∑ b : ZMod (p ^ k), f (scalarDigits p k (r, b)) := by
      rw [← Equiv.sum_comp (scalarDigits p k) f, Fintype.sum_prod_type]
    _ = (∑ b : ZMod (p ^ k), f (scalarDigits p k (0, b))) +
        ∑ r : {r : ZMod p // r ≠ 0}, ∑ b : ZMod (p ^ k),
          f (scalarDigits p k (r.val, b)) := by
      exact Fintype.sum_eq_add_sum_subtype_ne _ 0
    _ = (∑ b : ZMod (p ^ k), f ((p : ZMod (p ^ k * p)) * b.val)) +
        ∑ a : (ZMod p)ˣ, ∑ b : ZMod (p ^ k),
          f (scalarDigits p k ((a : ZMod p), b)) := by
      rw [← Equiv.sum_comp unitsEquivNeZero
        (fun r : {r : ZMod p // r ≠ 0} =>
          ∑ b : ZMod (p ^ k), f (scalarDigits p k (r.val, b)))]
      simp only [hz, unitsEquivNeZero_apply_coe]
    _ = _ := by rw [← hu, add_comm]

end QuaternaryQuadraticForms
