import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Prime residue conditions in an integer interval

The actual integers in an interval are encoded by their allowed prime
residues and by a quotient block of length the product of the primes.
The injectivity assertion is the uniqueness part of the Chinese remainder
theorem.  The prime set may be empty.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Integers in the indicated interval satisfying every allowed residue
condition.  The sets of allowed residues may vary with the prime. -/
def primeResidueInterval (S : Finset ℕ)
    (R : (p : S) → Finset (ZMod p.val)) (a b : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc a b).filter (fun z => ∀ p : S, (z : ZMod p.val) ∈ R p)

/-- Membership in the interval with its literal prime residue conditions. -/
theorem mem_primeResidueInterval (S : Finset ℕ)
    (R : (p : S) → Finset (ZMod p.val)) (a b z : ℤ) :
    z ∈ primeResidueInterval S R a b ↔
      a ≤ z ∧ z ≤ b ∧ ∀ p : S, (z : ZMod p.val) ∈ R p := by
  classical
  simp only [primeResidueInterval, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Equal residues at distinct primes give congruence modulo their
product, including the empty product. -/
theorem primeProduct_modEq (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (x y : ℤ)
    (hxy : ∀ p ∈ S, (x : ZMod p) = (y : ZMod p)) :
    x ≡ y [ZMOD (∏ p ∈ S, p : ℕ)] := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Int.ModEq]
  | @insert p S hp ih =>
    have hpprime := hS p (Finset.mem_insert_self p S)
    have hSprime : ∀ q ∈ S, Nat.Prime q :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpprime (hSprime q hq)).mpr (by
        intro hpq
        exact hp (hpq.symm ▸ hq))
    rw [Finset.prod_insert hp, Nat.cast_mul]
    apply (Int.modEq_and_modEq_iff_modEq_mul (by
      simpa only [← Nat.cast_prod, Int.natAbs_natCast] using hcop)).mp
    constructor
    · exact Int.modEq_iff_dvd.mpr
        ((ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp
          (hxy p (Finset.mem_insert_self p S)))
    · exact ih hSprime (fun q hq => hxy q (Finset.mem_insert_of_mem hq))

private theorem interval_quotient_residues_injective
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (a x y : ℤ) (hx : a ≤ x) (hy : a ≤ y)
    (hres : ∀ p ∈ S, (x : ZMod p) = (y : ZMod p))
    (hquot : (x - a).toNat / (∏ p ∈ S, p) =
      (y - a).toNat / (∏ p ∈ S, p)) : x = y := by
  have hmod := (primeProduct_modEq S hS x y hres).sub (Int.ModEq.refl a)
  have hnat : (x - a).toNat ≡ (y - a).toNat [MOD (∏ p ∈ S, p)] := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Int.toNat_of_nonneg (sub_nonneg.mpr hx),
      Int.toNat_of_nonneg (sub_nonneg.mpr hy)] using hmod
  have heq : (x - a).toNat = (y - a).toNat := by
    calc
      _ = (x - a).toNat % (∏ p ∈ S, p) +
          (∏ p ∈ S, p) * ((x - a).toNat / (∏ p ∈ S, p)) :=
        (Nat.mod_add_div _ _).symm
      _ = (y - a).toNat % (∏ p ∈ S, p) +
          (∏ p ∈ S, p) * ((y - a).toNat / (∏ p ∈ S, p)) := by
        rw [hnat, hquot]
      _ = _ := Nat.mod_add_div _ _
  omega

/-- The integral quotient-block count before passing to a real interval
length. -/
theorem primeResidueInterval_card_le_blocks
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (R : (p : S) → Finset (ZMod p.val)) (a b : ℤ) :
    (primeResidueInterval S R a b).card ≤
      (∏ p : S, (R p).card) * ((b - a).toNat / (∏ p ∈ S, p) + 1) := by
  classical
  let encode : {z // z ∈ primeResidueInterval S R a b} →
      ((p : S) → {r // r ∈ R p}) ×
        Fin ((b - a).toNat / (∏ p ∈ S, p) + 1) := fun z =>
    (fun p => ⟨(z.val : ZMod p.val),
      ((mem_primeResidueInterval S R a b z.val).mp z.property).2.2 p⟩,
    ⟨(z.val - a).toNat / (∏ p ∈ S, p), by
      apply Nat.lt_succ_of_le
      apply Nat.div_le_div_right
      apply Int.toNat_le_toNat
      exact sub_le_sub_right
        ((mem_primeResidueInterval S R a b z.val).mp z.property).2.1 a⟩)
  have hinj : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply interval_quotient_residues_injective S hS a x.val y.val
      ((mem_primeResidueInterval S R a b x.val).mp x.property).1
      ((mem_primeResidueInterval S R a b y.val).mp y.property).1
    · intro p hp
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst hxy) ⟨p, hp⟩)
    · exact congrArg Fin.val (congrArg Prod.snd hxy)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi,
    Fintype.card_fin] using Fintype.card_le_of_injective encode hinj

/-- Uniform interval count for arbitrary allowed prime residue sets.
Only the number of integers in the interval enters the estimate. -/
theorem primeResidueInterval_card_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (R : (p : S) → Finset (ZMod p.val)) (E : ℕ)
    (hR : ∀ p : S, (R p).card ≤ E) (a b : ℤ)
    (Y : ℝ) (_hY : 0 ≤ Y) (hI : ((Finset.Icc a b).card : ℝ) ≤ Y) :
    ((primeResidueInterval S R a b).card : ℝ) ≤
      (E : ℝ) ^ S.card * (Y / (∏ p ∈ S, (p : ℝ)) + 1) := by
  classical
  have hm : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hmR : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hm
  have hlen : ((b - a).toNat : ℝ) ≤ Y := by
    have hcard : (b - a).toNat ≤ (Finset.Icc a b).card := by
      rw [Int.card_Icc]
      exact Int.toNat_le_toNat (by omega)
    have hcardR : ((b - a).toNat : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
      exact_mod_cast hcard
    exact hcardR.trans hI
  have hquot : (((b - a).toNat / (∏ p ∈ S, p) : ℕ) : ℝ) ≤
      Y / (∏ p ∈ S, (p : ℝ)) := by
    apply (le_div_iff₀ hmR).mpr
    have hmul : (((b - a).toNat / (∏ p ∈ S, p) : ℕ) : ℝ) *
        (∏ p ∈ S, (p : ℝ)) ≤ ((b - a).toNat : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.div_mul_le_self (b - a).toNat (∏ p ∈ S, p)
    exact hmul.trans hlen
  have hprod : ∏ p : S, (R p).card ≤ E ^ S.card := by
    calc
      _ ≤ ∏ _p : S, E := Finset.prod_le_prod' (fun p _ => hR p)
      _ = _ := by simp
  calc
    _ ≤ ((∏ p : S, (R p).card) : ℝ) *
        ((((b - a).toNat / (∏ p ∈ S, p) : ℕ) : ℝ) + 1) := by
      exact_mod_cast primeResidueInterval_card_le_blocks S hS R a b
    _ ≤ (E : ℝ) ^ S.card * (Y / (∏ p ∈ S, (p : ℝ)) + 1) := by
      apply mul_le_mul
      · exact_mod_cast hprod
      · exact add_le_add_right hquot 1
      · positivity
      · positivity

end QuaternaryQuadraticForms
