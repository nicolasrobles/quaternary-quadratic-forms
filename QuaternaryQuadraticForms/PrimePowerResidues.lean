import QuaternaryQuadraticForms.CompleteSumAlgebra
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Residue digits without a coprimality hypothesis

The two digits are their canonical representatives. Unlike CRT, this
bijection applies when the two modulus factors have common primes.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem finEquiv_val (n : ℕ) [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private theorem finEquiv_symm_val (n : ℕ) [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The actual digit bijection `(r,s) ↦ r + m*s` modulo `m*n`. -/
def residueDigitsEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ZMod m × ZMod n ≃ ZMod (m * n) :=
  (Equiv.prodComm (ZMod m) (ZMod n)).trans
    ((Equiv.prodCongr (ZMod.finEquiv n).symm.toEquiv
      (ZMod.finEquiv m).symm.toEquiv).trans
      (finProdFinEquiv.trans ((ZMod.finEquiv (n * m)).toEquiv.trans
        (ZMod.ringEquivCongr (Nat.mul_comm n m)).toEquiv)))

/-- The digit map has the canonical representative predicted by division with remainder. -/
theorem residueDigitsEquiv_val (m n : ℕ) [NeZero m] [NeZero n]
    (r : ZMod m) (s : ZMod n) :
    (residueDigitsEquiv m n (r, s)).val = r.val + m * s.val := by
  simp only [residueDigitsEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    Equiv.prodCongr_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    ZMod.ringEquivCongr_val, finEquiv_val]
  change ((ZMod.finEquiv m).symm r).val + m * ((ZMod.finEquiv n).symm s).val = _
  rw [finEquiv_symm_val, finEquiv_symm_val]

/-- Integer-lift formula for the non-coprime digit bijection. -/
theorem residueDigitsEquiv_apply (m n : ℕ) [NeZero m] [NeZero n]
    (r : ZMod m) (s : ZMod n) :
    residueDigitsEquiv m n (r, s) =
      ((r.val : ℤ) + (m : ℤ) * (s.val : ℤ) : ZMod (m * n)) := by
  rw [← ZMod.natCast_zmod_val (residueDigitsEquiv m n (r, s)),
    residueDigitsEquiv_val]
  push_cast
  rfl

/-- The residue-digit bijection applied independently in each coordinate. -/
def residueDigitsVectorEquiv (ι : Type*) (m n : ℕ) [NeZero m] [NeZero n] :
    (ι → ZMod m) × (ι → ZMod n) ≃ (ι → ZMod (m * n)) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ => ZMod m) (fun _ => ZMod n)).symm.trans
    (Equiv.piCongrRight fun _ => residueDigitsEquiv m n)

/-- Each coordinate has the same explicit two-digit formula. -/
theorem residueDigitsVectorEquiv_apply (ι : Type*) (m n : ℕ)
    [NeZero m] [NeZero n] (r : ι → ZMod m) (s : ι → ZMod n) (i : ι) :
    residueDigitsVectorEquiv ι m n (r, s) i =
      ((r i).val : ZMod (m * n)) + m * ((s i).val : ZMod (m * n)) := by
  change residueDigitsEquiv m n (r i, s i) = _
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
    residueDigitsEquiv_apply m n (r i) (s i)

/-- Splitting a vector sum into actual low and high digits needs no coprimality. -/
theorem sum_residueLift_digits (m n : ℕ) [NeZero m] [NeZero n]
    (f : (Fin 4 → ℤ) → ℂ) :
    (∑ x : Fin 4 → ZMod (m * n), f (residueLift (m * n) x)) =
      ∑ r : Fin 4 → ZMod m, ∑ s : Fin 4 → ZMod n,
        f (fun i => residueLift m r i + (m : ℤ) * residueLift n s i) := by
  classical
  calc
    _ = ∑ rs : (Fin 4 → ZMod m) × (Fin 4 → ZMod n),
        f (residueLift (m * n) (residueDigitsVectorEquiv (Fin 4) m n rs)) :=
      (Equiv.sum_comp (residueDigitsVectorEquiv (Fin 4) m n) _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      funext i
      change (((residueDigitsEquiv m n (r i, s i)).val : ℕ) : ℤ) = _
      rw [residueDigitsEquiv_val]
      simp [residueLift]

/-- The two outer base-`p` digits leave an arbitrary positive middle modulus. -/
theorem sum_residueLift_three_digits (p m : ℕ) [NeZero p] [NeZero m]
    (f : (Fin 4 → ℤ) → ℂ) :
    (∑ x : Fin 4 → ZMod (p * (m * p)), f (residueLift (p * (m * p)) x)) =
      ∑ r : Fin 4 → ZMod p, ∑ w : Fin 4 → ZMod m, ∑ z : Fin 4 → ZMod p,
        f (fun i => residueLift p r i + (p : ℤ) *
          (residueLift m w i + (m : ℤ) * residueLift p z i)) := by
  rw [sum_residueLift_digits]
  apply Finset.sum_congr rfl
  intro r _
  exact sum_residueLift_digits m p
    (fun v => f (fun i => residueLift p r i + (p : ℤ) * v i))

end QuaternaryQuadraticForms
