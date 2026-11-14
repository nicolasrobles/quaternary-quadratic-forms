import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic

/-!
# Composite weights from the actual prime functions

The source weight `ξ_q` is the product of the local functions at the
distinct primes dividing `q`.  The family is indexed by natural numbers
for convenience, but values at nonprimes never occur in the product.
Every scalar-invariance hypothesis below concerns only primes dividing
the indicated modulus.  In particular no condition is imposed on local
functions at excluded primes.

The integer-vector definition makes periodicity and independence of a
residue representative explicit.  The residue-vector definition uses
the canonical coordinate lifts, including the modulus-one case.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The source product of the local functions over the primes dividing `q`. -/
def compositeWeight (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (x : Fin 4 → ℤ) : ℂ :=
  ∏ p ∈ q.primeFactors, ξ p (fun i => (x i : ZMod p))

/-- Evaluation on the canonical integer representatives of a residue vector. -/
def compositeWeight_mod (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) (x : Fin 4 → ZMod n) : ℂ :=
  compositeWeight ξ q (fun i => ((x i).val : ℤ))

/-- The empty prime product is the constant weight one. -/
@[simp]
theorem compositeWeight_one (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (x : Fin 4 → ℤ) : compositeWeight ξ 1 x = 1 := by
  simp [compositeWeight]

/-- At a prime, the product is the prescribed local function. -/
theorem compositeWeight_prime (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) (hp : p.Prime) (x : Fin 4 → ℤ) :
    compositeWeight ξ p x = ξ p (fun i => (x i : ZMod p)) := by
  simp [compositeWeight, hp.primeFactors]

/-- Coordinatewise congruence modulo `q` preserves the composite weight. -/
theorem compositeWeight_congr (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (x y : Fin 4 → ℤ)
    (hxy : ∀ i, (x i : ZMod q) = (y i : ZMod q)) :
    compositeWeight ξ q x = compositeWeight ξ q y := by
  unfold compositeWeight
  apply Finset.prod_congr rfl
  intro p hp
  congr 1
  funext i
  have h := congrArg (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p)) (hxy i)
  simpa only [map_intCast] using h

/-- Divisibility of every coordinate difference gives weight invariance. -/
theorem compositeWeight_congr_of_dvd_sub
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (x y : Fin 4 → ℤ)
    (hxy : ∀ i, (q : ℤ) ∣ x i - y i) :
    compositeWeight ξ q x = compositeWeight ξ q y := by
  apply compositeWeight_congr ξ q x y
  intro i
  apply sub_eq_zero.mp
  rw [← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hxy i)

/-- The source weight is periodic modulo `q` in every coordinate. -/
theorem compositeWeight_add_modulus
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (x y : Fin 4 → ℤ) :
    compositeWeight ξ q (fun i => x i + (q : ℤ) * y i) = compositeWeight ξ q x := by
  apply compositeWeight_congr ξ q _ x
  intro i
  simp

/-- Congruence modulo any multiple of `q` is enough for the weight. -/
theorem compositeWeight_congr_mod
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) (hqn : q ∣ n) (x y : Fin 4 → ℤ)
    (hxy : ∀ i, (x i : ZMod n) = (y i : ZMod n)) :
    compositeWeight ξ q x = compositeWeight ξ q y := by
  apply compositeWeight_congr ξ q x y
  intro i
  have h := congrArg (ZMod.castHom hqn (ZMod q)) (hxy i)
  simpa only [map_intCast] using h

/-- Coprime moduli have disjoint prime supports, giving the literal
product identity.  This also includes a factor equal to one. -/
theorem compositeWeight_mul
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q₁ q₂ : ℕ) (hcoprime : q₁.Coprime q₂) (x : Fin 4 → ℤ) :
    compositeWeight ξ (q₁ * q₂) x =
      compositeWeight ξ q₁ x * compositeWeight ξ q₂ x := by
  unfold compositeWeight
  rw [hcoprime.primeFactors_mul, Finset.prod_union hcoprime.disjoint_primeFactors]

/-- Only the local invariance at primes dividing `q` is used in scaling
the integer vector by a scalar nonzero at those primes. -/
theorem compositeWeight_smul_of_nonzero
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (t : ℤ) (x : Fin 4 → ℤ)
    (hξ : ∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y)
    (ht : ∀ p ∈ q.primeFactors, (t : ZMod p) ≠ 0) :
    compositeWeight ξ q (fun i => t * x i) = compositeWeight ξ q x := by
  unfold compositeWeight
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_mul] using
    hξ p hp (t : ZMod p) (ht p hp) (fun i => (x i : ZMod p))

/-- An integer coprime to `q` preserves the composite weight. -/
theorem compositeWeight_smul
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (t : ℤ) (x : Fin 4 → ℤ)
    (hξ : ∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y)
    (ht : t.natAbs.Coprime q) :
    compositeWeight ξ q (fun i => t * x i) = compositeWeight ξ q x := by
  apply compositeWeight_smul_of_nonzero ξ q t x hξ
  intro p hp hz
  have hcoprime : t.natAbs.Coprime p := ht.of_dvd_right (Nat.dvd_of_mem_primeFactors hp)
  have hnotdvd : ¬p ∣ t.natAbs :=
    (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hcoprime.symm
  apply hnotdvd
  have hdiv : (p : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp hz
  exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)

/-- The unit formulation of integer-scalar invariance modulo `q`. -/
theorem compositeWeight_smul_of_isUnit
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) (t : ℤ) (x : Fin 4 → ℤ)
    (hξ : ∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y)
    (ht : IsUnit (t : ZMod q)) :
    compositeWeight ξ q (fun i => t * x i) = compositeWeight ξ q x := by
  apply compositeWeight_smul_of_nonzero ξ q t x hξ
  intro p hp
  letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hunit := ht.map (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p))
  simpa only [map_intCast] using hunit.ne_zero

/-- The residue-vector weight at modulus one remains the constant one. -/
@[simp]
theorem compositeWeight_mod_one
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (n : ℕ) (x : Fin 4 → ZMod n) : compositeWeight_mod ξ 1 n x = 1 := by
  exact compositeWeight_one ξ _

/-- Any integer lift of a residue vector gives the same weight as the
canonical lift, provided `q` divides the residue modulus. -/
theorem compositeWeight_mod_eq_of_lift
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) [NeZero n] (hqn : q ∣ n)
    (x : Fin 4 → ZMod n) (z : Fin 4 → ℤ)
    (hz : ∀ i, (z i : ZMod n) = x i) :
    compositeWeight_mod ξ q n x = compositeWeight ξ q z := by
  unfold compositeWeight_mod
  apply compositeWeight_congr_mod ξ q n hqn
  intro i
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  exact (hz i).symm

/-- Reducing an integer vector and then taking its weight recovers the
original integer-vector weight. -/
theorem compositeWeight_mod_intCast
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) [NeZero n] (hqn : q ∣ n) (x : Fin 4 → ℤ) :
    compositeWeight_mod ξ q n (fun i => (x i : ZMod n)) = compositeWeight ξ q x :=
  compositeWeight_mod_eq_of_lift ξ q n hqn _ x (fun _ => rfl)

/-- On prime residue vectors the construction is exactly the given
local function, without any choice of representative. -/
theorem compositeWeight_mod_prime
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) (hp : p.Prime) (x : Fin 4 → ZMod p) :
    compositeWeight_mod ξ p p x = ξ p x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  unfold compositeWeight_mod
  rw [compositeWeight_prime ξ p hp]
  congr 1
  funext i
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Reduction between ambient residue moduli preserves the weight when
both moduli contain its prime support through divisibility by `q`. -/
theorem compositeWeight_mod_cast
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q m n : ℕ) [NeZero m] [NeZero n]
    (hqm : q ∣ m) (hmn : m ∣ n) (x : Fin 4 → ZMod n) :
    compositeWeight_mod ξ q m (fun i => ZMod.castHom hmn (ZMod m) (x i)) =
      compositeWeight_mod ξ q n x := by
  apply compositeWeight_mod_eq_of_lift ξ q m hqm _ (fun i => ((x i).val : ℤ))
  intro i
  have h := congrArg (ZMod.castHom hmn (ZMod m))
    (ZMod.natCast_zmod_val (x i))
  simpa only [map_natCast, Int.cast_natCast] using h

/-- Every unit of the ambient residue ring acts trivially on the weight
whose modulus divides that ring's modulus. -/
theorem compositeWeight_mod_units_smul
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q n : ℕ) [NeZero n] (hqn : q ∣ n)
    (hξ : ∀ p ∈ q.primeFactors, ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p (r • y) = ξ p y)
    (t : (ZMod n)ˣ) (x : Fin 4 → ZMod n) :
    compositeWeight_mod ξ q n (fun i => (t : ZMod n) * x i) =
      compositeWeight_mod ξ q n x := by
  calc
    _ = compositeWeight ξ q
        (fun i => (((t : ZMod n).val : ℤ) * ((x i).val : ℤ))) := by
      apply compositeWeight_mod_eq_of_lift ξ q n hqn
      intro i
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = compositeWeight ξ q (fun i => ((x i).val : ℤ)) := by
      apply compositeWeight_smul ξ q _ _ hξ
      simpa only [Int.natAbs_natCast] using
        (ZMod.val_coe_unit_coprime t).of_dvd_right hqn
    _ = _ := rfl

end QuaternaryQuadraticForms
