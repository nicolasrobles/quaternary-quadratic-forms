import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Analysis.Complex.Basic

/-!
# The global quadratic coefficient on good positive moduli

We use the actual Jacobi symbol, cast to the complex numbers. Its values
at positive moduli coprime to `2 * |α|` agree with the manuscript's
supplied Dirichlet character, because the two multiplicative functions
agree at every prime divisor. The agreement is proved below for an
actual Dirichlet character of any level, using precisely the source's
stated good-prime values. No identification at bad or zero moduli is
claimed, and no primitive character or quadratic field is redefined.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual Jacobi symbol as a complex coefficient. Source-character
agreement is asserted only at good positive moduli. -/
def globalQuadraticChar (α : ℤ) (n : ℕ) : ℂ := (jacobiSym α n : ℂ)

/-- The coefficient at modulus one is the empty product. -/
@[simp]
theorem globalQuadraticChar_one (α : ℤ) : globalQuadraticChar α 1 = 1 := by
  simp [globalQuadraticChar]

/-- Multiplicativity of the actual Jacobi coefficient at positive moduli. -/
theorem globalQuadraticChar_mul (α : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    globalQuadraticChar α (m * n) = globalQuadraticChar α m * globalQuadraticChar α n := by
  simp only [globalQuadraticChar, jacobiSym.mul_right, Int.cast_mul]

/-- At a prime the global coefficient is the exact Legendre symbol. -/
theorem globalQuadraticChar_prime (α : ℤ) (p : ℕ) [Fact p.Prime] :
    globalQuadraticChar α p = (legendreSym p α : ℂ) := by
  rw [globalQuadraticChar, ← jacobiSym.legendreSym.to_jacobiSym p α]

/-- Prime-power agreement includes the empty power at exponent zero. -/
theorem globalQuadraticChar_prime_power (α : ℤ) (p k : ℕ) [Fact p.Prime] :
    globalQuadraticChar α (p ^ k) = (legendreSym p α : ℂ) ^ k := by
  rw [globalQuadraticChar, jacobiSym.pow_right, ← jacobiSym.legendreSym.to_jacobiSym p α,
    Int.cast_pow]

/-- On coprime arguments the quadratic coefficient has square one. -/
theorem globalQuadraticChar_sq (α : ℤ) (n : ℕ) (hcoprime : n.Coprime α.natAbs) :
    globalQuadraticChar α n ^ 2 = 1 := by
  have h : α.gcd (n : ℤ) = 1 := by
    simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using hcoprime.symm
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) (jacobiSym.sq_one h)
  simpa only [Int.cast_pow, Int.cast_one, globalQuadraticChar] using hcast

/-- Good-prime values determine every positive value coprime to `2*|α|`
of an actual multiplicative map on the natural numbers. -/
theorem monoidHom_eq_globalQuadraticChar (α : ℤ) (χ : ℕ →* ℂ)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * α.natAbs →
      χ p = (legendreSym p α : ℂ))
    (n : ℕ) [NeZero n] (hgood : n.Coprime (2 * α.natAbs)) :
    χ n = globalQuadraticChar α n := by
  have hall : ∀ m : ℕ, m ≠ 0 → m.Coprime (2 * α.natAbs) →
      χ m = globalQuadraticChar α m := by
    apply induction_on_primes
    · intro h
      exact (h rfl).elim
    · intro _ _
      rw [map_one, globalQuadraticChar_one]
    · intro p m hp ih hpm hcoprime
      letI : Fact p.Prime := ⟨hp⟩
      letI : NeZero m := ⟨right_ne_zero_of_mul hpm⟩
      have hparts := Nat.coprime_mul_iff_left.mp hcoprime
      rw [map_mul, globalQuadraticChar_mul, globalQuadraticChar_prime,
        hχ p (hp.coprime_iff_not_dvd.mp hparts.1), ih (NeZero.ne m) hparts.2]
  exact hall n (NeZero.ne n) hgood

/-- The Jacobi coefficient equals the original supplied Dirichlet character
on every good positive modulus. The only character hypothesis is the
source's explicit Legendre value at good primes. -/
theorem globalQuadraticChar_eq_dirichletCharacter
    (α : ℤ) (d : ℕ) (χ : DirichletCharacter ℂ d)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * α.natAbs →
      χ (p : ZMod d) = (legendreSym p α : ℂ))
    (n : ℕ) [NeZero n] (hgood : n.Coprime (2 * α.natAbs)) :
    globalQuadraticChar α n = χ (n : ZMod d) := by
  let f : ℕ →* ℂ := χ.toMonoidHom.comp (Nat.castRingHom (ZMod d)).toMonoidHom
  have hf : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * α.natAbs →
      f p = (legendreSym p α : ℂ) := by
    intro p _ hp
    exact hχ p hp
  exact (monoidHom_eq_globalQuadraticChar α f hf n hgood).symm

end QuaternaryQuadraticForms
