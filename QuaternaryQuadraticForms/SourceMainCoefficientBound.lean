import QuaternaryQuadraticForms.SourceMainCoefficient
import QuaternaryQuadraticForms.MainCoefficientLocalBounds
import QuaternaryQuadraticForms.PrimeFactorEpsilon

/-!
# The uniform bound for the actual main coefficient

The literal local-product identity and the good-prime factor estimate
give the explicit (4K)^omega(q)/q bound. The subpower estimate is then
uniform in every source character, exceptional polynomial, local weight
and modulus: the final constant uses only the fixed ordered series for A,
K and epsilon.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The explicit inequality in equation Sxibound, for the actual coefficient
and original supplied local functions. -/
theorem sourceMainCoefficient_norm_le
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (N : ℕ) (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y)
    (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p))
    (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N),
      ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
          (hp.coprime_iff_not_dvd.mpr hpN) A 0‖ ≤
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) (D p hp hpN) = 0
            then 1 else 0)))
    (q : ℕ) [NeZero q] (hsq : Squarefree q) (hqN : q.Coprime N) :
    ‖sourceMainCoefficient N ξ q hqN A‖ ≤
      ‖singularSeriesConstant M χ A‖ * (4 * K) ^ q.primeFactors.card / (q : ℝ) := by
  classical
  have hqF := source_coprime_quadraticBadPrimeModulus N q A hdet hrad hqN
  have hprod : (∏ p : q.primeFactors, (p.val : ℝ)) = (q : ℝ) := by
    rw [Finset.prod_coe_sort, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hfactor (p : q.primeFactors) :
      letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
      ‖sourceConstrainedFourierSum N ξ p.val
          (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)) A 0 /
        ((p.val : ℂ) ^ 3 * (localQuadraticDensity p.val A : ℂ))‖ ≤
          4 * K / (p.val : ℝ) := by
    letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    have hpN : ¬p.val ∣ N := (Fact.out : p.val.Prime).coprime_iff_not_dvd.mp
      (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property))
    have hpF : ¬p.val ∣ quadraticBadPrimeModulus A :=
      (Fact.out : p.val.Prime).coprime_iff_not_dvd.mp
        (hqF.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property))
    exact sourceMainCoefficient_local_norm_le N ξ p.val hpN A hA hdet hpF
      (D p.val Fact.out hpN) K hK (hlocal p.val Fact.out hpN)
  rw [sourceMainCoefficient_eq_prime_product M χ A hA hdet hns hχ N hrad ξ hξ q hsq hqN,
    norm_mul, norm_prod]
  calc
    _ ≤ ‖singularSeriesConstant M χ A‖ *
        ∏ p : q.primeFactors, (4 * K / (p.val : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hfactor p)
    _ = ‖singularSeriesConstant M χ A‖ *
        (4 * K) ^ q.primeFactors.card / (q : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, hprod]
      ring

/-- The complete coefficient bound under the original Fourier-stratum
hypothesis. One positive constant is selected after A,K,epsilon and before
the character, its level, N, all local functions, polynomials, and q. The
explicit finite-prime-factor inequality is retained in the same endpoint. -/
theorem source_main_coefficient_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (K : ℝ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      (∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
        χ (p : ZMod M) = (legendreSym p A.det : ℂ)) →
      ∀ (N : ℕ), primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ),
      (∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
        ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y) →
      ∀ (D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)),
      (∀ p (hp : p.Prime) (hpN : ¬p ∣ N) (u : Fin 4 → ℤ),
        ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
            (hp.coprime_iff_not_dvd.mpr hpN) A u‖ ≤
          K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
            (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p hp hpN) = 0
              then 1 else 0))) →
      ∀ (q : ℕ) [NeZero q], Squarefree q → ∀ hqN : q.Coprime N,
        ‖sourceMainCoefficient N ξ q hqN A‖ ≤
          ‖singularSeriesConstant M χ A‖ * (4 * K) ^ q.primeFactors.card / (q : ℝ) ∧
        ‖sourceMainCoefficient N ξ q hqN A‖ ≤ C * (q : ℝ) ^ (-1 + ε) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  obtain ⟨B, hB, hsubpower⟩ :=
    primeFactor_pow_le_rpow (4 * K) (by linarith) ε hε
  refine ⟨(‖singularSeriesValue 1 A 0‖ + 1) * B, mul_pos (by positivity) hB, ?_⟩
  intro M _ χ hχ N hrad ξ hξ D hlocal q _ hsq hqN
  have hzero : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N),
      ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
          (hp.coprime_iff_not_dvd.mpr hpN) A 0‖ ≤
        K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
          (if MvPolynomial.eval (fun _ : Fin 4 => (0 : ZMod p)) (D p hp hpN) = 0
            then 1 else 0)) := by
    intro p hp hpN
    simpa only [Pi.zero_apply, Int.cast_zero] using hlocal p hp hpN 0
  have hexplicit := sourceMainCoefficient_norm_le
    M χ A hA hdet hns hχ N hrad ξ hξ D K hK0 hzero q hsq hqN
  refine ⟨hexplicit, ?_⟩
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hpow : (q : ℝ) ^ ε / (q : ℝ) = (q : ℝ) ^ (-1 + ε) := by
    rw [Real.rpow_add hqreal, Real.rpow_neg_one]
    ring
  have hb := hsubpower q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hsq
  rw [singularSeriesConstant_eq_orderedValue M χ A hA hdet hns hχ] at hexplicit
  calc
    _ ≤ ‖singularSeriesValue 1 A 0‖ * (4 * K) ^ q.primeFactors.card / (q : ℝ) :=
      hexplicit
    _ ≤ ‖singularSeriesValue 1 A 0‖ * (B * (q : ℝ) ^ ε) / (q : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) hqreal.le
    _ = ‖singularSeriesValue 1 A 0‖ * B * (q : ℝ) ^ (-1 + ε) := by
      rw [show ‖singularSeriesValue 1 A 0‖ * (B * (q : ℝ) ^ ε) / (q : ℝ) =
        ‖singularSeriesValue 1 A 0‖ * B * ((q : ℝ) ^ ε / (q : ℝ)) by ring, hpow]
    _ ≤ (‖singularSeriesValue 1 A 0‖ + 1) * B * (q : ℝ) ^ (-1 + ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hqreal.le _)
      apply mul_le_mul_of_nonneg_right _ hB.le
      linarith

end QuaternaryQuadraticForms

