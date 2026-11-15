import QuaternaryQuadraticForms.SourceFourierSums
import QuaternaryQuadraticForms.SourceGoodModulus
import QuaternaryQuadraticForms.SingularSeriesBoundary

/-!
# The actual source main coefficient

The coefficient is defined by the original source Fourier sum and the
already proved ordered coprime singular series. Its local product is a
finite algebraic consequence of the source CRT factorization and the
singular-series identity. The modulus-one specialization also identifies
the source singular-series constant independently of its supplied character.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The manuscript's main coefficient, using the literal source Fourier sum
and the increasing-modulus value of its coprime complete-sum series. -/
def sourceMainCoefficient (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) : ℂ :=
  sourceConstrainedFourierSum N ξ q hqN A 0 / (q : ℂ) ^ 3 *
    singularSeriesValue q A 0

/-- The reciprocal-density product can be indexed by the same finite prime
subtype as the actual source Fourier product. -/
theorem singularSeriesRemovalFactor_eq_primeFactors (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    singularSeriesRemovalFactor q A =
      ∏ p : q.primeFactors,
        letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
        (localQuadraticDensity p.val A : ℂ)⁻¹ := by
  classical
  unfold singularSeriesRemovalFactor singularSeriesPrimeDivisors
  apply Finset.prod_bij (fun (p : Nat.Primes) (hp : p ∈ q.primeFactors.subtype Nat.Prime) =>
    (⟨p.val, Finset.mem_subtype.mp hp⟩ : q.primeFactors))
  · intro p hp
    exact Finset.mem_univ _
  · intro p hp p' hp' heq
    exact Subtype.ext (congrArg (fun x : q.primeFactors => x.val) heq)
  · intro p _
    refine ⟨⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩, ?_, ?_⟩
    · exact Finset.mem_subtype.mpr p.property
    · rfl
  · intro p hp
    rfl

/-- With no prime factors removed, the correction is the empty product. -/
@[simp]
theorem singularSeriesRemovalFactor_one (A : Matrix (Fin 4) (Fin 4) ℤ) :
    singularSeriesRemovalFactor 1 A = 1 := by
  have hempty : singularSeriesPrimeDivisors 1 = ∅ := by
    unfold singularSeriesPrimeDivisors
    rw [Nat.primeFactors_one]
    exact Finset.subtype_eq_empty.mpr (by simp)
  rw [singularSeriesRemovalFactor, hempty, Finset.prod_empty]

/-- Every admissible supplied character yields the same source constant:
the actual ordered complete-sum series at modulus one. -/
theorem singularSeriesConstant_eq_orderedValue
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ)) :
    singularSeriesConstant M χ A = singularSeriesValue 1 A 0 := by
  simpa only [singularSeriesRemovalFactor_one, mul_one] using
    (singularSeriesValue_zero_eq M χ A hA hdet hns hχ 1 (Nat.coprime_one_left _)).symm

/-- The source constant is independent of the supplied character level and
character whenever both satisfy the original good-prime agreement. -/
theorem singularSeriesConstant_eq_of_goodPrimeAgreement
    (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ₁ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ₁ (p : ZMod M₁) = (legendreSym p A.det : ℂ))
    (hχ₂ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ₂ (p : ZMod M₂) = (legendreSym p A.det : ℂ)) :
    singularSeriesConstant M₁ χ₁ A = singularSeriesConstant M₂ χ₂ A := by
  rw [singularSeriesConstant_eq_orderedValue M₁ χ₁ A hA hdet hns hχ₁,
    singularSeriesConstant_eq_orderedValue M₂ χ₂ A hA hdet hns hχ₂]

/-- The modulus-one coefficient is the actual full ordered series, since
its source Fourier sum is the empty prime product. -/
@[simp]
theorem sourceMainCoefficient_one (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hN : Nat.Coprime 1 N) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    sourceMainCoefficient N ξ 1 hN A = singularSeriesValue 1 A 0 := by
  simp only [sourceMainCoefficient, sourceConstrainedFourierSum_one,
    Nat.cast_one, one_pow, div_one, one_mul]

/-- In the source notation the empty-product coefficient is exactly `S_F`. -/
theorem sourceMainCoefficient_one_eq_singularSeriesConstant
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hN : Nat.Coprime 1 N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ)) :
    sourceMainCoefficient N ξ 1 hN A = singularSeriesConstant M χ A := by
  rw [sourceMainCoefficient_one,
    singularSeriesConstant_eq_orderedValue M χ A hA hdet hns hχ]

/-- Equation `Sxi`: the actual global-series definition equals the product
of the original source prime sums divided by their actual counting densities.
Every factor belongs to a good prime; the empty product covers `q = 1`. -/
theorem sourceMainCoefficient_eq_prime_product
    (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (N : ℕ) (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p (hp : p.Prime) (hpN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hpN (r • y) = ξ p hp hpN y)
    (q : ℕ) [NeZero q] (hsq : Squarefree q) (hqN : q.Coprime N) :
    sourceMainCoefficient N ξ q hqN A =
      singularSeriesConstant M χ A *
        ∏ p : q.primeFactors,
          letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
          sourceConstrainedFourierSum N ξ p.val
            (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property)) A 0 /
            ((p.val : ℂ) ^ 3 * (localQuadraticDensity p.val A : ℂ)) := by
  classical
  have hq : q.Coprime (quadraticBadPrimeModulus A) :=
    source_coprime_quadraticBadPrimeModulus N q A hdet hrad hqN
  have hprod : (∏ p : q.primeFactors, (p.val : ℂ)) = (q : ℂ) := by
    rw [Finset.prod_coe_sort, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [sourceMainCoefficient, singularSeriesValue_zero_eq M χ A hA hdet hns hχ q hq,
    sourceConstrainedFourierSum_primeFactors N ξ q hqN A 0 hsq hξ,
    singularSeriesRemovalFactor_eq_primeFactors,
    Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, hprod,
    Finset.prod_inv_distrib]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end QuaternaryQuadraticForms
