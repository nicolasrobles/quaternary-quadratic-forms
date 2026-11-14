import QuaternaryQuadraticForms.PolynomialHeight
import QuaternaryQuadraticForms.BadReductionResultants

/-!
# The coefficient-height bound for the bad-reduction modulus

For the fixed quadratic matrix and degree, choose the finite resultant
family before choosing the coefficients of the second form. Its height
bound is therefore uniform in that form. Smoothness supplies a nonzero
integer value; every bad prime divides this value, giving finiteness and
the bound for the literal modulus in the manuscript.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Fixed constants bound a nonzero integer divisible by every actual
bad prime. The constants depend on the fixed matrix and degree, and are
chosen before the form `G` and its coefficients. -/
theorem exists_nonzero_badReduction_divisor_height_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        SmoothCharacteristicZero A G →
          ∃ z : ℤ, z ≠ 0 ∧
            (∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z) ∧
            z.natAbs ≤ K * (polynomialCoefficientHeight G) ^ C := by
  obtain ⟨s, R, hzero, hprime⟩ := badReduction_resultant_family A n hn
  obtain ⟨C, K, hC, hK, hbound⟩ :=
    finite_polynomial_family_coeff_eval_bound (τ := Fin 4) (Finset.univ : Finset (Fin s)) R
  refine ⟨C, K, hC, hK, ?_⟩
  intro G hG hsmooth
  obtain ⟨j, hj⟩ := (hzero G hG).mp hsmooth
  refine ⟨MvPolynomial.eval
    (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j), hj, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpprime, _, hpbad⟩ := hp
    letI : Fact p.Prime := ⟨hpprime⟩
    exact (hprime p G hG).mp hpbad j
  · exact hbound G (fun m : HomogeneousMonomial 4 n => m.val) j (Finset.mem_univ j)

/-- The actual modulus satisfies a uniform power bound in the actual
coefficient height, for every proof of finiteness of its defining set. -/
theorem polynomialBadPrimeModulus_height_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        SmoothCharacteristicZero A G →
          ∀ hfinite : (badReductionPrimes A G).Finite,
            polynomialBadPrimeModulus A G hfinite ≤
              K * (polynomialCoefficientHeight G) ^ C := by
  obtain ⟨C, K, hC, hK, hbound⟩ :=
    exists_nonzero_badReduction_divisor_height_bound A n hn
  refine ⟨C, primeRadical (quadraticBadPrimeModulus A) * K, hC, ?_, ?_⟩
  · have hrad : 1 ≤ primeRadical (quadraticBadPrimeModulus A) := primeRadical_pos _
    simpa only [one_mul] using Nat.mul_le_mul hrad hK
  · intro G hG hsmooth hfinite
    obtain ⟨z, hz, hdiv, hheight⟩ := hbound G hG hsmooth
    calc
      polynomialBadPrimeModulus A G hfinite ≤
          primeRadical (quadraticBadPrimeModulus A) * z.natAbs :=
        polynomialBadPrimeModulus_le_of_common_divisor A G hfinite z hz hdiv
      _ ≤ primeRadical (quadraticBadPrimeModulus A) *
          (K * (polynomialCoefficientHeight G) ^ C) := Nat.mul_le_mul_left _ hheight
      _ = (primeRadical (quadraticBadPrimeModulus A) * K) *
          (polynomialCoefficientHeight G) ^ C := (Nat.mul_assoc _ _ _).symm

/-- Lemma 4.1(i): characteristic-zero smoothness gives finiteness of the
literal bad-prime set and a coefficient-height bound for its modulus,
with constants chosen uniformly over all forms of the fixed degree. -/
theorem badReductionPrimes_finite_and_height_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        SmoothCharacteristicZero A G →
          ∃ hfinite : (badReductionPrimes A G).Finite,
            polynomialBadPrimeModulus A G hfinite ≤
              K * (polynomialCoefficientHeight G) ^ C := by
  obtain ⟨C, K, hC, hK, hbound⟩ := polynomialBadPrimeModulus_height_bound A n hn
  refine ⟨C, K, hC, hK, ?_⟩
  intro G hG hsmooth
  exact ⟨badReductionPrimes_finite_of_smooth A hn G hG hsmooth,
    hbound G hG hsmooth _⟩

end QuaternaryQuadraticForms
