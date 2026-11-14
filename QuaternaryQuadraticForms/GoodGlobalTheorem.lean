import QuaternaryQuadraticForms.ConeCompleteSum
import QuaternaryQuadraticForms.SourceGoodModulus
import QuaternaryQuadraticForms.SourceCompositeWeights

/-!
# Complete Lemma 3.5 with the original source character and weights

The source supplies a Dirichlet character with its stated Legendre
values at good primes. Their agreement at every good composite modulus
is proved by prime induction. The right-hand weight is the literal
product of the original functions at primes outside `N`.

Both conclusions use the actual gcd and quotient from source `eq:q1q2`.
The dual-cone conclusion permits every positive modulus, including
arbitrary bad-prime factors, using the source radical condition.
-/

noncomputable section

namespace QuaternaryQuadraticForms

local instance (q c : ℕ) [NeZero q] : NeZero (q.gcd c) :=
  ⟨Nat.gcd_ne_zero_left (NeZero.ne q)⟩

local instance (q c : ℕ) [NeZero q] : NeZero (q / q.gcd c) :=
  ⟨(Nat.div_gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

/-- The good-modulus clause of Lemma 3.5, with the original supplied
Dirichlet character and the literal product of supplied prime weights. -/
theorem source_mixedCompleteSum_good_modulus (N M : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (χ : DirichletCharacter ℂ M)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
    (u : Fin 4 → ℤ) :
    mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
      constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
        (q.gcd c : ℂ) * (c : ℂ) ^ 2 * χ ((q.gcd c * c : ℕ) : ZMod M) *
          sourceCompositeWeight N ξ (q.gcd c)
            (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
              integralRamanujanSum (q.gcd c * c)
                (dotProduct u (A.adjugate.mulVec u)) := by
  have hgood : (q.gcd c * c).Coprime (quadraticBadPrimeModulus A) :=
    (hc.of_dvd_left (Nat.gcd_dvd_right q c)).mul_left hc
  rw [mixedCompleteSum_good_modulus (extendPrimeWeights N ξ) q c hq A hA hc
    (primeWeightsInvariant_extend N q ξ hqN hξ) u,
    globalQuadraticChar_eq_dirichletCharacter A.det M χ hχ (q.gcd c * c) hgood,
    compositeWeight_extend_eq_source N (q.gcd c) ξ
      (hqN.of_dvd_left (Nat.gcd_dvd_left q c))]

/-- The full dual-cone clause for every positive modulus, using the
source radical condition and retaining the original character and weights. -/
theorem source_mixedCompleteSum_dual_cone (N M : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (χ : DirichletCharacter ℂ M)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
      constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
        (q.gcd c : ℂ) ^ 2 * χ ((q.gcd c : ℕ) : ZMod M) *
          sourceCompositeWeight N ξ (q.gcd c)
            (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
              unweightedCompleteSum c A u := by
  have hqA := source_coprime_quadraticBadPrimeModulus N q A hdet hrad hqN
  have hdA := hqA.of_dvd_left (Nat.gcd_dvd_left q c)
  rw [mixedCompleteSum_dual_cone (extendPrimeWeights N ξ) q c hq A hA hqA
    (primeWeightsInvariant_extend N q ξ hqN hξ) u hu,
    globalQuadraticChar_eq_dirichletCharacter A.det M χ hχ (q.gcd c) hdA,
    compositeWeight_extend_eq_source N (q.gcd c) ξ
      (hqN.of_dvd_left (Nat.gcd_dvd_left q c))]

/-- Both clauses of Lemma 3.5 for the source's supplied Dirichlet
character and prime functions, with its actual gcd factors and complete sums. -/
theorem source_good_global_complete_sum (N M : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (χ : DirichletCharacter ℂ M)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ))
    (hξ : ∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
      ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y)
    (u : Fin 4 → ℤ) :
    (c.Coprime (quadraticBadPrimeModulus A) →
      mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
        constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
          (q.gcd c : ℂ) * (c : ℂ) ^ 2 * χ ((q.gcd c * c : ℕ) : ZMod M) *
            sourceCompositeWeight N ξ (q.gcd c)
              (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
                integralRamanujanSum (q.gcd c * c)
                  (dotProduct u (A.adjugate.mulVec u))) ∧
    (dotProduct u (A.adjugate.mulVec u) = 0 →
      mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
        constrainedFourierSum (extendPrimeWeights N ξ) (q / q.gcd c) A u *
          (q.gcd c : ℂ) ^ 2 * χ ((q.gcd c : ℕ) : ZMod M) *
            sourceCompositeWeight N ξ (q.gcd c)
              (hqN.of_dvd_left (Nat.gcd_dvd_left q c)) (A.adjugate.mulVec u) *
                unweightedCompleteSum c A u) :=
  ⟨fun hc => source_mixedCompleteSum_good_modulus N M ξ χ q c hq hqN A hA hc hχ hξ u,
    fun hu => source_mixedCompleteSum_dual_cone N M ξ χ q c hq hqN A hA hdet hrad hχ hξ u hu⟩

end QuaternaryQuadraticForms
