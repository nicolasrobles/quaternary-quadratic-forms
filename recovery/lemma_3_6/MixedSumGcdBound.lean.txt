import QuaternaryQuadraticForms.MixedSumNormBounds
import QuaternaryQuadraticForms.RamanujanGcdBound

/-!
# Gcd estimates and divisibility support for mixed complete sums

The actual Ramanujan gcd estimate supplies a uniform pointwise bound
for every bad/good prime-support split. The repeated shared primes force
the actual complete sum to vanish outside the source's divisibility
condition, with no local norm hypothesis needed for that vanishing.
-/

noncomputable section

namespace QuaternaryQuadraticForms

local instance (q c : ℕ) [NeZero q] : NeZero (q.gcd c) :=
  ⟨Nat.gcd_ne_zero_left (NeZero.ne q)⟩

local instance (q c : ℕ) [NeZero q] : NeZero (q / q.gcd c) :=
  ⟨(Nat.div_gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

/-- The actual good-modulus mixed sum vanishes unless its shared
squarefree factor divides the integral dual value. -/
theorem mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ)
    (hu : ¬(q.gcd c : ℤ) ∣ dotProduct u (A.adjugate.mulVec u)) :
    mixedCompleteSum ξ q c A u = 0 := by
  rw [mixedCompleteSum_good_modulus ξ q c hq A hA hc hξ u,
    integralRamanujanSum_shared_eq_zero (q.gcd c) c
      (hq.squarefree_of_dvd (Nat.gcd_dvd_left q c)) (Nat.gcd_dvd_right q c) _ hu,
    mul_zero]

/-- The source's divisibility support holds at every positive modulus,
including arbitrary bad-prime factors and without a norm assumption. -/
theorem mixedCompleteSum_eq_zero_of_gcd_not_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ)
    (hu : ¬(q.gcd c : ℤ) ∣ dotProduct u (A.adjugate.mulVec u)) :
    mixedCompleteSum ξ q c A u = 0 := by
  obtain ⟨b, g, hb, hg, hcg, hbg, hgA, hbA⟩ :=
    exists_modulus_prime_split c (quadraticBadPrimeModulus A) (NeZero.ne c)
  letI : NeZero b := ⟨hb⟩
  letI : NeZero g := ⟨hg⟩
  have hgcd := gcd_eq_good_part_of_prime_support q c b g
    (quadraticBadPrimeModulus A) hqA hcg hbA
  have hug : ¬(q.gcd g : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) := by
    simpa only [hgcd] using hu
  rw [mixedCompleteSum_eq_bad_mul_good ξ q c b g A hqA hcg hbg hbA hξ u,
    mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd ξ q g hq A hA hgA hξ u hug,
    mul_zero]

/-- The actual Ramanujan gcd estimate turns the normalized mixed-sum
bound into the arithmetic expression summed in Lemma 3.6. -/
theorem mixedCompleteSum_div_cube_le_gcd_of_prime_split
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c b g : ℕ) [NeZero q] [NeZero c] [NeZero b] [NeZero g]
    (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hcg : c = b * g) (hbg : b.Coprime g)
    (hgA : g.Coprime (quadraticBadPrimeModulus A))
    (hbA : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ quadraticBadPrimeModulus A)
    (hξ : PrimeWeightsInvariant ξ q)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (u : Fin 4 → ℤ) :
    ‖mixedCompleteSum ξ q c A u‖ / (c : ℝ) ^ 3 ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) *
        ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) ^ 2 *
          (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ) := by
  calc
    _ ≤ 4 * Real.sqrt (A.det.natAbs : ℝ) *
        ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) *
          ‖integralRamanujanSum (q.gcd c * g)
            (dotProduct u (A.adjugate.mulVec u))‖ / (g : ℝ) :=
      mixedCompleteSum_div_cube_le_of_prime_split ξ q c b g hq A hA hdet
        hqA hcg hbg hgA hbA hξ hξnorm u
    _ ≤ 4 * Real.sqrt (A.det.natAbs : ℝ) *
        ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) *
          ((q.gcd c : ℝ) *
            (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ)) / (g : ℝ) := by
      gcongr
      exact integralRamanujanSum_mul_norm_le (q.gcd c) g _
    _ = _ := by ring

/-- The normalized arithmetic bound with the exact shared-factor
indicator, derived from the actual mixed sum's vanishing. -/
theorem mixedCompleteSum_div_cube_le_gcd_indicator_of_prime_split
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c b g : ℕ) [NeZero q] [NeZero c] [NeZero b] [NeZero g]
    (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hcg : c = b * g) (hbg : b.Coprime g)
    (hgA : g.Coprime (quadraticBadPrimeModulus A))
    (hbA : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ quadraticBadPrimeModulus A)
    (hξ : PrimeWeightsInvariant ξ q)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (u : Fin 4 → ℤ) :
    ‖mixedCompleteSum ξ q c A u‖ / (c : ℝ) ^ 3 ≤
      if (q.gcd c : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) then
        4 * Real.sqrt (A.det.natAbs : ℝ) *
          ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) ^ 2 *
            (Nat.gcd g (dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) / (g : ℝ)
      else 0 := by
  split_ifs with hu
  · exact mixedCompleteSum_div_cube_le_gcd_of_prime_split ξ q c b g hq A hA hdet
      hqA hcg hbg hgA hbA hξ hξnorm u
  · rw [mixedCompleteSum_eq_zero_of_gcd_not_dvd ξ q c hq A hA hqA hξ u hu,
      norm_zero, zero_div]

end QuaternaryQuadraticForms
