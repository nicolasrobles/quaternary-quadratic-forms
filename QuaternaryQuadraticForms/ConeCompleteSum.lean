import QuaternaryQuadraticForms.GoodGlobalCompleteSum
import QuaternaryQuadraticForms.ModulusPrimeSplit

/-!
# The mixed-sum identity on the dual cone

The good-modulus formula specializes using the actual Ramanujan value
at zero and the totient identity for a divisor of the modulus. For an
arbitrary modulus, the proved prime-support decomposition separates the
bad factor. The actual unweighted sum at that factor is multiplied
through both CRT identities, so its possible vanishing is included.
-/

noncomputable section

namespace QuaternaryQuadraticForms

local instance (q c : ℕ) [NeZero q] : NeZero (q.gcd c) :=
  ⟨Nat.gcd_ne_zero_left (NeZero.ne q)⟩

local instance (q c : ℕ) [NeZero q] : NeZero (q / q.gcd c) :=
  ⟨(Nat.div_gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

/-- On the actual dual cone, the good-modulus formula has the exact
source coefficient multiplying the existing unweighted complete sum. -/
theorem mixedCompleteSum_good_modulus_dual_cone
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ)
    (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    mixedCompleteSum ξ q c A u =
      constrainedFourierSum ξ (q / q.gcd c) A u *
        (q.gcd c : ℂ) ^ 2 * globalQuadraticChar A.det (q.gcd c) *
          compositeWeight ξ (q.gcd c) (A.adjugate.mulVec u) *
            unweightedCompleteSum c A u := by
  rw [mixedCompleteSum_good_modulus ξ q c hq A hA hc hξ u,
    unweightedCompleteSum_good_modulus c A hA hc u, hu,
    integralRamanujanSum_zero, integralRamanujanSum_zero,
    totient_mul_of_dvd _ _ (Nat.gcd_dvd_right q c),
    globalQuadraticChar_mul]
  push_cast
  ring

/-- The complete dual-cone clause of Lemma 3.5 for every positive
modulus, including arbitrary bad-prime factors and zero sum values. -/
theorem mixedCompleteSum_dual_cone
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ)
    (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    mixedCompleteSum ξ q c A u =
      constrainedFourierSum ξ (q / q.gcd c) A u *
        (q.gcd c : ℂ) ^ 2 * globalQuadraticChar A.det (q.gcd c) *
          compositeWeight ξ (q.gcd c) (A.adjugate.mulVec u) *
            unweightedCompleteSum c A u := by
  obtain ⟨b, g, hb, hg, hcg, hbg, hgA, hbA⟩ :=
    exists_modulus_prime_split c (quadraticBadPrimeModulus A) (NeZero.ne c)
  letI : NeZero b := ⟨hb⟩
  letI : NeZero g := ⟨hg⟩
  have hqb := coprime_of_prime_dvd_support q b (quadraticBadPrimeModulus A) hqA hbA
  have hblocks : (1 * b).Coprime (q * g) := by
    simpa only [Nat.one_mul] using hqb.symm.mul_right hbg
  have hξprod : PrimeWeightsInvariant ξ (1 * q) := by
    simpa only [Nat.one_mul] using hξ
  have hsplit := mixedCompleteSum_crt ξ 1 q b g A u hblocks hξprod
  have hSc := unweightedCompleteSum_mul b g A u hbg
  have hgcd := gcd_eq_good_part_of_prime_support q c b g
    (quadraticBadPrimeModulus A) hqA hcg hbA
  have hsplit' : mixedCompleteSum ξ q c A u =
      unweightedCompleteSum b A u * mixedCompleteSum ξ q g A u := by
    simpa only [Nat.one_mul, ← hcg, mixedCompleteSum_one_left] using hsplit
  have hSc' : unweightedCompleteSum c A u =
      unweightedCompleteSum b A u * unweightedCompleteSum g A u := by
    simpa only [← hcg] using hSc
  rw [hsplit', mixedCompleteSum_good_modulus_dual_cone ξ q g hq A hA hgA hξ u hu]
  simp only [hgcd]
  rw [hSc']
  ring

end QuaternaryQuadraticForms
