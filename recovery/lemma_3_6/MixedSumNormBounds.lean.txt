import QuaternaryQuadraticForms.GoodGlobalCompleteSum
import QuaternaryQuadraticForms.ModulusPrimeSplit
import QuaternaryQuadraticForms.BadPrimeBound
import QuaternaryQuadraticForms.SourceWeights
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Norm bounds for the actual mixed complete sums

The local weight hypotheses bound the actual prime product. Taking norms
in the proved good-modulus formula then leaves the constrained Fourier
sum and the actual Ramanujan sum. For an arbitrary positive modulus, the
proved CRT identity separates the bad-prime factor; the uniform unweighted
bound controls that factor, and only positive real modulus powers cancel.
-/

noncomputable section

namespace QuaternaryQuadraticForms

local instance (q c : ℕ) [NeZero q] : NeZero (q.gcd c) :=
  ⟨Nat.gcd_ne_zero_left (NeZero.ne q)⟩

local instance (q c : ℕ) [NeZero q] : NeZero (q / q.gcd c) :=
  ⟨(Nat.div_gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

/-- The actual Jacobi coefficient has norm at most one at every modulus. -/
theorem globalQuadraticChar_norm_le (α : ℤ) (n : ℕ) :
    ‖globalQuadraticChar α n‖ ≤ 1 := by
  rcases jacobiSym.trichotomy α n with h | h | h <;>
    simp [globalQuadraticChar, h]

/-- The source's local norm bounds control its actual composite weight. -/
theorem compositeWeight_norm_le
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (x : Fin 4 → ℤ) : ‖compositeWeight ξ q x‖ ≤ 1 := by
  rw [compositeWeight, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun p hp => hξnorm p hp _)

/-- The source family's norm bound is inherited at every prime of a
modulus coprime to its excluded-prime modulus. -/
theorem primeWeightsNorm_le_extend (N q : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hqN : q.Coprime N)
    (hξnorm : ∀ p (hp : p.Prime) (hN : ¬p ∣ N),
      ∀ x : Fin 4 → ZMod p, ‖ξ p hp hN x‖ ≤ 1) :
    ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p,
      ‖extendPrimeWeights N ξ p x‖ ≤ 1 := by
  intro p hp x
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hN : ¬p ∣ N := hprime.coprime_iff_not_dvd.mp
    (hqN.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  simpa only [extendPrimeWeights_apply N ξ p hprime hN] using hξnorm p hprime hN x

/-- Taking norms in the actual good-modulus evaluation removes just the
two factors whose norms are at most one. -/
theorem mixedCompleteSum_good_modulus_norm_le
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (hξ : PrimeWeightsInvariant ξ q)
    (hξnorm : ∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1)
    (u : Fin 4 → ℤ) :
    ‖mixedCompleteSum ξ q c A u‖ ≤
      ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ *
        (q.gcd c : ℝ) * (c : ℝ) ^ 2 *
          ‖integralRamanujanSum (q.gcd c * c)
            (dotProduct u (A.adjugate.mulVec u))‖ := by
  have hχ := globalQuadraticChar_norm_le A.det (q.gcd c * c)
  have hw := compositeWeight_norm_le ξ (q.gcd c)
    (fun p hp => hξnorm p (Nat.primeFactors_mono (Nat.gcd_dvd_left q c) (NeZero.ne q) hp))
    (A.adjugate.mulVec u)
  rw [mixedCompleteSum_good_modulus ξ q c hq A hA hc hξ u]
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ *
        (q.gcd c : ℝ) * (c : ℝ) ^ 2 * 1 * 1 *
          ‖integralRamanujanSum (q.gcd c * c)
            (dotProduct u (A.adjugate.mulVec u))‖ := by
      gcongr
    _ = _ := by ring

/-- The actual CRT factorization for a bad-prime part and its coprime
good-prime complement. It includes possible zero complete-sum values. -/
theorem mixedCompleteSum_eq_bad_mul_good
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q c b g : ℕ) [NeZero q] [NeZero c] [NeZero b] [NeZero g]
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hqA : q.Coprime (quadraticBadPrimeModulus A))
    (hcg : c = b * g) (hbg : b.Coprime g)
    (hbA : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ quadraticBadPrimeModulus A)
    (hξ : PrimeWeightsInvariant ξ q) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ q c A u =
      unweightedCompleteSum b A u * mixedCompleteSum ξ q g A u := by
  have hqb := coprime_of_prime_dvd_support q b (quadraticBadPrimeModulus A) hqA hbA
  have hblocks : (1 * b).Coprime (q * g) := by
    simpa only [Nat.one_mul] using hqb.symm.mul_right hbg
  have hξprod : PrimeWeightsInvariant ξ (1 * q) := by
    simpa only [Nat.one_mul] using hξ
  have hsplit := mixedCompleteSum_crt ξ 1 q b g A u hblocks hξprod
  simpa only [Nat.one_mul, ← hcg, mixedCompleteSum_one_left] using hsplit

/-- The uniform bad-prime bound and the actual good-modulus identity give
a normalized bound for every positive bad/good prime-support split. -/
theorem mixedCompleteSum_div_cube_le_of_prime_split
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
        ‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) *
          ‖integralRamanujanSum (q.gcd c * g)
            (dotProduct u (A.adjugate.mulVec u))‖ / (g : ℝ) := by
  have hgcd := gcd_eq_good_part_of_prime_support q c b g
    (quadraticBadPrimeModulus A) hqA hcg hbA
  have hgood := mixedCompleteSum_good_modulus_norm_le ξ q g hq A hA hgA hξ hξnorm u
  simp only [← hgcd] at hgood
  have hbad := unweightedCompleteSum_norm_le b A hA hdet u
  have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
  have hgpos : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hcgR : (c : ℝ) = (b : ℝ) * (g : ℝ) := by exact_mod_cast hcg
  rw [mixedCompleteSum_eq_bad_mul_good ξ q c b g A hqA hcg hbg hbA hξ u, norm_mul]
  calc
    _ ≤ (4 * Real.sqrt (A.det.natAbs : ℝ) * (b : ℝ) ^ 3) *
        (‖constrainedFourierSum ξ (q / q.gcd c) A u‖ * (q.gcd c : ℝ) *
          (g : ℝ) ^ 2 * ‖integralRamanujanSum (q.gcd c * g)
            (dotProduct u (A.adjugate.mulVec u))‖) / (c : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hcpos 3))
      exact mul_le_mul hbad hgood (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [hcgR]
      field_simp

end QuaternaryQuadraticForms
