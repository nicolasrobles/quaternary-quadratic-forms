import QuaternaryQuadraticForms.LocalDensityEulerProduct

/-!
# Complete Lemma 3.8

The endpoints assemble the actual counting limit, the absolutely convergent
complete-sum series, the exact good-prime density, and the corrected Euler
product with the original supplied source character. All intermediate
counting identities and convergence estimates have been proved internally.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped Topology

/-- The local assertions of Lemma 3.8 at every prime: the actual normalized
counts converge, the complete-sum series converges absolutely to that real
density, and its good-prime value is the exact rational expression. -/
theorem local_density (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Tendsto (normalizedPrimePowerZeroCount p A) atTop (𝓝 (localQuadraticDensity p A)) ∧
    Summable (fun k : ℕ => ‖localDensityTerm p A k‖) ∧
    HasSum (localDensityTerm p A) (localQuadraticDensity p A : ℂ) ∧
    (¬p ∣ quadraticBadPrimeModulus A →
      (localQuadraticDensity p A : ℂ) =
        (1 - (legendreSym p A.det : ℂ) / (p : ℂ) ^ 2) /
          (1 - (legendreSym p A.det : ℂ) / (p : ℂ))) :=
  ⟨tendsto_normalizedPrimePowerZeroCount p A hA hdet,
    summable_norm_localDensityTerm p A hA hdet,
    hasSum_localDensityTerm p A hA hdet,
    fun hp => localQuadraticDensity_goodPrime p A hA hdet hp⟩

/-- Complete Lemma 3.8 with the manuscript's original character: every
local-density limit and absolutely convergent local series, the good-prime
formula, and absolute convergence of the actual corrected Euler product.
The additional norm-product conclusion also covers finite zero bad factors. -/
theorem source_local_density (M : ℕ) (χ : DirichletCharacter ℂ M)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
      χ (p : ZMod M) = (legendreSym p A.det : ℂ)) :
    (∀ (p : ℕ) [Fact p.Prime],
      Tendsto (normalizedPrimePowerZeroCount p A) atTop (𝓝 (localQuadraticDensity p A)) ∧
      Summable (fun k : ℕ => ‖localDensityTerm p A k‖) ∧
      HasSum (localDensityTerm p A) (localQuadraticDensity p A : ℂ) ∧
      (¬p ∣ quadraticBadPrimeModulus A →
        (localQuadraticDensity p A : ℂ) =
          (1 - χ (p : ZMod M) / (p : ℂ) ^ 2) /
            (1 - χ (p : ZMod M) / (p : ℂ)))) ∧
    Summable (fun p : Nat.Primes => ‖correctedLocalDensityFactor M χ A p - 1‖) ∧
    Multipliable (correctedLocalDensityFactor M χ A) ∧
    Multipliable (fun p : Nat.Primes => ‖correctedLocalDensityFactor M χ A p‖) := by
  refine ⟨?_, summable_norm_correctedLocalDensityFactor_sub_one M χ A hA hdet hχ,
    multipliable_correctedLocalDensityFactor M χ A hA hdet hχ,
    multipliable_norm_correctedLocalDensityFactor M χ A hA hdet hχ⟩
  intro p _
  exact ⟨tendsto_normalizedPrimePowerZeroCount p A hA hdet,
    summable_norm_localDensityTerm p A hA hdet,
    hasSum_localDensityTerm p A hA hdet,
    fun hp => source_localQuadraticDensity_goodPrime M χ p A hA hdet hχ hp⟩

end QuaternaryQuadraticForms
