import QuaternaryQuadraticForms.EliminationFamily
import QuaternaryQuadraticForms.GenericQuadricFamily
import QuaternaryQuadraticForms.GeometricReduction

/-!
# Resultants for the actual bad-reduction equations

The fixed generic family is specialized before applying the literal
geometric rank criterion. The resulting integer polynomials depend only
on the fixed quadratic matrix and the degree, not on the coefficients of G
or on the field. Their integer values detect characteristic-zero smoothness
and bad reduction at each prime.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- A fixed integer family detects the actual common geometric zero
condition after every field specialization of every integral form. -/
theorem badReduction_resultants_over_fields
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (HomogeneousMonomial 4 n) ℤ),
      ∀ (K : Type) [Field K] (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        (HasNonzeroGeometricZero
          (fun i => (badReductionSystem A G i).map (Int.castRingHom K)) ↔
          ∀ j, ((MvPolynomial.eval
            (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j) : ℤ) : K) = 0) := by
  obtain ⟨s, R, hR⟩ := homogeneous_parameter_resultants 4 (by decide)
    BadReductionIndex (HomogeneousMonomial 4 n) (badReductionSystemDegree n)
    (badReductionSystemDegree_pos hn) (genericBadReductionSystem A n)
    (genericBadReductionSystem_homogeneous A hn)
  refine ⟨s, R, ?_⟩
  intro K _ G hG
  have h := hR K (fun m : HomogeneousMonomial 4 n => ((G.coeff m.val : ℤ) : K))
  have hsystem :
      (fun i => (genericBadReductionSystem A n i).map
        (MvPolynomial.eval₂Hom (Int.castRingHom K)
          (fun m : HomogeneousMonomial 4 n => ((G.coeff m.val : ℤ) : K)))) =
      (fun i => (badReductionSystem A G i).map (Int.castRingHom K)) := by
    funext i
    rw [genericBadReductionSystem_specialize_intCast A G hG i,
      badReductionSystem_map]
  rw [hsystem] at h
  have heval (j : Fin s) :
      MvPolynomial.eval₂ (Int.castRingHom K)
        (fun m : HomogeneousMonomial 4 n => ((G.coeff m.val : ℤ) : K)) (R j) =
      ((MvPolynomial.eval
        (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j) : ℤ) : K) :=
    (MvPolynomial.eval₂_comp (Int.castRingHom K)
      (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j)).symm
  simpa only [heval] using h

/-- The same fixed family has a nonzero integer value precisely under
characteristic-zero smoothness, and every value is divisible by a prime
precisely when the actual rank condition fails at that prime. -/
theorem badReduction_resultant_family
    (A : Matrix (Fin 4) (Fin 4) ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (R : Fin s → MvPolynomial (HomogeneousMonomial 4 n) ℤ),
      (∀ (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        (SmoothCharacteristicZero A G ↔
          ∃ j, MvPolynomial.eval
            (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j) ≠ 0)) ∧
      (∀ (p : ℕ) [Fact p.Prime] (G : MvPolynomial (Fin 4) ℤ), G.IsHomogeneous n →
        (¬ GoodReductionAt p A G ↔
          ∀ j, (p : ℤ) ∣ MvPolynomial.eval
            (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j))) := by
  obtain ⟨s, R, hR⟩ := badReduction_resultants_over_fields A n hn
  refine ⟨s, R, ?_, ?_⟩
  · intro G hG
    have h := hR ℚ G hG
    rw [hasNonzeroGeometricZero_badReductionSystem_rat_iff] at h
    constructor
    · intro hsmooth
      by_contra! hzero
      apply (h.mpr ?_) hsmooth
      intro j
      rw [hzero j]
      simp
    · rintro ⟨j, hj⟩
      by_contra hsmooth
      exact hj (Int.cast_eq_zero.mp (h.mp hsmooth j))
  · intro p _ G hG
    have h := hR (ZMod p) G hG
    rw [hasNonzeroGeometricZero_badReductionSystem_zmod_iff] at h
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using h

/-- Characteristic-zero smoothness produces one actual nonzero integer
divisible by every prime in the manuscript's bad-reduction set. -/
theorem exists_nonzero_badReduction_divisor
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ} (hn : 2 ≤ n)
    (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n)
    (hsmooth : SmoothCharacteristicZero A G) :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ p ∈ badReductionPrimes A G, (p : ℤ) ∣ z := by
  obtain ⟨s, R, hzero, hprime⟩ := badReduction_resultant_family A n hn
  obtain ⟨j, hj⟩ := (hzero G hG).mp hsmooth
  refine ⟨MvPolynomial.eval (fun m : HomogeneousMonomial 4 n => G.coeff m.val) (R j),
    hj, ?_⟩
  intro p hp
  obtain ⟨hpprime, _, hpbad⟩ := hp
  letI : Fact p.Prime := ⟨hpprime⟩
  exact (hprime p G hG).mp hpbad j

/-- The actual bad-prime set is finite under the manuscript's
characteristic-zero smoothness hypothesis. -/
theorem badReductionPrimes_finite_of_smooth
    (A : Matrix (Fin 4) (Fin 4) ℤ) {n : ℕ} (hn : 2 ≤ n)
    (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n)
    (hsmooth : SmoothCharacteristicZero A G) :
    (badReductionPrimes A G).Finite := by
  obtain ⟨z, hz, hdiv⟩ := exists_nonzero_badReduction_divisor A hn G hG hsmooth
  exact badReductionPrimes_finite_of_common_divisor A G z hz hdiv

end QuaternaryQuadraticForms
