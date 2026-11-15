import QuaternaryQuadraticForms.CongruenceBoxDefinitions
import QuaternaryQuadraticForms.CongruenceBoxPolynomials
import QuaternaryQuadraticForms.PolynomialBoxEpsilon

/-!
# The unweighted Euclidean congruence count

The actual source solutions lie in the integer coordinate box of side
cardinality at most `3 U`. Lemma 2.4 with degree bound `max 2 E` applies
to the actual combined polynomials. Its coefficient-independent constant
is selected before the matrix, exceptional polynomials, and all moduli.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Every actual Euclidean solution is a solution of the combined prime
polynomials in its containing integer coordinate box. -/
theorem congruenceEuclideanBall_subset_polynomialBox
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q h : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h) (hsq : Squarefree q)
    (hcop : q.Coprime h) (U : ℝ) :
    congruenceEuclideanBall A D q h U ⊆
      polynomialBoxSolutions (q * h).primeFactors (boxCongruencePolynomial A D q)
        (fun _ => -⌊U⌋) (fun _ => ⌊U⌋) := by
  intro u hu
  obtain ⟨hU, hdiv, hD⟩ := (mem_congruenceEuclideanBall A D q h U u).mp hu
  apply (mem_polynomialBoxSolutions _ _ _ _ _).mpr
  refine ⟨integerEuclideanNorm_le_mem_box U u hU, ?_⟩
  exact (boxCongruencePolynomial_eval_eq_zero_iff A D q h hq hh hsq hcop u).mpr
    ⟨hdiv, (exceptionalIndicator_eq_one_iff D h u).mp hD⟩

/-- The first clause of Lemma 3.10, with the constant uniform in every
coefficient and modulus parameter. -/
theorem congruenceEuclideanBall_card_le_rpow (E : ℕ) (hE : 1 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
        ∀ (N : ℕ), primeRadical (quadraticBadPrimeModulus A) ∣ N →
          ∀ (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)),
            (∀ p, p.Prime → ¬ p ∣ N → D p ≠ 0) →
            (∀ p, p.Prime → ¬ p ∣ N → (D p).totalDegree ≤ E) →
            ∀ (q h : ℕ), 1 ≤ q → 1 ≤ h → Squarefree q → Squarefree h →
              q.Coprime h → (q * h).Coprime N → ∀ (U : ℝ), 1 ≤ U →
                ((congruenceEuclideanBall A D q h U).card : ℝ) ≤
                  K * ((q * h : ℕ) : ℝ) ^ ε *
                    (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) := by
  obtain ⟨K, hK, hb⟩ := polynomialBox_squarefree_card_le_rpow 4 (max 2 E)
    (by omega) (hE.trans (le_max_right 2 E)) ε hε
  refine ⟨81 * K, by positivity, ?_⟩
  intro A hA hdet N hrad D hD hdeg q h hq hh hsq hhsq hcop hcopN U hU
  have hqh : 1 ≤ q * h := Nat.mul_pos (by omega) (by omega)
  have hqhsq : Squarefree (q * h) := (Nat.squarefree_mul hcop).mpr ⟨hsq, hhsq⟩
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hcount := hb (q * h) hqh hqhsq (boxCongruencePolynomial A D q)
    (boxCongruencePolynomial_ne_zero A hA hdet N hrad D hD q h hcopN)
    (boxCongruencePolynomial_totalDegree_le A N E D hdeg q h hcopN)
    (fun _ => -⌊U⌋) (fun _ => ⌊U⌋) (3 * U) (by linarith)
    (fun _ => integerEuclideanInterval_card_le_three_mul U hU)
  have hsubset := congruenceEuclideanBall_subset_polynomialBox A D q h hq hh hsq hcop U
  have hscale : (3 * U) ^ 4 / ((q * h : ℕ) : ℝ) + (3 * U) ^ 3 ≤
      81 * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) := by
    ring_nf
    nlinarith [pow_nonneg hU0 3]
  calc
    _ ≤ ((polynomialBoxSolutions (q * h).primeFactors (boxCongruencePolynomial A D q)
        (fun _ => -⌊U⌋) (fun _ => ⌊U⌋)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ K * ((q * h : ℕ) : ℝ) ^ ε *
        ((3 * U) ^ 4 / ((q * h : ℕ) : ℝ) + (3 * U) ^ 3) := hcount
    _ ≤ K * ((q * h : ℕ) : ℝ) ^ ε *
        (81 * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end QuaternaryQuadraticForms
