import QuaternaryQuadraticForms.CongruenceBoxCount
import QuaternaryQuadraticForms.InverseNormBoxBound

/-!
# Both bounds in Lemma 3.10

The coefficient-uniform polynomial-box estimate gives the unweighted
Euclidean count. Applying the finite halving lemma to the actual nonzero
congruence solutions gives the original indicator-weighted sum. A single
constant depending only on `E` and `ε` bounds both clauses, uniformly in
the integral matrix, its coefficients, the excluded primes and all local
polynomials.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Both source bounds with one constant chosen before every arithmetic,
polynomial and radius parameter. The weighted expression is the literal
sum of the original indicator divided by the Euclidean norm. -/
theorem congruenceBox_bounds (E : ℕ) (hE : 1 ≤ E) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (A : Matrix (Fin 4) (Fin 4) ℤ), A.transpose = A → A.det ≠ 0 →
      ∀ (N : ℕ), primeRadical (quadraticBadPrimeModulus A) ∣ N →
      ∀ (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p)),
        (∀ p, p.Prime → ¬ p ∣ N → D p ≠ 0) →
        (∀ p, p.Prime → ¬ p ∣ N → (D p).totalDegree ≤ E) →
      ∀ (q h : ℕ), 1 ≤ q → 1 ≤ h → Squarefree q → Squarefree h →
        q.Coprime h → (q * h).Coprime N →
      ∀ (U : ℝ), 1 ≤ U →
        ((congruenceEuclideanBall A D q h U).card : ℝ) ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) ∧
          weightedCongruenceEuclideanSum A D q h U ≤
            K * ((q * h : ℕ) : ℝ) ^ ε * (U ^ 3 / ((q * h : ℕ) : ℝ) + U ^ 2) := by
  classical
  obtain ⟨K, hK, hbound⟩ := congruenceEuclideanBall_card_le_rpow E hE ε hε
  refine ⟨3 * K, by positivity, ?_⟩
  intro A hA hdet N hrad D hD hdeg q h hq hh hsq hsh hcop hcopN U hU
  have hm : (0 : ℝ) < ((q * h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hq)
      (lt_of_lt_of_le Nat.zero_lt_one hh)
  let B : ℝ := K * ((q * h : ℕ) : ℝ) ^ ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (T : ℝ) (hT : 1 ≤ T) :
      ((congruenceEuclideanBall A D q h T).card : ℝ) ≤
        B * (T ^ 4 / ((q * h : ℕ) : ℝ) + T ^ 3) :=
    hbound A hA hdet N hrad D hD hdeg q h hq hh hsq hsh hcop hcopN T hT
  constructor
  · calc
      _ ≤ B * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) := hb U hU
      _ ≤ 3 * B * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) := by
        have hn : 0 ≤ B * (U ^ 4 / ((q * h : ℕ) : ℝ) + U ^ 3) := by positivity
        nlinarith
      _ = _ := by dsimp [B]; ring
  · rw [weightedCongruenceEuclideanSum_eq]
    let s := (congruenceEuclideanBall A D q h U).filter (fun u => u ≠ 0)
    have hs (u : Fin 4 → ℤ) (hu : u ∈ s) :
        u ∈ congruenceEuclideanBall A D q h U ∧ u ≠ 0 :=
      Finset.mem_filter.mp hu
    have hr (u : Fin 4 → ℤ) (hu : u ∈ s) : 1 ≤ integerEuclideanNorm u :=
      one_le_integerEuclideanNorm u (hs u hu).2
    have hrU (u : Fin 4 → ℤ) (hu : u ∈ s) : integerEuclideanNorm u ≤ U :=
      ((mem_congruenceEuclideanBall A D q h U u).mp (hs u hu).1).1
    have hsublevel (T : ℝ) (hT : 1 ≤ T) :
        ((s.filter (fun u => integerEuclideanNorm u ≤ T)).card : ℝ) ≤
          B * (T ^ 4 / ((q * h : ℕ) : ℝ) + T ^ 3) := by
      apply le_trans _ (hb T hT)
      exact_mod_cast Finset.card_le_card (show
        s.filter (fun u => integerEuclideanNorm u ≤ T) ⊆
          congruenceEuclideanBall A D q h T from by
            intro u hu
            obtain ⟨hus, hur⟩ := Finset.mem_filter.mp hu
            have huc := (mem_congruenceEuclideanBall A D q h U u).mp (hs u hus).1
            exact (mem_congruenceEuclideanBall A D q h T u).mpr ⟨hur, huc.2⟩)
    calc
      _ ≤ 3 * B * (U ^ 3 / ((q * h : ℕ) : ℝ) + U ^ 2) :=
        inverseRadiusSum_le_of_sublevel_card s integerEuclideanNorm B
          ((q * h : ℕ) : ℝ) U hB hm hU hr hrU hsublevel
      _ = _ := by dsimp [B]; ring

end QuaternaryQuadraticForms
