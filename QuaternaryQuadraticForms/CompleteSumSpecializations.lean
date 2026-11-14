import QuaternaryQuadraticForms.CompleteSums

/-!
# Definition bridges for the complete sums

The modulus-one cases recover the source's ordinary and constrained sums.
At a prime, the constrained sum is the actual finite-field cone sum, and
polynomial character weights recover the existing integral Fourier sum.
None of these identities needs scalar invariance or a character-order
condition on the weights.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- With cone modulus one, the mixed sum is the source's unweighted sum. -/
theorem mixedCompleteSum_one_left
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (c : ℕ) [NeZero c] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ 1 c A u = unweightedCompleteSum c A u := by
  let S (n : ℕ) [NeZero n] (a : ℤ) : ℂ :=
    ∑ x : Fin 4 → ZMod n, ZMod.stdAddChar
      ((a * integralQuadraticValue A (residueLift n x) +
        dotProduct u (residueLift n x) : ℤ) : ZMod n)
  have hS (m n : ℕ) [NeZero m] [NeZero n] (h : m = n) (a : ℤ) :
      S m a = S n a := by
    subst n
    rfl
  unfold mixedCompleteSum mixedIntegerSummand unweightedCompleteSum
  simp only [Nat.cast_one, one_dvd, ite_true, compositeWeight_one, one_mul]
  change (∑ a : (ZMod c)ˣ, S (1 * c) (((a : ZMod c).val : ℕ) : ℤ)) =
    ∑ a : (ZMod c)ˣ, S c (((a : ZMod c).val : ℕ) : ℤ)
  apply Finset.sum_congr rfl
  intro a _
  exact hS (1 * c) c (Nat.one_mul c) _

/-- With unit modulus one, its singleton unit contributes exactly the
constrained Fourier sum, including when the cone modulus is also one. -/
theorem mixedCompleteSum_one_right
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ q 1 A u = constrainedFourierSum ξ q A u := by
  have hunit (a : (ZMod 1)ˣ) : (((a : ZMod 1).val : ℕ) : ℤ) = 0 := by
    have ha : (a : ZMod 1) = 0 := Subsingleton.elim _ _
    simp [ha]
  let C (n : ℕ) [NeZero n] : ℂ :=
    ∑ x : Fin 4 → ZMod n,
      if (q : ℤ) ∣ integralQuadraticValue A (residueLift n x) then
        compositeWeight ξ q (residueLift n x) *
          ZMod.stdAddChar ((dotProduct u (residueLift n x) : ℤ) : ZMod n)
      else 0
  have hC (m n : ℕ) [NeZero m] [NeZero n] (h : m = n) : C m = C n := by
    subst n
    rfl
  unfold mixedCompleteSum mixedIntegerSummand constrainedFourierSum
  simp only [hunit, zero_mul, zero_add]
  change (∑ _a : (ZMod 1)ˣ, C (q * 1)) = C q
  rw [hC (q * 1) q (Nat.mul_one q)]
  simp

/-- The ordinary sum at modulus one has its source value one. -/
theorem unweightedCompleteSum_one
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    unweightedCompleteSum 1 A u = 1 := by
  simp [unweightedCompleteSum, stdAddChar_modulus_one]

/-- The constrained sum at modulus one has empty-prime-product weight one. -/
theorem constrainedFourierSum_one
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    constrainedFourierSum ξ 1 A u = 1 := by
  simp [constrainedFourierSum, stdAddChar_modulus_one]

/-- Both modulus-one conventions give the same actual mixed sum. -/
theorem mixedCompleteSum_one_one
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    mixedCompleteSum ξ 1 1 A u = 1 := by
  rw [mixedCompleteSum_one_left, unweightedCompleteSum_one]

/-- At a prime, the source prime-product weight is the given local
function on the actual finite-field quadratic cone. -/
theorem constrainedFourierSum_prime
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    constrainedFourierSum ξ p A u =
      ∑ x ∈ Finset.univ.filter (fun x : PrimeVector p =>
          quadraticValue (A.map (Int.castRingHom (ZMod p))) x = 0),
        ξ p x * ZMod.stdAddChar (dotProduct (reduceFrequency p u) x) := by
  classical
  have hvector (x : PrimeVector p) :
      (Int.castRingHom (ZMod p)) ∘ residueLift p x = x := by
    funext i
    exact residueLift_cast p x i
  have hquad (x : PrimeVector p) :
      (integralQuadraticValue A (residueLift p x) : ZMod p) =
        quadraticValue (A.map (Int.castRingHom (ZMod p))) x := by
    change (Int.castRingHom (ZMod p))
      (dotProduct (residueLift p x) (A.mulVec (residueLift p x))) = _
    rw [matrixQuadraticValue_map, hvector]
    rfl
  have hdiv (x : PrimeVector p) :
      ((p : ℤ) ∣ integralQuadraticValue A (residueLift p x)) ↔
        quadraticValue (A.map (Int.castRingHom (ZMod p))) x = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hquad]
  have hweight (x : PrimeVector p) :
      compositeWeight ξ p (residueLift p x) = ξ p x := by
    rw [compositeWeight_prime ξ p Fact.out]
    congr 1
    exact hvector x
  have hphase (x : PrimeVector p) :
      ((dotProduct u (residueLift p x) : ℤ) : ZMod p) =
        dotProduct (reduceFrequency p u) x := by
    rw [dotProduct_intCast]
    change dotProduct (reduceFrequency p u)
      ((Int.castRingHom (ZMod p)) ∘ residueLift p x) = _
    rw [hvector]
  rw [constrainedFourierSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (p : ℤ) ∣ integralQuadraticValue A (residueLift p x)
  · simp only [if_pos hx, if_pos ((hdiv x).mp hx), hweight, hphase]
  · have hz : quadraticValue (A.map (Int.castRingHom (ZMod p))) x ≠ 0 :=
      fun h => hx ((hdiv x).mpr h)
    simp only [if_neg hx, if_neg hz]

/-- Any local polynomial-character weight gives exactly the previously
defined integral Fourier sum, for arbitrary characters and polynomials. -/
theorem constrainedFourierSum_eq_integralFourierSum
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
    (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ)
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) ℤ)
    (hξ : ∀ x : PrimeVector p,
      ξ p x = ψ (MvPolynomial.eval x (G.map (Int.castRingHom (ZMod p))))) :
    constrainedFourierSum ξ p A u = integralFourierSum p A ψ G u := by
  rw [constrainedFourierSum_prime]
  simp only [integralFourierSum, fourierSum, polynomialCharacterWeight, hξ]

/-- The literal family of polynomial-character weights specializes to the
existing Fourier sum, with no matching-function assumption left over. -/
theorem constrainedFourierSum_polynomial_character
    (ψ : ∀ r : ℕ, MulChar (ZMod r) ℂ)
    (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ)
    (u : Fin 4 → ℤ) :
    constrainedFourierSum
        (fun r x => ψ r (MvPolynomial.eval x (G.map (Int.castRingHom (ZMod r)))))
        p A u = integralFourierSum p A (ψ p) G u :=
  constrainedFourierSum_eq_integralFourierSum _ p A u (ψ p) G (fun _ => rfl)

end QuaternaryQuadraticForms
