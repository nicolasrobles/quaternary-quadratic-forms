import QuaternaryQuadraticForms.SingularEulerAbsolute
import QuaternaryQuadraticForms.ShiftedLocalDefinitions

/-!
# The shifted singular series as its actual local Euler product

The coprimality restriction deletes precisely the prime factors dividing
`q`. Every remaining local factor is the actual complete-sum density series.
This step requires neither a nonzero local density nor an inversion of a
bad-prime factor.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- At a prime not dividing `q`, the global prime-power term is the
corresponding actual shifted local-density coefficient. -/
theorem singularSeriesTerm_primePower_of_not_dvd (q p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (k : ℕ) (hpq : ¬p ∣ q) :
    singularSeriesTerm q A z (p ^ k) = shiftedLocalDensityTerm p A z k := by
  have hcop : p.Coprime q := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hpq
  rw [singularSeriesTerm, coprimeCompleteSumValue, if_pos (hcop.pow_left k),
    unweightedCompleteSumValue_of_neZero, shiftedLocalDensityTerm_eq_primePower]

/-- At a prime dividing `q`, only the coefficient at the empty power survives. -/
theorem singularSeriesTerm_primePower_of_dvd (q p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (k : ℕ) (hpq : p ∣ q) :
    singularSeriesTerm q A z (p ^ k) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcop : ¬p.Coprime q := fun h =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp h) hpq
    have hpowcop : ¬(p ^ k).Coprime q := fun h =>
      hcop ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk) p q).mp h)
    simp only [singularSeriesTerm, coprimeCompleteSumValue, if_neg hpowcop,
      zero_div, if_neg hk]

/-- The local Euler factor of the restricted global sum is precisely one at
the deleted primes and the actual shifted density at every other prime. -/
theorem tsum_singularSeriesTerm_primePower (q p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) :
    (∑' k : ℕ, singularSeriesTerm q A z (p ^ k)) =
      if p ∣ q then 1 else shiftedLocalDensity p A z := by
  by_cases hpq : p ∣ q
  · rw [if_pos hpq]
    simp only [singularSeriesTerm_primePower_of_dvd q p A z _ hpq]
    simp
  · rw [if_neg hpq, shiftedLocalDensity]
    exact tsum_congr (fun k => singularSeriesTerm_primePower_of_not_dvd q p A z k hpq)

/-- The absolute Euler product for the actual shifted singular series,
with precisely the prime factors of `q` removed. -/
theorem singularSeries_eulerProduct_hasProd (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) :
    HasProd (fun p : Nat.Primes =>
      letI : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩
      if (p : ℕ) ∣ q then 1 else shiftedLocalDensity (p : ℕ) A z)
      (∑' c : ℕ, singularSeriesTerm q A z c) := by
  convert singularSeriesTerm_eulerProduct_hasProd q A hA hdet z hz using 1
  funext p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact (tsum_singularSeriesTerm_primePower q (p : ℕ) A z).symm

end QuaternaryQuadraticForms
