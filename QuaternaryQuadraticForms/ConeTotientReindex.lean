import QuaternaryQuadraticForms.TotientDivisorExpansion
import QuaternaryQuadraticForms.DivisorSumReindex

/-!
# The exact totient decomposition of the good cone sum

The relative totient expansion and the finite divisor rearrangement
give the actual double sum used in Lemma 3.7. Full multiplicativity of
the supplied arithmetic function is the only character property needed
for this identity; cancellation is established separately.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ArithmeticFunction.Moebius

private theorem totient_monomial_mul_expand (f : ℕ →* ℂ) (d n : ℕ) (hd : d ≠ 0) :
    f (d * n) * ((d * n : ℕ) : ℂ) ^ 2 * ((d * n).totient : ℂ) =
      f d * (d : ℂ) ^ 2 * (d.totient : ℂ) *
        ∑ h ∈ n.divisors.filter (fun h => h.Coprime d),
          (μ h : ℂ) * f h * (h : ℂ) ^ 2 *
            (f (n / h) * ((n / h : ℕ) : ℂ) ^ 3) := by
  classical
  calc
    _ = ∑ h ∈ n.divisors.filter (fun h => h.Coprime d),
        f (d * n) * ((d * n : ℕ) : ℂ) ^ 2 * (d.totient : ℂ) *
          (μ h : ℂ) * ((n / h : ℕ) : ℂ) := by
      rw [totient_mul_eq_sum_moebius d n hd, ← Finset.sum_filter,
        ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      have hdiv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hh).1
      have hn : n = h * (n / h) := (Nat.mul_div_cancel' hdiv).symm
      have hmap : f (d * n) = f d * f h * f (n / h) := by
        nth_rw 1 [hn]
        rw [map_mul, map_mul]
        ring
      have hcast : ((d * n : ℕ) : ℂ) = (d : ℂ) * (h : ℂ) * ((n / h : ℕ) : ℂ) := by
        nth_rw 1 [hn]
        push_cast
        ring
      rw [hmap, hcast]
      ring

/-- The exact finite double sum for a multiplicative function times
`c^2 * φ(c)`, retaining the actual gcd restriction and quotient cutoffs.
The identity holds without squarefreeness or analytic hypotheses. -/
theorem sum_gcd_totient_eq_moebius (f : ℕ →* ℂ) (q d e T : ℕ)
    (hd : 0 < d) (hqde : q = d * e) :
    (∑ c ∈ gcdModuliUpTo q d T, f c * (c : ℂ) ^ 2 * (c.totient : ℂ)) =
      f d * (d : ℂ) ^ 2 * (d.totient : ℂ) *
        ∑ h ∈ (Finset.Icc 1 (T / d)).filter (fun h => h.Coprime q),
          (μ h : ℂ) * f h * (h : ℂ) ^ 2 *
            ∑ k ∈ (Finset.Icc 1 (T / (d * h))).filter (fun k => k.Coprime e),
              f k * (k : ℂ) ^ 3 := by
  classical
  calc
    _ = ∑ n ∈ (Finset.Icc 1 (T / d)).filter (fun n => n.Coprime e),
        f (d * n) * ((d * n : ℕ) : ℂ) ^ 2 * ((d * n).totient : ℂ) :=
      sum_gcdModuliUpTo_eq_sum_coprime q d e T hd hqde _
    _ = f d * (d : ℂ) ^ 2 * (d.totient : ℂ) *
        ∑ n ∈ (Finset.Icc 1 (T / d)).filter (fun n => n.Coprime e),
          ∑ h ∈ n.divisors.filter (fun h => h.Coprime d),
            (μ h : ℂ) * f h * (h : ℂ) ^ 2 *
              (f (n / h) * ((n / h : ℕ) : ℂ) ^ 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      exact totient_monomial_mul_expand f d n hd.ne'
    _ = _ := by
      congr 1
      have hreindex := sum_coprime_divisors_eq_sum_mul (T / d) d e
        (fun h k => (μ h : ℂ) * f h * (h : ℂ) ^ 2 * (f k * (k : ℂ) ^ 3))
      simpa only [hqde, Nat.div_div_eq_div_mul, Finset.mul_sum] using hreindex

end QuaternaryQuadraticForms
