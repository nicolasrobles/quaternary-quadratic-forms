import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

/-!
# Bounding a finite sum by its actual factor pairs

An assigned factorization of each positive summation index is injective
as a map to pairs, because multiplication recovers the original index.
This allows the bad and good modulus factors to be counted separately.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- An actual factor-pair map bounds a finite sum by the product of a
factor count and an unrestricted nonnegative sum over the second factor. -/
theorem sum_le_product_of_factorization
    (S B G : Finset ℕ) (f : ℕ → ℕ × ℕ) (F H : ℕ → ℝ) (K : ℝ)
    (hmem : ∀ c ∈ S, f c ∈ B ×ˢ G)
    (hfac : ∀ c ∈ S, c = (f c).1 * (f c).2)
    (hbound : ∀ c ∈ S, F c ≤ K * H (f c).2)
    (hK : 0 ≤ K) (hH : ∀ g ∈ G, 0 ≤ H g) :
    ∑ c ∈ S, F c ≤ (B.card : ℝ) * K * ∑ g ∈ G, H g := by
  classical
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro c hc d hd hcd
    calc
      c = (f c).1 * (f c).2 := hfac c hc
      _ = (f d).1 * (f d).2 := congrArg (fun x : ℕ × ℕ => x.1 * x.2) hcd
      _ = d := (hfac d hd).symm
  have hsubset : S.image f ⊆ B ×ˢ G := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact hmem c hc
  calc
    _ ≤ ∑ c ∈ S, K * H (f c).2 := Finset.sum_le_sum hbound
    _ = ∑ x ∈ S.image f, K * H x.2 :=
      (Finset.sum_image (f := fun x : ℕ × ℕ => K * H x.2) hinj).symm
    _ ≤ ∑ x ∈ B ×ˢ G, K * H x.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun x hx _ => mul_nonneg hK (hH x.2 (Finset.mem_product.mp hx).2))
    _ = _ := by
      rw [Finset.sum_product]
      simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ac_rfl

end QuaternaryQuadraticForms
