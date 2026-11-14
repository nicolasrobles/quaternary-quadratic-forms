import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Weight

/-!
# Homogeneous forms and their literal coefficient vectors

The generic-coefficient elimination theorem uses one coefficient for each
monomial of a prescribed degree. These definitions identify that finite
coefficient vector with the corresponding actual multivariate polynomial.
All reconstruction and coefficient-map identities are proved here.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exponent vectors of monomials of degree `d` in `N` variables. -/
abbrev HomogeneousMonomial (N d : ℕ) := {m : Fin N →₀ ℕ // m.degree = d}

noncomputable instance homogeneousMonomialFintype (N d : ℕ) :
    Fintype (HomogeneousMonomial N d) := by
  have h : {m : Fin N →₀ ℕ | m.degree = d}.Finite :=
    (Finsupp.finite_of_degree_le d).subset (fun _ hm => hm.le)
  exact h.fintype

/-- The homogeneous form with the specified coefficient at every monomial
of the assigned degree. Zero coefficients and the zero form are allowed. -/
def homogeneousForm {R : Type*} [CommSemiring R] {N d : ℕ}
    (c : HomogeneousMonomial N d → R) : MvPolynomial (Fin N) R :=
  ∑ m : HomogeneousMonomial N d, MvPolynomial.monomial m.val (c m)

/-- The coefficient-vector construction has the assigned degree of
homogeneity, including when all coefficients vanish. -/
theorem homogeneousForm_isHomogeneous {R : Type*} [CommSemiring R] {N d : ℕ}
    (c : HomogeneousMonomial N d → R) : (homogeneousForm c).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro m _
  exact MvPolynomial.isHomogeneous_monomial (c m) m.property

/-- Recover a specified coefficient from the constructed form. -/
@[simp] theorem homogeneousForm_coeff {R : Type*} [CommSemiring R] {N d : ℕ}
    (c : HomogeneousMonomial N d → R) (m : HomogeneousMonomial N d) :
    (homogeneousForm c).coeff m.val = c m := by
  classical
  rw [homogeneousForm, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro a _ ham
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => ham (Subtype.ext h)
  · intro hm
    exact False.elim (hm (Finset.mem_univ m))

/-- The constructed form has no coefficient outside its assigned degree. -/
theorem homogeneousForm_coeff_eq_zero_of_degree_ne {R : Type*} [CommSemiring R]
    {N d : ℕ} (c : HomogeneousMonomial N d → R) {m : Fin N →₀ ℕ}
    (hm : m.degree ≠ d) : (homogeneousForm c).coeff m = 0 :=
  (homogeneousForm_isHomogeneous c).coeff_eq_zero hm

/-- The coefficient formula at an arbitrary exponent vector. -/
theorem homogeneousForm_coeff_formula {R : Type*} [CommSemiring R] {N d : ℕ}
    (c : HomogeneousMonomial N d → R) (m : Fin N →₀ ℕ) :
    (homogeneousForm c).coeff m = if h : m.degree = d then c ⟨m, h⟩ else 0 := by
  classical
  by_cases h : m.degree = d
  · simpa only [dif_pos h] using homogeneousForm_coeff c ⟨m, h⟩
  · simpa only [dif_neg h] using homogeneousForm_coeff_eq_zero_of_degree_ne c h

/-- Every homogeneous polynomial is exactly the form built from its
coefficients on the monomials of the assigned degree. -/
theorem homogeneousForm_coefficients {R : Type*} [CommSemiring R] {N d : ℕ}
    (P : MvPolynomial (Fin N) R) (hP : P.IsHomogeneous d) :
    homogeneousForm (fun m : HomogeneousMonomial N d => P.coeff m.val) = P := by
  ext m
  by_cases hm : m.degree = d
  · exact homogeneousForm_coeff (fun a : HomogeneousMonomial N d => P.coeff a.val) ⟨m, hm⟩
  · rw [homogeneousForm_coeff_eq_zero_of_degree_ne _ hm, hP.coeff_eq_zero hm]

/-- Forming the polynomial commutes with every homomorphism of coefficient
semirings, including coefficient specialization and reduction modulo primes. -/
theorem homogeneousForm_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    {N d : ℕ} (f : R →+* S) (c : HomogeneousMonomial N d → R) :
    (homogeneousForm c).map f = homogeneousForm (fun m => f (c m)) := by
  simp only [homogeneousForm, map_sum, MvPolynomial.map_monomial]

end QuaternaryQuadraticForms
