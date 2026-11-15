import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial slices for the box congruence bound

Separate the first variable of an actual multivariate polynomial.  The
coefficients are polynomials in the remaining variables, and specialization
of those variables produces the univariate polynomial used on each fibre.
All degree bounds concern formal polynomials; no identification with
polynomial functions over a finite field is made.
-/

noncomputable section

namespace QuaternaryQuadraticForms

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The coefficient of the first variable to the indicated power. -/
def polynomialBoxCoefficient (P : MvPolynomial (Fin (n + 1)) R) (j : ℕ) :
    MvPolynomial (Fin n) R :=
  (MvPolynomial.finSuccEquiv R n P).coeff j

/-- The actual univariate polynomial after fixing the remaining variables. -/
def polynomialBoxSlice (P : MvPolynomial (Fin (n + 1)) R) (y : Fin n → R) :
    Polynomial R :=
  Polynomial.map (MvPolynomial.eval y) (MvPolynomial.finSuccEquiv R n P)

/-- Evaluating a slice is the same as evaluating the original polynomial. -/
theorem polynomialBoxSlice_eval (P : MvPolynomial (Fin (n + 1)) R)
    (y : Fin n → R) (t : R) :
    (polynomialBoxSlice P y).eval t = MvPolynomial.eval (Fin.cons t y) P := by
  exact (MvPolynomial.eval_eq_eval_mv_eval' y t P).symm

/-- Each slice coefficient is the value of the corresponding coefficient polynomial. -/
theorem polynomialBoxSlice_coeff (P : MvPolynomial (Fin (n + 1)) R)
    (y : Fin n → R) (j : ℕ) :
    (polynomialBoxSlice P y).coeff j =
      MvPolynomial.eval y (polynomialBoxCoefficient P j) := by
  simp only [polynomialBoxSlice, polynomialBoxCoefficient, Polynomial.coeff_map]

/-- A fibre is identically zero precisely when every coefficient vanishes there. -/
theorem polynomialBoxSlice_eq_zero_iff (P : MvPolynomial (Fin (n + 1)) R)
    (y : Fin n → R) :
    polynomialBoxSlice P y = 0 ↔
      ∀ j, MvPolynomial.eval y (polynomialBoxCoefficient P j) = 0 := by
  constructor
  · intro h j
    rw [← polynomialBoxSlice_coeff, h, Polynomial.coeff_zero]
  · intro h
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_zero, polynomialBoxSlice_coeff, h]

/-- Fixing variables cannot increase the degree in the remaining variable. -/
theorem polynomialBoxSlice_natDegree_le (P : MvPolynomial (Fin (n + 1)) R)
    (y : Fin n → R) :
    (polynomialBoxSlice P y).natDegree ≤ P.totalDegree := by
  calc
    (polynomialBoxSlice P y).natDegree ≤
        (MvPolynomial.finSuccEquiv R n P).natDegree := Polynomial.natDegree_map_le
    _ = P.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv P
    _ ≤ P.totalDegree := MvPolynomial.degreeOf_le_totalDegree P 0

/-- A coefficient polynomial has total degree at most that of the original polynomial. -/
theorem polynomialBoxCoefficient_totalDegree_le
    (P : MvPolynomial (Fin (n + 1)) R) (j : ℕ) :
    (polynomialBoxCoefficient P j).totalDegree ≤ P.totalDegree := by
  by_cases h : polynomialBoxCoefficient P j = 0
  · simp only [h, MvPolynomial.totalDegree_zero, Nat.zero_le]
  · exact (Nat.le_add_right _ _).trans
      (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P j h)

/-- A nonzero polynomial has a nonzero coefficient in the first variable. -/
theorem exists_polynomialBoxCoefficient_ne_zero
    (P : MvPolynomial (Fin (n + 1)) R) (hP : P ≠ 0) :
    ∃ j, polynomialBoxCoefficient P j ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hP
  apply (MvPolynomial.finSuccEquiv R n).injective
  rw [map_zero]
  apply Polynomial.ext
  intro j
  simpa only [Polynomial.coeff_zero] using h j

/-- A single nonzero coefficient detects every identically zero fibre.
This is the lower-dimensional polynomial used by the induction. -/
theorem exists_polynomialBox_degeneracy_polynomial
    (P : MvPolynomial (Fin (n + 1)) R) (hP : P ≠ 0) (E : ℕ)
    (hE : P.totalDegree ≤ E) :
    ∃ Q : MvPolynomial (Fin n) R, Q ≠ 0 ∧ Q.totalDegree ≤ E ∧
      ∀ y, polynomialBoxSlice P y = 0 → MvPolynomial.eval y Q = 0 := by
  obtain ⟨j, hj⟩ := exists_polynomialBoxCoefficient_ne_zero P hP
  refine ⟨polynomialBoxCoefficient P j, hj,
    (polynomialBoxCoefficient_totalDegree_le P j).trans hE, ?_⟩
  intro y hy
  exact (polynomialBoxSlice_eq_zero_iff P y).mp hy j

/-- In dimension one, specialization of the empty tail is injective. -/
theorem polynomialBoxSlice_empty_ne_zero (P : MvPolynomial (Fin 1) R)
    (hP : P ≠ 0) (y : Fin 0 → R) :
    polynomialBoxSlice P y ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := exists_polynomialBoxCoefficient_ne_zero P hP
  apply hj
  apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
  rw [map_zero]
  have heval : (MvPolynomial.eval y : MvPolynomial (Fin 0) R →+* R) =
      (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.isEmptyRingEquiv, MvPolynomial.isEmptyAlgEquiv]
    · intro i
      exact Fin.elim0 i
  change (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
    (polynomialBoxCoefficient P j) = 0
  rw [← heval]
  exact (polynomialBoxSlice_eq_zero_iff P y).mp h j

end QuaternaryQuadraticForms
