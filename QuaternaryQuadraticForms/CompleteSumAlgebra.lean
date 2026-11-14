import QuaternaryQuadraticForms.MatrixPolynomial
import Mathlib.Data.ZMod.Coprime

/-!
# Integral quadratic values and residue representatives

These elementary identities identify the local sums with the manuscript's
matrix quadratic form and justify changes of residue representatives.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual integral quadratic form in the complete sums. -/
def integralQuadraticValue (A : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℤ) : ℤ :=
  dotProduct x (A.mulVec x)

/-- Canonical integer representatives of a residue vector. -/
def residueLift (n : ℕ) (x : Fin 4 → ZMod n) : Fin 4 → ℤ :=
  fun i => ((x i).val : ℤ)

/-- Reduction recovers the residue vector, including modulus one. -/
theorem residueLift_cast (n : ℕ) [NeZero n] (x : Fin 4 → ZMod n) (i : Fin 4) :
    (residueLift n x i : ZMod n) = x i := by
  simp [residueLift]

/-- The integral quadratic value is evaluation of the existing formal polynomial. -/
theorem integralQuadraticValue_eq_eval (A : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → ℤ) :
    integralQuadraticValue A x = MvPolynomial.eval x (matrixQuadraticPolynomial A) :=
  (eval_matrixQuadraticPolynomial A x).symm

/-- A coefficient homomorphism commutes with the matrix quadratic value. -/
theorem matrixQuadraticValue_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R) (x : Fin 4 → R) :
    f (dotProduct x (A.mulVec x)) =
      dotProduct (f ∘ x) ((A.map f).mulVec (f ∘ x)) := by
  simp [dotProduct, Matrix.mulVec, map_sum]

/-- Quadratic homogeneity holds over every commutative coefficient ring. -/
theorem matrixQuadraticValue_mul {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (t : R) (x : Fin 4 → R) :
    dotProduct (fun i => t * x i) (A.mulVec (fun i => t * x i)) =
      t ^ 2 * dotProduct x (A.mulVec x) := by
  change dotProduct (t • x) (A.mulVec (t • x)) = _
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Scalar multiplication of an integral vector multiplies its form by the square. -/
theorem integralQuadraticValue_mul (A : Matrix (Fin 4) (Fin 4) ℤ)
    (t : ℤ) (x : Fin 4 → ℤ) :
    integralQuadraticValue A (fun i => t * x i) = t ^ 2 * integralQuadraticValue A x :=
  matrixQuadraticValue_mul A t x

/-- Congruent vectors have congruent quadratic values. -/
theorem integralQuadraticValue_congr_mod (n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x y : Fin 4 → ℤ)
    (h : ∀ i, (x i : ZMod n) = (y i : ZMod n)) :
    (integralQuadraticValue A x : ZMod n) = (integralQuadraticValue A y : ZMod n) := by
  change (Int.castRingHom (ZMod n)) (dotProduct x (A.mulVec x)) =
    (Int.castRingHom (ZMod n)) (dotProduct y (A.mulVec y))
  rw [matrixQuadraticValue_map (Int.castRingHom (ZMod n)),
    matrixQuadraticValue_map (Int.castRingHom (ZMod n))]
  have hv : (Int.castRingHom (ZMod n)) ∘ x = (Int.castRingHom (ZMod n)) ∘ y :=
    funext h
  rw [hv]

/-- Congruence of vectors preserves the source divisibility constraint. -/
theorem integralQuadraticValue_dvd_congr (n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x y : Fin 4 → ℤ)
    (h : ∀ i, (x i : ZMod n) = (y i : ZMod n)) :
    ((n : ℤ) ∣ integralQuadraticValue A x) ↔
      (n : ℤ) ∣ integralQuadraticValue A y := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    integralQuadraticValue_congr_mod n A x y h]

/-- The bilinear Fourier pairing respects reduction of both vectors. -/
theorem dotProduct_intCast (n : ℕ) (u x : Fin 4 → ℤ) :
    ((dotProduct u x : ℤ) : ZMod n) =
      dotProduct (fun i => (u i : ZMod n)) (fun i => (x i : ZMod n)) := by
  simp [dotProduct]

/-- Congruent vectors have the same Fourier pairing modulo the modulus. -/
theorem dotProduct_congr_mod (n : ℕ) (u : Fin 4 → ℤ) (x y : Fin 4 → ℤ)
    (h : ∀ i, (x i : ZMod n) = (y i : ZMod n)) :
    ((dotProduct u x : ℤ) : ZMod n) = ((dotProduct u y : ℤ) : ZMod n) := by
  simp only [dotProduct_intCast]
  congr 1
  exact funext h

end QuaternaryQuadraticForms
