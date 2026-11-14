import QuaternaryQuadraticForms.QuadraticPlane

/-!
# Reduction at the manuscript's good primes

The modulus is the literal integer `N_F = 2 |det A|`, written as a natural
number. Its nondivisibility supplies odd characteristic and nonsingularity
of the reduced matrix. Symmetry and the adjugate commute with reduction.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The modulus used to exclude the primes of bad quadratic reduction. -/
def quadraticBadPrimeModulus (A : Matrix (Fin 4) (Fin 4) ℤ) : ℕ :=
  2 * A.det.natAbs

/-- The coefficient reduction of the manuscript's integral matrix. -/
def reduceQuadraticMatrix (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    Matrix (Fin 4) (Fin 4) (ZMod p) := A.map (Int.castRingHom (ZMod p))

theorem goodPrime_ne_two (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) : p ≠ 2 := by
  intro h
  subst p
  exact hp (dvd_mul_right 2 _)

theorem goodPrime_reduced_det_ne_zero (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) : (reduceQuadraticMatrix p A).det ≠ 0 := by
  intro hz
  have hcast : (A.det : ZMod p) = 0 := by
    exact ((Int.castRingHom (ZMod p)).map_det A).trans hz
  have hdiv : (p : ℤ) ∣ A.det := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  have hnat : p ∣ A.det.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
  exact hp (dvd_mul_of_dvd_right hnat 2)

theorem reduceQuadraticMatrix_symmetric (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) : (reduceQuadraticMatrix p A).transpose = reduceQuadraticMatrix p A := by
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ =>
    M.map (Int.castRingHom (ZMod p))) hA

theorem reduceQuadraticMatrix_adjugate (p : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) :
    A.adjugate.map (Int.castRingHom (ZMod p)) = (reduceQuadraticMatrix p A).adjugate :=
  (Int.castRingHom (ZMod p)).map_adjugate A

end QuaternaryQuadraticForms
