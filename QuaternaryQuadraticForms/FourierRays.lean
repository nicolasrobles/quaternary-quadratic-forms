import QuaternaryQuadraticForms.FiniteCharacters
import QuaternaryQuadraticForms.PolynomialWeights
import QuaternaryQuadraticForms.ProjectiveRays
import QuaternaryQuadraticForms.RayAlgebra
import Mathlib.Data.Matrix.Mul

/-!
# The Fourier identity on a quaternary quadratic cone

This file defines the actual finite-field sum in (4.1) of the frozen manuscript,
with `F(x) = xᵀ A x`, and the two sums over the corresponding projective quadric.
It proves equation (4.5), including the zero-frequency formula in Lemma 4.4.
The projective space is mathlib's quotient by nonzero scalar multiplication.

The identity needs neither nonsingularity of `A` nor smoothness of the divisor
defined by `G`.  Those hypotheses enter the estimates later in Lemma 4.4,
which are not proved here.  Positive degree and `ψ ^ n = 1` suffice for the
identity; the manuscript's hypotheses `n ≥ 2` and nonprincipality specialize it.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

/-- Four coordinates over the prime field. -/
abbrev PrimeVector (p : ℕ) := Fin 4 → ZMod p

/-- The actual projective three-space over the prime field. -/
abbrev PrimeProjective (p : ℕ) [Fact p.Prime] := ℙ (ZMod p) (PrimeVector p)

local instance primeProjectiveFintype (p : ℕ) [Fact p.Prime] :
    Fintype (PrimeProjective p) := Fintype.ofFinite _

variable {p : ℕ} [Fact p.Prime]

/-- The manuscript's matrix expression for the quadratic form. -/
def quadraticValue (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (x : PrimeVector p) : ZMod p :=
  dotProduct x (A.mulVec x)

theorem quadraticValue_smul (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (t : ZMod p) (x : PrimeVector p) :
    quadraticValue A (t • x) = (t * t) * quadraticValue A x := by
  simp only [quadraticValue, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, mul_assoc]

theorem quadraticValue_units_zero_iff (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (t : (ZMod p)ˣ) (x : PrimeVector p) :
    quadraticValue A (t • x) = 0 ↔ quadraticValue A x = 0 := by
  change quadraticValue A ((t : ZMod p) • x) = 0 ↔ _
  rw [quadraticValue_smul]
  simp [t.ne_zero]

theorem dotProduct_units_smul (u x : PrimeVector p) (t : (ZMod p)ˣ) :
    dotProduct u (t • x) = (t : ZMod p) * dotProduct u x := by
  change dotProduct u ((t : ZMod p) • x) = _
  exact dotProduct_smul (t : ZMod p) u x

theorem dotProduct_units_smul_zero_iff (u x : PrimeVector p) (t : (ZMod p)ˣ) :
    dotProduct u (t • x) = 0 ↔ dotProduct u x = 0 := by
  rw [dotProduct_units_smul]
  simp [t.ne_zero]

/-- The hyperplane condition defining the projective section is independent
of the chosen representative. -/
theorem hyperplane_rep_mk (u x : PrimeVector p) (hx : x ≠ 0) :
    dotProduct u (Projectivization.mk (ZMod p) x hx).rep = 0 ↔
      dotProduct u x = 0 :=
  cone_rep_mk (fun y => dotProduct u y = 0)
    (fun t y => dotProduct_units_smul_zero_iff u y t) x hx

/-- The finite set of points of the projective quadric `F = 0`. -/
def projectiveQuadric (A : Matrix (Fin 4) (Fin 4) (ZMod p)) :
    Finset (PrimeProjective p) := by
  classical
  exact Finset.univ.filter (fun P => quadraticValue A P.rep = 0)

/-- The quadratic-cone condition is independent of the representative. -/
theorem mem_projectiveQuadric_mk (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (x : PrimeVector p) (hx : x ≠ 0) :
    Projectivization.mk (ZMod p) x hx ∈ projectiveQuadric A ↔ quadraticValue A x = 0 := by
  classical
  simpa [projectiveQuadric] using
    cone_rep_mk (fun y => quadraticValue A y = 0)
      (quadraticValue_units_zero_iff A) x hx

/-- The projective weight agrees with its value on any representative. -/
theorem projectiveWeight_rep_mk (ψ : MulChar (ZMod p) ℂ)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hψ : ψ ^ n = 1)
    (x : PrimeVector p) (hx : x ≠ 0) :
    polynomialCharacterWeight ψ G (Projectivization.mk (ZMod p) x hx).rep =
      polynomialCharacterWeight ψ G x :=
  invariant_rep_mk (polynomialCharacterWeight ψ G)
    (polynomialCharacterWeight_units_smul ψ hG hψ) x hx

/-- The Fourier sum `C_p(u)` in (4.1), at a frequency reduced modulo `p`. -/
def fourierSum (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p))
    (u : PrimeVector p) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : PrimeVector p => quadraticValue A x = 0),
    polynomialCharacterWeight ψ G x * ZMod.stdAddChar (dotProduct u x)

/-- The quantity `a` in the proof of Lemma 4.4. -/
def projectiveTrace (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p)) : ℂ :=
  ∑ P ∈ projectiveQuadric A, polynomialCharacterWeight ψ G P.rep

/-- The quantity `a_u`, including the harmless extension `a_0 = a`. -/
def projectiveSectionTrace (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p))
    (u : PrimeVector p) : ℂ :=
  ∑ P ∈ (projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0),
    polynomialCharacterWeight ψ G P.rep

/-- Equation (4.5), proved for the literal Fourier and projective sums. -/
theorem fourierSum_ray_identity (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (hψ : ψ ^ n = 1)
    (u : PrimeVector p) :
    fourierSum A ψ G u =
      (p : ℂ) * projectiveSectionTrace A ψ G u - projectiveTrace A ψ G := by
  classical
  unfold fourierSum
  rw [sum_cone_weighted_eq_sum_projective
    (fun x : PrimeVector p => quadraticValue A x = 0)
    (quadraticValue_units_zero_iff A)
    (polynomialCharacterWeight ψ G) (fun x => ZMod.stdAddChar (dotProduct u x))
    (polynomialCharacterWeight_zero ψ hG hn.ne')
    (polynomialCharacterWeight_units_smul ψ hG hψ)]
  simp_rw [dotProduct_units_smul, stdAddChar_units_sum]
  exact weighted_ray_sum (projectiveQuadric A)
    (fun P => polynomialCharacterWeight ψ G P.rep)
    (fun P => dotProduct u P.rep = 0) (p : ℂ)

theorem projectiveSectionTrace_zero (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p)) :
    projectiveSectionTrace A ψ G 0 = projectiveTrace A ψ G := by
  simp [projectiveSectionTrace, projectiveTrace]

/-- The exact zero-frequency clause of Lemma 4.4. -/
theorem fourierSum_zero (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (ψ : MulChar (ZMod p) ℂ) {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (hψ : ψ ^ n = 1) :
    fourierSum A ψ G 0 = ((p : ℂ) - 1) * projectiveTrace A ψ G := by
  rw [fourierSum_ray_identity A ψ hG hn hψ, projectiveSectionTrace_zero]
  ring

/-- Coordinatewise reduction of an integral frequency. -/
def reduceFrequency (p : ℕ) (u : Fin 4 → ℤ) : PrimeVector p := fun i => (u i : ZMod p)

theorem reduceFrequency_eq_zero_iff (p : ℕ) (u : Fin 4 → ℤ) :
    reduceFrequency p u = 0 ↔ ∀ i, (p : ℤ) ∣ u i := by
  simp only [funext_iff, reduceFrequency, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The same Fourier sum with the integral input data used in the paper. -/
def integralFourierSum (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  fourierSum (A.map (Int.castRingHom (ZMod p))) ψ
    (G.map (Int.castRingHom (ZMod p))) (reduceFrequency p u)

/-- The ray identity after reduction of the manuscript's integral coefficients
and integral frequency. No homogeneity assumption on the reduction is added. -/
theorem integralFourierSum_ray_identity (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (ψ : MulChar (ZMod p) ℂ)
    {G : MvPolynomial (Fin 4) ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (hψ : ψ ^ n = 1) (u : Fin 4 → ℤ) :
    integralFourierSum p A ψ G u =
      (p : ℂ) * projectiveSectionTrace (A.map (Int.castRingHom (ZMod p))) ψ
        (G.map (Int.castRingHom (ZMod p))) (reduceFrequency p u) -
      projectiveTrace (A.map (Int.castRingHom (ZMod p))) ψ
        (G.map (Int.castRingHom (ZMod p))) :=
  fourierSum_ray_identity _ ψ (homogeneous_reduce_mod hG p) hn hψ _

/-- The `p ∣ u` case in (4.5), with divisibility of every integer coordinate. -/
theorem integralFourierSum_of_dvd (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (ψ : MulChar (ZMod p) ℂ)
    {G : MvPolynomial (Fin 4) ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (hψ : ψ ^ n = 1)
    (u : Fin 4 → ℤ) (hu : ∀ i, (p : ℤ) ∣ u i) :
    integralFourierSum p A ψ G u = ((p : ℂ) - 1) *
      projectiveTrace (A.map (Int.castRingHom (ZMod p))) ψ
        (G.map (Int.castRingHom (ZMod p))) := by
  unfold integralFourierSum
  rw [(reduceFrequency_eq_zero_iff p u).2 hu]
  exact fourierSum_zero _ ψ (homogeneous_reduce_mod hG p) hn hψ

end QuaternaryQuadraticForms
