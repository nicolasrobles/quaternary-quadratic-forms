import QuaternaryQuadraticForms.AffineDivisibility
import QuaternaryQuadraticForms.MatrixPolynomial
import QuaternaryQuadraticForms.QuadraticCharacter

/-!
# Integrality and divisibility of the projective quadratic trace

This file proves the integrality and prime-divisibility clauses of Lemma 5.9
of the frozen manuscript.  The traces are first defined as actual integer
sums of the quadratic character.  Their complex casts are then identified
with the Fourier and projective sums already used in the checked ray identity.

The bound `|a_p(G)| ≤ 4p` is not proved here.  Divisibility only needs an odd
prime and a quadratic homogeneous `G`; the nonsingularity and smoothness
hypotheses of the manuscript are needed for the separate size estimate.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- The integer-valued affine quadratic-character sum. -/
def affineQuadraticTrace (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x : PrimeVector p => quadraticValue A x = 0),
    quadraticChar (ZMod p) (MvPolynomial.eval x G)

/-- The integer-valued projective trace `a_p(G)` of the manuscript. -/
def projectiveQuadraticTrace (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) : ℤ :=
  ∑ P ∈ projectiveQuadric A, quadraticChar (ZMod p) (MvPolynomial.eval P.rep G)

/-- The integer summand is independent of the representative when `G` is
quadratic homogeneous. -/
theorem quadraticTraceWeight_rep_mk {G : MvPolynomial (Fin 4) (ZMod p)}
    (hG : G.IsHomogeneous 2) (x : PrimeVector p) (hx : x ≠ 0) :
    quadraticChar (ZMod p) (MvPolynomial.eval (Projectivization.mk (ZMod p) x hx).rep G) =
      quadraticChar (ZMod p) (MvPolynomial.eval x G) := by
  apply Int.cast_injective (α := ℂ)
  simpa only [polynomialCharacterWeight, complexQuadraticChar_apply] using
    projectiveWeight_rep_mk (complexQuadraticChar p) hG (complexQuadraticChar_sq p) x hx

/-- The complex cast of the integer affine sum is the literal zero-frequency
Fourier sum. -/
theorem affineQuadraticTrace_complex (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) :
    (affineQuadraticTrace A G : ℂ) = fourierSum A (complexQuadraticChar p) G 0 := by
  simp [affineQuadraticTrace, fourierSum, polynomialCharacterWeight]

/-- The complex projective trace is exactly the cast of the integer sum. -/
theorem projectiveQuadraticTrace_complex (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) :
    (projectiveQuadraticTrace A G : ℂ) = projectiveTrace A (complexQuadraticChar p) G := by
  simp [projectiveQuadraticTrace, projectiveTrace, polynomialCharacterWeight]

/-- The checked zero-frequency identity transported back to the integers. -/
theorem affineQuadraticTrace_eq (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    {G : MvPolynomial (Fin 4) (ZMod p)} (hG : G.IsHomogeneous 2) :
    affineQuadraticTrace A G = ((p : ℤ) - 1) * projectiveQuadraticTrace A G := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [affineQuadraticTrace_complex, projectiveQuadraticTrace_complex]
  exact fourierSum_zero A (complexQuadraticChar p) hG (by decide)
    (complexQuadraticChar_sq p)

/-- Affine divisibility for the manuscript's literal matrix quadratic form. -/
theorem affineQuadraticTrace_dvd (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) (hG : G.totalDegree ≤ 2) :
    (p : ℤ) ∣ affineQuadraticTrace A G := by
  simpa only [affineQuadraticTrace, eval_matrixQuadraticPolynomial_quadraticValue] using
    affineQuadraticCharacterSum_dvd p hp (matrixQuadraticPolynomial A) G
      (matrixQuadraticPolynomial_totalDegree_le A) hG

/-- The prime divides the actual integer projective trace. -/
theorem projectiveQuadraticTrace_dvd (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    {G : MvPolynomial (Fin 4) (ZMod p)} (hG : G.IsHomogeneous 2) :
    (p : ℤ) ∣ projectiveQuadraticTrace A G := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have hzero : (affineQuadraticTrace A G : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      (affineQuadraticTrace_dvd hp A G hG.totalDegree_le)
  rw [affineQuadraticTrace_eq A hG] at hzero
  simpa using hzero

/-- The two completed clauses of Lemma 5.9, expressed for the paper's
complex-valued projective trace with an explicit integer witness. -/
theorem projectiveTrace_quadratic_integral_dvd (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    {G : MvPolynomial (Fin 4) (ZMod p)} (hG : G.IsHomogeneous 2) :
    ∃ a : ℤ, projectiveTrace A (complexQuadraticChar p) G = (a : ℂ) ∧ (p : ℤ) ∣ a :=
  ⟨projectiveQuadraticTrace A G, (projectiveQuadraticTrace_complex A G).symm,
    projectiveQuadraticTrace_dvd hp A hG⟩

/-- The projective quadratic trace with integral input coefficients. -/
def integralProjectiveQuadraticTrace (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (G : MvPolynomial (Fin 4) ℤ) : ℤ :=
  projectiveQuadraticTrace (A.map (Int.castRingHom (ZMod p)))
    (G.map (Int.castRingHom (ZMod p)))

/-- Prime divisibility after reducing the manuscript's integral coefficients. -/
theorem integralProjectiveQuadraticTrace_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2) :
    (p : ℤ) ∣ integralProjectiveQuadraticTrace p A G :=
  projectiveQuadraticTrace_dvd hp _ (homogeneous_reduce_mod hG p)

/-- The source-level integrality and divisibility statement for integral
`A` and `G`, using the complex trace already defined for the paper. -/
theorem integralProjectiveTrace_quadratic_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2) :
    ∃ a : ℤ,
      projectiveTrace (A.map (Int.castRingHom (ZMod p))) (complexQuadraticChar p)
        (G.map (Int.castRingHom (ZMod p))) = (a : ℂ) ∧ (p : ℤ) ∣ a :=
  projectiveTrace_quadratic_integral_dvd hp _ (homogeneous_reduce_mod hG p)

end QuaternaryQuadraticForms
