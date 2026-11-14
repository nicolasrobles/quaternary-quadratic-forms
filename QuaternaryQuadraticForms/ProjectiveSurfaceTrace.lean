import QuaternaryQuadraticForms.GoodReduction

/-!
# The literal character sum on a projective hypersurface

The general literature interface uses a homogeneous defining polynomial.
Here its actual projective sum is identified with the matrix-quadric sum
already used in the manuscript. Representative independence and the
nonvanishing forced by geometric transversality are proved explicitly.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

local instance surfaceProjectiveFintype (p : ℕ) [Fact p.Prime] :
    Fintype (PrimeProjective p) := Fintype.ofFinite _

/-- The actual finite projective zero set of a homogeneous equation. -/
def projectiveHypersurfacePoints {p : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin 4) (ZMod p)) : Finset (PrimeProjective p) := by
  classical
  exact Finset.univ.filter (fun P => MvPolynomial.eval P.rep F = 0)

/-- The character sum over the actual projective hypersurface points. -/
def projectiveHypersurfaceTrace {p : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin 4) (ZMod p)) (ψ : MulChar (ZMod p) ℂ)
    (G : MvPolynomial (Fin 4) (ZMod p)) : ℂ :=
  ∑ P ∈ projectiveHypersurfacePoints F, polynomialCharacterWeight ψ G P.rep

/-- The homogeneous equation descends to the actual projective quotient. -/
theorem mem_projectiveHypersurfacePoints_mk {p : ℕ} [Fact p.Prime]
    {F : MvPolynomial (Fin 4) (ZMod p)} {m : ℕ} (hF : F.IsHomogeneous m)
    (x : PrimeVector p) (hx : x ≠ 0) :
    Projectivization.mk (ZMod p) x hx ∈ projectiveHypersurfacePoints F ↔
      MvPolynomial.eval x F = 0 := by
  classical
  simpa [projectiveHypersurfacePoints] using
    cone_rep_mk (fun y => MvPolynomial.eval y F = 0)
      (fun a y => by
        change MvPolynomial.eval ((a : ZMod p) • y) F = 0 ↔ _
        rw [homogeneous_eval_smul hF]
        simp [a.ne_zero]) x hx

/-- The general projective hypersurface set agrees with the literal matrix
quadric set when its defining polynomial is the matrix polynomial. -/
theorem projectiveHypersurfacePoints_matrix {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) :
    projectiveHypersurfacePoints (matrixQuadraticPolynomial A) = projectiveQuadric A := by
  classical
  simp [projectiveHypersurfacePoints, projectiveQuadric,
    eval_matrixQuadraticPolynomial_quadraticValue]

/-- The general literature sum is exactly the manuscript's projective trace. -/
theorem projectiveHypersurfaceTrace_matrix {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (ψ : MulChar (ZMod p) ℂ)
    (G : MvPolynomial (Fin 4) (ZMod p)) :
    projectiveHypersurfaceTrace (matrixQuadraticPolynomial A) ψ G =
      projectiveTrace A ψ G := by
  rw [projectiveHypersurfaceTrace, projectiveHypersurfacePoints_matrix]
  rfl

/-- A rank-two transverse polynomial cannot vanish identically if the
first equation has a nonzero geometric zero. -/
theorem transverse_polynomial_ne_zero {K : Type*} [Field K] {N : ℕ}
    (F G : MvPolynomial (Fin N) K)
    (htrans : ProjectiveIntersectionTransverseRank F G)
    (hpoint : ∃ x : Fin N → K, x ≠ 0 ∧ MvPolynomial.eval x F = 0) : G ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hF⟩ := hpoint
  have hlin := (rank_two_iff_linearIndependent _).mp (htrans x hx hF (by simp))
  have hne := hlin.ne_zero (1 : Fin 2)
  apply hne
  change polynomialGradient 0 x = 0
  funext i
  simp [polynomialGradient]

/-- The literal nonzero zero of a prime-field quadric supplies the geometric
point needed to exclude the zero transverse polynomial. -/
theorem quadric_transverse_polynomial_ne_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p))
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) : G ≠ 0 := by
  let f := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  obtain ⟨x, hx, hF, _⟩ := plane_exists_isotropic p A 0
  have hxmap : f ∘ x ≠ 0 := by
    intro hzero
    apply hx
    funext i
    apply f.injective
    simpa using congrFun hzero i
  have hFmap : MvPolynomial.eval (f ∘ x) ((matrixQuadraticPolynomial A).map f) = 0 := by
    rw [MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
    simpa [eval_matrixQuadraticPolynomial] using congrArg f hF
  have hGmap := transverse_polynomial_ne_zero _ _ htrans ⟨f ∘ x, hxmap, hFmap⟩
  intro hG
  apply hGmap
  simp [hG]

end QuaternaryQuadraticForms
