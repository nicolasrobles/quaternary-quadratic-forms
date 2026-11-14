import QuaternaryQuadraticForms.ProjectiveSurfaceTrace
import QuaternaryQuadraticForms.QuadricSmooth
import QuaternaryQuadraticForms.SurfaceChern

/-!
# Registered literature input: spectral data on a smooth projective surface

This is a composite literature premise. Katz's Theorem 8.1(1) (Theorem
18(1) in the author version) and trace formula give the spectral statement.
The general hypersurface adjunction and degree formulas identify its Chern
integral with the unevaluated coefficient below. Both source components
are registered as `EXT.KATZ` and `EXT.HYPERSURFACE_CHERN`; see
`certification/correspondence/katz_input.md` for exact locators and the
coordinate interpretation of the geometric hypotheses.

The premise concerns arbitrary smooth geometrically irreducible
hypersurfaces in projective three-space. It does not contain the quadric
coefficient, a scalar norm estimate, or any manuscript-specific geometric
deduction. These are proved in separate modules.
-/

noncomputable section

open QuaternaryQuadraticForms
open scoped BigOperators

axiom QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data
    (p : ℕ) [Fact p.Prime]
    (F G : MvPolynomial (Fin 4) (ZMod p)) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (hF : F.IsHomogeneous m) (hF0 : F ≠ 0)
    (hG : G.IsHomogeneous n) (hG0 : G ≠ 0)
    (hirr : Irreducible (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (hsmooth : ProjectiveHypersurfaceSmooth
      (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (htrans : ProjectiveIntersectionTransverseRank
      (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1) (horder : ψ ^ n = 1)
    (c : Polynomial ℤ) (hc : SurfaceChernRelation m c) :
    ∃ (r : ℕ) (eigenvalues : Fin r → ℂ),
      (r : ℤ) = surfaceSectionEulerCoefficient m n c ∧
      projectiveHypersurfaceTrace F ψ G = ∑ i, eigenvalues i ∧
      ∀ i, ‖eigenvalues i‖ = (p : ℝ)
