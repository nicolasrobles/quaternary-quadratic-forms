import QuaternaryQuadraticForms.Trusted.Bertini
import QuaternaryQuadraticForms.GoodReduction
import Mathlib.Tactic.FinCases

/-!
# A transverse plane for the actual two polynomial equations

The general Bertini input supplies a tangent vector on which the plane
normal is nonzero. The elementary linear-algebra argument below turns
this into rank three of the two actual gradient rows and the normal.
The specialization uses the manuscript's rank-two hypothesis directly.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- A linear functional nonzero on a common tangent vector is outside
the span of two independent rows, so adjoining it gives rank three. -/
theorem rank_three_of_rank_two_of_tangent {K : Type*} [Field K]
    (a b u v : Fin 4 → K) (hab : Matrix.rank ![a, b] = 2)
    (hav : dotProduct a v = 0) (hbv : dotProduct b v = 0)
    (huv : dotProduct u v ≠ 0) :
    Matrix.rank ![a, b, u] = 3 := by
  apply (rank_three_iff_linearIndependent _).mpr
  have hab' : LinearIndependent K ![a, b] :=
    (rank_two_iff_linearIndependent _).mp hab
  have hu : u ∉ Submodule.span K (Set.range ![a, b]) := by
    rw [Matrix.range_cons_cons_empty]
    intro hu
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hu
    apply huv
    rw [← hst]
    simp only [add_dotProduct, smul_dotProduct, hav, hbv, smul_zero, add_zero]
  have hrows : ![a, b, u] = Fin.snoc ![a, b] u := by
    funext i
    fin_cases i <;> rfl
  rw [hrows]
  exact linearIndependent_fin_snoc.mpr ⟨hab', hu⟩

/-- The general Bertini input produces a plane satisfying the literal
rank-three condition for a homogeneous quadratic and a degree-`n` form
whose common nonzero zeros all satisfy the rank-two condition. -/
theorem exists_transverse_plane_of_smooth_intersection
    (K : Type*) [Field K] [IsAlgClosed K]
    (F G : MvPolynomial (Fin 4) K) {n : ℕ}
    (hF : F.IsHomogeneous 2) (hG : G.IsHomogeneous n) (hn : 2 ≤ n)
    (htrans : ProjectiveIntersectionTransverseRank F G) :
    ∃ u : Fin 4 → K, u ≠ 0 ∧ PlaneTransverseRank F G u := by
  have hd : ∀ i : Fin 2, 0 < (![2, n] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i
    · change 0 < 2
      decide
    · exact lt_of_lt_of_le (by decide : 0 < 2) hn
  have hhomogeneous : ∀ i : Fin 2,
      ((![F, G] : Fin 2 → MvPolynomial (Fin 4) K) i).IsHomogeneous
        ((![2, n] : Fin 2 → ℕ) i) := by
    intro i
    fin_cases i
    · exact hF
    · exact hG
  have hjacobian : ∀ x : Fin 4 → K, x ≠ 0 →
      (∀ i : Fin 2, MvPolynomial.eval x ((![F, G] : Fin 2 → _) i) = 0) →
        Matrix.rank (fun i : Fin 2 => polynomialGradient ((![F, G] : Fin 2 → _) i) x) = 2 := by
    intro x hx hzero
    have hrows :
        (fun i : Fin 2 => polynomialGradient ((![F, G] : Fin 2 → _) i) x) =
          ![polynomialGradient F x, polynomialGradient G x] := by
      funext i
      fin_cases i <;> rfl
    rw [hrows]
    exact htrans x hx (hzero 0) (hzero 1)
  obtain ⟨u, hu, hplane⟩ := Trusted.bertini_homogeneous_tangent K 4 2
    (by decide) ![F, G] ![2, n] hd hhomogeneous hjacobian
  refine ⟨u, hu, ?_⟩
  intro x hx hFx hGx hux
  have hzero : ∀ i : Fin 2,
      MvPolynomial.eval x ((![F, G] : Fin 2 → MvPolynomial (Fin 4) K) i) = 0 := by
    intro i
    fin_cases i
    · exact hFx
    · exact hGx
  obtain ⟨v, hv, huv⟩ := hplane x hx hzero hux
  exact rank_three_of_rank_two_of_tangent
    (polynomialGradient F x) (polynomialGradient G x) u v
    (htrans x hx hFx hGx) (hv 0) (hv 1) huv

end QuaternaryQuadraticForms
