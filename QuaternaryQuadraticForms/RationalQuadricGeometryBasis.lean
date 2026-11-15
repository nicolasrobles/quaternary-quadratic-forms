import QuaternaryQuadraticForms.ConicNormalForm

/-!
# A rational hyperbolic pair and its two-dimensional complement
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open LinearMap Module Matrix

/-- The common orthogonal complement of a normalized hyperbolic pair has a
basis whose union with the pair is linearly independent. -/
theorem exists_hyperbolic_complement_basis
    (B : LinearMap.BilinForm ℚ (Fin 4 → ℚ)) (hB : B.IsSymm)
    (e f : Fin 4 → ℚ) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = (2 : ℚ)⁻¹) :
    ∃ v w : Fin 4 → ℚ,
      B e v = 0 ∧ B f v = 0 ∧ B e w = 0 ∧ B f w = 0 ∧
      LinearIndependent ℚ ![e, f, v, w] := by
  classical
  have hfe : B f e = (2 : ℚ)⁻¹ := (hB.eq f e).trans hef
  let L : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := LinearMap.pi ![B e, B f]
  have hL : Function.Surjective L := by
    intro y
    refine ⟨(2 * y 1) • e + (2 * y 0) • f, ?_⟩
    ext i
    fin_cases i <;>
      simp [L, hee, hff, hef, hfe] <;> ring
  have hdim : Module.finrank ℚ (LinearMap.ker L) = 2 := by
    have h := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hL] at h
    simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    omega
  let wb : Basis (Fin 2) ℚ (LinearMap.ker L) :=
    Module.finBasisOfFinrankEq ℚ (LinearMap.ker L) hdim
  let v : Fin 4 → ℚ := (wb 0).val
  let w : Fin 4 → ℚ := (wb 1).val
  have hez (i : Fin 2) : B e (wb i).val = 0 := congrFun (wb i).property 0
  have hfz (i : Fin 2) : B f (wb i).val = 0 := congrFun (wb i).property 1
  refine ⟨v, w, hez 0, hfz 0, hez 1, hfz 1, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hsum : a 0 • e + a 1 • f + a 2 • v + a 3 • w = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using ha
  have heval := congrArg (B e) hsum
  simp only [map_add, map_smul, smul_eq_mul, hee, hef, hez, v, w,
    mul_zero, zero_add, add_zero, map_zero] at heval
  have ha1 : a 1 = 0 := (mul_eq_zero.mp heval).resolve_right (by norm_num)
  have hfeval := congrArg (B f) hsum
  simp only [map_add, map_smul, smul_eq_mul, hfe, hff, hfz, v, w,
    mul_zero, add_zero, map_zero] at hfeval
  have ha0 : a 0 = 0 := (mul_eq_zero.mp hfeval).resolve_right (by norm_num)
  simp only [ha0, ha1, zero_smul, zero_add] at hsum
  have hsub : a 2 • wb 0 + a 3 • wb 1 = 0 := by
    apply Subtype.ext
    exact hsum
  have hcoeff : ∀ i : Fin 2, (![a 2, a 3] : Fin 2 → ℚ) i = 0 := by
    apply (Fintype.linearIndependent_iff.mp wb.linearIndependent)
    simpa [Fin.sum_univ_succ] using hsub
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact hcoeff 0
  · exact hcoeff 1

/-- Matrix congruence evaluates the bilinear form on the columns. -/
theorem rational_congruence_apply
    (S T : Matrix (Fin 4) (Fin 4) ℚ) (i j : Fin 4) :
    (Tᵀ * S * T) i j = S.toBilin' (T.col i) (T.col j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.toBilin'_apply',
    dotProduct, Matrix.mulVec, Matrix.col]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- A rational isotropic quaternary form has a hyperbolic plane and a binary
orthogonal complement, expressed by an invertible matrix. -/
theorem exists_rational_hyperbolic_matrix
    (S : Matrix (Fin 4) (Fin 4) ℚ) (hS : Sᵀ = S) (hdet : S.det ≠ 0)
    (hiso : ∃ e : Fin 4 → ℚ, e ≠ 0 ∧ dotProduct e (S.mulVec e) = 0) :
    ∃ (T : Matrix (Fin 4) (Fin 4) ℚ) (a d c : ℚ), T.det ≠ 0 ∧
      Tᵀ * S * T = !![(0 : ℚ), 1 / 2, 0, 0;
        1 / 2, 0, 0, 0;
        0, 0, a, d;
        0, 0, d, c] := by
  classical
  let B := S.toBilin'
  have hB : B.IsSymm := matrixBilin_isSymm S hS
  have hnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  obtain ⟨e, he, heq⟩ := hiso
  have hee : B e e = 0 := by simpa only [B, Matrix.toBilin'_apply'] using heq
  obtain ⟨f, hff, hef⟩ := exists_hyperbolic_partner B hB hnd (by norm_num) e he hee
  obtain ⟨v, w, hev, hfv, hew, hfw, hli⟩ :=
    exists_hyperbolic_complement_basis B hB e f hee hff hef
  let T : Matrix (Fin 4) (Fin 4) ℚ := fun i j => (![e, f, v, w] j) i
  have hTcol : T.col = ![e, f, v, w] := rfl
  have hT : IsUnit T := Matrix.linearIndependent_cols_iff_isUnit.mp (hTcol.symm ▸ hli)
  refine ⟨T, B v v, B v w, B w w,
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det T).mp hT), ?_⟩
  have hfe := (hB.eq f e).trans hef
  have hve := (hB.eq v e).trans hev
  have hvf := (hB.eq v f).trans hfv
  have hwe := (hB.eq w e).trans hew
  have hwf := (hB.eq w f).trans hfw
  have hwv := hB.eq w v
  ext i j
  rw [rational_congruence_apply, hTcol]
  change B (![e, f, v, w] i) (![e, f, v, w] j) = _
  fin_cases i <;> fin_cases j <;>
    simp [hee, hff, hef, hfe, hev, hfv, hew, hfw, hve, hvf, hwe, hwf, hwv]

end QuaternaryQuadraticForms
