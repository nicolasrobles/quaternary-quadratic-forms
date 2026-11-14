import QuaternaryQuadraticForms.QuadraticPlane
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fin.VecNotation

/-!
# A hyperbolic basis for the plane section

A nonzero isotropic vector of a nondegenerate ternary form has an isotropic
partner. Their common orthogonal complement supplies the third basis vector.
The resulting coordinate expression is `y₀*y₁ + a*y₂²`, with `a ≠ 0`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open LinearMap Module Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Normalize an isotropic partner so that the mixed quadratic coefficient is one. -/
theorem exists_hyperbolic_partner (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) (hnd : B.Nondegenerate) (h2 : (2 : K) ≠ 0)
    (e : V) (he : e ≠ 0) (heq : B e e = 0) :
    ∃ f : V, B f f = 0 ∧ B e f = (2 : K)⁻¹ := by
  have hline : B e ≠ 0 := by
    intro h
    exact he (hnd e fun x => LinearMap.congr_fun h x)
  obtain ⟨w, hw⟩ := LinearMap.surjective hline ((2 : K)⁻¹)
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  refine ⟨w - B w w • e, ?_, ?_⟩
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, heq, hB.eq w e, hw, mul_zero, sub_zero]
    calc
      B w w - B w w * (2 : K)⁻¹ - B w w * (2 : K)⁻¹ =
          B w w * (1 - ((2 : K)⁻¹ + (2 : K)⁻¹)) := by ring
      _ = 0 := by rw [hhalf, sub_self, mul_zero]
  · simp only [map_sub, map_smul, smul_eq_mul, heq, hw, mul_zero, sub_zero]

/-- In dimension three, two linear orthogonality conditions have a nonzero solution. -/
theorem exists_common_orthogonal [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) (B : LinearMap.BilinForm K V) (e f : V) :
    ∃ z : V, z ≠ 0 ∧ B e z = 0 ∧ B f z = 0 := by
  let T : V →ₗ[K] (Fin 2 → K) := LinearMap.pi ![B e, B f]
  have hdim' : Module.finrank K (Fin 2 → K) < Module.finrank K V := by
    simp [hdim]
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim')
  have he := congrFun hz 0
  have hf := congrFun hz 1
  exact ⟨z, hz0, he, hf⟩

/-- An isotropic hyperbolic pair and a nonzero common orthogonal vector are
linearly independent. -/
theorem hyperbolic_triple_linearIndependent (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) {e f z : V} {c : K}
    (hee : B e e = 0) (hff : B f f = 0) (hef : B e f = c) (hc : c ≠ 0)
    (hez : B e z = 0) (hfz : B f z = 0) (hz : z ≠ 0) :
    LinearIndependent K ![e, f, z] := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hsum : a 0 • e + a 1 • f + a 2 • z = 0 := by
    simpa [Fin.sum_univ_three] using ha
  have heval := congrArg (B e) hsum
  simp only [map_add, map_smul, smul_eq_mul, hee, hef, hez, mul_zero,
    zero_add, add_zero, map_zero] at heval
  have ha1 : a 1 = 0 := (mul_eq_zero.mp heval).resolve_right hc
  have hfe : B f e = c := (hB.eq f e).trans hef
  have hfeval := congrArg (B f) hsum
  simp only [map_add, map_smul, smul_eq_mul, hfe, hff, hfz, mul_zero,
    add_zero, map_zero] at hfeval
  have ha0 : a 0 = 0 := (mul_eq_zero.mp hfeval).resolve_right hc
  simp only [ha0, ha1, zero_smul, zero_add] at hsum
  have ha2 : a 2 = 0 := (smul_eq_zero.mp hsum).resolve_right hz
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2

/-- A nondegenerate ternary form with an isotropic vector admits the exact
hyperbolic normal form used in the conic parametrization. -/
theorem exists_ternary_hyperbolic_coordinates [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V = 3)
    (hisotropic : ∃ e : V, e ≠ 0 ∧ B e e = 0) :
    ∃ (a : K) (E : (Fin 3 → K) ≃ₗ[K] V), a ≠ 0 ∧
      ∀ y : Fin 3 → K, B (E y) (E y) = y 0 * y 1 + a * y 2 ^ 2 := by
  classical
  obtain ⟨e, he0, hee⟩ := hisotropic
  obtain ⟨f, hff, hef⟩ := exists_hyperbolic_partner B hB hnd h2 e he0 hee
  obtain ⟨z, hz0, hez, hfz⟩ := exists_common_orthogonal hdim B e f
  have hli := hyperbolic_triple_linearIndependent B hB hee hff hef (inv_ne_zero h2)
    hez hfz hz0
  let b : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hE (y : Fin 3 → K) : b.equivFun.symm y = y 0 • e + y 1 • f + y 2 • z := by
    simp [Basis.equivFun_symm_apply, b, Fin.sum_univ_three]
  have hze : B z e = 0 := (hB.eq z e).trans hez
  have hzf : B z f = 0 := (hB.eq z f).trans hfz
  have hzz : B z z ≠ 0 := by
    intro hzz
    apply hz0
    apply hnd z
    intro x
    obtain ⟨y, rfl⟩ := b.equivFun.symm.surjective x
    rw [hE]
    simp [hze, hzf, hzz]
  refine ⟨B z z, b.equivFun.symm, hzz, ?_⟩
  intro y
  have hfe : B f e = (2 : K)⁻¹ := (hB.eq f e).trans hef
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  rw [hE]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hee, hff, hef, hfe, hez, hfz, hze, hzf, mul_zero,
    add_zero, zero_add]
  calc
    _ = y 0 * y 1 * ((2 : K)⁻¹ + (2 : K)⁻¹) + B z z * y 2 ^ 2 := by ring
    _ = _ := by rw [hhalf, mul_one]

/-- The actual prime-field plane section has the required hyperbolic coordinates. -/
theorem plane_exists_hyperbolic_coordinates (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : Aᵀ = A) (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0) :
    ∃ (a : ZMod p) (E : (Fin 3 → ZMod p) ≃ₗ[ZMod p] planeSubspace u), a ≠ 0 ∧
      ∀ y : Fin 3 → ZMod p,
        dotProduct (E y).val (A.mulVec (E y).val) = y 0 * y 1 + a * y 2 ^ 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  let B := A.toBilin'.restrict (planeSubspace u)
  have hisotropic : ∃ e : planeSubspace u, e ≠ 0 ∧ B e e = 0 := by
    obtain ⟨x, hx0, hxq, hxu⟩ := plane_exists_isotropic p A u
    refine ⟨⟨x, hxu⟩, ?_, ?_⟩
    · intro h
      exact hx0 (congrArg Subtype.val h)
    · simpa only [B, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, Matrix.toBilin'_apply'] using hxq
  obtain ⟨a, E, ha, hE⟩ := exists_ternary_hyperbolic_coordinates B
    ((matrixBilin_isSymm A hA).restrict (planeSubspace u))
    (plane_bilin_nondegenerate A hA hdet u hu) h2 (planeSubspace_finrank A u hu) hisotropic
  refine ⟨a, E, ha, ?_⟩
  simpa only [B, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, Matrix.toBilin'_apply'] using hE

end QuaternaryQuadraticForms
