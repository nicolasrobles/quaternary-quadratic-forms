import QuaternaryQuadraticForms.QuadraticPlane
import QuaternaryQuadraticForms.PolynomialChainRule
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Extending coordinate maps to an overfield

The coordinates of the conic parametrization are chosen over the prime
field. These lemmas show that the same coordinates remain injective and
span the same hyperplane after any extension of coefficients.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

variable {K L : Type*} [Field K] [Field L]
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a linear map between coordinate spaces by mapping its actual matrix. -/
def extendCoordinateMap (f : K →+* L) (E : (ι → K) →ₗ[K] (κ → K)) :
    (ι → L) →ₗ[L] (κ → L) :=
  Matrix.toLin' ((LinearMap.toMatrix' E).map f)

theorem extendCoordinateMap_apply_map (f : K →+* L)
    (E : (ι → K) →ₗ[K] (κ → K)) (x : ι → K) :
    extendCoordinateMap f E (f ∘ x) = f ∘ E x := by
  unfold extendCoordinateMap
  ext i
  rw [Matrix.toLin'_apply, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

theorem extendCoordinateMap_comp [Fintype κ] [DecidableEq κ] (f : K →+* L)
    (E : (ι → K) →ₗ[K] (κ → K)) (D : (κ → K) →ₗ[K] (ν → K)) :
    extendCoordinateMap f (D.comp E) =
      (extendCoordinateMap f D).comp (extendCoordinateMap f E) := by
  simp only [extendCoordinateMap, LinearMap.toMatrix'_comp,
    Matrix.map_mul, Matrix.toLin'_mul]

@[simp] theorem extendCoordinateMap_id (f : K →+* L) :
    extendCoordinateMap f (LinearMap.id : (ι → K) →ₗ[K] (ι → K)) = LinearMap.id := by
  simp [extendCoordinateMap]

/-- An injective coordinate map remains injective over every extension field. -/
theorem extendCoordinateMap_injective [Fintype κ] [DecidableEq κ] (f : K →+* L)
    (E : (ι → K) →ₗ[K] (κ → K)) (hE : Function.Injective E) :
    Function.Injective (extendCoordinateMap f E) := by
  obtain ⟨D, hD⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE)
  have h := congrArg (extendCoordinateMap f) hD
  rw [extendCoordinateMap_comp, extendCoordinateMap_id] at h
  intro x y hxy
  have heq := congrArg (extendCoordinateMap f D) hxy
  simpa only [← LinearMap.comp_apply, h, LinearMap.id_apply] using heq

/-- Each coordinate of a linear map as a homogeneous linear polynomial. -/
def coordinatePolynomial (E : (ι → K) →ₗ[K] (κ → K)) (i : κ) : MvPolynomial ι K :=
  ∑ j, MvPolynomial.C (LinearMap.toMatrix' E i j) * MvPolynomial.X j

theorem eval_coordinatePolynomial (E : (ι → K) →ₗ[K] (κ → K)) (i : κ) (y : ι → K) :
    MvPolynomial.eval y (coordinatePolynomial E i) = E y i := by
  simp only [coordinatePolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  exact congrFun (LinearMap.toMatrix'_mulVec E y) i

theorem coordinatePolynomial_homogeneous (E : (ι → K) →ₗ[K] (κ → K)) (i : κ) :
    (coordinatePolynomial E i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem coordinatePolynomial_map (f : K →+* L)
    (E : (ι → K) →ₗ[K] (κ → K)) (i : κ) :
    (coordinatePolynomial E i).map f = coordinatePolynomial (extendCoordinateMap f E) i := by
  unfold coordinatePolynomial extendCoordinateMap
  rw [LinearMap.toMatrix'_toLin']
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

/-- Extension of coefficients preserves the equation defining the plane. -/
theorem extendCoordinateMap_mem_plane (f : K →+* L)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (u : Fin 4 → K)
    (hplane : ∀ y, dotProduct u (E y) = 0) (y : Fin 3 → L) :
    dotProduct (f ∘ u) (extendCoordinateMap f E y) = 0 := by
  have hrow : Matrix.vecMul u (LinearMap.toMatrix' E) = 0 := by
    funext j
    rw [← dotProduct_single_one (Matrix.vecMul u (LinearMap.toMatrix' E)) j,
      ← Matrix.dotProduct_mulVec, LinearMap.toMatrix'_mulVec]
    exact hplane (Pi.single j 1)
  have hrowL : Matrix.vecMul (f ∘ u) ((LinearMap.toMatrix' E).map f) = 0 := by
    ext j
    rw [← RingHom.map_vecMul, hrow]
    exact f.map_zero
  rw [extendCoordinateMap, Matrix.toLin'_apply, Matrix.dotProduct_mulVec, hrowL]
  exact zero_dotProduct _

/-- The actual hyperplane has dimension three over any field. -/
theorem planeSubspace_finrank_of_ne_zero (u : Fin 4 → K) (hu : u ≠ 0) :
    Module.finrank K (planeSubspace u) = 3 := by
  have hfunc : dotProductBilin K K u ≠ 0 := by
    intro h
    apply hu
    funext j
    have hj : dotProduct u (Pi.single j 1) = 0 := LinearMap.congr_fun h (Pi.single j 1)
    simpa only [dotProduct_single_one] using hj
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hfunc
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  change Module.finrank K (planeSubspace u) + 1 = 4 at h
  omega

/-- An injective three-coordinate parametrization of a hyperplane spans that
same hyperplane after every extension of coefficients. -/
theorem extendCoordinateMap_range_plane (f : K →+* L)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (u : Fin 4 → K) (hu : u ≠ 0) (hplane : ∀ y, dotProduct u (E y) = 0) :
    LinearMap.range (extendCoordinateMap f E) = planeSubspace (f ∘ u) := by
  have huL : f ∘ u ≠ 0 := by
    intro h
    apply hu
    funext i
    apply f.injective
    simpa using congrFun h i
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro x ⟨y, rfl⟩
    exact extendCoordinateMap_mem_plane f E u hplane y
  · rw [LinearMap.finrank_range_of_inj (extendCoordinateMap_injective f E hE),
      planeSubspace_finrank_of_ne_zero (f ∘ u) huL]
    simp

/-- Polynomial substitution commutes with extension of all coefficients. -/
theorem map_aeval_polynomial {σ τ : Type*} (f : K →+* L)
    (G : MvPolynomial σ K) (μ : σ → MvPolynomial τ K) :
    (MvPolynomial.aeval μ G).map f =
      MvPolynomial.aeval (fun j => (μ j).map f) (G.map f) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add G H hG hH => simp only [map_add, hG, hH]
  | mul_X G i hG => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hG]

/-- The literal matrix quadratic polynomial commutes with coefficient extension. -/
theorem matrixQuadraticPolynomial_map (f : K →+* L)
    (A : Matrix (Fin 4) (Fin 4) K) :
    (matrixQuadraticPolynomial A).map f = matrixQuadraticPolynomial (A.map f) := by
  simp only [matrixQuadraticPolynomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, Matrix.map_apply]

/-- The ternary normal-form identity is a polynomial identity and therefore
persists over every field extension, including infinite extensions. -/
theorem extendCoordinateMap_quadratic (f : K →+* L)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K))
    (A : Matrix (Fin 4) (Fin 4) K) (a : K)
    (hquadratic : ∀ y : Fin 3 → K,
      dotProduct (E y) (A.mulVec (E y)) = y 0 * y 1 + a * y 2 ^ 2)
    (y : Fin 3 → L) :
    dotProduct (extendCoordinateMap f E y)
      ((A.map f).mulVec (extendCoordinateMap f E y)) =
        y 0 * y 1 + f a * y 2 ^ 2 := by
  let F : MvPolynomial (Fin 3) K :=
    MvPolynomial.aeval (coordinatePolynomial E) (matrixQuadraticPolynomial A)
  let H : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.C a * MvPolynomial.X 2 ^ 2
  have hF : F.IsHomogeneous 2 := by
    simpa only [F, one_mul] using (matrixQuadraticPolynomial_homogeneous A).aeval
      (coordinatePolynomial E) (coordinatePolynomial_homogeneous E)
  have hH : H.IsHomogeneous 2 :=
    ((MvPolynomial.isHomogeneous_X K (0 : Fin 3)).mul
      (MvPolynomial.isHomogeneous_X K 1)).add
      ((MvPolynomial.isHomogeneous_X_pow (2 : Fin 3) 2).C_mul a)
  have hFH : F = H := hF.funext_of_le_card hH (fun x => by
      simpa only [F, H, eval_aeval_polynomial, eval_coordinatePolynomial,
        eval_matrixQuadraticPolynomial, map_add, map_mul, map_pow,
        MvPolynomial.eval_X, MvPolynomial.eval_C] using hquadratic x)
    (Cardinal.two_le_iff.mpr ⟨(0 : K), 1, zero_ne_one⟩)
  have hm := congrArg (MvPolynomial.map f) hFH
  simp only [F, H, map_aeval_polynomial, coordinatePolynomial_map,
    matrixQuadraticPolynomial_map, map_add, map_mul, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C] at hm
  have heval := congrArg (MvPolynomial.eval y) hm
  simpa only [eval_aeval_polynomial, eval_coordinatePolynomial,
    eval_matrixQuadraticPolynomial, map_add, map_mul, map_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_C] using heval

end QuaternaryQuadraticForms
