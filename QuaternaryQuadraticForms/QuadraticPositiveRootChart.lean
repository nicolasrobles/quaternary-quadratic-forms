import QuaternaryQuadraticForms.RealQuadraticGeometry
import QuaternaryQuadraticForms.SurfaceIntegralDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The positive-coordinate root chart of a real quadratic form

The distinguished coordinate is written first.  The chart covers exactly
the zeros at which its coordinate derivative is positive.  Its domain is
open, and it is smooth there; no assertion is made that the whole zero set
is one graph.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ContDiff
open InnerProductSpace

/-- The actual graph insertion as a linear map. -/
def graphPointLinearMap : (ℝ × RealVector3) →ₗ[ℝ] RealVector4 where
  toFun p := graphPoint p.1 p.2
  map_add' p q := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [graphPoint]
  map_smul' c p := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [graphPoint]

/-- The graph insertion is smooth in both arguments. -/
theorem graphPoint_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × RealVector3 => graphPoint p.1 p.2) :=
  graphPointLinearMap.toContinuousLinearMap.contDiff

/-- In particular, graph insertion is continuous. -/
theorem graphPoint_continuous :
    Continuous (fun p : ℝ × RealVector3 => graphPoint p.1 p.2) :=
  graphPoint_contDiff.continuous

/-- The first coordinate of graph insertion. -/
@[simp] theorem graphPoint_zero (t : ℝ) (y : RealVector3) :
    graphPoint t y 0 = t := rfl

/-- The remaining coordinates of graph insertion. -/
@[simp] theorem graphPoint_succ (t : ℝ) (y : RealVector3) (i : Fin 3) :
    graphPoint t y i.succ = y i := rfl

/-- The last three coordinates of a Euclidean four-vector. -/
def graphTail (x : RealVector4) : RealVector3 :=
  WithLp.toLp 2 (fun i : Fin 3 => x i.succ)

@[simp] theorem graphTail_apply (x : RealVector4) (i : Fin 3) :
    graphTail x i = x i.succ := rfl

/-- The actual tail projection is continuous for the Euclidean norms. -/
theorem graphTail_continuous : Continuous graphTail := by
  have h : Continuous (fun x : RealVector4 => fun i : Fin 3 => x i.succ) :=
    continuous_pi (fun i => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) i.succ).continuous)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp h

@[simp] theorem graphTail_graphPoint (t : ℝ) (y : RealVector3) :
    graphTail (graphPoint t y) = y := by
  apply WithLp.ofLp_injective 2
  rfl

/-- Every four-vector has the literal distinguished-coordinate decomposition. -/
theorem graphPoint_graphTail (x : RealVector4) : graphPoint (x 0) (graphTail x) = x := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The Euclidean inner product splits into the first and remaining coordinates. -/
theorem real_inner_graphPoint (g : RealVector4) (t : ℝ) (y : RealVector3) :
    inner ℝ g (graphPoint t y) = g 0 * t + inner ℝ (graphTail g) y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    Fin.sum_univ_succ, Fin.sum_univ_zero, PiLp.ofLp_apply,
    graphPoint_zero, graphPoint_succ, graphTail_apply]
  ring

/-- The Euclidean norm splits into the first and remaining coordinates. -/
theorem realVector4_norm_sq_graphTail (x : RealVector4) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + ‖graphTail x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_zero,
    graphTail_apply, Real.norm_eq_abs, sq_abs]

/-- The coefficient of the square of the distinguished coordinate. -/
def quadraticLeadingCoeff (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A 0 0

/-- The coefficient of the distinguished coordinate. -/
def quadraticLinearCoeff (A : Matrix (Fin 4) (Fin 4) ℝ) (y : RealVector3) : ℝ :=
  2 * ∑ i : Fin 3, A 0 i.succ * y i

/-- The restriction of the form to the other three coordinates. -/
def quadraticConstantCoeff (A : Matrix (Fin 4) (Fin 4) ℝ) (y : RealVector3) : ℝ :=
  realQuadraticValue A (graphPoint 0 y)

/-- The actual discriminant as a function of the other coordinates. -/
def quadraticDiscriminant (A : Matrix (Fin 4) (Fin 4) ℝ) (y : RealVector3) : ℝ :=
  quadraticLinearCoeff A y ^ 2 -
    4 * quadraticLeadingCoeff A * quadraticConstantCoeff A y

/-- The exact quadratic expansion in the distinguished coordinate. -/
theorem realQuadraticValue_graphPoint
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (t : ℝ) (y : RealVector3) :
    realQuadraticValue A (graphPoint t y) =
      quadraticLeadingCoeff A * t ^ 2 + quadraticLinearCoeff A y * t +
        quadraticConstantCoeff A y := by
  have hcol (i : Fin 4) : A i 0 = A 0 i :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 i) hA
  simp only [quadraticLeadingCoeff, quadraticLinearCoeff, quadraticConstantCoeff,
    realQuadraticValue, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero,
    PiLp.ofLp_apply, graphPoint_zero, graphPoint_succ, mul_zero, zero_mul, zero_add,
    add_zero]
  simp_rw [hcol]
  ring

/-- The first component of the explicit Euclidean gradient. -/
theorem realQuadraticGradient_graphPoint_zero
    (A : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (y : RealVector3) :
    realQuadraticGradient A (graphPoint t y) 0 =
      2 * quadraticLeadingCoeff A * t + quadraticLinearCoeff A y := by
  simp only [realQuadraticGradient, PiLp.smul_apply, smul_eq_mul,
    Matrix.toEuclideanLin_apply, PiLp.toLp_apply, PiLp.ofLp_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, quadraticLeadingCoeff, quadraticLinearCoeff,
    graphPoint_zero, graphPoint_succ]
  ring

/-- The linear coefficient is smooth on the full three-dimensional space. -/
theorem quadraticLinearCoeff_contDiff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ∞ (quadraticLinearCoeff A) := by
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff)

/-- The constant coefficient is a smooth restriction of the original form. -/
theorem quadraticConstantCoeff_contDiff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ∞ (quadraticConstantCoeff A) :=
  (realQuadraticValue_contDiff A).comp
    (graphPoint_contDiff.comp (contDiff_const.prodMk contDiff_id))

/-- The discriminant is a smooth polynomial function. -/
theorem quadraticDiscriminant_contDiff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ∞ (quadraticDiscriminant A) :=
  ((quadraticLinearCoeff_contDiff A).pow 2).sub
    (contDiff_const.mul (quadraticConstantCoeff_contDiff A))

/-- The open set on which the root has positive first derivative. -/
def quadraticPositiveRootDomain (A : Matrix (Fin 4) (Fin 4) ℝ) : Set RealVector3 :=
  if quadraticLeadingCoeff A = 0 then {y | 0 < quadraticLinearCoeff A y}
  else {y | 0 < quadraticDiscriminant A y}

/-- The positive-coordinate root, with a separate formula for the linear case. -/
def quadraticPositiveRoot (A : Matrix (Fin 4) (Fin 4) ℝ) (y : RealVector3) : ℝ :=
  if quadraticLeadingCoeff A = 0 then
    -quadraticConstantCoeff A y / quadraticLinearCoeff A y
  else
    (-quadraticLinearCoeff A y + Real.sqrt (quadraticDiscriminant A y)) /
      (2 * quadraticLeadingCoeff A)

/-- The total explicit root formula is measurable, including outside its
open smoothness domain. -/
theorem quadraticPositiveRoot_measurable (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Measurable (quadraticPositiveRoot A) := by
  unfold quadraticPositiveRoot
  split_ifs
  · exact (quadraticConstantCoeff_contDiff A).continuous.measurable.neg.div
      (quadraticLinearCoeff_contDiff A).continuous.measurable
  · exact ((quadraticLinearCoeff_contDiff A).continuous.measurable.neg.add
      (Real.continuous_sqrt.measurable.comp
        (quadraticDiscriminant_contDiff A).continuous.measurable)).div measurable_const

/-- The chart domain is genuinely open. -/
theorem quadraticPositiveRootDomain_isOpen (A : Matrix (Fin 4) (Fin 4) ℝ) :
    IsOpen (quadraticPositiveRootDomain A) := by
  unfold quadraticPositiveRootDomain
  split_ifs
  · exact isOpen_lt continuous_const (quadraticLinearCoeff_contDiff A).continuous
  · exact isOpen_lt continuous_const (quadraticDiscriminant_contDiff A).continuous

/-- The explicit positive root is smooth on its full open domain. -/
theorem quadraticPositiveRoot_contDiffOn (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiffOn ℝ ∞ (quadraticPositiveRoot A) (quadraticPositiveRootDomain A) := by
  unfold quadraticPositiveRoot quadraticPositiveRootDomain
  split_ifs
  ·
    exact (quadraticConstantCoeff_contDiff A).neg.contDiffOn.div
      (quadraticLinearCoeff_contDiff A).contDiffOn (fun y hy => ne_of_gt hy)
  ·
    exact ((quadraticLinearCoeff_contDiff A).neg.contDiffOn.add
      ((quadraticDiscriminant_contDiff A).contDiffOn.sqrt
        (fun y hy => ne_of_gt hy))).div_const _

/-- The first derivative at the selected root has the explicit positive sign. -/
theorem quadraticPositiveRoot_firstDerivative
    (A : Matrix (Fin 4) (Fin 4) ℝ) (y : RealVector3) :
    2 * quadraticLeadingCoeff A * quadraticPositiveRoot A y +
        quadraticLinearCoeff A y =
      if quadraticLeadingCoeff A = 0 then quadraticLinearCoeff A y
      else Real.sqrt (quadraticDiscriminant A y) := by
  by_cases ha : quadraticLeadingCoeff A = 0
  · simp [quadraticPositiveRoot, ha]
  · simp only [quadraticPositiveRoot, ha, ↓reduceIte]
    field_simp
    ring

/-- Every point in the chart domain is an actual zero of the original form. -/
theorem quadraticPositiveRoot_value_zero
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (y : RealVector3) (hy : y ∈ quadraticPositiveRootDomain A) :
    realQuadraticValue A (surfaceGraph (quadraticPositiveRoot A) y) = 0 := by
  rw [surfaceGraph, realQuadraticValue_graphPoint A hA]
  by_cases ha : quadraticLeadingCoeff A = 0
  · have hb : quadraticLinearCoeff A y ≠ 0 :=
      ne_of_gt (by simpa [quadraticPositiveRootDomain, ha] using hy)
    simp only [quadraticPositiveRoot, ha, ↓reduceIte, zero_mul, zero_add]
    field_simp
    ring
  · have hd : 0 < quadraticDiscriminant A y := by
      simpa [quadraticPositiveRootDomain, ha] using hy
    have hp := quadraticPositiveRoot_firstDerivative A y
    simp only [ha, ↓reduceIte] at hp
    have hs := Real.sq_sqrt hd.le
    rw [← hp, quadraticDiscriminant] at hs
    have hz : quadraticLeadingCoeff A *
        (quadraticLeadingCoeff A * quadraticPositiveRoot A y ^ 2 +
          quadraticLinearCoeff A y * quadraticPositiveRoot A y +
          quadraticConstantCoeff A y) = 0 := by
      nlinarith only [hs]
    exact (mul_eq_zero.mp hz).resolve_left ha

/-- The actual first gradient coordinate is positive throughout the chart. -/
theorem quadraticPositiveRoot_gradient_zero_pos
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (y : RealVector3) (hy : y ∈ quadraticPositiveRootDomain A) :
    0 < gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y) 0 := by
  rw [gradient_realQuadraticValue A hA, surfaceGraph,
    realQuadraticGradient_graphPoint_zero, quadraticPositiveRoot_firstDerivative]
  by_cases ha : quadraticLeadingCoeff A = 0
  · simpa [quadraticPositiveRootDomain, ha] using hy
  · simp only [ha, ↓reduceIte]
    exact Real.sqrt_pos.2 (by simpa [quadraticPositiveRootDomain, ha] using hy)

/-- Every zero having positive first gradient coordinate belongs to this
unique graph branch, including the case of a linear distinguished variable. -/
theorem quadraticPositiveRoot_unique
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (t : ℝ) (y : RealVector3)
    (hzero : realQuadraticValue A (graphPoint t y) = 0)
    (hpos : 0 < gradient (realQuadraticValue A) (graphPoint t y) 0) :
    y ∈ quadraticPositiveRootDomain A ∧ t = quadraticPositiveRoot A y := by
  rw [realQuadraticValue_graphPoint A hA] at hzero
  rw [gradient_realQuadraticValue A hA, realQuadraticGradient_graphPoint_zero] at hpos
  by_cases ha : quadraticLeadingCoeff A = 0
  · have hb : 0 < quadraticLinearCoeff A y := by simpa [ha] using hpos
    constructor
    · simpa [quadraticPositiveRootDomain, ha] using hb
    · simp only [quadraticPositiveRoot, ha, ↓reduceIte]
      apply (eq_div_iff (ne_of_gt hb)).2
      simp only [ha, zero_mul, zero_add] at hzero
      nlinarith
  · have hd : quadraticDiscriminant A y =
        (2 * quadraticLeadingCoeff A * t + quadraticLinearCoeff A y) ^ 2 := by
      unfold quadraticDiscriminant
      nlinarith only [congrArg (fun z : ℝ => 4 * quadraticLeadingCoeff A * z) hzero]
    have hs : Real.sqrt (quadraticDiscriminant A y) =
        2 * quadraticLeadingCoeff A * t + quadraticLinearCoeff A y := by
      rw [hd, Real.sqrt_sq hpos.le]
    constructor
    · simp only [quadraticPositiveRootDomain, ha, ↓reduceIte, Set.mem_setOf_eq, hd]
      exact sq_pos_of_pos hpos
    · simp only [quadraticPositiveRoot, ha, ↓reduceIte, hs]
      apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).2
      ring

/-- Exact characterization of the positive-coordinate portion of the zero set. -/
theorem quadraticPositiveRoot_characterization
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (t : ℝ) (y : RealVector3) :
    (realQuadraticValue A (graphPoint t y) = 0 ∧
      0 < gradient (realQuadraticValue A) (graphPoint t y) 0) ↔
      y ∈ quadraticPositiveRootDomain A ∧ t = quadraticPositiveRoot A y := by
  constructor
  · rintro ⟨hz, hp⟩
    exact quadraticPositiveRoot_unique A hA t y hz hp
  · rintro ⟨hy, rfl⟩
    exact ⟨quadraticPositiveRoot_value_zero A hA y hy,
      quadraticPositiveRoot_gradient_zero_pos A hA y hy⟩

/-- Differentiating the actual graph equation relates every remaining
gradient coordinate to the derivative of the selected root. -/
theorem quadraticPositiveRoot_gradient_succ
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (y : RealVector3) (hy : y ∈ quadraticPositiveRootDomain A) (i : Fin 3) :
    gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y) i.succ =
      -(gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y) 0) *
        gradient (quadraticPositiveRoot A) y i := by
  have hφ : DifferentiableAt ℝ (quadraticPositiveRoot A) y :=
    ((quadraticPositiveRoot_contDiffOn A).contDiffAt
      ((quadraticPositiveRootDomain_isOpen A).mem_nhds hy)).differentiableAt (by simp)
  have hg := graphPointLinearMap.toContinuousLinearMap.hasFDerivAt.comp y
    (hφ.hasGradientAt.hasFDerivAt.prodMk (hasFDerivAt_id y))
  have hf := (realQuadraticValue_hasGradientAt A hA
    (surfaceGraph (quadraticPositiveRoot A) y)).hasFDerivAt.comp y hg
  have hlocal : (fun z => realQuadraticValue A
      (surfaceGraph (quadraticPositiveRoot A) z)) =ᶠ[nhds y] (fun _ => (0 : ℝ)) :=
    Filter.Eventually.mono ((quadraticPositiveRootDomain_isOpen A).mem_nhds hy)
      (fun z hz => quadraticPositiveRoot_value_zero A hA z hz)
  have hz : HasFDerivAt (fun z => realQuadraticValue A
      (surfaceGraph (quadraticPositiveRoot A) z)) 0 y :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) y).congr_of_eventuallyEq hlocal
  have heq := hf.unique hz
  have hi := congrArg
    (fun L : RealVector3 →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ))) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply, LinearMap.coe_toContinuousLinearMap',
    graphPointLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hi
  rw [real_inner_graphPoint] at hi
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial,
    one_mul, graphTail_apply] at hi
  simp only [gradient_realQuadraticValue A hA]
  linarith only [hi]

/-- The full Euclidean gradient norm equals its positive first component
times the actual Euclidean graph area factor. -/
theorem quadraticPositiveRoot_gradient_norm
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (y : RealVector3) (hy : y ∈ quadraticPositiveRootDomain A) :
    ‖gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y)‖ =
      gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y) 0 *
        graphAreaFactor (quadraticPositiveRoot A) y := by
  let g := gradient (realQuadraticValue A) (surfaceGraph (quadraticPositiveRoot A) y)
  let p := gradient (quadraticPositiveRoot A) y
  have htail : graphTail g = -(g 0) • p := by
    apply WithLp.ofLp_injective 2
    funext i
    simpa only [PiLp.ofLp_apply, graphTail_apply, PiLp.smul_apply, smul_eq_mul]
      using quadraticPositiveRoot_gradient_succ A hA y hy i
  have hg : 0 < g 0 := quadraticPositiveRoot_gradient_zero_pos A hA y hy
  have hs : ‖g‖ ^ 2 = (g 0) ^ 2 * (1 + ‖p‖ ^ 2) := by
    rw [realVector4_norm_sq_graphTail, htail, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, neg_sq]
    ring
  change ‖g‖ = g 0 * Real.sqrt (1 + ‖p‖ ^ 2)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 1 + ‖p‖ ^ 2 by positivity)
  have hnonneg : 0 ≤ g 0 * Real.sqrt (1 + ‖p‖ ^ 2) :=
    mul_nonneg hg.le (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ (norm_nonneg g) hnonneg).mp
  rw [mul_pow, hsqrt, hs]

end QuaternaryQuadraticForms
