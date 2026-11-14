import QuaternaryQuadraticForms.ConicPolynomials
import QuaternaryQuadraticForms.ScalarExtension
import QuaternaryQuadraticForms.PlaneConic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# The conic parametrization in four coordinates

An injective linear map identifying the ternary normal form with a plane
section transports the actual projective parametrization and its two
independent polynomial derivatives. Polynomial identities are established
before quadratic substitution, so no inference from degree-four evaluation
over a small finite field is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization
open MvPolynomial

variable {K : Type*} [Field K]

/-- The four actual binary quadratic coordinate polynomials. -/
def embeddedConicPolynomials (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K) :
    Fin 4 → MvPolynomial (Fin 2) K :=
  fun i => aeval (canonicalConicPolynomials a) (coordinatePolynomial E i)

theorem embeddedConicPolynomials_eval
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K) (v : Fin 2 → K) :
    (fun i => eval v (embeddedConicPolynomials E a i)) = E (canonicalConicVector a v) := by
  ext i
  rw [embeddedConicPolynomials, eval_aeval_polynomial, canonicalConicPolynomials_eval,
    eval_coordinatePolynomial]

theorem embeddedConicPolynomials_homogeneous
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K) (i : Fin 4) :
    (embeddedConicPolynomials E a i).IsHomogeneous 2 := by
  exact (coordinatePolynomial_homogeneous E i).aeval _
    (canonicalConicPolynomials_homogeneous a)

/-- The same binary coordinate forms are obtained after extending every
coefficient to an overfield. -/
theorem embeddedConicPolynomials_map {L : Type*} [Field L] (f : K →+* L)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K) (i : Fin 4) :
    (embeddedConicPolynomials E a i).map f =
      embeddedConicPolynomials (extendCoordinateMap f E) (f a) i := by
  simp only [embeddedConicPolynomials, map_aeval_polynomial,
    canonicalConicPolynomials_map, coordinatePolynomial_map]

/-- A coordinate of a linear map has its matrix entry as formal derivative. -/
theorem coordinatePolynomial_pderiv
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (i : Fin 4) (j : Fin 3) :
    pderiv j (coordinatePolynomial E i) = C (LinearMap.toMatrix' E i j) := by
  simp [coordinatePolynomial, Pi.single_apply]

/-- The derivative vector is transported by the same linear map. -/
theorem embeddedConicPolynomials_partial
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K) (j : Fin 2) (v : Fin 2 → K) :
    (fun i => eval v (pderiv j (embeddedConicPolynomials E a i))) =
      E (fun k => eval v (pderiv j (canonicalConicPolynomials a k))) := by
  ext i
  rw [embeddedConicPolynomials, eval_pderiv_aeval_chain_rule]
  simp only [coordinatePolynomial_pderiv, eval_C]
  simpa only [Matrix.mulVec, dotProduct] using congrFun
    (LinearMap.toMatrix'_mulVec E (fun k => eval v (pderiv j (canonicalConicPolynomials a k)))) i

/-- The actual polynomial partials remain independent after the embedding. -/
theorem embeddedConicPolynomials_partials_independent
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (v : Fin 2 → K) (hv : v ≠ 0) :
    LinearIndependent K
      ![(fun i => eval v (pderiv 0 (embeddedConicPolynomials E a i))),
        (fun i => eval v (pderiv 1 (embeddedConicPolynomials E a i)))] := by
  rw [embeddedConicPolynomials_partial, embeddedConicPolynomials_partial]
  convert (canonicalConicPolynomials_partials_independent a ha h2 v hv).map' E
    (LinearMap.ker_eq_bot.mpr hE) using 1
  funext j
  fin_cases j <;> rfl

/-- The ternary normal form as a literal homogeneous quadratic polynomial. -/
def canonicalConicPolynomial (a : K) : MvPolynomial (Fin 3) K :=
  X 0 * X 1 + C a * X 2 ^ 2

theorem eval_canonicalConicPolynomial (a : K) (y : Fin 3 → K) :
    eval y (canonicalConicPolynomial a) = canonicalConicValue a y := by
  simp [canonicalConicPolynomial, canonicalConicValue]

theorem canonicalConicPolynomial_homogeneous (a : K) :
    (canonicalConicPolynomial a).IsHomogeneous 2 :=
  ((isHomogeneous_X K 0).mul (isHomogeneous_X K 1)).add
    (isHomogeneous_C_mul_X_pow a 2 2)

/-- The assumed normal form is an identity of quadratic polynomials. -/
theorem coordinateQuadratic_pullback
    (A : Matrix (Fin 4) (Fin 4) K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y) :
    aeval (coordinatePolynomial E) (matrixQuadraticPolynomial A) =
      canonicalConicPolynomial a := by
  apply MvPolynomial.IsHomogeneous.funext_of_le_card
    ((matrixQuadraticPolynomial_homogeneous A).aeval _
      (coordinatePolynomial_homogeneous E)) (canonicalConicPolynomial_homogeneous a)
  · intro y
    rw [eval_aeval_polynomial]
    simp only [eval_coordinatePolynomial, eval_matrixQuadraticPolynomial,
      eval_canonicalConicPolynomial]
    exact hF y
  · exact Cardinal.two_le_iff.mpr ⟨(0 : K), 1, zero_ne_one⟩

/-- Substituting the canonical quadratics into their conic equation is zero. -/
theorem canonicalConicPolynomial_substitution (a : K) :
    aeval (canonicalConicPolynomials a) (canonicalConicPolynomial a) = 0 := by
  simp [canonicalConicPolynomial, canonicalConicPolynomials]
  ring

/-- The embedded quadratic parametrization satisfies the actual equation F=0
as a polynomial identity. -/
theorem embeddedConicPolynomials_quadric_identity
    (A : Matrix (Fin 4) (Fin 4) K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y) :
    aeval (embeddedConicPolynomials E a) (matrixQuadraticPolynomial A) = 0 := by
  unfold embeddedConicPolynomials
  rw [← MvPolynomial.comp_aeval_apply,
    coordinateQuadratic_pullback A E a hF, canonicalConicPolynomial_substitution]

/-- The embedded linear coordinate map satisfies the plane equation as a
polynomial identity. -/
theorem coordinatePlane_pullback (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K))
    (hL : ∀ y, dotProduct u (E y) = 0) :
    aeval (coordinatePolynomial E) (planePolynomial u) = 0 := by
  have hpoly : (planePolynomial u).IsHomogeneous 1 := by
    unfold planePolynomial
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ _
  apply MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card
    (hpoly.aeval _ (coordinatePolynomial_homogeneous E))
  · intro y
    rw [eval_aeval_polynomial]
    simpa only [eval_coordinatePolynomial, eval_planePolynomial] using hL y
  · exact le_trans (by norm_num) (Cardinal.two_le_iff.mpr ⟨(0 : K), 1, zero_ne_one⟩)

/-- The four binary quadratic coordinates satisfy the actual plane equation
as a polynomial identity. -/
theorem embeddedConicPolynomials_plane_identity (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (a : K)
    (hL : ∀ y, dotProduct u (E y) = 0) :
    aeval (embeddedConicPolynomials E a) (planePolynomial u) = 0 := by
  unfold embeddedConicPolynomials
  rw [← MvPolynomial.comp_aeval_apply,
    coordinatePlane_pullback u E hL, map_zero]

/-- The two equations of the plane section are stable under nonzero scalars. -/
theorem planeConic_units_iff (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (c : Kˣ) (x : Fin 4 → K) :
    (dotProduct (c • x) (A.mulVec (c • x)) = 0 ∧ dotProduct u (c • x) = 0) ↔
      (dotProduct x (A.mulVec x) = 0 ∧ dotProduct u x = 0) := by
  change (dotProduct ((c : K) • x) (A.mulVec ((c : K) • x)) = 0 ∧
    dotProduct u ((c : K) • x) = 0) ↔ _
  simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, c.ne_zero]

/-- The normal-form embedding induces a map of the actual conic zero sets. -/
def embeddedCanonicalConicPoint (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0)
    (Q : CanonicalConic a) : PlaneConicPoints A u :=
  ⟨Projectivization.map E hE Q.val, by
    rw [← Q.val.mk_rep, Projectivization.map_mk]
    apply (cone_rep_mk
      (fun x => dotProduct x (A.mulVec x) = 0 ∧ dotProduct u x = 0)
      (planeConic_units_iff A u) _ _).mpr
    exact ⟨(hF Q.val.rep).trans Q.property, hL Q.val.rep⟩⟩

/-- Injectivity of the linear embedding gives injectivity on projective conics. -/
theorem embeddedCanonicalConicPoint_injective
    (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0) :
    Function.Injective (embeddedCanonicalConicPoint A u E hE a hF hL) := by
  intro P Q h
  apply Subtype.ext
  exact Projectivization.map_injective E hE (congrArg Subtype.val h)

/-- Spanning the hyperplane gives every projective point of the plane section. -/
theorem embeddedCanonicalConicPoint_surjective
    (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0)
    (hsurj : ∀ x, dotProduct u x = 0 → ∃ y, E y = x) :
    Function.Surjective (embeddedCanonicalConicPoint A u E hE a hF hL) := by
  rintro ⟨P, hP⟩
  obtain ⟨y, hy⟩ := hsurj P.rep hP.2
  have hy0 : y ≠ 0 := by
    intro hz
    apply P.rep_nonzero
    rw [← hy, hz, map_zero]
  have hyq : canonicalConicValue a y = 0 := by
    rw [← hF y, hy]
    exact hP.1
  let Q : CanonicalConic a := ⟨Projectivization.mk K y hy0,
    (cone_rep_mk (fun z => canonicalConicValue a z = 0)
      (canonicalConicValue_units_zero_iff a) _ _).mpr hyq⟩
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  change Projectivization.map E hE (Projectivization.mk K y hy0) = P
  rw [Projectivization.map_mk]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨1, by simp [hy]⟩ |>.trans P.mk_rep

/-- The binary quadratic map is a bijection onto the actual plane section. -/
def embeddedConicEquiv (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K) (ha : a ≠ 0)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0)
    (hsurj : ∀ x, dotProduct u x = 0 → ∃ y, E y = x) :
    ℙ K (Fin 2 → K) ≃ PlaneConicPoints A u :=
  (canonicalConicEquiv a ha).trans
    (Equiv.ofBijective (embeddedCanonicalConicPoint A u E hE a hF hL)
      ⟨embeddedCanonicalConicPoint_injective A u E hE a hF hL,
        embeddedCanonicalConicPoint_surjective A u E hE a hF hL hsurj⟩)

/-- On an arbitrary nonzero representative, the projective equivalence is
the literal embedded quadratic formula. -/
theorem embeddedConicEquiv_mk
    (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K) (ha : a ≠ 0)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0)
    (hsurj : ∀ x, dotProduct u x = 0 → ∃ y, E y = x)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    ((embeddedConicEquiv A u E hE a ha hF hL hsurj)
      (Projectivization.mk K v hv)).val =
      Projectivization.mk K (E (canonicalConicVector a v))
        (map_zero E ▸ hE.ne (canonicalConicVector_ne_zero ha hv)) := by
  change Projectivization.map E hE
    (canonicalConicProjective a ha (Projectivization.mk K v hv)) = _
  rw [canonicalConicProjective_mk, Projectivization.map_mk]

/-- All properties of the manuscript's parametrization, constructed from a
proved normal-form embedding and the literal binary quadratic coordinates. -/
def embeddedParametrizedPlaneSection
    (A : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (E : (Fin 3 → K) →ₗ[K] (Fin 4 → K)) (hE : Function.Injective E)
    (a : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hF : ∀ y, dotProduct (E y) (A.mulVec (E y)) = canonicalConicValue a y)
    (hL : ∀ y, dotProduct u (E y) = 0)
    (hsurj : ∀ x, dotProduct u x = 0 → ∃ y, E y = x) :
    ParametrizedPlaneSection A u (embeddedConicPolynomials E a) where
  homogeneous := embeddedConicPolynomials_homogeneous E a
  nonzero := by
    intro v hv
    change (fun i => eval v (embeddedConicPolynomials E a i)) ≠ 0
    rw [embeddedConicPolynomials_eval]
    intro he
    apply canonicalConicVector_ne_zero ha hv
    apply hE
    simpa using he
  pointEquiv := embeddedConicEquiv A u E hE a ha hF hL hsurj
  pointEquiv_mk := by
    intro v hv
    apply (embeddedConicEquiv_mk A u E hE a ha hF hL hsurj v hv).trans
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    simpa only [one_smul, polynomialVectorEval] using embeddedConicPolynomials_eval E a v
  partials := by
    intro v hv
    convert embeddedConicPolynomials_partials_independent E hE a ha h2 v hv using 1
    funext j
    fin_cases j <;> rfl
  quadric_identity := embeddedConicPolynomials_quadric_identity A E a hF
  plane_identity := embeddedConicPolynomials_plane_identity u E a hL

end QuaternaryQuadraticForms
