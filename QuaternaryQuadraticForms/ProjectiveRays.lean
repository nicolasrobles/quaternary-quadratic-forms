import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Decomposition into projective rays

The projective space in this file is mathlib's quotient of nonzero vectors by
nonzero scalar multiplication.  We prove that its chosen representatives,
together with the units of the scalar field, parametrize every nonzero vector
exactly once.  The resulting finite-sum identities are the geometric step in
the ray calculation preceding equation (4.5) of the frozen manuscript.

The cone and weight hypotheses below express invariance under scalar
multiplication.  They do not assume the sum decomposition.  Polynomial
homogeneity and the character condition supply those hypotheses separately.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

universe u v w

variable {K : Type u} {V : Type v}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The vector indexed by a projective point and a nonzero scalar. -/
noncomputable def projectiveRayVector (z : ℙ K V × Kˣ) : {x : V // x ≠ 0} :=
  ⟨z.2 • z.1.rep, (smul_ne_zero_iff_ne z.2).2 z.1.rep_nonzero⟩

/-- Taking the projective class forgets the nonzero scalar in a ray. -/
theorem projectiveRayVector_mk (z : ℙ K V × Kˣ) :
    Projectivization.mk K (projectiveRayVector z).1
      (projectiveRayVector z).2 = z.1 := by
  rw [← z.1.mk_rep]
  exact (Projectivization.mk_eq_mk_iff K _ _ _ _).2 ⟨z.2, rfl⟩

/-- Different projective points, or different scalars on a fixed ray, give
different nonzero vectors. -/
theorem projectiveRayVector_injective :
    Function.Injective (projectiveRayVector (K := K) (V := V)) := by
  rintro ⟨P, a⟩ ⟨Q, b⟩ h
  have hP : P = Q := by
    simpa only [projectiveRayVector_mk] using
      congrArg (fun x : {x : V // x ≠ 0} => Projectivization.mk K x.1 x.2) h
  subst Q
  apply Prod.ext
  · rfl
  · apply Units.ext
    apply smul_left_injective K P.rep_nonzero
    exact congrArg Subtype.val h

/-- Every nonzero vector lies on the ray of its own projective class. -/
theorem projectiveRayVector_surjective :
    Function.Surjective (projectiveRayVector (K := K) (V := V)) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  refine ⟨⟨Projectivization.mk K x hx, a⁻¹⟩, ?_⟩
  apply Subtype.ext
  change a⁻¹ • (Projectivization.mk K x hx).rep = x
  rw [← ha, inv_smul_smul]

/-- The actual ray parametrization, using the representatives of mathlib's
projectivization quotient. -/
noncomputable def projectiveRayEquiv : (ℙ K V × Kˣ) ≃ {x : V // x ≠ 0} :=
  Equiv.ofBijective projectiveRayVector
    ⟨projectiveRayVector_injective, projectiveRayVector_surjective⟩

@[simp]
theorem projectiveRayEquiv_apply (P : ℙ K V) (a : Kˣ) :
    (projectiveRayEquiv (P, a)).1 = a • P.rep := rfl

/-- A scalar-invariant function has the same value on any two representatives
of the same projective point. -/
theorem invariant_eq_of_projective_eq {A : Type w} (f : V → A)
    (hf : ∀ (a : Kˣ) (x : V), f (a • x) = f x)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Projectivization.mk K x hx = Projectivization.mk K y hy) :
    f x = f y := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K x y hx hy).1 hxy
  rw [← ha, hf]

/-- Evaluation on the chosen representative agrees with evaluation on the
original nonzero vector, for every scalar-invariant function. -/
theorem invariant_rep_mk {A : Type w} (f : V → A)
    (hf : ∀ (a : Kˣ) (x : V), f (a • x) = f x)
    (x : V) (hx : x ≠ 0) :
    f (Projectivization.mk K x hx).rep = f x := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  rw [← ha, hf]

/-- Membership in a scalar-stable cone also descends to projective space. -/
theorem cone_rep_mk (C : V → Prop)
    (hC : ∀ (a : Kˣ) (x : V), C (a • x) ↔ C x)
    (x : V) (hx : x ≠ 0) :
    C (Projectivization.mk K x hx).rep ↔ C x := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  rw [← ha, hC]

section FiniteSums

variable [Fintype V] [DecidableEq V] [Fintype Kˣ] [Fintype (ℙ K V)]

/-- Summing over nonzero vectors is summing once over each projective ray
and then over its nonzero scalar multiples. -/
theorem sum_nonzero_eq_sum_projective {A : Type w} [AddCommMonoid A]
    (f : V → A) :
    (∑ x : {x : V // x ≠ 0}, f x.1) =
      ∑ P : ℙ K V, ∑ a : Kˣ, f (a • P.rep) := by
  rw [← (projectiveRayEquiv (K := K) (V := V)).sum_comp
    (fun x : {x : V // x ≠ 0} => f x.1)]
  exact Fintype.sum_prod_type _

/-- The zero vector may be included when its summand vanishes. -/
theorem sum_eq_sum_projective_of_zero {A : Type w} [AddCommMonoid A]
    (f : V → A) (hf : f 0 = 0) :
    (∑ x : V, f x) = ∑ P : ℙ K V, ∑ a : Kˣ, f (a • P.rep) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]
  exact sum_nonzero_eq_sum_projective f

/-- The ray partition restricts to any cone invariant under nonzero scalar
multiplication. -/
theorem sum_cone_eq_sum_projective {A : Type w} [AddCommMonoid A]
    (C : V → Prop) [DecidablePred C]
    (hC : ∀ (a : Kˣ) (x : V), C (a • x) ↔ C x)
    (f : V → A) (hf : f 0 = 0) :
    (∑ x ∈ Finset.univ.filter C, f x) =
      ∑ P ∈ Finset.univ.filter (fun P : ℙ K V => C P.rep),
        ∑ a : Kˣ, f (a • P.rep) := by
  rw [Finset.sum_filter]
  rw [sum_eq_sum_projective_of_zero (K := K) (fun x => if C x then f x else 0)
    (by simp [hf])]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  simp_rw [hC]
  by_cases h : C P.rep <;> simp [h]

/-- A scalar-invariant weight can be taken outside each ray sum.  This is the
projective decomposition used by the Fourier identity, before evaluating the
additive-character sum over the nonzero scalars. -/
theorem sum_cone_weighted_eq_sum_projective {R : Type w} [Semiring R]
    (C : V → Prop) [DecidablePred C]
    (hC : ∀ (a : Kˣ) (x : V), C (a • x) ↔ C x)
    (weight phase : V → R) (hzero : weight 0 = 0)
    (hweight : ∀ (a : Kˣ) (x : V), weight (a • x) = weight x) :
    (∑ x ∈ Finset.univ.filter C, weight x * phase x) =
      ∑ P ∈ Finset.univ.filter (fun P : ℙ K V => C P.rep),
        weight P.rep * ∑ a : Kˣ, phase (a • P.rep) := by
  rw [sum_cone_eq_sum_projective C hC (fun x => weight x * phase x)
    (by simp [hzero])]
  apply Finset.sum_congr rfl
  intro P _
  simp_rw [hweight]
  exact (Finset.mul_sum _ _ _).symm

end FiniteSums

end QuaternaryQuadraticForms
