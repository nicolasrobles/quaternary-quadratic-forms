import QuaternaryQuadraticForms.ProjectiveRays
import Mathlib.Data.Fin.VecNotation

/-!
# The two charts of the projective line

The points here belong to mathlib's projectivization of `Fin 2 → K`.
The affine chart is represented by `(z,1)` and its complement by `(1,0)`.
These explicit representatives give a bijection, the finite-sum identity,
and the corresponding decomposition of the zeros of any homogeneous form.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

variable {K : Type*}

/-- The binary vector with coordinates `s,t`, in that order. -/
def binaryVector (s t : K) : Fin 2 → K := Fin.cases s (fun _ => t)

@[simp] theorem binaryVector_zero (s t : K) : binaryVector s t 0 = s := rfl
@[simp] theorem binaryVector_one (s t : K) : binaryVector s t 1 = t := rfl

/-- A binary vector is determined by its two coordinates. -/
theorem binaryVector_eta (x : Fin 2 → K) : binaryVector (x 0) (x 1) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

/-- Agreement with mathlib's vector notation. -/
theorem binaryVector_eq_vec (s t : K) : binaryVector s t = ![s, t] :=
  binaryVector_eta ![s, t]

variable [Field K]

theorem binaryVector_infinity_ne_zero : binaryVector (1 : K) 0 ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

theorem binaryVector_affine_ne_zero (z : K) : binaryVector z 1 ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 1)

/-- `none` is the point at infinity; `some z` is the affine point `(z:1)`. -/
def projectiveLinePoint : Option K → ℙ K (Fin 2 → K)
  | none => Projectivization.mk K (binaryVector 1 0) binaryVector_infinity_ne_zero
  | some z => Projectivization.mk K (binaryVector z 1) (binaryVector_affine_ne_zero z)

theorem projectiveLinePoint_injective : Function.Injective (projectiveLinePoint (K := K)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h
      have ha1 := congrFun ha 1
      change (a : K) * 1 = 0 at ha1
      have haz : (a : K) = 0 := (mul_one (a : K)).symm.trans ha1
      exact False.elim (a.ne_zero haz)
  | some x =>
    cases y with
    | none =>
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h
      have ha1 := congrFun ha 1
      change (a : K) * 0 = 1 at ha1
      have hz : (0 : K) = 1 := (mul_zero (a : K)).symm.trans ha1
      exact False.elim (zero_ne_one hz)
    | some y =>
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h
      have ha1 : (a : K) = 1 := by
        have h1 := congrFun ha 1
        change (a : K) * 1 = 1 at h1
        simpa using h1
      have hyx : y = x := by
        have h0 := congrFun ha 0
        change (a : K) * y = x at h0
        simpa [ha1] using h0
      exact congrArg some hyx.symm

theorem projectiveLinePoint_surjective : Function.Surjective (projectiveLinePoint (K := K)) := by
  intro P
  by_cases ht : P.rep 1 = 0
  · have hs : P.rep 0 ≠ 0 := by
      intro hs
      apply P.rep_nonzero
      rw [← binaryVector_eta P.rep, hs, ht]
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    refine ⟨none, ?_⟩
    apply Eq.trans ?_ P.mk_rep
    apply Eq.symm
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
    refine ⟨Units.mk0 (P.rep 0) hs, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change P.rep 0 * 1 = P.rep 0
      exact mul_one _
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change P.rep 0 * 0 = P.rep 1
      simpa using ht.symm
  · refine ⟨some (P.rep 0 / P.rep 1), ?_⟩
    apply Eq.trans ?_ P.mk_rep
    apply Eq.symm
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
    refine ⟨Units.mk0 (P.rep 1) ht, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change P.rep 1 * (P.rep 0 / P.rep 1) = P.rep 0
      rw [mul_comm, div_mul_cancel₀ _ ht]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change P.rep 1 * 1 = P.rep 1
      exact mul_one _

/-- The two standard charts form an actual equivalence with the projective line. -/
def projectiveLineEquiv : Option K ≃ ℙ K (Fin 2 → K) :=
  Equiv.ofBijective projectiveLinePoint
    ⟨projectiveLinePoint_injective, projectiveLinePoint_surjective⟩

@[simp] theorem projectiveLineEquiv_apply (z : Option K) :
    projectiveLineEquiv z = projectiveLinePoint z := rfl

/-- A scalar-invariant weight evaluated on the standard chart representatives. -/
theorem projectiveLinePoint_weight {A : Type*} (f : (Fin 2 → K) → A)
    (hf : ∀ (a : Kˣ) x, f (a • x) = f x) (z : Option K) :
    f (projectiveLinePoint z).rep =
      match z with
      | none => f (binaryVector 1 0)
      | some z => f (binaryVector z 1) := by
  cases z <;> exact invariant_rep_mk f hf _ _

/-- The projective-line sum consists of its affine chart and the point at infinity. -/
theorem sum_projectiveLine [Fintype K] [Fintype (ℙ K (Fin 2 → K))]
    {A : Type*} [AddCommMonoid A] (f : (Fin 2 → K) → A)
    (hf : ∀ (a : Kˣ) x, f (a • x) = f x) :
    (∑ P : ℙ K (Fin 2 → K), f P.rep) =
      f (binaryVector 1 0) + ∑ z : K, f (binaryVector z 1) := by
  rw [← (projectiveLineEquiv (K := K)).sum_comp (fun P => f P.rep)]
  simp_rw [projectiveLineEquiv_apply, projectiveLinePoint_weight f hf]
  exact Fintype.sum_option _

/-- A scalar-stable condition can be tested on the standard chart representatives. -/
theorem projectiveLinePoint_predicate (C : (Fin 2 → K) → Prop)
    (hC : ∀ (a : Kˣ) x, C (a • x) ↔ C x) (z : Option K) :
    C (projectiveLinePoint z).rep ↔
      match z with
      | none => C (binaryVector 1 0)
      | some z => C (binaryVector z 1) := by
  cases z <;> exact cone_rep_mk C hC _ _

/-- Restricting the two chart parametrization to a scalar-stable condition
gives its affine locus and its possible point at infinity. -/
def projectiveLinePredicateEquiv (C : (Fin 2 → K) → Prop)
    (hC : ∀ (a : Kˣ) x, C (a • x) ↔ C x) :
    {P : ℙ K (Fin 2 → K) // C P.rep} ≃
      {z : K // C (binaryVector z 1)} ⊕ {_u : Unit // C (binaryVector 1 0)} := by
  let chartCondition : Option K → Prop := fun z =>
    match z with
    | none => C (binaryVector 1 0)
    | some z => C (binaryVector z 1)
  let e : {z : Option K // chartCondition z} ≃
      {P : ℙ K (Fin 2 → K) // C P.rep} :=
    projectiveLineEquiv.subtypeEquiv (fun z => (projectiveLinePoint_predicate C hC z).symm)
  refine e.symm.trans ?_
  exact {
    toFun := fun z => match z with
      | ⟨none, hz⟩ => Sum.inr ⟨(), hz⟩
      | ⟨some z, hz⟩ => Sum.inl ⟨z, hz⟩
    invFun := fun z => match z with
      | Sum.inl z => ⟨some z.1, z.2⟩
      | Sum.inr z => ⟨none, z.2⟩
    left_inv := by rintro ⟨z, hz⟩; cases z <;> rfl
    right_inv := by rintro (⟨z, hz⟩ | ⟨⟨⟩, hz⟩) <;> rfl }

end QuaternaryQuadraticForms
