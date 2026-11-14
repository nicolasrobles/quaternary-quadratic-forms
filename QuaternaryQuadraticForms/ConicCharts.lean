import QuaternaryQuadraticForms.ProjectiveLine
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The standard parametrization of a smooth split conic

The conic `y₀y₁ + a y₂² = 0` is parametrized by
`(-a s²,t²,st)`. All projective points are mathlib's actual quotient
by nonzero scalars. The results hold over every field with `a ≠ 0`;
the derivative independence additionally requires characteristic not two.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- The ternary quadratic form in the split normal form. -/
def canonicalConicValue (a : K) (y : Fin 3 → K) : K :=
  y 0 * y 1 + a * (y 2) ^ 2

/-- The literal quadratic parametrization of the conic. -/
def canonicalConicVector (a : K) (v : Fin 2 → K) : Fin 3 → K :=
  ![-a * (v 0) ^ 2, (v 1) ^ 2, v 0 * v 1]

theorem canonicalConicVector_smul (a c : K) (v : Fin 2 → K) :
    canonicalConicVector a (c • v) = c ^ 2 • canonicalConicVector a v := by
  ext i
  fin_cases i <;> simp [canonicalConicVector] <;> ring

theorem canonicalConicVector_ne_zero {a : K} (ha : a ≠ 0)
    {v : Fin 2 → K} (hv : v ≠ 0) : canonicalConicVector a v ≠ 0 := by
  intro h
  have ht : v 1 = 0 := by
    have h1 := congrFun h 1
    simpa [canonicalConicVector, Units.smul_def] using h1
  have hs : v 0 = 0 := by
    have h0 := congrFun h 0
    simpa [canonicalConicVector, ha] using h0
  apply hv
  ext i
  fin_cases i <;> simp [hs, ht]

theorem canonicalConicValue_vector (a : K) (v : Fin 2 → K) :
    canonicalConicValue a (canonicalConicVector a v) = 0 := by
  simp [canonicalConicValue, canonicalConicVector]
  ring

theorem canonicalConicValue_smul (a c : K) (y : Fin 3 → K) :
    canonicalConicValue a (c • y) = c ^ 2 * canonicalConicValue a y := by
  simp [canonicalConicValue]
  ring

theorem canonicalConicValue_units_zero_iff (a : K) (c : Kˣ) (y : Fin 3 → K) :
    canonicalConicValue a (c • y) = 0 ↔ canonicalConicValue a y = 0 := by
  change canonicalConicValue a ((c : K) • y) = 0 ↔ _
  rw [canonicalConicValue_smul]
  simp [Units.ne_zero c]

/-- The projective zero set of the canonical conic. -/
def CanonicalConic (a : K) :=
  {P : ℙ K (Fin 3 → K) // canonicalConicValue a P.rep = 0}

/-- The projective point represented by the quadratic parametrization. -/
def canonicalConicProjective (a : K) (ha : a ≠ 0)
    (P : ℙ K (Fin 2 → K)) : ℙ K (Fin 3 → K) :=
  Projectivization.mk K (canonicalConicVector a P.rep)
    (canonicalConicVector_ne_zero ha P.rep_nonzero)

/-- The projective map agrees with the literal formula on any representative. -/
theorem canonicalConicProjective_mk (a : K) (ha : a ≠ 0)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    canonicalConicProjective a ha (Projectivization.mk K v hv) =
      Projectivization.mk K (canonicalConicVector a v)
        (canonicalConicVector_ne_zero ha hv) := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
  refine ⟨c ^ 2, ?_⟩
  change (↑(c ^ 2) : K) • canonicalConicVector a v =
    canonicalConicVector a (Projectivization.mk K v hv).rep
  rw [← hc]
  simpa using (canonicalConicVector_smul a (c : K) v).symm

/-- The projective parametrization lands on the actual conic zero set. -/
def canonicalConicPoint (a : K) (ha : a ≠ 0)
    (P : ℙ K (Fin 2 → K)) : CanonicalConic a :=
  ⟨canonicalConicProjective a ha P, by
    apply (cone_rep_mk (fun y => canonicalConicValue a y = 0)
      (canonicalConicValue_units_zero_iff a) _ _).mpr
    exact canonicalConicValue_vector a P.rep⟩

private theorem canonicalConicProjective_chart_injective (a : K) (ha : a ≠ 0) :
    Function.Injective (fun z : Option K =>
      canonicalConicProjective a ha (projectiveLinePoint z)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      simp only [projectiveLinePoint, canonicalConicProjective_mk] at h
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
      have h1 := congrFun hc 1
      simp [canonicalConicVector, Units.smul_def] at h1
  | some x =>
    cases y with
    | none =>
      simp only [projectiveLinePoint, canonicalConicProjective_mk] at h
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
      have h1 := congrFun hc 1
      simp [canonicalConicVector] at h1
    | some y =>
      simp only [projectiveLinePoint, canonicalConicProjective_mk] at h
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
      have hc1 : (c : K) = 1 := by
        have h1 := congrFun hc 1
        simpa [canonicalConicVector, Units.smul_def] using h1
      have hyx : y = x := by
        have h2 := congrFun hc 2
        simpa [canonicalConicVector, Units.smul_def, hc1] using h2
      exact congrArg some hyx.symm

/-- Distinct projective parameters give distinct points of the conic. -/
theorem canonicalConicPoint_injective (a : K) (ha : a ≠ 0) :
    Function.Injective (canonicalConicPoint a ha) := by
  intro P Q h
  obtain ⟨x, rfl⟩ := projectiveLinePoint_surjective P
  obtain ⟨y, rfl⟩ := projectiveLinePoint_surjective Q
  apply congrArg projectiveLinePoint
  apply canonicalConicProjective_chart_injective a ha
  exact congrArg Subtype.val h

/-- Every nonzero zero of the ternary form is a scalar multiple of a
parametrized vector. This statement works over an arbitrary field. -/
theorem canonicalConicVector_surjective_projective (a : K) (ha : a ≠ 0)
    (y : Fin 3 → K) (hy : y ≠ 0) (hq : canonicalConicValue a y = 0) :
    ∃ (v : Fin 2 → K) (hv : v ≠ 0),
      Projectivization.mk K y hy =
        Projectivization.mk K (canonicalConicVector a v)
          (canonicalConicVector_ne_zero ha hv) := by
  by_cases ht : y 1 = 0
  · have hz : y 2 = 0 := by
      simpa [canonicalConicValue, ht, ha] using hq
    refine ⟨binaryVector 1 0, binaryVector_infinity_ne_zero, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨-y 0 / a, ?_⟩
    ext i
    fin_cases i
    · simp [canonicalConicVector]
      field_simp
    · simp [canonicalConicVector, ht]
    · simp [canonicalConicVector, hz]
  · refine ⟨binaryVector (y 2 / y 1) 1, binaryVector_affine_ne_zero _, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨y 1, ?_⟩
    have hy0 : y 0 * y 1 = -a * (y 2) ^ 2 := by
      calc
        _ = -(a * (y 2) ^ 2) := eq_neg_of_add_eq_zero_left hq
        _ = _ := by ring
    ext i
    fin_cases i
    · change y 1 * (-a * (y 2 / y 1) ^ 2) = y 0
      calc
        _ = (-a * (y 2) ^ 2) / y 1 := by field_simp
        _ = y 0 := by rw [← hy0, mul_div_cancel_right₀ _ ht]
    · simp [canonicalConicVector]
    · simpa [canonicalConicVector] using mul_div_cancel₀ (y 2) ht

/-- Every actual projective zero lies in the parametrization. -/
theorem canonicalConicPoint_surjective (a : K) (ha : a ≠ 0) :
    Function.Surjective (canonicalConicPoint a ha) := by
  rintro ⟨P, hP⟩
  obtain ⟨v, hv, heq⟩ := canonicalConicVector_surjective_projective a ha
    P.rep P.rep_nonzero hP
  refine ⟨Projectivization.mk K v hv, ?_⟩
  apply Subtype.ext
  change canonicalConicProjective a ha (Projectivization.mk K v hv) = P
  rw [canonicalConicProjective_mk, ← heq, P.mk_rep]

/-- The standard quadratic formula is a bijection onto the conic. -/
def canonicalConicEquiv (a : K) (ha : a ≠ 0) :
    ℙ K (Fin 2 → K) ≃ CanonicalConic a :=
  Equiv.ofBijective (canonicalConicPoint a ha)
    ⟨canonicalConicPoint_injective a ha, canonicalConicPoint_surjective a ha⟩

/-- Derivative of the parametrization with respect to the first variable. -/
def canonicalConicDs (a : K) (v : Fin 2 → K) : Fin 3 → K :=
  ![-2 * a * v 0, 0, v 1]

/-- Derivative of the parametrization with respect to the second variable. -/
def canonicalConicDt (v : Fin 2 → K) : Fin 3 → K :=
  ![0, 2 * v 1, v 0]

/-- The two explicit tangent vectors are independent away from the origin
in characteristic different from two. -/
theorem canonicalConic_derivatives_independent (a : K) (ha : a ≠ 0)
    (h2 : (2 : K) ≠ 0) (v : Fin 2 → K) (hv : v ≠ 0) :
    LinearIndependent K ![canonicalConicDs a v, canonicalConicDt v] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hs : v 0 = 0 := by
      have he := congrFun h 2
      simpa [canonicalConicDt] using he
    have ht : v 1 = 0 := by
      have he := congrFun h 1
      simpa [canonicalConicDt, h2] using he
    apply hv
    ext i
    fin_cases i <;> simp [hs, ht]
  · intro c h
    have hs : v 0 = 0 := by
      have he := congrFun h 0
      simpa [canonicalConicDt, canonicalConicDs, h2, ha] using he.symm
    have ht : v 1 = 0 := by
      have he := congrFun h 2
      simpa [canonicalConicDt, canonicalConicDs, hs] using he.symm
    apply hv
    ext i
    fin_cases i <;> simp [hs, ht]

end QuaternaryQuadraticForms
