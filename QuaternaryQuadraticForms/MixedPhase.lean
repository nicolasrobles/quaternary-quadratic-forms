import QuaternaryQuadraticForms.MatrixPolynomial
import QuaternaryQuadraticForms.CRTCharacters

/-!
# The literal mixed-sum phase

The cone congruence makes the phase independent of a lift of the unit
parameter modulo `c`. The source CRT calculation holds for arbitrary
integer representatives, including modulus one and without requiring
coprimality between the cone modulus and the unit modulus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The cone condition kills the change in phase caused by replacing
the parameter by another integer in the same residue class modulo `c`. -/
theorem mixedPhase_intCast_lift_independent (q c : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x u : Fin 4 → ℤ) (a b : ℤ)
    (hF : (q : ℤ) ∣ dotProduct x (A.mulVec x))
    (hab : (a : ZMod c) = (b : ZMod c)) :
    ((a * dotProduct x (A.mulVec x) + dotProduct u x : ℤ) : ZMod (q * c)) =
      ((b * dotProduct x (A.mulVec x) + dotProduct u x : ℤ) : ZMod (q * c)) := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b c).mp hab
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨k * l, ?_⟩
  push_cast
  calc
    b * dotProduct x (A.mulVec x) + dotProduct u x -
        (a * dotProduct x (A.mulVec x) + dotProduct u x) =
        (b - a) * dotProduct x (A.mulVec x) := by ring
    _ = (c : ℤ) * l * ((q : ℤ) * k) := by rw [hl, hk]
    _ = _ := by ring

/-- Lift independence for the actual standard additive-character phase. -/
theorem mixedPhase_lift_independent (q c : ℕ) [NeZero q] [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x u : Fin 4 → ℤ) (a b : ℤ)
    (hF : (q : ℤ) ∣ dotProduct x (A.mulVec x))
    (hab : (a : ZMod c) = (b : ZMod c)) :
    ZMod.stdAddChar (N := q * c)
        ((a * dotProduct x (A.mulVec x) + dotProduct u x : ℤ) : ZMod (q * c)) =
      ZMod.stdAddChar (N := q * c)
        ((b * dotProduct x (A.mulVec x) + dotProduct u x : ℤ) : ZMod (q * c)) := by
  rw [mixedPhase_intCast_lift_independent q c A x u a b hF hab]

private theorem matrixQuadraticValue_scaled_add
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x y : Fin 4 → ℤ) (r s : ℤ) :
    dotProduct (r • x + s • y) (A.mulVec (r • x + s • y)) =
      r ^ 2 * dotProduct x (A.mulVec x) + s ^ 2 * dotProduct y (A.mulVec y) +
        r * s * (dotProduct x (A.mulVec y) + dotProduct y (A.mulVec x)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- The source CRT phase congruence for arbitrary integral representatives.
Only the two cone conditions are needed; coprimality is needed later for
the CRT bijections, not for this polynomial congruence. -/
theorem mixedPhase_crt_intCast (q₁ q₂ c₁ c₂ : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x₁ x₂ u : Fin 4 → ℤ) (a₁ a₂ : ℤ)
    (hF₁ : (q₁ : ℤ) ∣ dotProduct x₁ (A.mulVec x₁))
    (hF₂ : (q₂ : ℤ) ∣ dotProduct x₂ (A.mulVec x₂)) :
    let n₁ := q₁ * c₁
    let n₂ := q₂ * c₂
    let x := (n₂ : ℤ) • x₁ + (n₁ : ℤ) • x₂
    ((((c₂ : ℤ) * a₁ + (c₁ : ℤ) * a₂) * dotProduct x (A.mulVec x) +
        dotProduct u x : ℤ) : ZMod (n₁ * n₂)) =
      (((n₂ : ℤ) * ((c₂ : ℤ) * (n₂ : ℤ) * a₁ * dotProduct x₁ (A.mulVec x₁) +
          dotProduct u x₁) +
        (n₁ : ℤ) * ((c₁ : ℤ) * (n₁ : ℤ) * a₂ * dotProduct x₂ (A.mulVec x₂) +
          dotProduct u x₂) : ℤ) : ZMod (n₁ * n₂)) := by
  dsimp only
  obtain ⟨k₁, hk₁⟩ := hF₁
  obtain ⟨k₂, hk₂⟩ := hF₂
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨-(a₂ * ((q₂ * c₂ : ℕ) : ℤ) * k₁ +
      a₁ * ((q₁ * c₁ : ℕ) : ℤ) * k₂ +
      ((c₂ : ℤ) * a₁ + (c₁ : ℤ) * a₂) *
        (dotProduct x₁ (A.mulVec x₂) + dotProduct x₂ (A.mulVec x₁))), ?_⟩
  rw [matrixQuadraticValue_scaled_add]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hk₁, hk₂]
  push_cast
  ring

/-- The two source CRT factors of the actual standard additive phase.
The unit parameters are arbitrary integer representatives at this stage. -/
theorem mixedPhase_crt (q₁ q₂ c₁ c₂ : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero c₁] [NeZero c₂]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x₁ x₂ u : Fin 4 → ℤ) (a₁ a₂ : ℤ)
    (hF₁ : (q₁ : ℤ) ∣ dotProduct x₁ (A.mulVec x₁))
    (hF₂ : (q₂ : ℤ) ∣ dotProduct x₂ (A.mulVec x₂)) :
    let n₁ := q₁ * c₁
    let n₂ := q₂ * c₂
    let x := (n₂ : ℤ) • x₁ + (n₁ : ℤ) • x₂
    ZMod.stdAddChar (N := n₁ * n₂)
        ((((c₂ : ℤ) * a₁ + (c₁ : ℤ) * a₂) * dotProduct x (A.mulVec x) +
          dotProduct u x : ℤ) : ZMod (n₁ * n₂)) =
      ZMod.stdAddChar (N := n₁)
        (((c₂ : ℤ) * (n₂ : ℤ) * a₁ * dotProduct x₁ (A.mulVec x₁) +
          dotProduct u x₁ : ℤ) : ZMod n₁) *
      ZMod.stdAddChar (N := n₂)
        (((c₁ : ℤ) * (n₁ : ℤ) * a₂ * dotProduct x₂ (A.mulVec x₂) +
          dotProduct u x₂ : ℤ) : ZMod n₂) := by
  dsimp only
  rw [mixedPhase_crt_intCast q₁ q₂ c₁ c₂ A x₁ x₂ u a₁ a₂ hF₁ hF₂]
  exact stdAddChar_crt_split (q₁ * c₁) (q₂ * c₂) _ _

end QuaternaryQuadraticForms
