import QuaternaryQuadraticForms.ConicNormalForm
import QuaternaryQuadraticForms.EmbeddedConic
import QuaternaryQuadraticForms.GoodPrime

/-!
# The manuscript's conic parametrization

The coordinate forms are chosen once over the prime field. The same forms,
with their coefficients mapped, give the required bijection and independent
formal derivatives over every extension field. The final statement uses
the manuscript's integral matrix and the actual modulus `2 |det A|`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

universe v

/-- Odd characteristic supplied by the prime-field hypothesis. -/
theorem primeField_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h2

/-- Lemma 4.2 over the prime field: one tuple of literal binary quadratic
forms works over every field extension, with every parametrization clause proved. -/
theorem conic_parametrization_prime_field (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p)
    (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0) :
    ∃ μ : Fin 4 → MvPolynomial (Fin 2) (ZMod p),
      (∀ i, (μ i).IsHomogeneous 2) ∧
      ∀ (L : Type v) [Field L] [Algebra (ZMod p) L],
        Nonempty (ParametrizedPlaneSection
          (A.map (algebraMap (ZMod p) L))
          ((algebraMap (ZMod p) L) ∘ u)
          (fun i => (μ i).map (algebraMap (ZMod p) L))) := by
  obtain ⟨a, E, ha, hnormal⟩ := plane_exists_hyperbolic_coordinates p hp A hA hdet u hu
  let e : (Fin 3 → ZMod p) →ₗ[ZMod p] (Fin 4 → ZMod p) :=
    (planeSubspace u).subtype.comp E.toLinearMap
  have he : Function.Injective e := by
    intro x y h
    apply E.injective
    exact Subtype.ext h
  have hplane : ∀ y, dotProduct u (e y) = 0 := fun y => (E y).property
  have hu0 : u ≠ 0 := by
    intro hz
    apply hu
    simp [hz]
  let μ := embeddedConicPolynomials e a
  refine ⟨μ, embeddedConicPolynomials_homogeneous e a, ?_⟩
  intro L _ _
  let f : ZMod p →+* L := algebraMap (ZMod p) L
  let eL := extendCoordinateMap f e
  have heL : Function.Injective eL := extendCoordinateMap_injective f e he
  have haL : f a ≠ 0 := fun hz => ha (f.injective (hz.trans f.map_zero.symm))
  have h2L : (2 : L) ≠ 0 := by
    intro hz
    apply primeField_two_ne_zero p hp
    apply f.injective
    simpa only [map_ofNat, map_zero] using hz
  have hnormalL : ∀ y, dotProduct (eL y) ((A.map f).mulVec (eL y)) =
      canonicalConicValue (f a) y := by
    intro y
    exact extendCoordinateMap_quadratic f e A a hnormal y
  have hplaneL : ∀ y, dotProduct (f ∘ u) (eL y) = 0 :=
    extendCoordinateMap_mem_plane f e u hplane
  have hsurjL : ∀ x, dotProduct (f ∘ u) x = 0 → ∃ y, eL y = x := by
    intro x hx
    have hrange := extendCoordinateMap_range_plane f e he u hu0 hplane
    change x ∈ LinearMap.range eL
    rw [hrange]
    exact hx
  have hμ : (fun i => (μ i).map f) = embeddedConicPolynomials eL (f a) := by
    funext i
    exact embeddedConicPolynomials_map f e a i
  change Nonempty (ParametrizedPlaneSection (A.map f) (f ∘ u) (fun i => (μ i).map f))
  rw [hμ]
  exact ⟨embeddedParametrizedPlaneSection (A.map f) (f ∘ u) eL heL (f a)
    haL h2L hnormalL hplaneL hsurjL⟩

/-- Lemma 4.2 with the manuscript's integral matrix and good-prime condition. -/
theorem conic_parametrization (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (u : Fin 4 → ZMod p)
    (hu : dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0) :
    ∃ μ : Fin 4 → MvPolynomial (Fin 2) (ZMod p),
      (∀ i, (μ i).IsHomogeneous 2) ∧
      ∀ (L : Type v) [Field L] [Algebra (ZMod p) L],
        Nonempty (ParametrizedPlaneSection
          ((reduceQuadraticMatrix p A).map (algebraMap (ZMod p) L))
          ((algebraMap (ZMod p) L) ∘ u)
          (fun i => (μ i).map (algebraMap (ZMod p) L))) :=
  conic_parametrization_prime_field p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) u hu

end QuaternaryQuadraticForms
