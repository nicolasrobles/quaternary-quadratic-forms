import QuaternaryQuadraticForms.RankMinors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The equations detecting bad reduction

For the actual quadratic polynomial and a second homogeneous polynomial,
we form the two equations and all ordered two-by-two minors of their
gradient rows. A nonzero common zero of this system is exactly a failure
of the projective rank condition. The construction works over arbitrary
commutative coefficient rings, so it also applies before specializing
indeterminate coefficients to integers.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- One literal two-by-two minor of the formal gradient rows. -/
def gradientMinor {σ R : Type*} [CommRing R]
    (F G : MvPolynomial σ R) (i j : σ) : MvPolynomial σ R :=
  MvPolynomial.pderiv i F * MvPolynomial.pderiv j G -
    MvPolynomial.pderiv j F * MvPolynomial.pderiv i G

/-- The two equations followed by all sixteen ordered gradient minors. -/
abbrev BadReductionIndex := Fin 2 ⊕ (Fin 4 × Fin 4)

/-- The integral bad-reduction system, with the same definition available
over any commutative ring of coefficients. -/
def badReductionSystem {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (G : MvPolynomial (Fin 4) R) :
    BadReductionIndex → MvPolynomial (Fin 4) R :=
  Sum.elim ![matrixQuadraticPolynomial A, G]
    (fun ij => gradientMinor (matrixQuadraticPolynomial A) G ij.1 ij.2)

/-- The assigned homogeneous degrees: two, then the degree of `G`, and
that same degree for each minor. A zero polynomial retains its assigned
degree, as required for homogeneous elimination. -/
def badReductionSystemDegree (n : ℕ) : BadReductionIndex → ℕ :=
  Sum.elim ![2, n] (fun _ => n)

/-- The system has eighteen entries; ordered repetitions add no zeros. -/
theorem card_badReductionIndex : Fintype.card BadReductionIndex = 18 := by
  decide

/-- A gradient minor of a quadratic and a degree-`n` homogeneous
polynomial is homogeneous of degree `n`. -/
theorem gradientMinor_homogeneous {σ R : Type*} [CommRing R]
    (F G : MvPolynomial σ R) {n : ℕ} (hn : 1 ≤ n)
    (hF : F.IsHomogeneous 2) (hG : G.IsHomogeneous n) (i j : σ) :
    (gradientMinor F G i j).IsHomogeneous n := by
  have hdegree : (2 - 1) + (n - 1) = n := by omega
  rw [gradientMinor, ← hdegree]
  exact (hF.pderiv.mul hG.pderiv).sub (hF.pderiv.mul hG.pderiv)

/-- Every entry of the literal system has its prescribed homogeneous
degree, over the original coefficient ring. -/
theorem badReductionSystem_homogeneous {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (G : MvPolynomial (Fin 4) R)
    {n : ℕ} (hn : 2 ≤ n) (hG : G.IsHomogeneous n)
    (k : BadReductionIndex) :
    (badReductionSystem A G k).IsHomogeneous (badReductionSystemDegree n k) := by
  rcases k with k | ⟨i, j⟩
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact matrixQuadraticPolynomial_homogeneous A
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      exact hG
  · exact gradientMinor_homogeneous _ _ (by omega)
      (matrixQuadraticPolynomial_homogeneous A) hG i j

/-- All prescribed degrees are positive when the manuscript's `n ≥ 2`
hypothesis holds. -/
theorem badReductionSystemDegree_pos {n : ℕ} (hn : 2 ≤ n)
    (k : BadReductionIndex) : 0 < badReductionSystemDegree n k := by
  rcases k with k | ⟨i, j⟩
  · refine Fin.cases ?_ (fun k => ?_) k
    · change 0 < 2
      decide
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      exact lt_of_lt_of_le (by decide : 0 < 2) hn
  · exact lt_of_lt_of_le (by decide : 0 < 2) hn

/-- The matrix quadratic polynomial commutes with arbitrary coefficient
homomorphisms, including reduction from the integers. -/
theorem matrixQuadraticPolynomial_map_ring {ι R S : Type*} [Fintype ι]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix ι ι R) :
    (matrixQuadraticPolynomial A).map f = matrixQuadraticPolynomial (A.map f) := by
  simp only [matrixQuadraticPolynomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, Matrix.map_apply]

/-- Formal gradient minors commute with coefficient reduction and
extension, with no assumption on the characteristic or on `n`. -/
theorem gradientMinor_map {σ R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F G : MvPolynomial σ R) (i j : σ) :
    (gradientMinor F G i j).map f = gradientMinor (F.map f) (G.map f) i j := by
  simp only [gradientMinor, map_sub, map_mul, MvPolynomial.pderiv_map]

/-- Mapping the literal system is the literal system of the mapped
matrix and polynomial. -/
theorem badReductionSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) (k : BadReductionIndex) :
    (badReductionSystem A G k).map f = badReductionSystem (A.map f) (G.map f) k := by
  rcases k with k | ⟨i, j⟩
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact matrixQuadraticPolynomial_map_ring f A
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      rfl
  · exact (gradientMinor_map f _ _ i j).trans (by
      rw [matrixQuadraticPolynomial_map_ring]
      rfl)

/-- Evaluation after coefficient specialization is the same as directly
evaluating the original polynomial through that coefficient homomorphism. -/
theorem eval_badReductionSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) (x : Fin 4 → S) (k : BadReductionIndex) :
    MvPolynomial.eval x (badReductionSystem (A.map f) (G.map f) k) =
      MvPolynomial.eval₂ f x (badReductionSystem A G k) := by
  rw [← badReductionSystem_map, MvPolynomial.eval_map]

/-- At an extended point, each specialized equation is the image of its
value at the original point. -/
theorem eval_badReductionSystem_map_point {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) (x : Fin 4 → R) (k : BadReductionIndex) :
    MvPolynomial.eval (f ∘ x) (badReductionSystem (A.map f) (G.map f) k) =
      f (MvPolynomial.eval x (badReductionSystem A G k)) := by
  rw [eval_badReductionSystem_map, MvPolynomial.eval₂_comp]

/-- Evaluation of a formal gradient minor is the actual scalar minor of
the two evaluated gradient rows. -/
theorem eval_gradientMinor {σ R : Type*} [CommRing R]
    (F G : MvPolynomial σ R) (x : σ → R) (i j : σ) :
    MvPolynomial.eval x (gradientMinor F G i j) =
      polynomialGradient F x i * polynomialGradient G x j -
        polynomialGradient F x j * polynomialGradient G x i := by
  simp only [gradientMinor, map_sub, map_mul, polynomialGradient]

/-- At any point over a field, the system vanishes exactly when both
equations vanish and the two actual gradient rows fail to have rank two. -/
theorem badReductionSystem_zero_iff {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (G : MvPolynomial (Fin 4) K)
    (x : Fin 4 → K) :
    (∀ k, MvPolynomial.eval x (badReductionSystem A G k) = 0) ↔
      MvPolynomial.eval x (matrixQuadraticPolynomial A) = 0 ∧
      MvPolynomial.eval x G = 0 ∧
      Matrix.rank ![polynomialGradient (matrixQuadraticPolynomial A) x,
        polynomialGradient G x] ≠ 2 := by
  simp [badReductionSystem, Fin.forall_fin_two,
    eval_gradientMinor, rank_two_ne_iff_minors_zero, and_assoc]

/-- The nonzero common zeros of this explicit polynomial system are
precisely the failures of the manuscript's projective rank condition. -/
theorem exists_badReductionSystem_zero_iff {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (G : MvPolynomial (Fin 4) K) :
    (∃ x : Fin 4 → K, x ≠ 0 ∧
      ∀ k, MvPolynomial.eval x (badReductionSystem A G k) = 0) ↔
      ¬ ProjectiveIntersectionTransverseRank (matrixQuadraticPolynomial A) G := by
  simp only [badReductionSystem_zero_iff, ProjectiveIntersectionTransverseRank]
  push_neg
  rfl

/-- The same zero-locus statement after an arbitrary coefficient map to
a field. This form applies directly to integral or universal coefficients. -/
theorem exists_badReductionSystem_eval₂_zero_iff {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) :
    (∃ x : Fin 4 → K, x ≠ 0 ∧
      ∀ k, MvPolynomial.eval₂ f x (badReductionSystem A G k) = 0) ↔
      ¬ ProjectiveIntersectionTransverseRank
        ((matrixQuadraticPolynomial A).map f) (G.map f) := by
  simp_rw [← eval_badReductionSystem_map]
  rw [exists_badReductionSystem_zero_iff, matrixQuadraticPolynomial_map_ring]

/-- The two-step prime reduction and algebraic-closure extension is
exactly evaluation of the original integral system through the composite
coefficient map. -/
theorem exists_badReductionSystem_zero_iff_not_goodReductionAt
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) :
    (∃ x : Fin 4 → AlgebraicClosure (ZMod p), x ≠ 0 ∧
      ∀ k, MvPolynomial.eval₂
        ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp
          (Int.castRingHom (ZMod p))) x (badReductionSystem A G k) = 0) ↔
      ¬ GoodReductionAt p A G := by
  rw [exists_badReductionSystem_eval₂_zero_iff]
  simp only [GoodReductionAt, reduceQuadraticMatrix, ← MvPolynomial.map_map,
    matrixQuadraticPolynomial_map_ring]
  rfl

/-- The prime-field specialization in the direct integer-cast form used
by homogeneous elimination. -/
theorem exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (G : MvPolynomial (Fin 4) ℤ) :
    (∃ x : Fin 4 → AlgebraicClosure (ZMod p), x ≠ 0 ∧
      ∀ k, MvPolynomial.eval₂ (Int.castRingHom (AlgebraicClosure (ZMod p))) x
        (badReductionSystem A G k) = 0) ↔
      ¬ GoodReductionAt p A G := by
  have hmap :
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp
          (Int.castRingHom (ZMod p)) =
        Int.castRingHom (AlgebraicClosure (ZMod p)) := RingHom.ext_int _ _
  simpa only [hmap] using
    exists_badReductionSystem_zero_iff_not_goodReductionAt p A G

end QuaternaryQuadraticForms
