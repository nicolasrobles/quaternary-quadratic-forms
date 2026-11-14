import QuaternaryQuadraticForms.BadReductionSystem
import QuaternaryQuadraticForms.RankThreeMinors
import QuaternaryQuadraticForms.EliminationData

/-!
# The equations detecting a nontransverse plane

The second homogeneous system in Lemma 4.1 consists of the actual
quadratic equation, the second form, the plane equation and the minors
of the two gradient rows and the plane normal. All ordered triples of
columns are retained; repetitions do not change the common zero set.
The construction is over arbitrary commutative rings, before any
specialization of either the form coefficients or the plane normal.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal plane equation, also over a ring of polynomial parameters. -/
def planeEquationPolynomial {R : Type*} [CommSemiring R]
    (u : Fin 4 → R) : MvPolynomial (Fin 4) R :=
  ∑ i, MvPolynomial.C (u i) * MvPolynomial.X i

/-- The ring-general equation agrees with the previously used field equation. -/
theorem planeEquationPolynomial_eq_planePolynomial {K : Type*} [Field K]
    (u : Fin 4 → K) : planeEquationPolynomial u = planePolynomial u := rfl

/-- Evaluation of the plane equation is the actual dot product. -/
theorem eval_planeEquationPolynomial {R : Type*} [CommSemiring R]
    (u x : Fin 4 → R) :
    MvPolynomial.eval x (planeEquationPolynomial u) = dotProduct u x := by
  simp [planeEquationPolynomial, dotProduct]

/-- The plane equation retains homogeneous degree one even for zero normal. -/
theorem planeEquationPolynomial_homogeneous {R : Type*} [CommSemiring R]
    (u : Fin 4 → R) : (planeEquationPolynomial u).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X (u i) i

/-- Plane equations commute with every coefficient homomorphism. -/
theorem planeEquationPolynomial_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (u : Fin 4 → R) :
    (planeEquationPolynomial u).map f = planeEquationPolynomial (f ∘ u) := by
  simp only [planeEquationPolynomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, Function.comp_apply]

/-- One three-by-three minor, expanded along the constant plane-normal row. -/
def gradientPlaneMinor {R : Type*} [CommRing R]
    (F G : MvPolynomial (Fin 4) R) (u : Fin 4 → R) (i j k : Fin 4) :
    MvPolynomial (Fin 4) R :=
  MvPolynomial.C (u k) * gradientMinor F G i j -
    MvPolynomial.C (u j) * gradientMinor F G i k +
    MvPolynomial.C (u i) * gradientMinor F G j k

/-- Such a minor has degree `n` in the geometric variables. -/
theorem gradientPlaneMinor_homogeneous {R : Type*} [CommRing R]
    (F G : MvPolynomial (Fin 4) R) {n : ℕ} (hn : 1 ≤ n)
    (hF : F.IsHomogeneous 2) (hG : G.IsHomogeneous n)
    (u : Fin 4 → R) (i j k : Fin 4) :
    (gradientPlaneMinor F G u i j k).IsHomogeneous n := by
  exact (((gradientMinor_homogeneous F G hn hF hG i j).C_mul (u k)).sub
    ((gradientMinor_homogeneous F G hn hF hG i k).C_mul (u j))).add
      ((gradientMinor_homogeneous F G hn hF hG j k).C_mul (u i))

/-- The minors commute with coefficient maps, including prime reduction. -/
theorem gradientPlaneMinor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F G : MvPolynomial (Fin 4) R)
    (u : Fin 4 → R) (i j k : Fin 4) :
    (gradientPlaneMinor F G u i j k).map f =
      gradientPlaneMinor (F.map f) (G.map f) (f ∘ u) i j k := by
  simp only [gradientPlaneMinor, map_add, map_sub, map_mul,
    MvPolynomial.map_C, gradientMinor_map, Function.comp_apply]

/-- The formal polynomial minor evaluates to the actual scalar row minor. -/
theorem eval_gradientPlaneMinor {R : Type*} [CommRing R]
    (F G : MvPolynomial (Fin 4) R) (u x : Fin 4 → R) (i j k : Fin 4) :
    MvPolynomial.eval x (gradientPlaneMinor F G u i j k) =
      rowTripleMinor (polynomialGradient F x) (polynomialGradient G x) u i j k := by
  simp only [gradientPlaneMinor, map_add, map_sub, map_mul, MvPolynomial.eval_C,
    eval_gradientMinor, rowTripleMinor]
  ring

/-- The three equations followed by all sixty-four ordered minors. -/
abbrev PlaneReductionIndex := Fin 3 ⊕ (Fin 4 × Fin 4 × Fin 4)

/-- The actual second system of Lemma 4.1, over any coefficient ring. -/
def planeReductionSystem {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (G : MvPolynomial (Fin 4) R)
    (u : Fin 4 → R) : PlaneReductionIndex → MvPolynomial (Fin 4) R :=
  Sum.elim ![matrixQuadraticPolynomial A, G, planeEquationPolynomial u]
    (fun ijk => gradientPlaneMinor (matrixQuadraticPolynomial A) G u
      ijk.1 ijk.2.1 ijk.2.2)

/-- The assigned degrees are two, `n`, one and `n` for all the minors. -/
def planeReductionSystemDegree (n : ℕ) : PlaneReductionIndex → ℕ :=
  Sum.elim ![2, n, 1] (fun _ => n)

/-- Ordered repetition changes neither the equations nor their finite nature. -/
theorem card_planeReductionIndex : Fintype.card PlaneReductionIndex = 67 := by
  decide

/-- Every entry has its positive prescribed homogeneous degree. -/
theorem planeReductionSystem_homogeneous {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (G : MvPolynomial (Fin 4) R)
    {n : ℕ} (hn : 2 ≤ n) (hG : G.IsHomogeneous n)
    (u : Fin 4 → R) (k : PlaneReductionIndex) :
    (planeReductionSystem A G u k).IsHomogeneous (planeReductionSystemDegree n k) := by
  rcases k with k | ⟨i, j, k⟩
  · fin_cases k
    · exact matrixQuadraticPolynomial_homogeneous A
    · exact hG
    · exact planeEquationPolynomial_homogeneous u
  · exact gradientPlaneMinor_homogeneous _ _ (by omega)
      (matrixQuadraticPolynomial_homogeneous A) hG u i j k

/-- Positivity of all assigned degrees for homogeneous elimination. -/
theorem planeReductionSystemDegree_pos {n : ℕ} (hn : 2 ≤ n)
    (k : PlaneReductionIndex) : 0 < planeReductionSystemDegree n k := by
  rcases k with k | ⟨i, j, k⟩
  · fin_cases k <;> simp [planeReductionSystemDegree]
    omega
  · exact lt_of_lt_of_le (by decide : 0 < 2) hn

/-- Forming this entire system commutes with coefficient specialization. -/
theorem planeReductionSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) (u : Fin 4 → R) (k : PlaneReductionIndex) :
    (planeReductionSystem A G u k).map f =
      planeReductionSystem (A.map f) (G.map f) (f ∘ u) k := by
  rcases k with k | ⟨i, j, k⟩
  · fin_cases k
    · exact matrixQuadraticPolynomial_map_ring f A
    · rfl
    · exact planeEquationPolynomial_map f u
  · exact (gradientPlaneMinor_map f _ _ u i j k).trans (by
      rw [matrixQuadraticPolynomial_map_ring]
      rfl)

/-- Evaluation after mapping equals evaluation through the coefficient map. -/
theorem eval_planeReductionSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 4) (Fin 4) R)
    (G : MvPolynomial (Fin 4) R) (u : Fin 4 → R)
    (x : Fin 4 → S) (k : PlaneReductionIndex) :
    MvPolynomial.eval x (planeReductionSystem (A.map f) (G.map f) (f ∘ u) k) =
      MvPolynomial.eval₂ f x (planeReductionSystem A G u k) := by
  rw [← planeReductionSystem_map, MvPolynomial.eval_map]

/-- Vanishing of this system is the actual failure of rank three at a
common zero of the quadratic, the form and the plane equation. -/
theorem planeReductionSystem_zero_iff {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (G : MvPolynomial (Fin 4) K)
    (u x : Fin 4 → K) :
    (∀ k, MvPolynomial.eval x (planeReductionSystem A G u k) = 0) ↔
      MvPolynomial.eval x (matrixQuadraticPolynomial A) = 0 ∧
      MvPolynomial.eval x G = 0 ∧ dotProduct u x = 0 ∧
      Matrix.rank ![polynomialGradient (matrixQuadraticPolynomial A) x,
        polynomialGradient G x, u] ≠ 3 := by
  constructor
  · intro h
    refine ⟨h (Sum.inl 0), h (Sum.inl 1), ?_, ?_⟩
    · exact (eval_planeEquationPolynomial u x).symm.trans (h (Sum.inl 2))
    · apply (rank_three_ne_iff_minors_zero _ _ _).mpr
      intro i j k
      exact (eval_gradientPlaneMinor _ _ u x i j k).symm.trans (h (Sum.inr (i, j, k)))
  · rintro ⟨hF, hG, hu, hrank⟩ k
    rcases k with k | ⟨i, j, k⟩
    · fin_cases k
      · exact hF
      · exact hG
      · exact (eval_planeEquationPolynomial u x).trans hu
    · exact (eval_gradientPlaneMinor _ _ u x i j k).trans
        ((rank_three_ne_iff_minors_zero _ _ _).mp hrank i j k)

/-- Nonzero common zeros are precisely failures of the manuscript's
literal plane-transversality condition. -/
theorem exists_planeReductionSystem_zero_iff {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (G : MvPolynomial (Fin 4) K)
    (u : Fin 4 → K) :
    (∃ x : Fin 4 → K, x ≠ 0 ∧
      ∀ k, MvPolynomial.eval x (planeReductionSystem A G u k) = 0) ↔
      ¬ PlaneTransverseRank (matrixQuadraticPolynomial A) G u := by
  simp only [planeReductionSystem_zero_iff, PlaneTransverseRank]
  push_neg
  rfl

/-- The geometric zero condition is rank failure over the algebraic closure. -/
theorem hasNonzeroGeometricZero_planeReductionSystem_iff {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (G : MvPolynomial (Fin 4) K)
    (u : Fin 4 → K) :
    HasNonzeroGeometricZero (planeReductionSystem A G u) ↔
      ¬ PlaneTransverseRank
        ((matrixQuadraticPolynomial A).map (algebraMap K (AlgebraicClosure K)))
        (G.map (algebraMap K (AlgebraicClosure K)))
        ((algebraMap K (AlgebraicClosure K)) ∘ u) := by
  simp only [HasNonzeroGeometricZero, planeReductionSystem_map]
  rw [exists_planeReductionSystem_zero_iff, matrixQuadraticPolynomial_map_ring]

end QuaternaryQuadraticForms
