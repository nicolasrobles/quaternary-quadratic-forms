import QuaternaryQuadraticForms.BinaryForms
import QuaternaryQuadraticForms.GeometricRoots
import QuaternaryQuadraticForms.PolynomialWeights
import QuaternaryQuadraticForms.ProjectiveLine
import Lean.Elab.Tactic.Omega

/-!
# Geometric roots of a binary form

The geometric hypothesis in Corollary 2.6 is a count of actual points of the
projective line over an algebraic closure.  The chart equivalence proves that
this count is the number of affine roots, with one additional point precisely
when the form vanishes at infinity.  The degree bound then forces all affine
roots to be simple, and forces the affine degree to be `n` or `n - 1`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped LinearAlgebra.Projectivization
open Polynomial

variable {K : Type*} [Field K]

/-- The actual projective zero set, evaluated on mathlib's chosen representatives. -/
def binaryProjectiveZeros (g : MvPolynomial (Fin 2) K) :
    Set (ℙ K (Fin 2 → K)) :=
  {P | MvPolynomial.eval P.rep g = 0}

/-- The projective zero set after extending the coefficients to an algebraic closure. -/
def geometricBinaryProjectiveZeros (g : MvPolynomial (Fin 2) K) :
    Set (ℙ (AlgebraicClosure K) (Fin 2 → AlgebraicClosure K)) :=
  binaryProjectiveZeros (g.map (algebraMap K (AlgebraicClosure K)))

/-- The zero condition is independent of the projective representative. -/
theorem homogeneous_binary_zero_units_smul {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (a : Kˣ) (x : Fin 2 → K) :
    MvPolynomial.eval (a • x) g = 0 ↔ MvPolynomial.eval x g = 0 := by
  change MvPolynomial.eval ((a : K) • x) g = 0 ↔ _
  rw [homogeneous_eval_smul hg]
  simp [Units.ne_zero a]

/-- Affine-chart zeros are the root set of the literal polynomial `g(X,1)`. -/
def binaryAffineZerosEquiv {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) :
    {z : K // MvPolynomial.eval (binaryVector z 1) g = 0} ≃
      (binaryDehom g).rootSet K :=
  Equiv.subtypeEquivRight fun z => by
    rw [Polynomial.mem_rootSet_of_ne (binaryDehom_ne_zero hg hg0)]
    simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, binaryVector_eq_vec,
      binaryDehom_eval]

open Classical in
private theorem card_unit_subtype (P : Prop) :
    Nat.card {_u : Unit // P} = if P then 1 else 0 := by
  by_cases h : P
  · letI : Nonempty {_u : Unit // P} := ⟨⟨(), h⟩⟩
    simp [h]
  · letI : IsEmpty {_u : Unit // P} := ⟨fun x => h x.property⟩
    simp [h]

open Classical in
/-- The projective zero count is the affine root count plus the possible point
at infinity.  No separability assumption is used in this count. -/
theorem binaryProjectiveZeros_card {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) :
    Nat.card (binaryProjectiveZeros g) =
      Fintype.card ((binaryDehom g).rootSet K) +
        if MvPolynomial.eval ![1, 0] g = 0 then 1 else 0 := by
  let C : (Fin 2 → K) → Prop := fun x => MvPolynomial.eval x g = 0
  let e := projectiveLinePredicateEquiv C (homogeneous_binary_zero_units_smul hg)
  let ea := binaryAffineZerosEquiv hg hg0
  letI : Finite {z : K // C (binaryVector z 1)} :=
    Finite.of_equiv ((binaryDehom g).rootSet K) ea.symm
  calc
    Nat.card (binaryProjectiveZeros g) =
        Nat.card ({z : K // C (binaryVector z 1)} ⊕
          {_u : Unit // C (binaryVector 1 0)}) := Nat.card_congr e
    _ = Nat.card {z : K // C (binaryVector z 1)} +
        Nat.card {_u : Unit // C (binaryVector 1 0)} := Nat.card_sum
    _ = Fintype.card ((binaryDehom g).rootSet K) +
        if MvPolynomial.eval ![1, 0] g = 0 then 1 else 0 := by
      rw [Nat.card_congr ea, Nat.card_eq_fintype_card, card_unit_subtype]
      simp only [C, binaryVector_eq_vec]

open Classical in
/-- Having `n` distinct projective zeros forces a degree-`n` form to have a
positive affine degree, all of its affine roots distinct, and degree `n - 1`
exactly when infinity is a zero. -/
theorem binaryDehom_degree_and_rootCount {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) (hn : 2 ≤ n)
    (hroots : Nat.card (binaryProjectiveZeros g) = n) :
    0 < (binaryDehom g).natDegree ∧
      (binaryDehom g).natDegree =
        (if MvPolynomial.eval ![1, 0] g = 0 then n - 1 else n) ∧
      Fintype.card ((binaryDehom g).rootSet K) = (binaryDehom g).natDegree := by
  have hle := rootSet_card_le_natDegree (L := K) (binaryDehom g)
  rw [binaryProjectiveZeros_card hg hg0] at hroots
  by_cases hinf : MvPolynomial.eval ![1, 0] g = 0
  · rw [if_pos hinf] at hroots ⊢
    have hlt := binaryDehom_natDegree_lt_of_infinity_zero hg hg0 hinf
    omega
  · rw [if_neg hinf] at hroots ⊢
    have heq := (binaryDehom_natDegree_eq_iff hg hg0).mpr hinf
    omega

/-- The exact affine hypotheses used in the Weil bound, derived from the
manuscript's geometric projective-root condition over the algebraic closure. -/
theorem binaryDehom_geometric_data {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) (hn : 2 ≤ n)
    (hroots : Nat.card (geometricBinaryProjectiveZeros g) = n) :
    0 < (binaryDehom g).natDegree ∧ (binaryDehom g).natDegree ≤ n ∧
      Fintype.card ((binaryDehom g).rootSet (AlgebraicClosure K)) =
        (binaryDehom g).natDegree := by
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hgL0 : g.map i ≠ 0 := by
    intro hz
    apply hg0
    apply MvPolynomial.map_injective (f := i) i.injective
    simpa using hz
  have hdata := binaryDehom_degree_and_rootCount (hg.map i) hgL0 hn hroots
  refine ⟨?_, binaryDehom_natDegree_le hg, ?_⟩
  · simpa only [binaryDehom_map, Polynomial.natDegree_map] using hdata.1
  · simpa only [i, binaryDehom_map, Polynomial.natDegree_map, Polynomial.rootSet,
      Polynomial.aroots_map] using hdata.2.2

/-- In particular, the affine polynomial has no repeated geometric roots. -/
theorem binaryDehom_geometric_separable {g : MvPolynomial (Fin 2) K} {n : ℕ}
    (hg : g.IsHomogeneous n) (hg0 : g ≠ 0) (hn : 2 ≤ n)
    (hroots : Nat.card (geometricBinaryProjectiveZeros g) = n) :
    (binaryDehom g).Separable :=
  (geometricRootCount_eq_natDegree_iff _ (binaryDehom_ne_zero hg hg0)).mp
    (binaryDehom_geometric_data hg hg0 hn hroots).2.2

end QuaternaryQuadraticForms
