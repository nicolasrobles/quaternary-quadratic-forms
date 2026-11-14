import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Distinct geometric roots

The manuscript's condition that a degree `m` polynomial has `m` distinct
zeros in an algebraic closure is expressed using the actual root set.
These lemmas identify that condition with separability and provide the
degree bound used when passing from projective roots to an affine chart.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The number of distinct roots in any field extension cannot exceed the degree. -/
theorem rootSet_card_le_natDegree (g : K[X]) :
    Fintype.card (g.rootSet L) ≤ g.natDegree := by
  classical
  simp only [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (Polynomial.natDegree_map_le))

/-- For a nonzero polynomial, the root-set subtype is the literal geometric
zero set of its evaluation in the extension field. -/
def rootSetEquivEvalZeros (g : K[X]) (hg : g ≠ 0) :
    g.rootSet L ≃ {z : L // aeval z g = 0} :=
  Equiv.subtypeEquivRight fun _ => Polynomial.mem_rootSet_of_ne hg

/-- Counting all distinct roots over the algebraic closure detects separability. -/
theorem geometricRootCount_eq_natDegree_iff (g : K[X]) (hg : g ≠ 0) :
    Fintype.card (g.rootSet (AlgebraicClosure K)) = g.natDegree ↔ g.Separable :=
  Polynomial.card_rootSet_eq_natDegree_iff_of_splits hg (IsAlgClosed.splits_codomain g)

/-- A separable polynomial has exactly its degree many geometric roots. -/
theorem geometricRootCount_eq_natDegree (g : K[X]) (hg : g.Separable) :
    Fintype.card (g.rootSet (AlgebraicClosure K)) = g.natDegree :=
  Polynomial.card_rootSet_eq_natDegree hg (IsAlgClosed.splits_codomain g)

end QuaternaryQuadraticForms
