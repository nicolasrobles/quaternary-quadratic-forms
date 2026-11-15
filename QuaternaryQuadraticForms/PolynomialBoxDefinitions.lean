import QuaternaryQuadraticForms.PolynomialBoxSlices
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Integer boxes and their polynomial congruence solutions

The finite sets below consist of actual integer tuples.  The fibre identity
separates the first coordinate without losing empty intervals or empty tails.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The integer points of the Cartesian product of closed integer intervals. -/
def integerPolynomialBox {n : ℕ} (a b : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (a i) (b i)

/-- The actual simultaneous polynomial congruence solutions in an integer box. -/
def polynomialBoxSolutions {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)) (a b : Fin n → ℤ) :
    Finset (Fin n → ℤ) := by
  classical
  exact (integerPolynomialBox a b).filter
    fun z => ∀ p ∈ S, MvPolynomial.eval (fun i => (z i : ZMod p)) (P p) = 0

/-- Membership in the box is coordinatewise interval membership. -/
theorem mem_integerPolynomialBox {n : ℕ} (a b z : Fin n → ℤ) :
    z ∈ integerPolynomialBox a b ↔ ∀ i, a i ≤ z i ∧ z i ≤ b i := by
  simp only [integerPolynomialBox, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Membership in the solution set retains all the literal congruences. -/
theorem mem_polynomialBoxSolutions {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)) (a b z : Fin n → ℤ) :
    z ∈ polynomialBoxSolutions S P a b ↔
      z ∈ integerPolynomialBox a b ∧
        ∀ p ∈ S, MvPolynomial.eval (fun i => (z i : ZMod p)) (P p) = 0 := by
  classical
  simp only [polynomialBoxSolutions, Finset.mem_filter]

/-- The exact box cardinality is the product of the one-dimensional cardinalities. -/
theorem integerPolynomialBox_card {n : ℕ} (a b : Fin n → ℤ) :
    (integerPolynomialBox a b).card =
      ∏ i, (Finset.Icc (a i) (b i)).card := by
  exact Fintype.card_piFinset _

/-- Uniform interval cardinality bounds give the usual box-volume bound. -/
theorem integerPolynomialBox_card_le {n : ℕ} (a b : Fin n → ℤ) (Y : ℝ)
    (_hY : 0 ≤ Y) (hI : ∀ i, ((Finset.Icc (a i) (b i)).card : ℝ) ≤ Y) :
    ((integerPolynomialBox a b).card : ℝ) ≤ Y ^ n := by
  rw [integerPolynomialBox_card, Nat.cast_prod]
  calc
    ∏ i, ((Finset.Icc (a i) (b i)).card : ℝ) ≤ ∏ _i : Fin n, Y :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hI i)
    _ = Y ^ n := by simp

/-- No congruence condition is imposed by the empty set of primes. -/
theorem polynomialBoxSolutions_empty {n : ℕ}
    (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)) (a b : Fin n → ℤ) :
    polynomialBoxSolutions ∅ P a b = integerPolynomialBox a b := by
  classical
  simp [polynomialBoxSolutions]

/-- Every solution is an actual point of the box. -/
theorem polynomialBoxSolutions_card_le_box {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)) (a b : Fin n → ℤ) :
    (polynomialBoxSolutions S P a b).card ≤ (integerPolynomialBox a b).card := by
  classical
  exact Finset.card_filter_le _ _

/-- Separating the first coordinate preserves exact box membership. -/
theorem cons_mem_integerPolynomialBox {n : ℕ} (a b : Fin (n + 1) → ℤ)
    (t : ℤ) (y : Fin n → ℤ) :
    Fin.cons t y ∈ integerPolynomialBox a b ↔
      t ∈ Finset.Icc (a 0) (b 0) ∧
        y ∈ integerPolynomialBox (Fin.tail a) (Fin.tail b) := by
  simp [integerPolynomialBox, Fin.forall_iff_succ, Fin.tail]

/-- The zero-dimensional box contains its unique empty tuple. -/
theorem integerPolynomialBox_zero (a b : Fin 0 → ℤ) :
    integerPolynomialBox a b = {Fin.elim0} := by
  ext y
  constructor
  · intro _
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  · intro _
    exact Fintype.mem_piFinset.mpr (fun i => Fin.elim0 i)

/-- An exact fibre decomposition for any predicate on the integer box. -/
theorem integerPolynomialBox_filter_card_succ {n : ℕ}
    (a b : Fin (n + 1) → ℤ) (Q : (Fin (n + 1) → ℤ) → Prop) [DecidablePred Q] :
    ((integerPolynomialBox a b).filter Q).card =
      ∑ y ∈ integerPolynomialBox (Fin.tail a) (Fin.tail b),
        ((Finset.Icc (a 0) (b 0)).filter fun t => Q (Fin.cons t y)).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun z _ => ⟨Fin.tail z, z 0⟩) ?_ ?_ ?_
  · intro z hz
    obtain ⟨hz, hQ⟩ := Finset.mem_filter.mp hz
    have hc := (cons_mem_integerPolynomialBox a b (z 0) (Fin.tail z)).mp
      (by simpa only [Fin.cons_self_tail] using hz)
    exact Finset.mem_sigma.mpr ⟨hc.2, Finset.mem_filter.mpr
      ⟨hc.1, by simpa only [Fin.cons_self_tail] using hQ⟩⟩
  · intro z hz w hw h
    have htail : Fin.tail z = Fin.tail w := congrArg Sigma.fst h
    have hzero : z 0 = w 0 := congrArg (fun v => v.2) h
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail w, htail, hzero]
  · rintro ⟨y, t⟩ hyt
    obtain ⟨hy, ht⟩ := Finset.mem_sigma.mp hyt
    obtain ⟨ht, hQ⟩ := Finset.mem_filter.mp ht
    refine ⟨Fin.cons t y, Finset.mem_filter.mpr
      ⟨(cons_mem_integerPolynomialBox a b t y).mpr ⟨ht, hy⟩, hQ⟩, ?_⟩
    simp

/-- The simultaneous-congruence count is the sum of its one-dimensional fibres. -/
theorem polynomialBoxSolutions_card_succ {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin (n + 1)) (ZMod p))
    (a b : Fin (n + 1) → ℤ) :
    (polynomialBoxSolutions S P a b).card =
      ∑ y ∈ integerPolynomialBox (Fin.tail a) (Fin.tail b),
        ((Finset.Icc (a 0) (b 0)).filter fun t =>
          ∀ p ∈ S, (polynomialBoxSlice (P p) (fun i => (y i : ZMod p))).eval
            (t : ZMod p) = 0).card := by
  classical
  rw [polynomialBoxSolutions, integerPolynomialBox_filter_card_succ]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  apply Finset.filter_congr
  intro t ht
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [polynomialBoxSlice_eval]
  have hc : (fun i : Fin (n + 1) => ((Fin.cons t y : Fin (n + 1) → ℤ) i : ZMod p)) =
      Fin.cons (t : ZMod p) (fun i => (y i : ZMod p)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hc]

end QuaternaryQuadraticForms
