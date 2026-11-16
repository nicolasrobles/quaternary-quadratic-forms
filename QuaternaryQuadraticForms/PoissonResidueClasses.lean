import QuaternaryQuadraticForms.PoissonDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Exact residue-class decomposition of the integer lattice

The quotient coordinates use integer Euclidean division, so the construction
includes negative lattice coordinates and modulus one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Reassemble a residue vector and an integer quotient vector. -/
def poissonResidueVector (n : ℕ) (z : Fin 4 → ZMod n) (m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => residueLift n z i + (n : ℤ) * m i

/-- Reduction of the reassembled vector recovers its residue. -/
theorem poissonResidueVector_cast (n : ℕ) [NeZero n]
    (z : Fin 4 → ZMod n) (m : Fin 4 → ℤ) (i : Fin 4) :
    (poissonResidueVector n z m i : ZMod n) = z i := by
  simp [poissonResidueVector, residueLift_cast]

/-- Reassembly is injective in the residue and quotient together. -/
theorem poissonResidueVector_injective (n : ℕ) [NeZero n] :
    Function.Injective (fun p : (Fin 4 → ZMod n) × (Fin 4 → ℤ) =>
      poissonResidueVector n p.1 p.2) := by
  rintro ⟨z, m⟩ ⟨w, k⟩ h
  have hzw : z = w := by
    funext i
    have hi := congrArg (fun x : Fin 4 → ℤ => (x i : ZMod n)) h
    simpa only [poissonResidueVector_cast] using hi
  subst w
  have hmk : m = k := by
    funext i
    have hi := congrFun h i
    dsimp [poissonResidueVector] at hi
    exact mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast (NeZero.ne n))
      (add_left_cancel hi)
  subst k
  rfl

/-- Every integer vector has its canonical residue and integer quotient. -/
theorem poissonResidueVector_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (fun p : (Fin 4 → ZMod n) × (Fin 4 → ℤ) =>
      poissonResidueVector n p.1 p.2) := by
  intro x
  refine ⟨⟨fun i => (x i : ZMod n), fun i => x i / (n : ℤ)⟩, ?_⟩
  funext i
  change ((x i : ZMod n).val : ℤ) + (n : ℤ) * (x i / (n : ℤ)) = x i
  rw [ZMod.val_intCast]
  exact Int.emod_add_mul_ediv (x i) n

/-- The exact residue/quotient equivalence for the four-dimensional lattice. -/
def poissonResidueEquiv (n : ℕ) [NeZero n] :
    ((Fin 4 → ZMod n) × (Fin 4 → ℤ)) ≃ (Fin 4 → ℤ) :=
  Equiv.ofBijective (fun p => poissonResidueVector n p.1 p.2)
    ⟨poissonResidueVector_injective n, poissonResidueVector_surjective n⟩

/-- The residue equivalence has the literal reassembly formula. -/
theorem poissonResidueEquiv_apply (n : ℕ) [NeZero n]
    (z : Fin 4 → ZMod n) (m : Fin 4 → ℤ) :
    poissonResidueEquiv n (z, m) = poissonResidueVector n z m := rfl

/-- Integer reassembly agrees with the affine real lattice used in Poisson summation. -/
theorem integerRealVector_poissonResidueVector (n : ℕ)
    (z : Fin 4 → ZMod n) (m : Fin 4 → ℤ) :
    integerRealVector (poissonResidueVector n z m) =
      integerRealVector (residueLift n z) + (n : ℝ) • integerRealVector m := by
  ext i
  simp [integerRealVector, poissonResidueVector]

/-- A finitely supported lattice summand is exactly the sum over all residue classes. -/
theorem poisson_tsum_residue_classes (n : ℕ) [NeZero n]
    (F : (Fin 4 → ℤ) → ℂ) (hF : (Function.support F).Finite) :
    (∑' x : Fin 4 → ℤ, F x) =
      ∑ z : Fin 4 → ZMod n, ∑' m : Fin 4 → ℤ, F (poissonResidueVector n z m) := by
  classical
  have hs : Summable F := by
    apply summable_of_ne_finset_zero (s := hF.toFinset)
    intro x hx
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hx
  have hp : Summable (F ∘ poissonResidueEquiv n) :=
    (poissonResidueEquiv n).summable_iff.mpr hs
  calc
    _ = ∑' p : (Fin 4 → ZMod n) × (Fin 4 → ℤ), F (poissonResidueEquiv n p) :=
      ((poissonResidueEquiv n).tsum_eq F).symm
    _ = ∑' z : Fin 4 → ZMod n, ∑' m : Fin 4 → ℤ,
        F (poissonResidueVector n z m) := hp.tsum_prod
    _ = _ := tsum_fintype _

/-- A unit-modulus additive phase preserves absolute summability. -/
theorem poisson_phase_mul_summable (n : ℕ) [NeZero n] (z : Fin 4 → ℤ)
    (f : (Fin 4 → ℤ) → ℂ) (hf : Summable (fun u => ‖f u‖)) :
    Summable (fun u : Fin 4 → ℤ =>
      ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod n) * f u) := by
  apply hf.of_norm_bounded
  intro u
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, le_refl]

end QuaternaryQuadraticForms
