import QuaternaryQuadraticForms.DiagonalForms
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The literal diagonal pencil

These are the coefficients, cubic polynomial, singular-parameter forms,
and pair products in Lemma 4.6. Coefficient maps and evaluation identities
refer to the actual source expressions.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The coefficient of the `i`th square in `G + t F`. -/
def diagonalPencilCoeff {R : Type*} [CommRing R]
    (a b : Fin 4 → R) (t : R) (i : Fin 4) : R := b i + t * a i

/-- The source coefficient `κ_i`. -/
def diagonalKappa {R : Type*} [CommRing R]
    (a b : Fin 4 → R) (i : Fin 4) : R :=
  -a i * ∏ j ∈ Finset.univ.erase i, (a i * b j - a j * b i)

/-- The actual cubic pencil polynomial `Φ_u`. -/
def diagonalPencilPhi {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) : Polynomial R :=
  ∑ i, Polynomial.C (u i ^ 2) *
    ∏ j ∈ Finset.univ.erase i,
      (Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j))

/-- The actual singular-parameter quadratic expression `ν_i(u)`. -/
def diagonalPencilNu {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) (i : Fin 4) : R :=
  ∑ j ∈ Finset.univ.erase i, u j ^ 2 *
    ∏ l ∈ (Finset.univ.erase i).erase j, (a i * b l - a l * b i)

/-- The product of all four coefficients of `G + t F`. -/
def diagonalPencilDelta {R : Type*} [CommRing R]
    (a b : Fin 4 → R) (t : R) : R := ∏ i, diagonalPencilCoeff a b t i

/-- The singular parameter `t_i = -b_i/a_i`. -/
def diagonalPencilRoot {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) : K := -b i / a i

/-- The product of the three remaining coefficients at the singular parameter. -/
def diagonalPencilDeltaAtRoot {K : Type*} [Field K]
    (a b : Fin 4 → K) (i : Fin 4) : K :=
  ∏ j ∈ Finset.univ.erase i, diagonalPencilCoeff a b (diagonalPencilRoot a b i) j

/-- The three-term reciprocal sum at a singular parameter. -/
def diagonalPencilW {K : Type*} [Field K]
    (a b u : Fin 4 → K) (i : Fin 4) : K :=
  ∑ j ∈ Finset.univ.erase i,
    u j ^ 2 / diagonalPencilCoeff a b (diagonalPencilRoot a b i) j

/-- Evaluation of `Φ_u` is the source sum of complementary coefficient products. -/
theorem eval_diagonalPencilPhi {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) (t : R) :
    (diagonalPencilPhi a b u).eval t =
      ∑ i, u i ^ 2 * ∏ j ∈ Finset.univ.erase i, diagonalPencilCoeff a b t j := by
  simp only [diagonalPencilPhi, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    diagonalPencilCoeff]

/-- Coefficient homomorphisms preserve the pencil coefficients. -/
theorem diagonalPencilCoeff_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Fin 4 → R) (t : R) (i : Fin 4) :
    diagonalPencilCoeff (f ∘ a) (f ∘ b) (f t) i = f (diagonalPencilCoeff a b t i) := by
  simp [diagonalPencilCoeff]

/-- Coefficient homomorphisms preserve the source `κ_i`. -/
theorem diagonalKappa_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Fin 4 → R) (i : Fin 4) :
    diagonalKappa (f ∘ a) (f ∘ b) i = f (diagonalKappa a b i) := by
  simp [diagonalKappa, map_prod, Function.comp_apply]

/-- The formal polynomial `Φ_u` commutes with coefficient maps. -/
theorem diagonalPencilPhi_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b u : Fin 4 → R) :
    (diagonalPencilPhi a b u).map f =
      diagonalPencilPhi (f ∘ a) (f ∘ b) (f ∘ u) := by
  simp [diagonalPencilPhi, Polynomial.map_sum, Polynomial.map_prod, Function.comp_apply]

/-- Coefficient homomorphisms preserve the actual forms `ν_i`. -/
theorem diagonalPencilNu_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b u : Fin 4 → R) (i : Fin 4) :
    diagonalPencilNu (f ∘ a) (f ∘ b) (f ∘ u) i = f (diagonalPencilNu a b u i) := by
  simp [diagonalPencilNu, map_sum, map_prod, Function.comp_apply]

end QuaternaryQuadraticForms
