import QuaternaryQuadraticForms.RankMinors
import QuaternaryQuadraticForms.TransversalityRank

/-!
# Rank failure for three rows in four coordinates

The ordered three-column minors detect exactly the failure of rank three.
We use their literal polynomial expansion, so that the same expression can
be formed in a polynomial coefficient ring before evaluation. Repeated
columns give zero minors and do not change the common zero locus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The literal determinant expansion for three rows and three chosen
columns. The columns are ordered and need not be distinct. -/
def rowTripleMinor {R : Type*} [CommRing R]
    (a b c : Fin 4 → R) (i j k : Fin 4) : R :=
  a i * (b j * c k - b k * c j) -
    a j * (b i * c k - b k * c i) +
    a k * (b i * c j - b j * c i)

/-- The polynomial expression is the determinant of the corresponding
three-column matrix, including choices with repeated columns. -/
theorem rowTripleMinor_eq_det {R : Type*} [CommRing R]
    (a b c : Fin 4 → R) (i j k : Fin 4) :
    rowTripleMinor a b c i j k =
      Matrix.det ![![a i, a j, a k], ![b i, b j, b k], ![c i, c j, c k]] := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, rowTripleMinor]
  ring

/-- Every coefficient homomorphism commutes with the literal minor. -/
theorem rowTripleMinor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c : Fin 4 → R) (i j k : Fin 4) :
    f (rowTripleMinor a b c i j k) =
      rowTripleMinor (f ∘ a) (f ∘ b) (f ∘ c) i j k := by
  simp only [rowTripleMinor, map_add, map_sub, map_mul, Function.comp_apply]

/-- Three rows have rank different from three precisely when every
ordered three-by-three column minor vanishes. -/
theorem rank_three_ne_iff_minors_zero {K : Type*} [Field K]
    (a b c : Fin 4 → K) :
    Matrix.rank ![a, b, c] ≠ 3 ↔
      ∀ i j k, rowTripleMinor a b c i j k = 0 := by
  classical
  change (¬ Matrix.rank ![a, b, c] = 3) ↔ _
  rw [rank_three_iff_linearIndependent]
  constructor
  · intro h
    by_cases hbc : LinearIndependent K ![b, c]
    · have ha : a ∈ Submodule.span K (Set.range ![b, c]) := by
        by_contra ha
        exact h (linearIndependent_fin_cons.mpr ⟨hbc, ha⟩)
      rw [Matrix.range_cons_cons_empty] at ha
      obtain ⟨s, t, ha⟩ := Submodule.mem_span_pair.mp ha
      intro i j k
      rw [← ha]
      simp only [rowTripleMinor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · have hbc' : ¬ (c ≠ 0 ∧ ∀ t : K, t • c ≠ b) := by
        simpa only [linearIndependent_fin2, Matrix.cons_val_zero, Matrix.cons_val_one]
          using hbc
      intro i j k
      by_cases hc : c = 0
      · subst c
        simp [rowTripleMinor]
      · obtain ⟨t, ht⟩ : ∃ t : K, t • c = b := by
          by_contra ht
          exact hbc' ⟨hc, fun t ht' => ht ⟨t, ht'⟩⟩
        rw [← ht]
        simp only [rowTripleMinor, Pi.smul_apply, smul_eq_mul]
        ring
  · intro h hli
    obtain ⟨hbc, ha⟩ := linearIndependent_fin_cons.mp hli
    have hbc_rank : Matrix.rank ![b, c] = 2 :=
      (rank_two_iff_linearIndependent _).mpr hbc
    obtain ⟨i, j, hij⟩ := (rank_two_iff_exists_minor_ne_zero b c).mp hbc_rank
    apply ha
    rw [Matrix.range_cons_cons_empty]
    apply Submodule.mem_span_pair.mpr
    refine ⟨(a i * c j - a j * c i) / (b i * c j - b j * c i),
      (b i * a j - b j * a i) / (b i * c j - b j * c i), ?_⟩
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (a i * c j - a j * c i) / (b i * c j - b j * c i) * b k +
          (b i * a j - b j * a i) / (b i * c j - b j * c i) * c k =
          ((a i * c j - a j * c i) * b k + (b i * a j - b j * a i) * c k) /
            (b i * c j - b j * c i) := by ring
      _ = a k := (div_eq_iff hij).mpr (by
        calc
          (a i * c j - a j * c i) * b k + (b i * a j - b j * a i) * c k =
              a k * (b i * c j - b j * c i) - rowTripleMinor a b c i j k := by
            dsimp only [rowTripleMinor]
            ring
          _ = a k * (b i * c j - b j * c i) := by rw [h i j k, sub_zero])

/-- Full rank is witnessed by a nonzero ordered three-column minor. -/
theorem rank_three_iff_exists_minor_ne_zero {K : Type*} [Field K]
    (a b c : Fin 4 → K) :
    Matrix.rank ![a, b, c] = 3 ↔
      ∃ i j k, rowTripleMinor a b c i j k ≠ 0 := by
  classical
  have h := not_congr (rank_three_ne_iff_minors_zero a b c)
  simpa only [not_not, not_forall] using h

end QuaternaryQuadraticForms
