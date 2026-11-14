import QuaternaryQuadraticForms.SourceGoodPrime

/-!
# Good moduli from the source radical condition

The source condition `(q,N)=1` excludes every prime dividing `N_F`, since
`rad(N_F)` divides `N`. Integer nonsingularity ensures that the literal
radical membership theorem is applicable, exactly as in the prime case.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Every source modulus coprime to `N` is coprime to the actual bad-prime
modulus, using precisely the source radical divisibility condition. -/
theorem source_coprime_quadraticBadPrimeModulus (N q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (hqN : q.Coprime N) : q.Coprime (quadraticBadPrimeModulus A) := by
  by_contra h
  obtain ⟨p, hp, hpq, hpA⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  letI : Fact p.Prime := ⟨hp⟩
  have hpN : ¬ p ∣ N := hp.coprime_iff_not_dvd.mp (hqN.of_dvd_left hpq)
  exact source_not_dvd_quadraticBadPrimeModulus N p A hdet hrad hpN hpA

end QuaternaryQuadraticForms
