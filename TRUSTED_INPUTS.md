# Trusted literature inputs

The authors authorize source-relative certification: exact cited inputs used by the proofs are trusted and are not reproved. Their mathematical statements, hypotheses, source locators, and Lean declarations must be registered before use. All specializations, hypothesis checks, coefficient uniformity, and deductions made in this manuscript remain proof obligations.

**19 input groups are mapped; 2 external premise declarations are currently registered in Lean.** Mapping an input is not the same as formalizing its interface. Use a suitable official mathlib result where available.

| Input | Source locator | Accepted mathematical scope | Lean interface |
|---|---|---|---|
| `EXT.HB_DELTA` | [HB], Theorem 1; Section 3, equation (3.3) | Delta-symbol identity, common smooth h, support and size, and c_Q=1+O_j(Q^-j); use the manuscript-safe range Q>=3. | Pending |
| `EXT.HB_WEIGHT_LOCALIZATION` | [HB], Sections 2 and 6; Lemmas 2 and 12 | Uniform small-support localization of a bounded smooth family with gradient bounded below; coordinate permutations/sign changes and membership in the admissible local weight class. | Pending |
| `EXT.HB_INTEGRAL_ESTIMATES` | [HB], Theorem 3; Lemmas 13, 14, 15, 18 and 22 | Singular integral normalization, zero-frequency approximation, derivative reduction and decay estimates for the local oscillatory integrals. | Pending |
| `EXT.WEIL` | [K], Published equation (1.2); matching multiplicative-character bound in Section 1, page 1 of the author version dated April 19, 2001 | For a prime p, a nonprincipal multiplicative character of F_p extended by zero, and a polynomial f of degree d>=1 with d distinct zeros in an algebraic closure, the norm of sum_{z in F_p} psi(f(z)) is at most (d-1)*sqrt(p). No condition p not dividing d is imposed. | [`QuaternaryQuadraticForms.Trusted.weil_simple_roots`](QuaternaryQuadraticForms/Trusted/Weil.lean) |
| `EXT.KATZ` | [K], Published Theorem 8.1(1) and (5.3); directly inspected author-version Theorem 18(1), printed p.12, trace formula p.5; composite hypersurface interpretation uses EXT.HYPERSURFACE_CHERN | For prime p, nonzero homogeneous F,G in four variables over F_p of positive degrees m,n, assume the coefficient extension of F to the algebraic closure is irreducible and satisfies the nonvanishing-gradient condition, and the extended pair F,G satisfies the actual rank-two condition at every nonzero common geometric zero. For a nonprincipal multiplicative character psi with psi^n principal and any integer polynomial c satisfying coeff_j((1+m*T)*c)=coeff_j((1+T)^4) for j<=2, there exist r:Nat and lambda:Fin r->Complex such that (r:Int)=m*coeff_2(c*(1-n*T+n^2*T^2)), the actual projective hypersurface character sum equals sum lambda, and every lambda has norm p. This combines Katz spectral data with the general hypersurface adjunction and degree formulas; it contains no quadric specialization or scalar trace bound. | [`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data`](QuaternaryQuadraticForms/Trusted/Katz.lean) |
| `EXT.MV_GAUSS` | [MV], Theorems 9.5 and 9.7 | Quadratic Gauss-sum conjugation and norm identities, giving tau_p^2=chi_p(-1)p and tau_p^4=p^2 for odd p. | Pending |
| `EXT.MV_RAMANUJAN` | [MV], Theorem 4.1 | R_n(t)=sum_{a mod n, gcd(a,n)=1} e_n(a*t)=sum_{h\|gcd(n,t)} h*mu(n/h). | Pending |
| `EXT.MV_DIRICHLET_L` | [MV], Section 4.3 | Euler products for Re(s)>1 and continuity at s=1 for the nonprincipal Dirichlet-character L-series; the needed boundary convergence follows from bounded partial sums. | Pending |
| `EXT.LANG_ELIMINATION` | [La], Chapter IX, Theorems 3.2 and 4.1 | Finite universal elimination equations detecting a common nonzero geometric zero for the homogeneous systems used in Lemma4.1, uniformly under field specialization. | Pending |
| `EXT.HARTSHORNE_BERTINI` | [Ha], Chapter II, Theorem 8.18 | Dense open set of hyperplanes meeting each smooth projective curve component regularly over an algebraically closed field. | Pending |
| `EXT.POISSON_R4` | [HB and reputable analysis library], Poisson formula used in the proof of HB Theorem2; standard R4 lattice Poisson theorem | Schwartz/compactly supported smooth functions and affine-lattice scaling; exact signs and absolute convergence must be instantiated. Prefer the precise official mathlib theorem when available; otherwise register the exact cited Poisson input before use. | Pending |
| `EXT.MV_PNT_AP` | [MV], Corollary11.21 | Fixed-modulus prime-number theorem in arithmetic progressions, specialized to a lower bound in (z,2z] for p=1 mod r. | Pending |
| `EXT.LANG_CYCLOTOMIC` | [La], ChapterVI, Theorem3.1 | The phi(r) automorphisms of Q(zeta_r), indexed by reduced residues, with sigma_t(zeta_r)=zeta_r^t. | Pending |
| `EXT.SALBERGER_COUNT` | [S], Theorem0.6, second bound, d1=2,d2=r | Uniform count outside lines on a smooth complete intersection in P4: O_(r,epsilon)(B^(3/sqrt(2r)+epsilon)+B). | Pending |
| `EXT.SALBERGER_LINES` | [S], Published p1094, paragraph following Theorem0.6 | Number of geometric lines bounded in terms of the fixed degrees for these smooth complete intersections. | Pending |
| `EXT.IM_FULL_TRANSFORM` | [IM], Lemma4.3 | For the explicit good diagonal forms in Remark4.1, the full-space transform sum_x chi_p(G(x)) e_p(u.x) has absolute value at most p^2. | Pending |
| `EXT.HB_SQUARE_DETERMINANT` | [HB], Theorem7 | The untwisted count for square determinant has B^2 log B main term, B^2 secondary term and O(B^(3/2+epsilon)) remainder, under the source weight hypotheses. | Pending |
| `EXT.HSS_RESIDUE_ERROR` | [HSS], Theorem4.1 | Published per-residue-class upper error bound O(B^(2-tau+epsilon)/L), L^2=O(B^(1-tau)), -1<tau<1; comparison input, not the actual-error lower bound. | Pending |
| `EXT.HYPERSURFACE_CHERN` | [Fulton; Stacks Project], Fulton, Intersection Theory, 2nd ed., Examples 2.5.1-2.5.2 (p.42), 3.2.11-3.2.12 (pp.59-60); Stacks tags 0FMH, 01V4, 02UF, 00T1, 089X | For a smooth degree-m hypersurface X in P^3, c(T_X)=(1+L)^4/(1+mL) through degree two and integral_X L^2=m, over arbitrary fields. The standard homogeneous hypersurface/Jacobian interpretation identifies actual geometric irreducibility and rank predicates with the scheme hypotheses of Katz. | Component of [`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data`](QuaternaryQuadraticForms/Trusted/Katz.lean) (no separate premise declaration) |

## Registered premise inspection

### `EXT.WEIL`

[Exact source and correspondence review](certification/correspondence/weil_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `b0960f2d277d5160db6210e278adff703637d34f2bb29ee86470ddf64cba2f85`.

### `EXT.KATZ`

[Exact source and correspondence review](certification/correspondence/katz_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `0841ce91d4525dc10d64c991df75e176c85f1b67c77823926abf82cbf4d6a722`.

This is a composite interface with source components `EXT.KATZ`, `EXT.HYPERSURFACE_CHERN`. Their combined statement is one registered Lean premise. The correspondence review identifies the general geometric translations and formulas included in that statement.


## Cited claims excluded from the premise registry

The paper gives counterexamples to the following claims. They are comparison targets and must never be accepted as axioms of this certificate.

| Source | Reason |
|---|---|
| [IM], Lemma4.6 | Uniform O(p^(5/2)) for S_(p,p)(u) is explicitly refuted by Remark4.1; comparison target only. |
| [M], Lemma5.3 | Uniform O(p^(3/2)) for its S_(p,1)(u)=C_p(u) is explicitly refuted by Remark4.1. |
| [M], Lemma5.4 | Uniform O(p^(9/2)) for the ramified sum is explicitly refuted by Remark4.1. |
| [M], Proposition2.1 | Its B^2 q^(-3/2) leading bound is contradicted in the introduction by exact-order B^2/q examples; it is not an assumed input. |

Other citations used only for attribution, background, or a description of related work are not automatically Lean assumptions. In particular, the square/power-sieve references motivate the method; the manuscript's actual sieve inequality is a deduction to be proved.

The matrix geometry, polynomial calculations, and finite-product supporting exports use no external literature premises. The ledger records 7 exports with the exact Weil premise, for the univariate, projective-line, and plane-section bounds, and 8 with the general Katz surface premise, for Lemma 2.7 and the quadratic-trace bounds. Their actual axiom dependencies are inspected separately in the verification report.

The Katz premise explicitly combines its spectral theorem and trace formula with Fulton/Stacks general hypersurface geometry, adjunction, and degree formulas. The matrix-quadric geometry, the numerical coefficient 2n²−4n+4, and the final scalar norm estimate are proved internally. Every future input must likewise be listed separately from proved exports and appear explicitly in the inspected axiom dependencies.
