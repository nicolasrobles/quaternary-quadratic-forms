# Trusted literature inputs

The authors authorize source-relative certification: exact cited inputs used by the proofs are trusted and are not reproved. Their mathematical statements, hypotheses, source locators, and Lean declarations must be registered before use. All specializations, hypothesis checks, coefficient uniformity, and deductions made in this manuscript remain proof obligations.

**18 input groups are mapped; zero external premise declarations are currently registered in Lean.** Mapping an input is not the same as formalizing its interface. Use a suitable official mathlib result where available.

| Input | Source locator | Accepted mathematical scope | Lean interface |
|---|---|---|---|
| `EXT.HB_DELTA` | [HB], Theorem 1; Section 3, equation (3.3) | Delta-symbol identity, common smooth h, support and size, and c_Q=1+O_j(Q^-j); use the manuscript-safe range Q>=3. | Pending |
| `EXT.HB_WEIGHT_LOCALIZATION` | [HB], Sections 2 and 6; Lemmas 2 and 12 | Uniform small-support localization of a bounded smooth family with gradient bounded below; coordinate permutations/sign changes and membership in the admissible local weight class. | Pending |
| `EXT.HB_INTEGRAL_ESTIMATES` | [HB], Theorem 3; Lemmas 13, 14, 15, 18 and 22 | Singular integral normalization, zero-frequency approximation, derivative reduction and decay estimates for the local oscillatory integrals. | Pending |
| `EXT.WEIL` | [K or IK], K equation (1.2); alternatively IK Theorem 11.23 | Nonprincipal multiplicative-character estimate for a nonconstant polynomial not a constant multiple of the appropriate perfect power; instantiate the simple-root case. | Pending |
| `EXT.KATZ` | [K], Theorem 8.1(1), with trace identity (5.3) | Cohomological vanishing, Frobenius magnitude and Euler-characteristic/Chern expression under the precise smoothness/transversality and character hypotheses; scalar trace bound is deduced. | Pending |
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

## Cited claims excluded from the premise registry

The paper gives counterexamples to the following claims. They are comparison targets and must never be accepted as axioms of this certificate.

| Source | Reason |
|---|---|
| [IM], Lemma4.6 | Uniform O(p^(5/2)) for S_(p,p)(u) is explicitly refuted by Remark4.1; comparison target only. |
| [M], Lemma5.3 | Uniform O(p^(3/2)) for its S_(p,1)(u)=C_p(u) is explicitly refuted by Remark4.1. |
| [M], Lemma5.4 | Uniform O(p^(9/2)) for the ramified sum is explicitly refuted by Remark4.1. |
| [M], Proposition2.1 | Its B^2 q^(-3/2) leading bound is contradicted in the introduction by exact-order B^2/q examples; it is not an assumed input. |

Other citations used only for attribution, background, or a description of related work are not automatically Lean assumptions. In particular, the square/power-sieve references motivate the method; the manuscript's actual sieve inequality is a deduction to be proved.

The current Lean exports use no external literature premises. Future inputs must be listed separately from proved exports and appear explicitly in the inspected axiom dependencies.
