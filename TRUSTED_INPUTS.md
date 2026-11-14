# Trusted literature inputs

The authors authorize source-relative certification: exact cited inputs used by the proofs are trusted and are not reproved. Their mathematical statements, hypotheses, source locators, and Lean declarations must be registered before use. All specializations, hypothesis checks, coefficient uniformity, and deductions made in this manuscript remain proof obligations.

**20 input groups are mapped; 4 external premise declarations are currently registered in Lean.** Mapping an input is not the same as formalizing its interface. Use a suitable official mathlib result where available.

| Input | Source locator | Accepted mathematical scope | Lean interface |
|---|---|---|---|
| `EXT.HB_DELTA` | [HB], Theorem 1; Section 3, equation (3.3) | Delta-symbol identity, common smooth h, support and size, and c_Q=1+O_j(Q^-j); use the manuscript-safe range Q>=3. | Pending |
| `EXT.HB_WEIGHT_LOCALIZATION` | [HB], Sections 2 and 6; Lemmas 2 and 12 | Uniform small-support localization of a bounded smooth family with gradient bounded below; coordinate permutations/sign changes and membership in the admissible local weight class. | Pending |
| `EXT.HB_INTEGRAL_ESTIMATES` | [HB], Theorem 3; Lemmas 13, 14, 15, 18 and 22 | Singular integral normalization, zero-frequency approximation, derivative reduction and decay estimates for the local oscillatory integrals. | Pending |
| `EXT.WEIL` | [K], Published equation (1.2); matching multiplicative-character bound in Section 1, page 1 of the author version dated April 19, 2001 | For a prime p, a nonprincipal multiplicative character of F_p extended by zero, and a polynomial f of degree d>=1 with d distinct zeros in an algebraic closure, the norm of sum_{z in F_p} psi(f(z)) is at most (d-1)*sqrt(p). No condition p not dividing d is imposed. | [`QuaternaryQuadraticForms.Trusted.weil_simple_roots`](QuaternaryQuadraticForms/Trusted/Weil.lean) |
| `EXT.KATZ` | [K], Published Theorem 8.1(1) and (5.3); directly inspected author-version Theorem 18(1), printed p.12, trace formula p.5; composite hypersurface interpretation uses EXT.HYPERSURFACE_CHERN | For prime p, nonzero homogeneous F,G in four variables over F_p of positive degrees m,n, assume the coefficient extension of F to the algebraic closure is irreducible and satisfies the nonvanishing-gradient condition, and the extended pair F,G satisfies the actual rank-two condition at every nonzero common geometric zero. For a nonprincipal multiplicative character psi with psi^n principal and any integer polynomial c satisfying coeff_j((1+m*T)*c)=coeff_j((1+T)^4) for j<=2, there exist r:Nat and lambda:Fin r->Complex such that (r:Int)=m*coeff_2(c*(1-n*T+n^2*T^2)), the actual projective hypersurface character sum equals sum lambda, and every lambda has norm p. This combines Katz spectral data with the general hypersurface adjunction and degree formulas; it contains no quadric specialization or scalar trace bound. | [`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data`](QuaternaryQuadraticForms/Trusted/Katz.lean) |
| `EXT.MV_GAUSS` | [MV], Theorems 9.5 and 9.7 | Quadratic Gauss-sum conjugation and norm identities, giving tau_p^2=chi_p(-1)p and tau_p^4=p^2 for odd p. | Needed prime-field identities [proved using official mathlib](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean); no external premise declaration |
| `EXT.MV_RAMANUJAN` | [MV], Theorem 4.1 | R_n(t)=sum_{a mod n, gcd(a,n)=1} e_n(a*t)=sum_{h\|gcd(n,t)} h*mu(n/h). | Pending |
| `EXT.MV_DIRICHLET_L` | [MV], Section 4.3 | Euler products for Re(s)>1 and continuity at s=1 for the nonprincipal Dirichlet-character L-series; the needed boundary convergence follows from bounded partial sums. | Pending |
| `EXT.LANG_ELIMINATION` | [La: S. Lang, Algebra, revised third edition, GTM 211, Springer, 2002], Chapter IX, Theorem 4.1, printed p. 402; generic coefficient convention and Theorem 3.2, p. 390; projective and algebraic-closure conventions following Theorem 3.1, p. 389; zero-form and empty-output cases, pp. 404–405 | For any positive number N of variables and finite nonempty family of positive assigned degrees d_i, there exists a finite family R_j of integer polynomials in all generic homogeneous coefficients, chosen before the coefficient field and coefficient assignment. Over every field K and every coefficient assignment w, the actual forms homogeneousSystem N d w have a common nonzero zero over AlgebraicClosure K if and only if every R_j evaluates to zero in K. The output family may be empty and specialized input forms may be zero. No characteristic restriction or manuscript-specific bad-reduction, witness, finiteness, or height conclusion is included. | [`QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants`](QuaternaryQuadraticForms/Trusted/Elimination.lean) |
| `EXT.HARTSHORNE_BERTINI` | [Ha], Chapter II, Theorem 8.18 and proof, printed pp. 179-180; inspected book PDF pp. 194-195. The generic coordinate interpretation uses EXT.PROJECTIVE_JACOBIAN. Stacks Lemma 33.47.3, tag 0FD6, independently gives the smooth-scheme version. | For any algebraically closed field K, natural numbers N,c with c+2<=N, positive assigned degrees d_i and literal homogeneous polynomials P_i in N variables, assume that at every nonzero common zero x the matrix with rows the formal gradients of the P_i at x has rank c. Then there exists a nonzero vector u in K^N such that for every nonzero common zero x also satisfying u dot x=0 there is v in K^N with every gradient(P_i,x) dot v=0 and u dot v != 0. The geometric Jacobian, dimension and tangent interpretation is an explicit source component of this general coordinate Bertini interface. No rank increase, quadric specialization, finite-field rational hyperplane, elimination polynomial, or quantitative bound is asserted. | [`QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent`](QuaternaryQuadraticForms/Trusted/Bertini.lean) |
| `EXT.POISSON_R4` | [HB and reputable analysis library], Poisson formula used in the proof of HB Theorem2; standard R4 lattice Poisson theorem | Schwartz/compactly supported smooth functions and affine-lattice scaling; exact signs and absolute convergence must be instantiated. Prefer the precise official mathlib theorem when available; otherwise register the exact cited Poisson input before use. | Pending |
| `EXT.MV_PNT_AP` | [MV], Corollary11.21 | Fixed-modulus prime-number theorem in arithmetic progressions, specialized to a lower bound in (z,2z] for p=1 mod r. | Pending |
| `EXT.LANG_CYCLOTOMIC` | [La], ChapterVI, Theorem3.1 | The phi(r) automorphisms of Q(zeta_r), indexed by reduced residues, with sigma_t(zeta_r)=zeta_r^t. | Pending |
| `EXT.SALBERGER_COUNT` | [S], Theorem0.6, second bound, d1=2,d2=r | Uniform count outside lines on a smooth complete intersection in P4: O_(r,epsilon)(B^(3/sqrt(2r)+epsilon)+B). | Pending |
| `EXT.SALBERGER_LINES` | [S], Published p1094, paragraph following Theorem0.6 | Number of geometric lines bounded in terms of the fixed degrees for these smooth complete intersections. | Pending |
| `EXT.IM_FULL_TRANSFORM` | [IM], Lemma4.3 | For the explicit good diagonal forms in Remark4.1, the full-space transform sum_x chi_p(G(x)) e_p(u.x) has absolute value at most p^2. | Pending |
| `EXT.HB_SQUARE_DETERMINANT` | [HB], Theorem7 | The untwisted count for square determinant has B^2 log B main term, B^2 secondary term and O(B^(3/2+epsilon)) remainder, under the source weight hypotheses. | Pending |
| `EXT.HSS_RESIDUE_ERROR` | [HSS], Theorem4.1 | Published per-residue-class upper error bound O(B^(2-tau+epsilon)/L), L^2=O(B^(1-tau)), -1<tau<1; comparison input, not the actual-error lower bound. | Pending |
| `EXT.HYPERSURFACE_CHERN` | [Fulton; Stacks Project], Fulton, Intersection Theory, 2nd ed., Examples 2.5.1-2.5.2 (p.42), 3.2.11-3.2.12 (pp.59-60); Stacks tags 0FMH, 01V4, 02UF, 00T1, 089X | For a smooth degree-m hypersurface X in P^3, c(T_X)=(1+L)^4/(1+mL) through degree two and integral_X L^2=m, over arbitrary fields. The standard homogeneous hypersurface/Jacobian interpretation identifies actual geometric irreducibility and rank predicates with the scheme hypotheses of Katz. | Component of [`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data`](QuaternaryQuadraticForms/Trusted/Katz.lean) (no separate premise declaration) |
| `EXT.PROJECTIVE_JACOBIAN` | [Hartshorne; Stacks Project], Hartshorne II.8.18 proof, p.180; Stacks Definition 10.137.5 (00T6), Lemma 10.137.6 (00T7), Theorem 10.34.1 (00FV), Lemmas 10.140.1 (00TR), 10.140.5 (00TV), 10.106.3 (00NQ), 28.9.4 (02IR), and 28.7.6 (033M). | For any finite homogeneous system in N variables over an algebraically closed field, full rank c of the Jacobian at every nonzero common zero gives a smooth projective closed subscheme locally of dimension N-1-c. Its cone tangent is the common kernel of the formal gradients, its projective tangent is the quotient by the radial line, and a proper regular hyperplane section has nonzero differential on that tangent. The smooth projective scheme has finitely many disjoint smooth integral components. Empty loci are handled vacuously. No characteristic restriction or divisibility hypothesis on the degrees is imposed. | Component of [`QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent`](QuaternaryQuadraticForms/Trusted/Bertini.lean) (no separate premise declaration) |

## Registered premise inspection

### `EXT.WEIL`

[Exact source and correspondence review](certification/correspondence/weil_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `b0960f2d277d5160db6210e278adff703637d34f2bb29ee86470ddf64cba2f85`.

### `EXT.KATZ`

[Exact source and correspondence review](certification/correspondence/katz_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `0841ce91d4525dc10d64c991df75e176c85f1b67c77823926abf82cbf4d6a722`.

This is a composite interface with source components `EXT.KATZ`, `EXT.HYPERSURFACE_CHERN`. Their combined statement is one registered Lean premise. The correspondence review identifies the general geometric translations and formulas included in that statement.

### `EXT.LANG_ELIMINATION`

[Exact source and correspondence review](certification/correspondence/elimination_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `5b055036c52e02383dce3540c86432f6756ed153d264cc1e3667088f45199c10`.

### `EXT.HARTSHORNE_BERTINI`

[Exact source and correspondence review](certification/correspondence/bertini_input.md). The verifier checks the declaration kind, inspected Lean type, type hash, and actual axiom dependencies separately from proved exports.

Expected type hash: `dd54ac5f90f102a6351991ddeda32af07e27a39aef27950f7b8ac390f60b92e2`.

This is a composite interface with source components `EXT.HARTSHORNE_BERTINI`, `EXT.PROJECTIVE_JACOBIAN`. Their combined statement is one registered Lean premise. The correspondence review identifies the general geometric translations and formulas included in that statement.


## Cited claims excluded from the premise registry

The paper gives counterexamples to the following claims. They are comparison targets and must never be accepted as axioms of this certificate.

| Source | Reason |
|---|---|
| [IM], Lemma4.6 | Uniform O(p^(5/2)) for S_(p,p)(u) is explicitly refuted by Remark4.1; comparison target only. |
| [M], Lemma5.3 | Uniform O(p^(3/2)) for its S_(p,1)(u)=C_p(u) is explicitly refuted by Remark4.1. |
| [M], Lemma5.4 | Uniform O(p^(9/2)) for the ramified sum is explicitly refuted by Remark4.1. |
| [M], Proposition2.1 | Its B^2 q^(-3/2) leading bound is contradicted in the introduction by exact-order B^2/q examples; it is not an assumed input. |

Other citations used only for attribution, background, or a description of related work are not automatically Lean assumptions. In particular, the square/power-sieve references motivate the method; the manuscript's actual sieve inequality is a deduction to be proved.

## Dependencies of proved exports

The matrix geometry, ordered gradient minors, homogeneous coefficient reconstruction, coefficient specialization, polynomial-height estimates, finite-product arithmetic, prime-field Gauss calculations, exact diagonal pencil evaluations, composite weights, scaled CRT, complete-sum factorizations, general matrix Gauss evaluations, prime-power residue recurrences, quadric point counts, uniform norm bounds, actual residue kernels, determinant-index comparisons, weighted stationary expansions, adjugate weight extraction, and shared-prime complete-sum evaluations use only the standard logical foundations. The ledger records 18 exports with the exact Weil premise, 16 with the general Katz surface premise, 20 with the Lang resultant premise, and 4 with the general composite Bertini premise. These counts overlap when an export uses more than one premise. The following table groups exports by their exact recorded allowance; actual axiom dependencies are inspected separately in the verification report.

| Permitted literature premises | Proved exports |
|---|---:|
| None (standard logical foundations only) | 524 |
| Bertini with general projective geometry | 1 |
| Katz with general hypersurface geometry | 10 |
| Lang | 14 |
| Weil | 14 |
| Bertini with general projective geometry; Lang | 2 |
| Katz with general hypersurface geometry; Lang | 2 |
| Katz with general hypersurface geometry; Weil | 2 |
| Katz with general hypersurface geometry; Lang; Weil | 1 |
| Bertini with general projective geometry; Katz with general hypersurface geometry; Lang; Weil | 1 |

Lemma 4.1(i) uses Lang's general homogeneous resultant family. Its specialization to the actual F, G and gradient minors, the nonzero integer witness, finiteness of the literal bad-prime set, and the coefficient-height bound are proved internally. The complete Lemma 5.9 uses both Lang and Katz: Lang supplies the finiteness deduction needed to form the literal N_G, while Katz supplies the projective trace bound. The trace's integrality and divisibility are proved without either literature premise.

Lemma 4.1(ii) combines Lang with the general composite Bertini interface. Hartshorne's theorem and the explicitly attributed projective Jacobian and tangent-space facts supply a transverse tangent direction for a general homogeneous system over an algebraically closed field. The rank-three consequence, actual second elimination system, coefficient specialization, descent of polynomial nonvanishing, and construction D_p = F* R_j(G,·) with a uniform degree bound are internal proofs. No rational transverse plane over the prime field is assumed.

The complete uniform Fourier theorem in Lemma 4.4 uses all four existing premises through the checked results above. The given-polynomial integral theorem uses Weil, Katz and Lang; the prime-field estimate uses Weil and Katz. The exceptional section count, including tangent and singular sections, is proved with the official mathlib Schwartz–Zippel theorem and the actual projective-ray decomposition, with no external premise. The constant comparisons and assembly of the indicator bound are internal deductions. No new literature declaration is introduced.

The complete diagonal bad-prime lemma, Lemma 4.5, uses none of the registered literature premises. The actual gradient-minor calculation, geometric singular witness, coefficient reduction, direct finiteness from M and exact radical product are proved using standard logical foundations and proved library results.

The complete diagonal pencil lemma, Lemma 4.6, retains every regular and singular member of the actual Fourier sum. Its Gauss identities, reciprocal phases, Ramanujan factors and exact integer projective trace are proved internally with official mathlib results and no registered literature premise. The generic bound uses only the existing affine Weil premise in the separable cubic case. A nonseparable cubic is factored over the perfect prime field, and its character sum is evaluated exactly, so no separability assumption survives in the final bound. Those one-dimensional Gauss identities provide a proved ingredient for the full prime-power Lemma 3.2 described below.

The complete CRT lemma, Lemma 3.1, uses none of the registered literature premises. Its actual prime-product weights, good-prime source-domain extension, representative independence, scaled residue and unit bijections, exact mixed phases, and frequency invariance are proved internally. Only invariance at primes dividing q is used; (q,N)=1 makes each factor one of the supplied good-prime functions. The direct C_q and S_c factorization corollaries and the prime polynomial-character Fourier bridge likewise use only standard logical foundations. No coprimality between q and c within a CRT block is imposed, and modulus-one cases are retained.

The full prime-power Gauss lemma, Lemma 3.2, likewise uses none of the registered literature premises. An actual orthogonal basis diagonalizes the source's symmetric matrix over the prime field, and the change-of-basis determinant square is proved harmless under the quadratic character. Actual residue-digit bijections and additive orthogonality prove the recurrence at powers of p. Adjugate square completion uses the exact inverse phase; the good-prime condition N_F=2|det A| supplies the required units. The Ramanujan conclusion reindexes the actual unit group, and the projective count follows from the actual affine zero set and projective rays. All intermediate constant-Gauss hypotheses are discharged in the final source theorem. The pure modulus-one base and the k≥1 requirement when lifting a prime-power unit to an integer coprime to p are kept separate. No fifth literature premise is introduced.

The uniform complete-sum estimate in Lemma 3.3 uses none of the registered literature premises. The squared-norm identity and additive orthogonality concern the actual sum at every positive modulus. The residue-kernel bound uses the actual integer range, surjective coordinate reduction, finite-endomorphism index, and mathlib's proved Smith-normal-form determinant-index theorem. Its new public kernel endpoint is the determinant bound; no separate exact gcd-product kernel formula is claimed. Doubling the source matrix gives the factor sixteen, and the checked nonnegative square-root calculation gives the constant four. The triangle inequality is applied to the existing complete sum over actual unit parameters. All inner-bound hypotheses are discharged from symmetry and integer nonsingularity in the final source theorem, including at modulus one and every bad prime. The 17 new exports have exactly the three standard logical axioms; no literature input is added or used.

The full shared-prime identity in Lemma 3.4 uses none of the registered literature premises. Its actual weighted Gauss and unit sums, residue-digit phase calculation, stationary orthogonality, and adjugate multiplication are internal proofs. The equality adj(A)u=−(2a det A)y modulo p uses a proved nonzero scalar, so the original weight invariance supplies the constant weight on every surviving term. The completed Lemma 3.2 then evaluates the remaining sum. The actual unit-digit bijection proves 𝒰_{k+1}=p 𝒮_{p,p^k} with the literal cone divisibility condition; cancelling the nonzero p gives the exponent 2k+1. The source radical hypothesis rad(N_F)∣N is used exactly, with det A≠0 ensuring N_F is nonzero. The supplied-prime family extension is proved equal to the original local weight on the right. Every k≥1 and integral frequency is included. The weight's zero value, norm and Fourier stratification bounds, and the global nonsquare assumption are unnecessary. All 18 new exports have exactly the three standard logical axioms. No stationary-phase, weighted-factor, or unit-lift conclusion is left as a premise in the final source theorem.

The Katz premise explicitly combines its spectral theorem and trace formula with Fulton/Stacks general hypersurface geometry, adjunction, and degree formulas. The matrix-quadric geometry, the numerical coefficient 2n²−4n+4, and the final scalar norm estimate are proved internally. Every future input must likewise be listed separately from proved exports and appear explicitly in the inspected axiom dependencies.
