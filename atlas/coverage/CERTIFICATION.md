# What each mapped kernel covers, and what it does not

Generated from `coverage.json` by `scripts/build_certification.py`. 122 of 207 cards carry a mapped kernel: 80 with a kernel in this repository, 42 only in a companion repository.

Every card keeps `full_card_certified: false`, and the validator requires that: a kernel proves the finite statement it names under its written hypotheses, not the card's physical reading, measured exponent or genericity claim. The table states, per card, what is proved and what is not.

How far a finite proof can carry a card depends on its source grade:

- **theorem** — A displayed statement the card presents as proved. A finite kernel can come close to complete.
- **derived** — A consequence the card draws from a cited result. The citation stays an input.
- **measured** — A number or exponent read off data or a simulation. No Lean statement can certify the measurement; only the algebra behind it is formalisable.
- **conjecture** — An open claim. Only the established sub-claims can be formalised.
- **reading** — An interpretation, not a mathematical assertion. Not certifiable in any form.
## Cards with a kernel in this repository

| Card | Grade | Kernels | What is proved, and what is not |
| :--- | :--- | :---: | :--- |
| B1 | theorem | 13 | Card-normalised Lagrange identity: 4 det g = Ω² in two real parameters, the Gram entries, and |Ω| = 2√(det g); the general-rank Cauchy–Schwarz inequality in higher dimension is a separate argument. |
| B2 | theorem | 4 | Exact finite real-matrix commutator identity and normality equivalence. |
| B6 | theorem | 1 | Scalar binary-entropy properties; the free-fermion entropy construction and spectrum-to-channel interpretation are not proved here. |
| B13 | measured | 13 | Half-angle monodromy of H = [[0,1],[z,0]]: λ² = z, the exhaustiveness and distinctness of ±λ, one loop swaps the pair and two restore it, while the matrix family is already 2π-periodic; winding numbers and the discriminant integral are not formalised. |
| B15 | measured | 5 | Refutation: the raw log-det comparator is not globally subadditive (explicit equal-step witness), with the √S reading left open. **refuted**: The global subadditivity S(a∪b) ≤ S(a)+S(b) is false for the raw log-det comparator S(A,B) = log det((A+B)/2) − ½log det A − ½log det B: S(1,4) = log(5/4) = 0.2231 exceeds S(1,2)+S(2,4) = log(9/8) = 0.1178, and the two steps have equal cost so the failure is not a subdivision artefact. The √S metric reading, which the archived HTML and the ledger spell differently, is not addressed. |
| B16 | theorem | 5 | Rank-one projector-distance identity for real unit vectors in dimension two; no general packing theorem. |
| B18 | theorem | 4 | n ≤ log C₀/log(1/a) from 1 ≤ C₀ aⁿ, with the equality case C₀ aⁿ = 1; support sets, δ-nets and the trackability threshold are not formalised. |
| B20 | theorem | 13 | For the Fisher matrix F(D,σ) = Σ_k conj(D_ki)D_kj/σ_k², uniform precision scaling gives F(D,sσ) = s^{−2}F and leaves every inverse-Fisher correlation fixed; non-uniform precision does move them (ρ = −4/5 at (1,1), unchanged at (1,1)/50, but −319/481 at (5,12)). |
| B21 | conjecture | 1 | V² + P² + E² = 1 for every normalized two-qubit pure state with E the pure-state concurrence; the card's naming of E as the census and the rank-15/20 measurement are not formalised. |
| B24 | measured | 17 | For a Hermitian 2×2 perturbation: f′(0) = a/A + d/B and ½f″(0) = −½Tr(RERE) = −½(a²/A² + d²/B² + 2|b|²/(AB)), so the two displayed c₂ forms agree. They disagree for non-Hermitian E (H = I, E = [[0,1],[0,0]]: true c₂ = 0, modulus sum 1), and positivity of H + η is needed for any finite expansion. **missing-hypothesis**: The equality of the two displayed c₂ forms needs E Hermitian: with H = I, η = 0, E = [[0,1],[0,0]] the true c₂ vanishes (E² = 0) while the modulus-squared sum is 1. Separately, positivity of H + η is needed for any finite expansion: H = diag(0,1), η = 0, E = I gives log det = log(ε(1+ε)) → −∞. **provenance**: The local atlas/cards/html/B24.html has SHA 1f06fe... while coverage.json pins 3f9377...; the audited claims were checked against the official v7 card, whose hash matches. Separately, the unconditional trace identities use totalised division at a zero eigenvalue, so nondegeneracy should be stated rather than inherited from Lean's x/0 = 0. |
| B25 | theorem | 13 | The ordered susceptibility sum χ = Σ_{m≠n}|A_nm|²/γ_nm² is conjugation-fixed, real, nonnegative without Hermiticity, and strictly positive on a contributing nondegenerate term; the two-level case gives χ = 2/δ². Degenerate labels with a zero gap give x/0 = 0 in Lean, which is not the physical value, so the formula needs non-degeneracy. **clarification**: The susceptibility formula needs a nonzero gap for a contributing term. With degenerate labels and a zero gap, Lean's x/0 = 0 makes the sum vanish; that is not the physical limit, as the file states, so the corrected hypothesis is E_n ≠ E_m on contributing terms. |
| B26 | theorem | 6 | The Jordan block has charpoly (X−λ)², is not diagonalizable and not normal, while λI has the same coalesced charpoly and is diagonalizable; the κ√δ asymptotics are not formalised. |
| B31 | theorem | 16 | Trace and vanishing equivalence for idempotents; Frobenius norm identity is not in these declarations. |
| B32 | theorem | 10 | Coordinate Lagrange identity in the displayed normalization; geometric two-band identification is additional. |
| B37 | theorem | 7 | A finite rank makes the singular-value sum finite, with Σσᵢ² = Re tr(T*T) and the matrix Gram form; the continuum trace-class statement is not formalised. |
| B39 | theorem | 3 | Critical-angle inequality and complex trigonometric identities; no derivation of a physical transmission model. |
| B44 | theorem | 32 | finrank 5 for the symmetric traceless 3×3 sector and the lift bound ‖exp(tS)‖ ≤ ‖exp(tT)‖ for an isometric intertwining; the card's minimality clause and its squared form are not formalised. **ledger-error**: coverage.json (and the batch brief) carried the squared form max_t‖e^{tA}‖ ≥ max_t‖e^{tJ}‖²; the current card HTML displays the unsquared G(H) ≥ G(block). The squared form is false even for a surjective isometric embedding: J = A = [[−1/2,1],[0,−1/2]] in the max norm has M = 2e^{−1/2} > 1, so max_A = M < M². The unsquared lift is proved. |
| B46 | theorem | 6 | (Π + hV)² − (Π + hV) = h²V² for V tangent to the idempotents, over any commutative ring; the unrestricted linear term is h(ΠV + VΠ − V), so tangency is exactly what removes it. A 2×2 witness shows the identity fails without tangency. **provenance**: The archived card HTML read for B46 (SHA b1e69c…) displays Ẇ = Π_TGr(Ẇ) + δ, while coverage.json pins 3626f1…, so the local 93-card edition and the Zenodo v7 card are different documents. The ledger's B46 claim text therefore does not describe the local file; the Lean kernel follows the ledger's formula. |
| B48 | derived | 9 | General invertible-block determinant identity; identification of the paper interface with these blocks is additional. |
| B51 | theorem | 4 | Quartic reduction and both directions of the unit-circle coordinate correspondence; not the knot census/classification. |
| B54 | measured | 10 | det g < 0 with |Ω|² ≥ 0 forces 4 det g < |Ω|² and excludes positive definiteness; det g > 0 does not certify a metric (−I₂), and the flat path separates the three regimes. **overreach**: det g > 0 does not certify that the form is still a metric: −I₂ has determinant 1 and is negative definite. The universal reading of the first clause ('det g > 0 ⇒ |Ω|² overruns') is false, e.g. g = I₂, |Ω|² = 0. The second clause is true as stated: det g < 0 with |Ω|² ≥ 0 gives 4 det g < |Ω|² and excludes positive definiteness. |
| B56 | theorem | 1 | Corrected rank obstruction R^2 to R^3 only. The published headline that a curve and point do not meet is not certified. |
| B57 | theorem | 7 | Nonzero null vector in x^2-y^2; not construction of a moving biorthogonal projector. |
| B60 | theorem | 13 | Only the arithmetic implication k*q=1 => k=q=1; not the full saturation/equality characterization. |
| B61 | theorem | 4 | Inverse mass algebra under nonzero constants; no empirical mass-running/cosmological prediction. |
| B64 | theorem | 2 | Ring commutator identity only; normalized rank-one angle/stress identifications require separate proofs. |
| B66 | theorem | 4 | Exact Gram determinant square; covering-space and branching claims require additional topology. |
| B68 | theorem | 2 | Nonzero opposite-eigenvalue partner under an anticommuting involution; not a derivation of every index/signature/winding claim. |
| B72 | theorem | 29 | The projector derivative is the off-block resolvent: Hermitian response, ΠR+RΠ=R, the Sylvester equation, exact 1/|gap| singular scaling, diagonal blocks as the kernel and ‖R‖_F ≤ ‖H‖_F/gap. |
| B74 | theorem | 6 | Conditional scalar turning inequality; conservation law and geometric applicability must be supplied. |
| B75 | theorem | 3 | Signs of ordered-spectrum terms under explicit weight/sign hypotheses; opposite signs alone do not imply exact cancellation, and the Euler growth-rate claim is separate. |
| B78 | theorem | 15 | Spectral/Lagrange calculus for diagonalizable matrices: projectors idempotent, orthogonal and summing to I, every function realised by its Lagrange polynomial at distinct eigenvalues; the contour integral is not formalised. |
| B85 | theorem | 4 | Exact negative-square determinant and nonpositivity; covers the displayed algebraic kernel. |
| B86 | theorem | 29 | The diagonal witness of the reciprocity identity: B = diag(t/g) symmetric, det B = ∏t/∏g and det B = 0 ⇔ some tᵢ = 0, with a non-symmetric 2×2 witness; ‖B‖ = max tᵢ/gᵢ and the det g ≤ 0 consequence are not formalised. **ledger-error**: Three readings of B86's determinant clause disagree: the ledger says det g ≤ 0 for symmetric probes, the archived HTML prose says det g ≡ 0. Arbitrary real symmetry does not give the inequality (G = I₂ beside a regular reciprocity witness), the generic det ≡ 0 is false, and the true content for the intended bilinear form Re(uuᵀ) is det = −Im(conj(u₁)u₂)² ≤ 0, zero exactly at real parallelism — so the non-positivity comes from the bilinear structure, not from reciprocity. The norm clause ‖B‖ = max tᵢ/gᵢ also needs tᵢ ≥ 0. |
| B87 | theorem | 15 | SO(2) equivariance kills the linear coupling while Z₃ allows the Jahn–Teller term; conical gap 2r and protected gap sin²ϑ; the card's holonomy half is not formalised. |
| B89 | theorem | 12 | tr(AB) = 0 for symmetric A and antisymmetric B, so the response is tr(A²) + b²tr(BᵀB): no linear term, and the first visible one is quadratic. |
| B90 | theorem | 3 | Exact selected normal forms only; not genericity, integrated-distance exponents, physical clock or openness classification. |
| B91 | theorem | 17 | Q = g − (i/2)Ω has det Q = det g − |Ω|²/4. The card's criterion Q ⪰ 0 ⟺ g₁₁ ≥ 0 ∧ 4 det g ≥ |Ω|² fails at g₁₁ = 0, where the determinant condition carries no information about g₂₂; adding 0 ≤ d (equivalently 0 ≤ a + d) repairs it, and under a > 0 the card's criterion is exact. The literal wall ⊂ {det g > 0} also fails on zero data. **missing-hypothesis**: The displayed criterion Q ⪰ 0 ⟺ g₁₁ ≥ 0 ∧ 4 det g ≥ |Ω|² fails at g₁₁ = 0: with (a,b,d,w) = (0,0,−1,0) both displayed conditions hold and Q = diag(0,−1) is not positive semidefinite. The repair is 0 ≤ d (equivalently 0 ≤ a + d); under a > 0 the card's criterion is exact. The literal wall ⊂ {det g > 0} also fails on zero data. |
| B92 | theorem | 4 | w = (1/2π)Σ arg λ ∈ ℤ when det R = 1, and det = exp Tr log in diagonal normal form. |
| B100 | theorem | 17 | |r|² > |a|² ⇔ |x − x_c| > |x_c| for r = (a+x)/(1+ax), A = 1−|a|⁴, C = ā(1−a²), x_c = −C̄/A. |
| B105 | theorem | 2 | (x⋆y)⋆z − x⋆(y⋆z) = P[xQ(yz) − Q(xy)z] for an additive idempotent P, with a nonzero defect. |
| B109 | theorem | 15 | With ρ = P/k, L = 2Ṗ and tangency VP + PV = V: the SLD equation holds, Tr(V²) = 2Tr(PV²), F_Q = 4g/k and Bures² = g/k under ds_B² = F_Q ds²/4; the rank-one witness gives g = 1, F_Q = 4, Bures² = 1. |
| B112 | theorem | 14 | The entrywise Sylvester equation has a solution exactly when the kernel–kernel block of V vanishes; the solution is the quotient off the zero sums and an arbitrary block remains there. **clarification**: 'pᵢ = pⱼ = 0 ⇒ Vᵢⱼ must vanish' is a compatibility condition, not an automaticity claim: with p ≥ 0, existence of L is *equivalent* to it, the solution is the quotient off the zero sums, and an arbitrary block remains on the kernel–kernel pairs. The witness p = 0, V = 1 shows it cannot be dropped. |
| B114 | theorem | 3 | First-nonzero-jet tangency: if P⁽¹⁾…P⁽ᵐ⁻¹⁾ vanish then P⁽ᵐ⁾ is tangent, for a curve in a real normed algebra; m > 0 is essential and is exhibited by the constant path at 1. **clarification**: The displayed jet identity needs m > 0: at m = 0 it would read P = P² + P², which fails for the constant path at 1. For m ≥ 1 it is exact, and the C^(m+1) hypothesis can be weakened to C^m. |
| B116 | theorem | 15 | ‖P_σ − P_τ‖²_F = 2·|support(σ⁻¹τ)|, vanishing iff σ = τ. |
| B119 | theorem | 16 | Γ_{xx,y} = g_{xy,x} − ½g_{xx,y}, so the displayed −½∂_y g_xx is the Killing specialization; pointwise vanishing of g_xy is insufficient and the raised-index coefficient differs. **missing-hypothesis**: The transverse coefficient −½∂_y g_xx is the *Killing* specialization of Γ_{xx,y} = g_{xy,x} − ½g_{xx,y}, not the general symbol: pointwise vanishing of g_xy is insufficient (g = [[1,xy],[xy,2]] at (0,1) has g_xy = 0 and coefficient 1, not 0), so ∂_x g_{xy} = 0 is essential. The raised-index coefficient differs as well (−9/8 first kind against −9/32 when g_yy = 4). |
| B122 | theorem | 34 | ‖e^{−bt}(I−μtN)‖ = e^{−bt}(√(4+μ²t²)+|μt|)/2 in the L2 operator norm (both bounds), with A′ = −AJ and uniqueness of the global solution. |
| B128 | theorem | 14 | δ + g² ≤ 4 for a nonempty finite unit-modulus spectrum, δ the mean |λ−1|² and g² the minimum |λ+1|², with equality at the single eigenvalue 1. |
| B129 | theorem | 14 | D² + V² = 1 and det [[1,v],[v̄,1]] = 1−|v|² = D², with the equal-prior scaled coherence and a Lean counterexample to the unscaled convention. |
| B131 | theorem | 21 | B/β(a) ≤ g ≤ F^{1/4}(B/2)^{3/4} for g = Σw/t², F = Σtw, the divided difference B and β(a) = 2a³/((a²−y₁)(a²−y₂)). |
| B132 | theorem | 8 | The identifiability dichotomy holds for symmetric F; without symmetry the antisymmetric part is invisible to every symmetric probe and the 'otherwise' branch is empty. **refuted**: The 'otherwise' clause fails without F symmetric: with one zero probe u = 0 and F = [[0,1],[−1,0]], F is outside span{uᵢuᵢᵀ} and every reading vanishes, yet Tr(HF) = 0 for every symmetric H, so the invisible detecting H cannot exist. The antisymmetric part of F is invisible to every symmetric probe. With F = Fᵀ the dichotomy is proved in both directions. |
| B133 | theorem | 30 | C − C² = BBᵀ from idempotence, the equality of the occupation and squared-singular-value censuses, and N_ε ≤ ‖B‖²_F/(ε(1−ε)). |
| B138 | theorem | 18 | Join edges of Cₙ[K_r] form a triangle-free subgraph with nr² edges against the two-planar triangle-free budget 4N−8, giving Θ ≥ 3 for n,r ≥ 4 (conditional on the planar bound, which Mathlib lacks). |
| B142 | theorem | 6 | Γ(H,K) = −½(HG⁻¹K + KG⁻¹H) with g(Γ(H,K),L) = ½C(G;H,K,L), and C = −2tr(G⁻¹HG⁻¹KG⁻¹L) for symmetric data. |
| B144 | theorem | 7 | The glued block resolvent obeys ‖(z−H_{A∪B})⁻¹‖ ≤ 2K/δ for Re z ≥ δ from ‖(z−H_X)⁻¹‖ ≤ K/δ and ‖C‖ ≤ δ/(2K), by the D−E/Neumann argument with no seam-square hypothesis; the constant 2 is sharp at r = q = 1/2. |
| B145 | theorem | 18 | The pseudospectrum of the Jordan block is exactly the open disk |z−b| < √(ε|μ|+ε²), with the resolvent norm (|μ|+√(|μ|²+4|w|²))/(2|w|²), the boundary excluded and the normal case μ = 0 reduced to the ε-ball. |
| B148 | theorem | 21 | The tensor-product composition 1 − S(u⊗u′, v⊗v′) = (1−S(u,v))(1−S(u′,v′)), with a Lean counterexample to the naive product law for misses. **clarification**: Miss probabilities do not multiply: the composition law is q_A + q_B − q_A q_B, with a Lean counterexample (3/4 ≠ 1/4 at q = 1/2). What multiplies is the *stress* 1 − S under the tensor product. |
| B152 | theorem | 13 | U C U† = I − C with U unitary forces det(I−C) = det C, hence τ = log det(I−C) − log det C = 0; the transpose variant gives the same. Hermiticity and 0 < C < I are not needed for the cancellation. Dropping unitarity is refuted by U = [2], C = [1/5], where the relation holds but τ = log 4 ≠ 0. **clarification**: The offset theorem is proved faithfully, but the card's spectral nu -> 1 - nu and offset eps -> -eps clauses are neither formalised nor listed among the report's omissions. |
| B154 | theorem | 5 | A single β is equivalent to K_A − βh_A being a scalar on traceless Hermitian directions, provided K is Hermitian; the antisymmetric witness shows the hypothesis cannot be dropped. **missing-hypothesis**: The equivalence 'Tr(K_A δC) = βTr(h_A δC) for all traceless Hermitian δC ⟺ K_A − βh_A = λI' needs K Hermitian. With K = [[0,1],[−1,0]], h = 0, β = 1 every symmetric C is invisible to K (an antisymmetric matrix never pairs with a symmetric one) yet K is not a scalar. The card supplies the hypothesis only through the word 'Hamiltonian'. |
| B155 | theorem | 23 | The shape Gram matrix is diag(cos²ϑ, 1), charpoly (X−cos²ϑ)(X−1), gap sin²ϑ, with a counterexample to the generic two-unit-vector reading. **ledger-error**: The generic two-unit-vector reading of the Gram matrix is false: for unit vectors with inner product cos ϑ the Gram determinant is sin²ϑ and the characteristic roots are 1 ± cos ϑ. The card's diag(cos²ϑ, 1) is specific to its own shape-sphere parametrisation dΦ(eϑ) = (cosϑcosφ, cosϑsinφ), dΦ(eφ) = (−sinφ, cosφ). |
| B158 | theorem | 16 | p₀|A_w|² ≤ Re⟨i|A(A i)⟩ = ‖Ai‖² under Hermiticity and normalisation — an independent local re-proof of the theorem already mapped to dirac-time-lean. |
| B171 | theorem | 39 | g_W(W,H) = ¼Tr H, the compression A(H) = D_T(H) − 2Tr(TH)W on trace-zero tangents, self-adjointness of P_W, D_T, Q_W and A in the displayed pairing, and the hidden block is line-valued — rank at most one, and zero at uniform weights with T = I. **overreach**: The hidden block P_W D_T² P_W − A² is line-valued, hence of rank at most one, not rank one: hidden(H) = Tr(D_T(P_W(H)))·C^ad(W). At uniform weights with T = I the trace factor vanishes identically and the block is zero, so the card's 'rank one because Q_W = I − P_W does' is an overstatement. |
| B173 | theorem | 30 | n(z) = (1−z², i(1+z²), −2z) is isotropic, n·n = 0; ψ_Q = nᵀQn depends only on the traceless part (ψ_{Q+tI} = ψ_Q); the coefficient map between the five traceless parameters and the binary quartic is invertible with determinant 3072, and the canonical examples realise Q² = 0 ≠ Q, Q³ = 0 ≠ Q² and the non-squarefree case. |
| B177 | theorem | 22 | With L² = r²/(r−3), V″/2 = (r−6)/(r³(r−3)) exactly (q(7) = 1/1372, q(5) = −1/250), ω_r²/Ω² = 1 − 6/r, and the wobble is a nonzero nilpotent exactly at r = 6. Substituting the constraint before differentiating gives the wrong value 1/162 at r = 6; the card differentiates first and is right. |
| B179 | reading | 14 | The fold normal form as a coordinate change: X = λ² gives dX²/(4c²X) = dλ²/c² for c ≠ 0, λ ≠ 0, with both card specializations; λ ↦ −λ is an isometry of the regular form and the integrated distance. The raw quotient fails at λ = 0 (the horizon), where the regular extension gives the correct value. **clarification**: The raw quotient dX²/(4c²X) needs λ ≠ 0; at λ = 0 (the horizon X = 0) it gives 0 rather than the limiting 1, which the regular extension supplies. The card's two expressions agree except at that single point. **clarification**: The integrated-distance statement needs c != 0 as well as lambda != 0; the metric identity carries both and the file states them, but the distance wording is positive only under that hypothesis. |
| B180 | theorem | 8 | F_Q = 4g(Ġ,Ġ) = 8K for fixed-spectrum purely-angular qutrit motion, with an explicit trace-one example. |
| B181 | measured | 11 | For V(σ) = f(σ²): V_σ(0) = 0 and V_σσ(0) = 2V_w(0), with the square inverse-distance potential giving U(0) = −4√2−2 and U_w(0) = 2√2−1. The displayed 1.912290 is a six-place rounding: the file proves 1.912290 < √(2(2√2−1)) < 1.9122905. **rounding**: The displayed ω = 1.912290 is a six-place rounding of √(2(2√2−1)) = 1.912290315…; the file proves 1.912290 < √(2(2√2−1)) < 1.9122905 so the final equality cannot be read as exact. **clarification**: The file's summary sentence overstates one theorem: no declaration joins the square-frequency identity to the transverse stiffness, so 'formalised omega^2 = V_ss = 2V_w' describes two separate statements. A docstring in squarePotential also gives the diagonal squared length as 1/4 - w/4 rather than 1 - w; the theorem is unaffected. |
| B183 | theorem | 39 | H = diag(D) + A with Hermitian blocks D_i and A a unitary connection on a finite graph: H² − H*² = 2(DA + AD), ‖H²−H*²‖²/8 = oppositeEnergy both as an ordered sum and as an edge sum, and energy zero iff H² is Hermitian. The unitarity of the edge blocks is load-bearing — with unstructured complex weights the identity fails — and ‖D_iA_ij + A_ijD_j‖ = ‖D_i + A_ijD_jA_ij^H‖ is the unitary-invariance step. **clarification**: The ⅛ identity needs the edge blocks to be unitary, not merely skew-Hermitian: with unstructured complex weights ‖H²−H*²‖²/8 and Σ_E‖D_i + A_ijD_jA_ij^H‖² differ by a non-constant factor. Given a unitary connection the identity is exact, the step being ‖D_iA_ij + A_ijD_j‖ = ‖D_i + A_ijD_jA_ij^H‖. |
| B184 | theorem | 39 | With E∓ = 2‖Herm/Skew X‖² and X = DA: E⁻+E⁺ = 2‖X‖², E⁻−E⁺ = 2Re Tr X², the graph budget 2Σdeg(i)‖D_i‖² = 2‖DA‖², the identification of E⁺ with B183, and normal & H² Hermitian ⇒ D_i = 0 on every incident edge. |
| B186 | theorem | 18 | ΓA = iUAU* with U = (1−iΓ)/√2, the grading identities, Tr X² + Tr(ΓX)² = 2Tr B² and J² = −I; the identification U = exp(−iπΓ/4) is not formalised. |
| B190 | theorem | 10 | Pe² + Ve² + Le² = 1 for a scalar edge, with Le = 0 ⇔ b = r a guarded by a ≠ 0 and a counterexample to the unguarded reading. **missing-hypothesis**: 'Le = 0 exactly when b is a real multiple of a' fails at a = 0, b ≠ 0, where the displayed Le² is 0 but b is not a multiple of 0. The corrected statement is proved under a ≠ 0. |
| B194 | theorem | 54 | For a rank-one projector with unit real Bloch vector the Pauli commutator energies sum to the squared Frobenius norms |[P,sigma_x]|^2 + |[P,sigma_z]|^2 = 2(1 + n_y^2) >= 2, with equality exactly when n_y = 0; and the two bow-tie minima are IsLeast statements over all unit Bloch fields: 4 - 2*sqrt(2) for a shared edge and 6 - 3*sqrt(3) for a shared vertex. The card's arbitrary-unitary generality is not formalised. |
| B195 | theorem | 24 | K_ρ(u) = I − uA_ρ + u²(Deg − I) with K(1) = Deg − A = L⁻ and K(−1) = Deg + A = L⁺; det(I − uB_ρ) = (1−u²)^{(m−card v)d} det K_ρ(u) over any field, with the exponent checked exactly on a two-vertex one-edge graph and the reversed exponent refuted at u = 1/2. **clarification**: The report says q = 1 - u^2 != 0 is needed only for the negative-power statement, but the polynomial determinant identity bass_determinant_cross assumes it too; the exponent and both pencil ends are correct. |
| B198 | theorem | 36 | E∓ = 2p(1 ∓ cos 2θ) gives E⁻ = 4p − a² and E⁺ = a² for a = 2√p cos θ; τ = 2 artanh(a/(p+1)), Γ = tanh(τ/2) = a/(p+1), Ad(−U) = Ad(U), a² < 4p, and non-balancing at odd primes. The card's auxiliary conjugation carries the wrong sign on σ_y: p = 2, θ = π/4 gives −σ_y, not +σ_y. **sign**: The auxiliary conjugation display carries the wrong sign: conjugating σ_x by U = diag(e^{iθ}, e^{−iθ}) gives cos2θ σ_x − sin2θ σ_y, so the printed plus sign on σ_y is wrong. Witness p = 2, θ = π/4 gives −σ_y. The book energies are unaffected. |
| B199 | theorem | 12 | T² = q(T)I for traceless real 2×2 with q = ½(‖Herm T‖² − ‖Skew T‖²); q = 0 ∧ T ≠ 0 ⇔ nonzero nilpotent; q = h²−r², oscillator ω²(ζ²−1), orbit −κ². |
| B200 | derived | 20 | Q = Σm/(Σ√m)², h²/s² = 3Q−1 and Q = 2/3 ⟺ h = s; the centred Koide matrix squares to (h₁²+h₂²−s²)I, so Q = 2/3 is exactly its nilpotency. |
| B202 | theorem | 12 | The books are blind to orientation and the resolvent is not: the transpose identities and the exact |R₂₁(0.5i)| = 6√85/425 against the card's rounded 0.130158. **rounding**: The displayed |R₂₁(0.5i)| = 0.130158 is the rounded value of 6√85/425 = 0.130158…; the exact value is proved and the decimal equality is refuted. |
| B203 | theorem | 12 | L_rec = 2Σ|r_j|, D_end = 2|Σ r_j| and L_rec − D_end = 4 min(R₊,R₋) exactly, with equality iff every step is weakly of one sign, and L_rec = 2Σ artanh√(E⁻/E⁺) from the card's tanh² relation. |
| B206 | theorem | 25 | D^(1/k) ≤ F ≤ ρ and ρ − F = Var(√c) for principal cosines, and three rank-one projectors in ℂ² with all pairwise overlaps ½ have Tr(P₀P₁P₂) = (1±i)/4. |
| B207 | reading | 17 | The displayed hyperbolic system λ = (1−a/ρ)/(1+a/ρ) = tanh(½log(ρ/a)), ψ = 1 + a/ρ, the involution ρ ↦ a²/ρ sending λ ↦ −λ, r₊r₋ = Q² and τ₊ = −τ₋, all for a > 0; two boundary witnesses show a > 0 cannot be dropped. **clarification**: The displayed hyperbolic solution needs a > 0; two zero-mass and ρ = 1 witnesses show the totalised log formula fails without it. The card is stated for positive mass, so this is a boundary remark. **scope**: The card's Arrive field names the extremal hole at tau = 0, but the file's Q < M hypothesis excludes Q = M and no declaration treats the extremal case; the non-extremal RN constants that are proved are correct. |

## Cards mapped only to a companion repository

These kernels are pinned by commit and hash and their declarations exist in the snapshot, but they were not audited statement-by-statement in this repository, and four of the snapshots cannot even be re-elaborated here because they import a sibling module that was never pinned. Treat them as citations with a checked inventory.

| Card | Grade | Companion kernels |
| :--- | :--- | :--- |
| B12 | theorem | 1 in foft-lean |
| B19 | theorem | 5 in price-of-a-direction-lean |
| B22 | theorem | 4 in upg-lean |
| B30 | theorem | 4 in upg-lean |
| B35 | measured | 3 in price-of-a-direction-lean |
| B38 | theorem | 2 in foft-lean |
| B42 | theorem | 5 in square-case-lean |
| B43 | theorem | 2 in square-case-lean |
| B45 | theorem | 2 in spectral-stress-lean |
| B82 | derived | 4 in spectral-stress-lean |
| B95 | theorem | 5 in light-ledger-lean |
| B97 | theorem | 4 in votkp-lean |
| B98 | theorem | 5 in votkp-lean |
| B99 | theorem | 4 in votkp-lean |
| B102 | theorem | 2 in votkp-lean |
| B103 | theorem | 1 in votkp-lean |
| B104 | theorem | 2 in dirac-time-lean |
| B108 | measured | 4 in dirac-time-lean |
| B110 | theorem | 2 in dirac-time-lean |
| B111 | theorem | 4 in dirac-time-lean |
| B113 | theorem | 3 in price-of-a-direction-lean |
| B123 | theorem | 7 in gravity-ledger-lean, light-ledger-lean |
| B124 | theorem | 6 in gravity-ledger-lean |
| B127 | theorem | 5 in light-ledger-lean |
| B130 | theorem | 5 in light-ledger-lean |
| B134 | theorem | 4 in what-transport-keeps-lean |
| B135 | theorem | 3 in what-transport-keeps-lean |
| B136 | theorem | 2 in spectral-stress-lean |
| B137 | theorem | 4 in nonnormality-connection-energy-lean |
| B139 | theorem | 5 in foft-lean |
| B146 | theorem | 8 in coboundary-k3-lean |
| B149 | measured | 3 in what-transport-keeps-lean |
| B153 | theorem | 2 in votkp-lean |
| B159 | theorem | 2 in dirac-time-lean |
| B160 | theorem | 6 in dirac-time-lean |
| B161 | theorem | 3 in dirac-time-lean |
| B162 | theorem | 3 in dirac-time-lean |
| B163 | theorem | 3 in dirac-time-lean |
| B168 | measured | 2 in electron-screening-lean |
| B175 | theorem | 7 in light-ledger-lean |
| B189 | theorem | 2 in votkp-lean |
| B191 | theorem | 2 in foft-lean |
