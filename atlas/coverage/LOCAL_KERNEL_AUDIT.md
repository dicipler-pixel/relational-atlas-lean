# Audit of the local Lean kernels

Jeromie Beasley's Operator-First Relational Atlas, local library only.
Audit run of 25 November 2026 on the toolchain installed in the VM:
**Lean 4.35.0 with Mathlib 4.35.0**. The repository now pins the same toolchain
(`leanprover/lean4:v4.35.0` in `lean-toolchain`, `rev = "v4.35.0"` in `lakefile.toml`), so the
audit environment and the CI environment coincide; nothing in this library was ever elaborated on
the previously pinned v4.34.1.

## What was run

| Command | What it establishes |
| :--- | :--- |
| `python3 scripts/verify_local.py` | Elaborates every library module, every pinned external snapshot and every false control; audits `#print axioms` for all local theorems; rejects `sorry`/`admit`/`axiom`; requires each control to fail for a mathematical reason. |
| `python3 scripts/verify_coverage.py --self-test` | All 207 card records, the 41 pinned external snapshots and the metadata tamper controls. |
| `python3 atlas/cards/calculus/verify_atlas_calculus.py` | The finite calculus companion: 40 deterministic cochains, exact rational identity; `all_passed: true`. |

## Result

Final run of `python3 scripts/verify.py` and `python3 scripts/verify_local.py --core` (25 November
2026, Lean 4.35.0): thirteen library modules, 41 pinned external snapshots, 7 false controls,
**3033 theorem declarations audited** (16 in `Basic.lean`, 21 in `AtlasFormalCore.lean`, 178 in
`Extended.lean`, 229, 262, 314, 188, 19, 579, 295, 244, 303 and 385 in `Extended11.lean`).

The count is of unique fully-qualified theorem and lemma names, which is what the three checkers
agree on. It is neither the raw declaration count nor a short-name count: ten declarations in
`Extended9.lean` and two in `Extended10.lean` are indented by one space in the contributing files,
so the inventory walkers (which anchor `theorem` at column 0) do not see them, and `Extended7.lean`
holds namespaces that share short names, so a short-name count under-counts it. The indented
declarations are kernel-checked all the same and are registered in the ledger.

* **3033/3033** axiom audits return a subset of `{propext, Classical.choice, Quot.sound}`;
  no `sorryAx`, no `Lean.ofReduceBool`, no project axiom.
* **0** occurrences of `sorry`, `admit` or `axiom` in the compiled local sources.
* **7/7** false controls are rejected, each with a mathematical failure
  (`unsolved goals`, `linarith failed`, …), not a name or syntax error. This needs a caveat:
  the controls import the library, so in a standalone check the library objects must be built
  first. The first version of the harness did not do that and every control failed at the import
  instead — a green "rejected" that proved nothing. `scripts/verify_local.py` now builds
  `Basic`/`AtlasFormalCore` objects with `lean -o` before running the controls.
* **0** of the original 37 ledger statements is false as written. Two statements are weaker
  than their names or docstrings suggest (F1, F2 below), and four card claims that
  the ledger lists as open were closed by the additions listed under "New
  kernels". Later batches found the false statements listed under "Refutations and
  corrections" instead, each with the theorem that settles it.

## Findings

**F1 — B32: the displayed normalization and the proved one differ by a factor.**
The card displays `g = ¼ ∂n̂·∂n̂` and `Ω = ½ n̂·(∂x n̂ × ∂y n̂)`, for which
`4 det g = Ω²` exactly. `AtlasFormal.gram2_saturation` proves
`4 · [((a²+b²)/2)((c²+d²)/2) − ((ac+bd)/2)²] = (ad−bc)²`, i.e. it reads the
bracket as the determinant of `g = ½ ∂n̂·∂n̂`, not `¼ ∂n̂·∂n̂`; the identity is
correct, the normalization label in the docstring is not exact. Under the card's
own normalization the statement is `4 det g = ((ad−bc)/2)²`, proved as
`AtlasFormal.card_metric_saturation` in `RelationalAtlas/Extended.lean`.
This is a bookkeeping defect, not a mathematical error: the two forms differ by
the substitution `g ↦ 4g`, `Ω ↦ 4Ω`.

**F2 — B75: `middle_cancels` proves signs, not cancellation.**
The theorem proves that the middle band's two pair terms `s/(λ₂−λ₁)` and
`s/(λ₂−λ₃)` have opposite signs. The card's phrase is "terms cancel", and opposite
signs do not cancel. The exact condition is proved as
`AtlasFormal.balanced_middle_terms_cancel`: with `λ₁ < λ₂ < λ₃` the two terms sum
to zero exactly when `w₂₁(λ₃−λ₂) = w₂₃(λ₂−λ₁)`, and
`middle_terms_opposite_but_not_cancelled` exhibits an ordered spectrum with
opposite signs that do not cancel. The coverage ledger already records this
correction; the new theorem is its Lean form.

**F3 — B31: the Frobenius norm identity was not formalized.**
The card displays `‖F‖_F = ‖[Ω, Π]‖_F` in addition to `Tr F = 0` and
`F = 0 ⇔ [Ω, Π] = 0`; the ledger recorded the norm identity as absent. It holds:
`F` is the sum of the two cross-subspace blocks, `[Ω, Π]` is their difference, and
the two blocks are orthogonal in the Frobenius inner product, so both norms equal
`‖ΠΩ(1−Π)‖² + ‖(1−Π)ΩΠ‖²`. Formalized as
`AtlasFormal.offBlock_frobSq_eq_commutator` (orthogonal projector, complex
matrices) in `RelationalAtlas/Extended.lean`.

**F4 — B66 and B85: the zero sets the cards name were not stated.**
B66 identifies `{det G = 0}` with `{det X = 0}`; B85 says the rank-one
determinant vanishes only at real parallelism. Both are now stated and proved
(`gram_det_zero_iff`, `rank_one_det_zero_iff`), each a one-line consequence of the
identity already in `AtlasFormalCore.lean`.

**F5 — B57 was the weakest mapping.**
`indefinite_null_direction_exists` proves that `x² − y²` has the null direction
`(1,1)`. That is an analogue of the card, not the card's biorthogonal projector;
the ledger says so. It is now backed by a real construction: for an orthogonal
projector the quadratic trace form is positive definite on the tangent space,
while for the oblique projector `Π = [[1,1],[0,0]]` the tangent `T = [[0,1],[0,0]]`
is nonzero and has `Tr(T²) = 0`. See `B57TraceForm.lean` in
`RelationalAtlas/Extended.lean`'s B57 section.

**F7 — B190's "Le = 0 exactly when b is a real multiple of a" needs `a ≠ 0`.**
At `a = 0`, `b ≠ 0` the displayed `Le² = 4(‖a‖²‖b‖² − ⟨a,b⟩²)/s²` is `0` although `b` is not a
real multiple of `a`. The corrected statement (`a ≠ 0` and then `Le = 0 ⇔ b = r a`) is proved
with the counterexample supplied, and the card's wording should be guarded accordingly.

**F6 — the axiom audit did not cover five declarations.**
`AtlasFormalCore.lean` ends with `#print axioms` lines for 16 of its 21
theorems; `symmetric_skew_commute_gives_zero`, `tangent_occupied_block`,
`tangent_empty_block`, `rank_one_complex_realpart_not_definite` and
`open_soft_crosses` have no line, and `Basic.lean` has none at all. The file is
preserved byte-for-byte as first checked, so the fix is not an edit to it:
`scripts/verify_local.py` compiles a copy of each module with `#print axioms`
appended for every declaration it finds. All 37 pass.

## Per-declaration verdicts

"Card" is the coverage-ledger claim; "verdict" is this audit's reading of the Lean
statement against that claim, not a judgement of the card's physics.

| Card | Declaration | Lean statement | Verdict |
| :--- | :--- | :--- | :--- |
| B2 | `normal_commutator` | `(S+K)(S+K)ᵀ − (S+K)ᵀ(S+K) = −2(SK−KS)` for `Sᵀ=S`, `Kᵀ=−K` | Exact, faithful. |
| B2 | `normal_iff_commute` | normality of `S+K` ⇔ `SK = KS`, same hypotheses | Exact, faithful. |
| B2/B64 | `symmetric_skew_commutator_identity` | same identity in any ring, with `S−K` standing in for the transpose side | Faithful as a ring identity; it does not itself prove `Hᵀ = S−K` (the matrix form above does). |
| B2/B64 | `symmetric_skew_commute_gives_zero` | the identity vanishes when `S`, `K` commute | Exact. |
| B6 | `binary_entropy` | `H(0)=H(1)=0`, `H(1−ν)=H(ν)`, `0 ≤ H(ν) ≤ log 2`, `H(1/2)=log 2` | Faithful for the scalar `H`; the sum `S = Σ H(ν_k)` and the free-fermion construction are not formalized (declared in the ledger). |
| B16 | `rankOne_projector_distance` | `½‖uuᵀ − vvᵀ‖²_F = 1 − ⟨u,v⟩²` for unit vectors in `ℝ²` | Exact; dimension two is the card's own setting. The depth formula `2 log(1/δ)` is not proved. |
| B31 | `offBlock_trace` | `Tr F = 0` for `P²=P` | Exact, over any ring of matrices. |
| B31 | `offBlock_eq_zero_iff` | `F = 0 ⇔ ΩP = PΩ` | Exact. |
| B31 | `tangent_occupied_block`, `tangent_empty_block`, `tangent_split` | tangency to the idempotent manifold forces the diagonal blocks to vanish and `D` to be purely off-diagonal | Exact, any ring. |
| B32 | `gram2_saturation` | the Lagrange identity in `g = ½`-Gram normalization | True, but normalized differently from the card — see F1. |
| B39 | `critical_angle` | `1 < κ sin²θ ⇔ √(1/κ) < sin θ` for `κ>0`, `sin θ ≥ 0` | Exact form of the critical-angle claim. |
| B39 | `complex_angle_sin`, `complex_angle_cos` | `sin(π/2+iy) = cosh y`; `Re cos(π/2+iy) = 0` | Exact. |
| B48 | `seam_schur` | Mathlib's `det [[A,B],[C,D]] = det D · det(A − B D⁻¹ C)` | Exact; the identification of the interface with this block form is the card's, not proved (declared). |
| B48 | `scalar_schur_complement` | `ad − bc = d(a − b d⁻¹c)`, `d ≠ 0` | Exact one-channel instance. |
| B51 | `reciprocal_reduction` | the reciprocal quartic equals `t²(au²+bu+(c−2a))`, `u = t+1/t` | Exact. |
| B51 | `unit_circle_u` | `e^{iφ} + e^{−iφ} = 2cos φ ∈ [−2,2]` | Exact forward direction. |
| B51 | `u_from_unit_circle` | every `u ∈ [−2,2]` is `t + 1/t` for a unit `t` | Exact backward direction. |
| B51 | `reciprocal_quartic_reduction` | the real form of the reduction divided by `t²` | Exact. |
| B56 | `b56_combined_derivative_not_surjective` | no linear map `ℝ² → ℝ³` is onto | Exact kernel of the corrected rank obstruction; the withdrawn "do not meet" caption is not certified, as the ledger states. |
| B57 | `indefinite_null_direction_exists` | `(1,1)` is null for `x²−y²` | True but only an analogue — see F5; now superseded. |
| B122 | `b122_shift_opNorm` (both bounds, genuine L2 operator norm), `b122_semigroup_norm`, `b122_semigroup_hasDerivAt`, `b122_semigroup_unique` | `‖e^{−bt}(I−μtN)‖ = e^{−bt}(√(4+μ²t²)+|μt|)/2` for `J = [[b,μ],[0,b]]` |
| B60 | `tangent_dimension_one_factors` | `k·q = 1 ⇒ k = q = 1` in `ℕ` | Exact arithmetic kernel only; the complex-parallel characterization is not formalized (declared). |
| B61 | `bohr_rod` | `(ħ/(αmc))·m = ħ/(αc)` for nonzero `α,m,c` | Exact. |
| B66 | `gram_det`, `gram_det_is_square` | `det(XᵀX) = (det X)²` | Exact for square `X`. |
| B68 | `paired_spectrum` | `σ²=1`, `σD = −Dσ`, `Dv = λv`, `v≠0` give `D(σv) = −λσv` and `σv ≠ 0` | Exact; this form does prove the partner is nonzero. |
| B68 | `chiral_eigenvalue_pair` | the eigenvalue equation without `σ²=1` | Honest weaker form: no nonzeroness claim, as its docstring says. |
| B74 | `stratum_repels`, `refraction_turning_barrier` | `g sin²θ = C`, `g ≥ 0`, `sin²θ ≤ 1` ⇒ `C ≤ g` | Exact scalar inequality. |
| B75 | `middle_cancels` | signs of the three bands' pair terms | Signs only — see F2. |
| B85 | `rank_one_complex_realpart_det` | `(x²−y²)(s²−t²) − (xs−yt)² = −(xt−ys)²` | Exact. |
| B85 | `rank_one_complex_realpart_not_definite` | the same expression is `≤ 0` | Exact. |
| B90 | `hermitian_soft_lapse`, `open_soft_crosses`, `open_lapse_square` | `√(t²)=|t|`; a crossing changes sign; `(√|t|)²=|t|` | Exact normal forms; genericity is not claimed, as the docstrings say. |

## What this audit does not establish

* It does not re-derive the physics, the measured exponents or the continuum
  limits of any card; a Lean kernel is a finite statement and the ledger's
  scopes say which one.
* It does not audit the **52 external card mappings** statement by statement, and the pinned
  snapshots are not all independently compilable. On the final run, 34 of the 41 snapshots
  elaborate standalone on Lean 4.35.0; `CoboundaryK3/Basic.lean` needs about fourteen minutes and
  7.5 GB resident under this VM's load, so an earlier run with a 900 s cap timed it out even though
  it passes when given the time. Four cannot elaborate from this repository at all because they
  import a sibling module that was never pinned — `DiracTime/FiniteReturn.lean` needs
  `DiracTime.PredictiveQuotient`, `LightBridges/Census.lean` needs `LightBridges.Algebra`,
  `NonNormality/SelfCommutator.lean` needs `NonNormality.Frobenius`, and
  `NonNormality/Holonomy.lean` needs `NonNormality.SelfCommutator`. Three more need only module
  resolution, because their sibling *is* pinned (`LightSpectral.lean` ← `Rigidity.lean`,
  `SquareCase/Secular.lean` ← `SquareCase/Transport.lean`, `VOTKP/Film.lean` ← `VOTKP/Smith.lean`);
  I built each sibling's object in the right module path and put it on `LEAN_PATH`, and all three
  then elaborate cleanly (`Rigidity` 29 s, `Transport` → `Secular` 4 min, `Smith` → `Film` 2 min).
  That raises the checkable count from 34 to 37, leaving the four unpinned-sibling snapshots as the
  only ones that cannot be re-elaborated here. Every card mapped only to one of those four rests on
  a citation and a pinned hash, not on a fresh elaboration.
* It does not certify the 37 cards the ledger lists as unmapped, nor the local
  theorem count against anything but `scripts/config.json` and the three checkers.
* It cannot re-verify the published archive: the Zenodo zip is not in the repository, so the
  regenerated [`validation.json`](validation.json) records `archive_verified: false` for this run.
  The archive was matched to the Zenodo checksums on 23 October 2026, and `coverage.json` keeps
  the archive SHA-256 as the record of that check.


## What each kernel covers, and what it does not

[`CERTIFICATION.md`](CERTIFICATION.md) is generated by `scripts/build_certification.py` from
`coverage.json`, and states for every mapped card what its Lean kernel proves and what would still
be needed before the card itself could be called certified. It exists because
`full_card_certified` must stay `false` — the validator refuses `true` without a new schema — and a
boolean hides the difference between "the finite statement is proved" and "the card is proved".
The 42 cards mapped only to a companion repository are listed separately: their declarations exist
in the pinned snapshot, but they were not audited statement-by-statement here, and four of those
snapshots cannot be re-elaborated at all.

## The CI pipeline, run for real

The workflow was unexercised until 25 November 2026. It has now been executed end to end in
this VM by `scripts/ci_local.sh`, which copies the installed Mathlib to a writable directory
(Lake must write hash files beside the objects, which a root-owned installation forbids),
points a scratch copy of the project at it as a path dependency, and runs the workflow's three
steps:

| Step | Result |
| :--- | :--- |
| `lake build` (Lean 4.35.0, Mathlib 4.35.0) | **Build completed successfully (9059 jobs)**, all twelve modules including `Extended10` |
| `lake env leanchecker` per module (independent kernel replay) | all twelve exit 0 |
| `python3 scripts/verify.py` | **OK: 2648 theorems**, axioms `{propext, Classical.choice, Quot.sound}`, 7 false controls rejected |

Two defects were found by doing it rather than by reading it. The first was in `scripts/verify.py`
(it required one namespace per file, counted only `theorem`, rejected the short spelling of the
choice axiom and mis-parsed wrapped axiom lists — fixed). The second was in `lakefile.toml`:
`RelationalAtlas.Extended7` was registered in `config.json` and in the ledger but missing from the
Lake roots, so `lake build` would have silently skipped it and the audit would then have failed on
its import. Both are fixed and the run above is after the fix.

What this run does **not** establish: it used the Mathlib shipped with the VM image rather than a
fresh clone plus `lake exe cache get`, so the workflow's own download steps remain unverified, and
the pins were moved from v4.34.1 to v4.35.0 precisely because every proof here was elaborated on
4.35.0 and nothing on 4.34.1.

## Refutations and corrections

Every card whose displayed claim, or whose ledger transcription, did not survive contact with Lean is listed here with the theorem that settles it. `kind` is `refuted` (false as written), `missing-hypothesis` (true only with a hypothesis the card does not state), `overreach` / `scope` (true but weaker than the words), `ledger-error` (the card is fine and the ledger is not), `sign`, `rounding`, `provenance` or `clarification`.

Fifteen cards were false as literally written in batches one to eight and carry Lean counterexamples: **B15** (the raw log-det comparator is not subadditive), **B28** (the SLD tensor is `F/4 + C/8`, not `F/4 − iC/8`), **B67** (a closed loop need not lift), **B91** (the positivity criterion fails at `g11 = 0`), **B121** (the Jordan criterion drops `A12 ≠ 0`), **B132** (the dichotomy needs `F` symmetric), **B169** (no −0.99 correlation floor), **B185** (nonunitary does not imply non-stochastic), **B196** (minimality holds at `|c| = 2`), **B200** (the shift is `−hI`), **B205** (even blocks can carry half modes), plus the ledger's squared B44, B86, B155 and the rounded B202. Batch nine adds **B4** and **B62** unconditionally and **B49** conditionally on the cited torsion formula; B58, B76 and B53 carry `overreach`, `scope`, `provenance` and `clarification` records instead, and B125 survived the hunt without a correction.

**B15 — refuted.** The global subadditivity S(a∪b) ≤ S(a)+S(b) is false for the raw log-det comparator S(A,B) = log det((A+B)/2) − ½log det A − ½log det B: S(1,4) = log(5/4) = 0.2231 exceeds S(1,2)+S(2,4) = log(9/8) = 0.1178, and the two steps have equal cost so the failure is not a subdivision artefact. The √S metric reading, which the archived HTML and the ledger spell differently, is not addressed.  
Evidence: `AtlasB15.not_subadditive` in `RelationalAtlas/Extended3.lean`.

**B44 — ledger-error.** coverage.json (and the batch brief) carried the squared form max_t‖e^{tA}‖ ≥ max_t‖e^{tJ}‖²; the current card HTML displays the unsquared G(H) ≥ G(block). The squared form is false even for a surjective isometric embedding: J = A = [[−1/2,1],[0,−1/2]] in the max norm has M = 2e^{−1/2} > 1, so max_A = M < M². The unsquared lift is proved.  
Evidence: `literal_squared_B44_claim_is_false` in `RelationalAtlas/Extended3.lean`.

**B54 — overreach.** det g > 0 does not certify that the form is still a metric: −I₂ has determinant 1 and is negative definite. The universal reading of the first clause ('det g > 0 ⇒ |Ω|² overruns') is false, e.g. g = I₂, |Ω|² = 0. The second clause is true as stated: det g < 0 with |Ω|² ≥ 0 gives 4 det g < |Ω|² and excludes positive definiteness.  
Evidence: `positive_det_does_not_imply_positiveDef` in `RelationalAtlas/Extended3.lean`.

**B86 — ledger-error.** Three readings of B86's determinant clause disagree: the ledger says det g ≤ 0 for symmetric probes, the archived HTML prose says det g ≡ 0. Arbitrary real symmetry does not give the inequality (G = I₂ beside a regular reciprocity witness), the generic det ≡ 0 is false, and the true content for the intended bilinear form Re(uuᵀ) is det = −Im(conj(u₁)u₂)² ≤ 0, zero exactly at real parallelism — so the non-positivity comes from the bilinear structure, not from reciprocity. The norm clause ‖B‖ = max tᵢ/gᵢ also needs tᵢ ≥ 0.  
Evidence: `symmetric_alone_does_not_imply_det_nonpos` in `RelationalAtlas/Extended3.lean`.

**B112 — clarification.** 'pᵢ = pⱼ = 0 ⇒ Vᵢⱼ must vanish' is a compatibility condition, not an automaticity claim: with p ≥ 0, existence of L is *equivalent* to it, the solution is the quotient off the zero sums, and an arbitrary block remains on the kernel–kernel pairs. The witness p = 0, V = 1 shows it cannot be dropped.  
Evidence: `exists_entrywise_sld_iff` in `RelationalAtlas/Extended3.lean`.

**B114 — clarification.** The displayed jet identity needs m > 0: at m = 0 it would read P = P² + P², which fails for the constant path at 1. For m ≥ 1 it is exact, and the C^(m+1) hypothesis can be weakened to C^m.  
Evidence: `order_zero_literal_claim_false` in `RelationalAtlas/Extended3.lean`.

**B119 — missing-hypothesis.** The transverse coefficient −½∂_y g_xx is the *Killing* specialization of Γ_{xx,y} = g_{xy,x} − ½g_{xx,y}, not the general symbol: pointwise vanishing of g_xy is insufficient (g = [[1,xy],[xy,2]] at (0,1) has g_xy = 0 and coefficient 1, not 0), so ∂_x g_{xy} = 0 is essential. The raised-index coefficient differs as well (−9/8 first kind against −9/32 when g_yy = 4).  
Evidence: `pointwise_vanishing_gxy_is_insufficient` in `RelationalAtlas/Extended3.lean`.

**B132 — refuted.** The 'otherwise' clause fails without F symmetric: with one zero probe u = 0 and F = [[0,1],[−1,0]], F is outside span{uᵢuᵢᵀ} and every reading vanishes, yet Tr(HF) = 0 for every symmetric H, so the invisible detecting H cannot exist. The antisymmetric part of F is invisible to every symmetric probe. With F = Fᵀ the dichotomy is proved in both directions.  
Evidence: `literal_otherwise_clause_counterexample` in `RelationalAtlas/Extended3.lean`.

**B154 — missing-hypothesis.** The equivalence 'Tr(K_A δC) = βTr(h_A δC) for all traceless Hermitian δC ⟺ K_A − βh_A = λI' needs K Hermitian. With K = [[0,1],[−1,0]], h = 0, β = 1 every symmetric C is invisible to K (an antisymmetric matrix never pairs with a symmetric one) yet K is not a scalar. The card supplies the hypothesis only through the word 'Hamiltonian'.  
Evidence: `skewWitness_refutes_dropping_symmetry` in `RelationalAtlas/Extended3.lean`.

**B171 — overreach.** The hidden block P_W D_T² P_W − A² is line-valued, hence of rank at most one, not rank one: hidden(H) = Tr(D_T(P_W(H)))·C^ad(W). At uniform weights with T = I the trace factor vanishes identically and the block is zero, so the card's 'rank one because Q_W = I − P_W does' is an overstatement.  
Evidence: `hidden_rank_le_one` in `RelationalAtlas/Extended3.lean`.

**B183 — clarification.** The ⅛ identity needs the edge blocks to be unitary, not merely skew-Hermitian: with unstructured complex weights ‖H²−H*²‖²/8 and Σ_E‖D_i + A_ijD_jA_ij^H‖² differ by a non-constant factor. Given a unitary connection the identity is exact, the step being ‖D_iA_ij + A_ijD_j‖ = ‖D_i + A_ijD_jA_ij^H‖.  
Evidence: `b183_oppositeEnergy` in `RelationalAtlas/Extended3.lean`.

**B190 — missing-hypothesis.** 'Le = 0 exactly when b is a real multiple of a' fails at a = 0, b ≠ 0, where the displayed Le² is 0 but b is not a multiple of 0. The corrected statement is proved under a ≠ 0.  
Evidence: `LeSq_eq_zero_iff` in `RelationalAtlas/Extended.lean`.

**B155 — ledger-error.** The generic two-unit-vector reading of the Gram matrix is false: for unit vectors with inner product cos ϑ the Gram determinant is sin²ϑ and the characteristic roots are 1 ± cos ϑ. The card's diag(cos²ϑ, 1) is specific to its own shape-sphere parametrisation dΦ(eϑ) = (cosϑcosφ, cosϑsinφ), dΦ(eφ) = (−sinφ, cosφ).  
Evidence: `literal_unit_vector_counterexample` in `RelationalAtlas/Extended2.lean`.

**B202 — rounding.** The displayed |R₂₁(0.5i)| = 0.130158 is the rounded value of 6√85/425 = 0.130158…; the exact value is proved and the decimal equality is refuted.  
Evidence: `rounded_decimal_not_exact` in `RelationalAtlas/Extended2.lean`.

**B148 — clarification.** Miss probabilities do not multiply: the composition law is q_A + q_B − q_A q_B, with a Lean counterexample (3/4 ≠ 1/4 at q = 1/2). What multiplies is the *stress* 1 − S under the tensor product.  
Evidence: `b148_miss_product_counterexample` in `RelationalAtlas/Extended2.lean`.

**B91 — missing-hypothesis.** The displayed criterion Q ⪰ 0 ⟺ g₁₁ ≥ 0 ∧ 4 det g ≥ |Ω|² fails at g₁₁ = 0: with (a,b,d,w) = (0,0,−1,0) both displayed conditions hold and Q = diag(0,−1) is not positive semidefinite. The repair is 0 ≤ d (equivalently 0 ≤ a + d); under a > 0 the card's criterion is exact. The literal wall ⊂ {det g > 0} also fails on zero data.  
Evidence: `B91.literal_equivalence_false` in `RelationalAtlas/Extended4.lean`.

**B24 — missing-hypothesis.** The equality of the two displayed c₂ forms needs E Hermitian: with H = I, η = 0, E = [[0,1],[0,0]] the true c₂ vanishes (E² = 0) while the modulus-squared sum is 1. Separately, positivity of H + η is needed for any finite expansion: H = diag(0,1), η = 0, E = I gives log det = log(ε(1+ε)) → −∞.  
Evidence: `B24.nonHermitian_perturbation_breaks_two_forms` in `RelationalAtlas/Extended4.lean`.

**B24 — provenance.** The local atlas/cards/html/B24.html has SHA 1f06fe... while coverage.json pins 3f9377...; the audited claims were checked against the official v7 card, whose hash matches. Separately, the unconditional trace identities use totalised division at a zero eigenvalue, so nondegeneracy should be stated rather than inherited from Lean's x/0 = 0.  
Evidence: `RelationalAtlas.B24.logdet_c2_eq_trace_RERE` in `RelationalAtlas/Extended4.lean`.

**B198 — sign.** The auxiliary conjugation display carries the wrong sign: conjugating σ_x by U = diag(e^{iθ}, e^{−iθ}) gives cos2θ σ_x − sin2θ σ_y, so the printed plus sign on σ_y is wrong. Witness p = 2, θ = π/4 gives −σ_y. The book energies are unaffected.  
Evidence: `B198.printed_auxiliary_conjugation_false` in `RelationalAtlas/Extended4.lean`.

**B181 — rounding.** The displayed ω = 1.912290 is a six-place rounding of √(2(2√2−1)) = 1.912290315…; the file proves 1.912290 < √(2(2√2−1)) < 1.9122905 so the final equality cannot be read as exact.  
Evidence: `B181.squareOmega_ne_displayed_exactly` in `RelationalAtlas/Extended4.lean`.

**B181 — clarification.** The file's summary sentence overstates one theorem: no declaration joins the square-frequency identity to the transverse stiffness, so 'formalised omega^2 = V_ss = 2V_w' describes two separate statements. A docstring in squarePotential also gives the diagonal squared length as 1/4 - w/4 rather than 1 - w; the theorem is unaffected.  
Evidence: `RelationalAtlas.B181.foldPotential_second_deriv` in `RelationalAtlas/Extended4.lean`.

**B46 — provenance.** Resolved in the ledger's favour: the coverage claim is an exact extraction from the official v7 card (archive SHA-256 cdc604b1..., member cards/html/B46.html SHA-256 3626f1bb...), whose display is the idempotency-defect formula the kernel proves. The local 93-card edition (b1e69c...) displays a different formula (W-dot = Pi_TGr(W-dot) + delta) and is the divergent document. All seven source-derived fields reproduce with build_coverage.py's own extraction algorithm.  
Evidence: `B46.b46_idempotency_defect` in `RelationalAtlas/Extended4.lean`.

**Which document is "the card", measured (25 November 2026).** The B46 resolution above is not a special case: it is the general situation. Every local file in `atlas/cards/html/` was hashed against the `source_sha256` that `coverage.json` pins for the official v7 member. **None of the 93 local files matches** — the directory is the historical 93-card edition throughout — and 114 of the 207 cards have no local file at all (the 93 files cover B1–B90 and B94–B96; B91–B93 and B97–B207 are absent). So the rule for every verdict is:

* The `claim` / `Carry` / `Check` / `Arrive` / `closed_when` fields of `coverage.json` are the v7 card. A kernel or a counterexample is judged against those.
* A local `atlas/cards/html/B<id>.html` is a *different document* and never overrides the ledger. Where the two disagree, the disagreement is itself a finding, and a refutation of the local text has not touched the card.
* The v7 archive is obtainable from the DOI and can be checked: `python3 scripts/verify_coverage.py --source-archive <atlas_cards_v7_html.zip>` re-verifies all 207 member digests and the archive checksum. It was run on 25 November 2026 against the archive from <https://zenodo.org/records/23590925/files/atlas_cards_v7_html.zip?download=1> (zip SHA-256 `cdc604b1…`, md5 `0adae1e0cf28dd26d76397330eceef09`, both matching the ledger) and reports **`archive_verified: true`** — every card's `source_sha256` matches the member it pins. The archive itself is not committed (2.7 MB and DOI-stable); `validation.json` records the result.

This already decided three cases, and the third is the instructive one:

* **B46** — the local edition displays a different formula; the ledger's v7 extraction is the card, and the kernel proves it.
* **B29** — the ledger transcription is exact: v7 really does display `Σ_k a_k t^{(k−d)/2}` with `a₀ = Area/4π, a₁ = (1/4π)∫R/6` in the Check. The index defect is *in the card*, not in the transcription, and the card's own witness chart gives the expansion `1/3 + t/15 + 4t²/315 + t³/315`, which places `1/3` at the constant term — the power the display assigns to `a₂`.
* **B36** — the two editions make opposite claims at the same locus, and the local one states the thing the v7 card exists to correct. Local (`ae5a50c4…`): title "Three mechanisms arrive at one place", display `g ∼ 1/(6w₃) → ∞, ‖R‖ → ∞, Jordan block of size two`. v7 (`aeaf9090…`): title "One fold, read three ways", display `ds² = dw₃²/(4w₃) = dσ₃²/σ₃ = sign(det X)√w₃ · K finite at w₃ = 0 · B(0) = λ*I`, and prose saying the Gram coordinate shows "a metric coefficient that diverges, curvature that seems to, and a Jordan block", that "the wall lies at finite distance, the curvature stays finite, and the block is a plain double point on the oriented cover", and that "a cone read through a singular change of frame becomes a Jordan block". So a counterexample showing the Gram-frame block is diagonalisable rather than defective is, if anything, an instance of the v7 claim; it is a refutation only of the 93-card edition, which asserts what the v7 card denies.

**B179 — clarification.** The raw quotient dX²/(4c²X) needs λ ≠ 0; at λ = 0 (the horizon X = 0) it gives 0 rather than the limiting 1, which the regular extension supplies. The card's two expressions agree except at that single point.  
Evidence: `B179.b179_raw_formula_fails_at_fold` in `RelationalAtlas/Extended4.lean`.

**B179 — clarification.** The integrated-distance statement needs c != 0 as well as lambda != 0; the metric identity carries both and the file states them, but the distance wording is positive only under that hypothesis.  
Evidence: `RelationalAtlas.B179.b179_reflection_isometry_dist` in `RelationalAtlas/Extended4.lean`.

**B25 — clarification.** The susceptibility formula needs a nonzero gap for a contributing term. With degenerate labels and a zero gap, Lean's x/0 = 0 makes the sum vanish; that is not the physical limit, as the file states, so the corrected hypothesis is E_n ≠ E_m on contributing terms.  
Evidence: `B25.degenerate_gap_witness` in `RelationalAtlas/Extended4.lean`.

**B207 — clarification.** The displayed hyperbolic solution needs a > 0; two zero-mass and ρ = 1 witnesses show the totalised log formula fails without it. The card is stated for positive mass, so this is a boundary remark.  
Evidence: `B207.tanh_claim_fails_at_zero_mass` in `RelationalAtlas/Extended4.lean`.

**B207 — scope.** The card's Arrive field names the extremal hole at tau = 0, but the file's Q < M hypothesis excludes Q = M and no declaration treats the extremal case; the non-extremal RN constants that are proved are correct.  
Evidence: `RelationalAtlas.B207.horizon_rapidities_opposite` in `RelationalAtlas/Extended4.lean`.

**B195 — clarification.** The report says q = 1 - u^2 != 0 is needed only for the negative-power statement, but the polynomial determinant identity bass_determinant_cross assumes it too; the exponent and both pencil ends are correct.  
Evidence: `RelationalAtlas.B195.bass_determinant_cross` in `RelationalAtlas/Extended4.lean`.

**B152 — clarification.** The offset theorem is proved faithfully, but the card's spectral nu -> 1 - nu and offset eps -> -eps clauses are neither formalised nor listed among the report's omissions.  
Evidence: `RelationalAtlas.B152.offset_eq_zero` in `RelationalAtlas/Extended4.lean`.

**B67 — refuted.** A closed loop in shape space need not admit an open lift even with horizontality, collision-freeness and regularity throughout (explicit nonconstant radial witness), so the card's unrestricted 'closed loop => open lift' is false; the sharp replacement is the gap condition. The isotropy clause r <= d-2 is exact: a nonidentity determinant-one isometry fixing the span exists iff finrank K + 2 <= finrank E.  
Evidence: `B67.admissible_B67_open_lift_claim_is_false` in `RelationalAtlas/Extended5.lean`.

**B169 — refuted.** No -0.99 correlation floor: on the card's own grid the correlation is -sqrt(7/10) at uniform weights and -1/5 at (133,1,...,1), and -4/sqrt(17) in the normalization-free model, so it moves with the precision profile. The measured -0.999475 is not replayed: the nonlinear sensitivity data is absent, so that number stays unverified rather than refuted.  
Evidence: `B169.B169_no_precision_floor` in `RelationalAtlas/Extended5.lean`.

**B185 — refuted.** The closing sentence reads as a universal: nonunitary transport implies non-stochastic weights. It is false in that direction: the constant 2x2 matrix with every entry (1+i)/2 is not unitary, yet all Born weights are 1/2 and W is doubly stochastic. The other direction does hold (U = [2] is nonunitary with weight 4), so the correct statement is an implication, not an equivalence.  
Evidence: `B185.equalPhaseTransport_bornWeights_doublyStochastic` in `RelationalAtlas/Extended7.lean`.

**B196 — refuted.** 'Minimal solution iff |lambda| > 2 sqrt q' fails at the boundary: at c = 2r with r^2 = 1 every solution is r^n(a + bn), a non-proportional partner forces b != 0, and r^n/s_n = 1/(a + bn) -> 0, so the fundamental solution is minimal also at |c| = 2. The witness is graph-realised (q = 1, lambda = -2 by a C4 adjacency matrix with an alternating eigenvector). The correct criterion is |lambda| >= 2 sqrt q.  
Evidence: `B196.fundamental_isMinimalSolution` in `RelationalAtlas/Extended7.lean`.

**B205 — refuted.** 'nu = 1/2 in odd blocks only' is false as a universal: in the card-allowed dimer limit t1 = 1, t2 = 0, v = 0 the even block carries C_B = (1/2) I2, two half modes. The odd-block existence half is proved (a forced nu = 1/2 eigenvector for odd |n|); only the exclusion fails.  
Evidence: `riceMele_oddBlock_halfMode` in `RelationalAtlas/Extended7.lean`.

**B191 — overreach.** The prose net-increment reading cannot drop the uncentered linear terms: on one scalar edge with D = U = c = 1 the shifted E+ is 16 while the old E+ plus 4rc^2 is 8. Also, uncentered balance and k/r-centered balance are different conditions: the first holds iff rho = 0, the second iff rho = k/r.  
Evidence: `B191` in `RelationalAtlas/Extended7.lean`.

**B121 — refuted.** The displayed Jordan criterion is false as an iff: at t1 = t2 = t3 = 1, w = (1/2,1/2,0), T = I, G = diag(1/2,1/2,0) every stated hypothesis holds and the displayed equality reads 0 = 0, yet the transport A(H) = TH + HT - 2 tr(TH)G is 2H on traceless H, so it is diagonalisable and not a nontrivial Jordan block. The card's own Why paragraph requires A12 != 0, which the display omits.  
Evidence: `B121` in `RelationalAtlas/Extended8.lean`.

**B143 — overreach.** 'lambda_max = 1/eps - 1 + O(eps), lambda_frame ~ eps^-1/2, all rates eps^-1' is right for the large eigenvalues but false for the full operator: on the corner geometry the mixed rates are not bounded below by any c/eps, with the witness eps = 144/5329 giving eps*lambda_mixed = 12/71 < 1/4.  
Evidence: `B143` in `RelationalAtlas/Extended8.lean`.

**B28 — refuted.** The displayed SLD tensor identity Q = 1/4 F - (i/8)Tr(rho[L1,L2]) is false: at rho = diag(3/4,1/4), L1 = sigma_x, L2 = sigma_y every hypothesis holds (PosDef, trace one, Hermitian, both SLD equations) and Q = i/8 while the displayed right-hand side is 1/8. The correct identity for arbitrary finite complex matrices is Q = F/4 + C/8 with F = 1/2 Tr(rho{L1,L2}) and C = Tr(rho[L1,L2]); for Hermitian data Re Q = F/4 and the imaginary part equals -iC/8 only as a real scalar.  
Evidence: `B28` in `RelationalAtlas/Extended9.lean`.

**B201 — scope.** The referee audit confirms the local derivative laws, the -32 normalization and both directions of dE+ = 0 iff K^2 normal, but records what is weaker than the card: power traces are only infinitesimally stationary rather than invariants along a flow, the improper budget assumes integrability and convergence, the spectral budget never identifies v with the spectrum, and the endpoint limits assume convergence to a unitary diagonal, with no global existence or Barbalat argument.  
Evidence: `B201` in `RelationalAtlas/Extended7.lean`.

**B94 — scope.** The displayed |Delta (1/n) log det eta| = C_K d_H is only partly formalisable here: the padding law and the 2/n Hamming cost of a transposition are proved, but C_K is a knot-dependent regulator constant that this repository does not construct, so the card's exact identity remains conditional on knot theory.  
Evidence: `B94` in `RelationalAtlas/Extended8.lean`.

**B147 — scope.** The displayed D_l and both limits are proved, but the entropy-to-lattice identity the card derives D_l from (the S_l sum over sin^2 of h) is not formalised, so the kernel covers the series and its asymptotics, not its origin.  

**B4 — refuted.** The displayed identity ½‖Π₁−Π₂‖²_F = Σ sin²θᵢ is stated with no equal-rank hypothesis and is false as written, although the card calls this side 'a theorem'. In ℝ³, Π₁ = diag(1,0,0) and Π₂ = diag(1,1,0) are orthogonal projectors with nested ranges: ‖Π₁−Π₂‖²_F = 1, so the left side is ½, while the principal-angle list is [0] and the sum is 0 — or 1 if the extra angle is padded as π/2, so neither customary convention repairs it. With p = rank Π₁ and q = rank Π₂ the correct identity is ½‖Π₁−Π₂‖²_F = Σ_{i≤min(p,q)} sin²θᵢ + |p−q|/2, which is exactly the card's identity when p = q; both the false display and the repair are proved at the witness. The refraction equation R₁sin²θ₁ = R₂sin²θ₂ is not addressed (the card defines neither R).  
Evidence: `B4Counterexample.B4_display_false` in `RelationalAtlas/Extended10.lean`.

**B49 — refuted (conditional on the cited torsion formula).** The display det Hess(potential) = adjoint torsion does not hold in the card's own Riley coordinates. Conditional on Yoon's two-bridge formula (arXiv:2009.12051, Thm 1.1/3.1) the meridian torsion on the regular figure-eight Riley curve is T = ∓R_u/2, while the one-variable Hessian is R_u under the charitable reading V_u = R and R_uu under the literal V = R; at m = 2, u = (5+√105)/8 the two readings give R_u = √105/4 and R_uu = 2, neither equal to T = ∓√105/8, and the same failure occurs at m = 3, u = (55+√5005)/18, a regular point with disc_u R = 5005/81 ≠ 0. A factor 2 and the chart normalisation are missing from the display, and no choice of torsion sign or of the two potential readings repairs it. The three-name locus also fails at the branch point m₀ = (1+i√3)/2, u = −2: there R = (u+2)² and R_u = 0, while A(−1,m₀) = A_l(−1,m₀) = 0 with A_m ≠ 0 makes the meridian torsion continuation 0, not a pole. The torsion formulas are external inputs; the correctly normalised Neumann–Zagier 1-loop theorem at a regular hyperbolic point is not refuted.  
Evidence: `B49Counterexample.hessian_cannot_equal_torsion_on_regular_curve` and `B49.witness_meridian_torsion_zero` in `RelationalAtlas/Extended10.lean`.

**B58 — overreach.** The log-determinant seam ledger survives exactly: for A = B = [4] and coupling K = 3, μ = K²/(det A det B) = 9/16 and det M = 7 = 16(1−μ), so O(M) = O(A) + O(B) + log(1−μ) ≤ O(A) + O(B) holds — it is the scalar Fischer inequality, and positive definiteness prevents a large-coupling attack. What does not follow is the cone inclusion: for the natural anti-monotone, scale-invariant cone C(o) = {(x,y) : x ≥ 0, |y|e^o ≤ x}, the direction w = (1,1/5) satisfies (1/5)·4 ≤ 1 but (1/5)·7 > 1, so w lies in both part cones and not in the glued one. Subadditivity relative to a sum gives neither O(M) ≤ O(A) nor O(M) ≤ O(B), which is what monotonicity would need. The card leaves C undefined, so this is a countermodel to the displayed inference, not to an unstated cone; the implication is repaired by additionally assuming both part obstructions nonpositive.  
Evidence: `RelationalAtlas.B58.cone_inclusion_fails` in `RelationalAtlas/Extended10.lean`.

**B62 — refuted.** The unqualified clause 'any real secondary parameter must clear 0.080 dex per galaxy' is false. Eight synthetic galaxies with one positive mass m and one positive radius R, exact proxies M/R and M/R² and linear mass control have proxy partial correlation exactly 1, while a separate RAR-residual structural effect has per-galaxy amplitude ±0.0046 dex < 0.080 at ε = 1/1000, compactness partial correlation exactly 23/50 = 0.46 and recovered slope 23/25 ≠ 0; scaling ε shrinks the per-galaxy effect without changing either correlation. So no positive universal dex floor follows from the card's Carry/Check. The source's 0.080 and 0.106 dex are stated as SPARC- and protocol-specific and are neither replayed nor falsified here.  
Evidence: `B62Empirical.unconditional_floor_countermodel` in `RelationalAtlas/Extended10.lean`.

**B62 — clarification.** The correlation half survives and is sharpened: with one common radius and positive exponents, residualising on the mass makes the two log-proxies exact scalar multiples, so their mass-controlled partial correlation is exactly ±1 — +1 when the exponent product is positive, −1 when it is negative, and undefined when the residual variance vanishes (a zero exponent or zero residual radius). The algebra produces no numerical noise floor, which is why the 0.080 dex figure needs its dataset and protocol.  
Evidence: `B62.partialCorr_eq_one` in `RelationalAtlas/Extended10.lean`.

**B76 — scope.** The displayed arithmetic 24 > (n−1)² = 16 at n = 5 is correct, and the blow-up polynomial has exactly 21 critical points, all nondegenerate (origin, two axial, six planar, twelve off-planar), with the exact rational charge q_ε = (3/4)ε³ − (5/32)ε⁵; no counterexample was found, and an independent 6000-start Newton search over the charges' convex hull reproduced the same 24 points with no further equilibrium (residuals ≤ 10⁻¹⁵, numerical evidence rather than a Lean theorem). Two corrections to the prose: the cited theorem (Arathoon–Ball–Kvalheim, arXiv:2607.27197, Theorem 1 and Lemma 2) states at least 24 for all sufficiently small ε and k ≥ 24 after generic perturbation, not an exact global count, so the card must not be read as 'exactly 21 + 3 = 24'; and at the paper's own q_ε the centre is nondegenerate, with Hessian eigenvalues (5ε²/16, 5ε²/16, −5ε²/8), so 'a degenerate critical point unfolds' describes the mechanism at ε = 0, not a property of the origin at the stated charge law. The 21 points sit at scale ε² in the blow-up.  
Evidence: `B76.nonzero_radius_critical_branches` in `RelationalAtlas/Extended10.lean`.

**B53 — provenance.** The pinned HTML displays J_N → Δ_K; the ledger and MMR display 1/Δ_K, and in the normalisation where the comparison is meaningful the inverse is the correct target: with s_n = J_n''(1) = −2(n²−1) for the trefoil the h² coefficient of J_n(exp(h/n)) is exactly s_n/(2n²) = −1 + 1/n² → −1, while Δ_{3₁}(e^h) = 1 + h² + O(h⁴) has h² coefficient +1 and its reciprocal has −1, so the large-colour limit matches 1/Δ_K and not the bare Δ_K printed in the pinned document. The bare Δ is a defect of that document, not of the claim the ledger states.  
Evidence: `B53Domain.mmr_reciprocal_and_html_bare_polynomial_incompatible` in `RelationalAtlas/Extended10.lean`.

**B53 — clarification.** Two limits on the card's reading, both certified. (i) Domain: Δ_{3₁}(z) = z²−z+1 vanishes at ω = (1+i√3)/2, which has |ω| = 1, so a pointwise statement J_N(z) → 1/Δ(z) is undefined at a unit-modulus zero, and the reciprocal series does not converge there; only the formal, power-series reading about z = 0 is well posed. That is a domain obstruction, not an MMR failure. (ii) Determination: 'two shadows of one object' asserts a common source, not a factorisation A = G(Δ); that stronger reading is false — 7₄ and 9₂ share Δ = 4t²−7t+4, while Hoste's two-bridge table gives A(L,1) = (L+1)⁵ and (L+1)⁷, so no G returns both, and the quotient (L+1)² is not a unit in the Laurent ring. The A-polynomial values are an external table input.  
Evidence: `B53.no_A_function_of_Alexander` in `RelationalAtlas/Extended10.lean`.

**B70 — refuted.** The displayed metric dichotomy 'along ⇒ Π constant on the locus, a coordinate pole · across ⇒ Π varies, a genuine stratum' is false in both directions, and the two properties it bundles are independent. F(x,y) = (x, y²) has derivative diag(1, 2y): on the wall the kernel is the transverse y-axis, the wall image (x,0) is nonconstant and the collapsed metric eigenvalue is 4y², yet the kernel projector is diag(0,1) for every x and its Frobenius variation vanishes — across with constant Π. F(x,y) = (y−x², xy−x³) collapses its whole locus to the origin — the card's own 'preimage of a single point' — with the tangent line as kernel, and its orthogonal projector (1/(1+4x²))[[1,2x],[2x,4x²]] has off-diagonal 2x/(1+4x²), so Π varies — along with varying Π. The projector is normalised in the ambient Euclidean inner product, the pullback metric being degenerate at the locus. What survives is the spectral half — gaps 2√(a²+b²) and 2√r, with the geometric fit returning 1 and 1/2 — and the diagnosis that Π's variation is governed by the rotation of the kernel direction along the locus, not by its tangency; the higher-order tangency that gives another exponent is excluded by the card's own Closed field.  
Evidence: `B70Strong.wall_projector_delta_norm` and `B70CurvedPole.poleKernelProjector_not_constant` in `RelationalAtlas/Extended11.lean`.

**B9 — missing-hypothesis.** The Closed sentence 'the winding is defined up to gauge; its value on a closed loop is not' is false for gauges of nonzero winding and true only for gauges continuously deformable to a constant. On the constant family diag(1,−1) and again on the non-constant chiral family [[0,z],[z*,0]] with z = e^{iθ} (gap 2, spectrum ±1 throughout), two closed nowhere-zero representatives of the same eigenline differ by a closed unit-modulus gauge and have displayed integrals 0 and 1. The winding is additive over phase functions, so a gauge of winding n shifts it by n and gauges of zero winding leave it fixed; integrality holds for a fixed closed nowhere-zero loop. The repair is to fix a gauge or to state the invariance modulo the gauge's own winding.  
Evidence: `AtlasB9Comparison.periodic_gauge_changes_displayed_integral` in `RelationalAtlas/Extended11.lean`.

**B29 — clarification.** The displayed exponent (k−d)/2 and the Check's a₁ disagree about which power the ∫R/6 coefficient multiplies. On the unit round sphere the exact spectrum gives Tr e^{−tΔ} = 1/t + 1/3 + t/15 + 4t²/315 + …, which is the series the card's own witness chart plots beside 'a₁ = χ/6 = 1/3'; but in the display index 1 in d = 2 multiplies t^{−1/2}, where the true coefficient vanishes, and 1/3 sits at t⁰, which the display calls a₂. So the card's a₁ is a₂ under its own law (a₀ = 1, a₁ = 0, a₂ = 1/3 on S²). Either renumber, or display the (4πt)^{−d/2} prefactor and then a₀ = Area, a₁ = (1/6)∫R. The values are correct and the substantive claim is untouched.  
Evidence: `B29.unitSphere_curvature_index_discrepancy` in `RelationalAtlas/Extended11.lean`.

**B36 — clarification, and a displayed clause proved.** Writing the wall block on span{diag(1,−1,0), diag(1,1,−2)} as [[λ₁, b],[0, 2t₃]] with λ₁ = 2t₁(1−w₁)+2t₂w₁ and b = 2(t₁−t₃−(t₁+t₂−2t₃)w₁): the joint condition is exactly λ₁ = 2t₃, so JC alone is the repeated-eigenvalue condition, and the block is defective exactly when JC holds and b ≠ 0. Every scalar T lies on the vanishing locus and gives 2sI; at equal weights the block is [[t₁+t₂, t₁−t₂],[0,2t₃]] and is defective exactly when t₁ ≠ t₂. Separately the lift B = J⁻¹AJ with J = diag(1, σ₃) is proved to be a genuine conjugation off the wall, to equal (2t₃)·I at the wall under the joint condition — the display's B(0) = λI — and to be diagonal without it. This matters because the historical 93-card edition of B36 displays '‖R‖ → ∞, Jordan block of size two' at this locus, which is exactly what the v7 card corrects; two members' first verdicts refuted that other document.  
Evidence: `B36m7.lifted_zero_eq_scalar_of_joint` in `RelationalAtlas/Extended11.lean`.

**B58 — referee note.** A tenth-batch referee pass judged the batch-nine cone argument a counterexample to an invented cone rather than to the card: the card defines no admissible cone C, so refuting the inference through one particular cone shows only that the inference is not automatic and needs an explicit monotonicity hypothesis. The record now says so; the log-determinant seam identity itself is unaffected.

**B125 — survived, no correction.** Tr₁₁ = 3R was confirmed three ways — the constant-curvature form-space spectrum R (×1), R/4 (×4), R/6 (×6); the unit S⁴ spectrum 36β + 102β²; and a Lorentzian non-conformally-flat product dS²(k)×S²(l) — so the card keeps its coefficients and no entry is added to the ledger's corrections.
Evidence: `B147` in `RelationalAtlas/Extended8.lean`.

## New kernels added by this audit: `RelationalAtlas/Extended.lean`

A third local module, self-contained (`import Mathlib`) in the style of the other two, holds 178
kernel declarations: the kernels this audit found missing or weak, and one faithful kernel for each
further card whose displayed formula is a finite algebraic statement. Nothing in `Basic.lean` or `AtlasFormalCore.lean` was
edited; every declaration there is preserved byte for byte.

| Card | New declarations | What they add |
| :--- | :--- | :--- |
| B1 / B32 | `card_metric_saturation`, `lagrange_identity`, `gram2_entries`, `gram2_det_eq`, `gram2_det_nonneg`, `b1_two_parameter_saturation`, `b1_curvature_le_metric`, `b1_abs_curvature_le_metric`, `b32_two_parameter_saturation` | the bound `4 det g ≥ Ω²` and its two-parameter saturation `4 det g = Ω²`, `|Ω| = 2√det g`, in the card's own normalization (F1) and in the unnormalized Gram form |
| B13 | `b13_lambda_sq`, `b13_root_iff`, `b13_lambda_ne_zero`, `b13_lambda_ne_neg`, `b13_charpoly`, `b13_charpoly_factor`, `b13_charpoly_root_iff`, `b13_lambda_add_two_pi`, `b13_one_loop_swaps`, `b13_lambda_add_four_pi`, `b13_two_loops_restore`, `b13_z_add_two_pi`, `b13_family_add_two_pi` | one loop swaps the square-root eigenvalue pair, two restore it, while the matrix family itself is already periodic |
| B18 | `capacity_deficit_bound`, `capacity_deficit_eq_iff`, `capacity_log_lower_bound`, `log_cutoff_depth` | the displayed `n − d ≤ log C₀ / log(1/a)` and its equality case |
| B21 | `b21_triality` | `V² + P² + E² = 1` for every normalized two-qubit pure state, with `E` the pure-state concurrence |
| B26 | `jordanBlock₂_charpoly`, `jordanBlock₂_not_diagonalizable`, `jordanBlock₂_normality_defect`, `jordanBlock₂_not_normal`, `scalar₂_charpoly`, `scalar₂_diagonalizable` | coalescence plus loss of diagonalizability, and the scalar matrix as the counterexample to "coalescence is enough" |
| B31 | `offBlock_frobSq_eq_commutator` and its helpers | the Frobenius identity `‖F‖_F = ‖[Ω, Π]‖_F` the ledger had left open (F3) |
| B57 | `orthogonal_tangent_trace_pos`, `obliqueT_null`, `obliquePi_*`, `obliqueT_*` | the trace form is positive definite on the Hermitian tangent space and degenerate on the oblique projector — the card's "zero length, still moving" (F5) |
| B66 | `gram_det_zero_iff` | `{det G = 0} = {det X = 0}` |
| B75 | `balanced_middle_terms_cancel`, `middle_terms_opposite_but_not_cancelled` | the exact cancellation condition and a witness that opposite signs do not cancel (F2) |
| B85 | `rank_one_det_zero_iff` | the determinant vanishes exactly at real parallelism |
| B129 | `complementarity_squared`, `subnormalized_complementarity`, `markerGram_det`, `marker_complementarity`, `gram_det_real_identity`, `unscaled_overlap_counterexample` | `D² + V² = 1`, `det G = D²`, and a counterexample to the unscaled overlap convention |
| B158 | `weak_value_bound`, `postselected_weak_value_sq`, `second_moment_eq_norm_sq` | `p₀|A_w|² ≤ ⟨A²⟩`; an independent local re-proof of a theorem already mapped to `dirac-time-lean` |
| B60 | `b60_dimension_one_forces_two_levels`, `b60_two_levels_force_saturation`, the `Fin 2` identity `4 det g = Ω² + 4|⟨u,v⟩_cross|²`, the complex-parallel criterion, and an n=3, k=2 converse counterexample | B60's saturation criterion and the failure of its converse |
| B87 | `so2_linear_term_forbidden`, `z3_linear_term_allowed`, `conical_gap`, `protected_gap` | the selection rule (which symmetry forbids the linear coupling) and both gap normal forms; the card's holonomy half is not formalized |
| B92 | `phaseWrap`, `prod_eq_exp_sum_log`, `sum_arg_eq_int_mul_two_pi_of_prod_eq_one`, `b92_determinant_discards_wrap`, `det_diagonal_eq_exp_trace_log` | the wrap integer `w = (1/2π)∑ arg λ ∈ ℤ` when `det R = 1`, and `det = exp Tr log` in diagonal form |
| B100 | `echo_circle`, `circle_identity`, `circle_criterion`, `echo_gt_bulk_iff`, `one_radius_cannot_decide`, `b100_concrete_witness` | `|r|² > |a|² ⇔ |x − x_c| > |x_c|` with the card's own `A = 1−|a|⁴`, `C = ā(1−a²)`, `x_c = −C̄/A` |
| B105 | `reduced_associator` and the diagonal-average witness | `(x⋆y)⋆z − x⋆(y⋆z) = P[xQ(yz) − Q(xy)z]`, with a nonzero defect |
| B190 | `complementarity`, `Ve_eq`, `LeSq_eq_zero_iff` (with `a ≠ 0`) | `Pe² + Ve² + Le² = 1` for a scalar edge |
| B199 | `traceless_sq_eq_traceFormQ`, `traceFormQ_eq_zero_iff_sq_eq_zero`, `balanced_iff_nonzero_nilpotent`, `keyMatrix_*`, `oscillatorPart_*`, `orbitMatrix_*` | `T² = q(T)I`, `q = ½(‖Herm T‖² − ‖Skew T‖²)`, `q = 0 ∧ T ≠ 0 ⇔` nonzero nilpotent, with `q = h² − r²`, `ω²(ζ²−1)`, `−κ²` |

B199 deserves one remark beyond its row. Its kernel is the shared wall: for a *traceless* 2×2
operator the trace form `q` vanishes exactly when the square does, so "on the wall" and "a nonzero
nilpotent" are the same condition — the spinning key, critical damping and the ISCO
(`[[0,1],[−k²,0]]` at `k = 0`) are instances of it, and a complex instance uses the same criterion
over `ℂ`. The formalisation covers the criterion and the three model families; it does not cover
the unfolding constants. If those are `√2` for a complex wall and `√2/18` for the ISCO, the ratio
is 18, not 36, and any text saying otherwise should be checked before it is published.

The module ends with `#print axioms` for every declaration; all of them rest on a subset of
`{propext, Classical.choice, Quot.sound}`. `scripts/verify_local.py` elaborates it as a third
library module, so it is covered by the same checks as the other two. Both extension modules are now records in
`atlas/coverage/coverage.json`: every one of their declarations is mapped to its card (178 for
`Extended.lean`, 229 for `Extended2.lean`, 444 in total with the original 37), the ledger's
summary now reads 49 locally mapped cards and 116 still unmapped, and
`python3 scripts/verify_coverage.py --self-test` passes before and after the change.

## Independent checks against external databases (23 November 2026)

Two families of card claims are *computational* rather than algebraic, and were re-checked
outside Lean against published data.

**B146 — "the permutation coboundary constant of the complete complex is k/3."** The pinned
snapshot `atlas/coverage/external/coboundary-k3-lean/CoboundaryK3/Basic.lean` proves, for the
witness cochains `w4 … w8`, the triangle defect `N`, the gauge minimum `D` and `N/D = k/3`, by
exhaustive `decide +kernel` over all `6^(k−1)` gauges. That computation was redone independently
in GAP 4.14.0 (`/opt/math/bin/gap`, script `.scratch/b146.g`, 7 s): with `S3` acting on three
points, the defect `N = Σ_{u<v<w} moved(α(u,v)α(v,w)α(w,u))` and the minimum gauge cost
`D = min_β Σ_{u<v} moved(β(u)⁻¹α(u,v)β(v))` reproduce the Lean values exactly —

| k | N (GAP) | D (GAP) | N/D | Lean `N`, `D` |
| --- | --- | --- | --- | --- |
| 4 | 8 | 6 | 4/3 | 8, 6 |
| 5 | 10 | 6 | 5/3 | 10, 6 |
| 6 | 36 | 18 | 2 | 36, 18 |
| 7 | 28 | 12 | 7/3 | 28, 12 |
| 8 | 72 | 27 | 8/3 | 72, 27 |

(GAP composes permutations in the opposite order to Lean's `*`; the defect and cost products were
therefore written reversed, and `moved` counts images `c^s ≠ c`. The first two attempts at this
script were wrong for exactly those two reasons and disagreed with Lean before they were fixed —
which is what makes the agreement evidence rather than a restatement.)

**B51 — "a root sits on the circle iff the reduced polynomial has a real root in [−2, 2]".**
Checked on every Alexander polynomial in KnotInfo (release 2026.11.2, crossings ≤ 10: 249
polynomials of degree ≥ 1, all reciprocal). For each, `q(u) = c_g + Σ_{j≥3} c_{g+j} S_j(u)` with
`S_j = t^j + t^{-j}` was formed symbolically and `p(t) = t^g q(t+1/t)` verified as a polynomial
identity — 249/249 — and the number of real roots of `q` in `[−2, 2]` counted by Sturm sequences:
184 polynomials have one, 65 do not. Examples: `3_1`, `Δ = 1 − t + t²`, `q = u − 1` (root 1, on
the circle); `4_1`, `Δ = 1 − 3t + t²`, `q = u − 3` (no root in the interval); `5_2`,
`q = 2u − 3`; `8_20`, `q = (u − 1)²`. A float64 root-finding version of this check first
"disagreed" on 7 clustered polynomials; exact polynomial arithmetic resolved all 7 in the
criterion's favour, so the disagreement was numerical, not mathematical.

**B7 — "the square knot has a double root there and a signature identically zero."** KnotInfo
gives `Δ(3_1) = 1 − t + t² = Φ₆(t)` and `σ(3_1) = −2`. The square knot's Alexander polynomial is
`Φ₆²`, whose roots are the primitive sixth roots of unity, each double and each on `|t| = 1`; and
`σ(3_1 # m3_1) = −2 + 2 = 0` by additivity of the signature under connected sum (a cited theorem,
not proved here). The card's example is consistent with the data.

**B11 — the two displayed volumes.** KnotInfo (release 2026.11.2) gives the figure-eight
`4_1` volume as `2.0298832128`, matching the card's "2.029883…"; LinkInfo gives the Whitehead
link `L5a1{1}` volume as `3.66386237670887604523`, and `4G = 3.66386237670888` with Catalan's
constant, so the card's "4G" is the same number to fifteen digits. The arithmetic *field* of the
shapes (Eisenstein vs Gaussian), which is what the card uses to predict the absence of a
relation, is not something these tables contain and was not verified here.

SnapPy 3.3.2 (installed with approval in `.venv-snappy`, census data 1.4, SageMath present) gives
both volumes again with interval verification, which is stronger than a numerical estimate:

| manifold | verified volume | verified hyperbolic | CS/(2π²) |
| :--- | :--- | :--- | :--- |
| `4_1` (figure-eight) | `2.0298832128193?` | yes | `0.00000000` |
| `L5a1` (Whitehead link) | `3.6638623767089?` | yes | `−0.12500000` |

So the card's `2.029883…` and `4G` are certified to 13–14 digits, and `CS = −π²/4` for the
Whitehead link is an extra fact the card does not display.

**Not checked.** The knots in B10's Riley-polynomial identity are not named in the published card
text, and KnotInfo carries no Riley polynomials, so that identity was not re-checked against data.
No card's claim was checked against LMFDB or the Erdős problems database: the corpus makes no
number-field or Erdős-problem assertion that those databases could confirm or refute.
