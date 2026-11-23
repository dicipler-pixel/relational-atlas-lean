# Audit of the local Lean kernels

Jeromie Beasley's Operator-First Relational Atlas, local library only.
Audit run of 23 November 2026 on the toolchain installed in the VM:
**Lean 4.35.0 with Mathlib 4.35.0**. The repository pins `leanprover/lean4:v4.34.1`
in `lean-toolchain` and `rev = "v4.34.1"` in `lakefile.toml`; the proofs were
re-elaborated here on the newer toolchain, which is a stricter test in the sense
that it compiles the same sources against a different Mathlib, and a weaker one
in the sense that it is not the pinned CI environment.

## What was run

| Command | What it establishes |
| :--- | :--- |
| `python3 scripts/verify_local.py` | Elaborates the two library modules, every pinned external snapshot and every false control; audits `#print axioms` for all local theorems; rejects `sorry`/`admit`/`axiom`; requires each control to fail for a mathematical reason. |
| `python3 scripts/verify_coverage.py --self-test` | All 207 card records, the 41 pinned external snapshots and the metadata tamper controls. |
| `python3 atlas/cards/calculus/verify_atlas_calculus.py` | The finite calculus companion: 40 deterministic cochains, exact rational identity; `all_passed: true`. |

## Result

Final run of `python3 scripts/verify_local.py` (23 November 2026, Lean 4.35.0): three library
modules, 41 pinned external snapshots, 7 false controls, **368 theorem declarations audited**
(37 in the ledger modules, 178 in `Extended.lean`, 153 in `Extended2.lean`).

* **37/37** ledger theorems elaborate with zero errors, and so do all 331 extension theorems
  (`Extended.lean` 178, `Extended2.lean` 153; the latter adds B37, B86, B89, B116, B128, B131,
  B133, B142, B148, B155, B180 and B202).
* **37/37** axiom audits return a subset of `{propext, Classical.choice, Quot.sound}`;
  no `sorryAx`, no `Lean.ofReduceBool`, no project axiom.
* **0** occurrences of `sorry`, `admit` or `axiom` in the compiled local sources.
* **7/7** false controls are rejected, each with a mathematical failure
  (`unsolved goals`, `linarith failed`, …), not a name or syntax error. This needs a caveat:
  the controls import the library, so in a standalone check the library objects must be built
  first. The first version of the harness did not do that and every control failed at the import
  instead — a green "rejected" that proved nothing. `scripts/verify_local.py` now builds
  `Basic`/`AtlasFormalCore` objects with `lean -o` before running the controls.
* **0** of the 37 local statements is false as written. Two statements are weaker
  than their names or docstrings suggest (F1, F2 below), and four card claims that
  the ledger lists as open are now closed by the additions listed under "New
  kernels".

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
  snapshots are not all independently compilable. Of the 41 snapshots, 32 elaborate standalone on
  Lean 4.35.0. Four cannot elaborate from this repository at all because they import a sibling
  module that was never pinned — `DiracTime/FiniteReturn.lean` needs `DiracTime.PredictiveQuotient`,
  `LightBridges/Census.lean` needs `LightBridges.Algebra`,
  `NonNormality/SelfCommutator.lean` needs `NonNormality.Frobenius`, and
  `NonNormality/Holonomy.lean` needs `NonNormality.SelfCommutator`. Three more need only module
  resolution, because their sibling *is* pinned (`LightSpectral.lean` ← `Rigidity.lean`,
  `SquareCase/Secular.lean` ← `SquareCase/Transport.lean`, `VOTKP/Film.lean` ← `VOTKP/Smith.lean`);
  I built the sibling object in the right module path and put it on `LEAN_PATH`, and all three then
  elaborate cleanly (`Rigidity` 29 s, `Transport` → `Secular` 4 min under load, `Smith` → `Film`
  2 min), which raises the count of snapshots that can be checked from 32 to 35. Two timed out at 900 s under this VM's load
  (`CoboundaryK3/Basic.lean`, which takes 96 s and peaks at 7.5 GB resident when run alone, and
  `DiracTime/MovingFrame.lean`). Every card that depends on one of those nine snapshots therefore
  rests on a citation and a pinned hash, not on a fresh elaboration.
* It does not certify the 136 cards the ledger lists as unmapped, nor the card
  count "37 theorems" against anything but `scripts/config.json`.


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
library module, so it is covered by the same checks as the other two. It is committed as `8fb0e1a`
(together with this audit and `scripts/verify_local.py`), but it is **not** yet a record in
`atlas/coverage/coverage.json`: that ledger requires every declaration of every configured module
to be mapped to a card, so registering the module means writing 178 card mappings at once. That is
a mechanical but separate change; until it is made, the ledger still covers the original 37.

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
