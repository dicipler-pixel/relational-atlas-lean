<div align="center">

# The Operator-First Relational Atlas — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.35.0-blue)
![Theorems](https://img.shields.io/badge/theorems-3045-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21972561-blue)](https://doi.org/10.5281/zenodo.21972561)

Jeromie Beasley

</div>

---

## Current 207-card edition and proof coverage

The published [continuous edition v4 / card set v7, B1–B207](https://doi.org/10.5281/zenodo.23590925)
has a [complete card-by-card Lean coverage ledger](atlas/coverage/README.md), with
[machine-readable claims, hypotheses and proof links](atlas/coverage/coverage.json).
The source archive and continuous HTML were matched to the Zenodo checksums on 23 October 2026.

The ledger maps kernels for 137 cards to this repository and 40 additional cards to sixteen
companion repositories. The remaining 30 are 23 `measured`, 6 `reading` and 1 `derived`: **every
card graded `theorem` now has a local kernel**, seven of them added by the tenth batch, and the
ledger gives its reason per card for each of the 30 that remain. These are card counts, not theorem
counts or full-card certifications. The local library is 3045 theorem declarations across thirteen
modules. Proved kernels, empirical witnesses, interpretations and remaining obligations are
recorded separately. The historical 93-card files below remain preserved.

Run the ledger integrity check with `python3 scripts/verify_coverage.py --self-test`.
This checks evidence and mappings; the separate Lean workflow checks the actual proofs.

## The idea in one line

The Atlas links its strata by numbered bridges, each graded. This repository takes the bridges
graded THEOREM whose content is finite algebra and checks each one in Lean.

## What is proved

| Bridge | Result | Theorem |
| :--- | :--- | :--- |
| B2 | `H Hᵀ − Hᵀ H = −2[S, K]` for `H = S + K`; `H` is normal exactly when `S` and `K` commute | `normal_commutator`, `normal_iff_commute` |
| B6 | Binary entropy: zero at certainty, symmetric, nonnegative, at most `log 2`, equal to `log 2` at `ν = 1/2` | `binary_entropy` |
| B31 | `F = ΠΩ(1−Π) + (1−Π)ΩΠ` is traceless and vanishes exactly when `[Ω, Π] = 0` | `offBlock_trace`, `offBlock_eq_zero_iff` |
| B39 | For `κ > 0` and `sin θ₁ ≥ 0`, `κ sin²θ₁ > 1 ⇔ sin θ₁ > √(1/κ)`; at `θ₂ = π/2 + iy` the sine is `cosh y` and the cosine is purely imaginary | `critical_angle`, `complex_angle_sin`, `complex_angle_cos` |
| B48 | The seam determinant is a Schur complement | `seam_schur` |
| B51 | `at⁴+bt³+ct²+bt+a = t²(au²+bu+(c−2a))`, `u = t + 1/t`; unit-circle roots give `u = 2cos φ ∈ [−2,2]`, and every `u ∈ [−2,2]` comes from a unit-circle `t` | `reciprocal_reduction`, `unit_circle_u`, `u_from_unit_circle` |
| B66 | `det(XᵀX) = (det X)²` | `gram_det` |
| B68 | A chirality `σ` (`σ² = 1`, `σD = −Dσ`) sends each `λ`-eigenvector `v` of `D` to the nonzero `−λ`-eigenvector `σv` | `paired_spectrum` |
| B74 | `g sin²θ = C`, `g ≥ 0` force `g ≥ C`: a degenerate stratum repels | `stratum_repels` |
| B75 | Extremal bands' pair terms share a sign; the middle band's have opposite signs | `middle_cancels` |

The file is [`RelationalAtlas/Basic.lean`](RelationalAtlas/Basic.lean).

### The Atlas card core

[`RelationalAtlas/AtlasFormalCore.lean`](RelationalAtlas/AtlasFormalCore.lean) holds the finite
kernels of the Atlas cards, 21 theorems, kept byte-for-byte as they were first checked. Some
restate bridges above in a second form; these are new here:

| Bridge | Result | Theorem |
| :--- | :--- | :--- |
| B2/B64 | `(S+K)(S−K) − (S−K)(S+K) = −2[S,K]` in any ring; zero when `S`, `K` commute | `symmetric_skew_commutator_identity`, `symmetric_skew_commute_gives_zero` |
| B31 | A tangent `D` to `P² = P` has zero diagonal blocks and splits as `PD(1−P) + (1−P)DP` | `tangent_occupied_block`, `tangent_empty_block`, `tangent_split` |
| B16 | For unit vectors in `ℝ²`, half the squared Frobenius distance of `uuᵀ` and `vvᵀ` is `1 − ⟨u,v⟩²` | `rankOne_projector_distance` |
| B32 | Lagrange's identity in the metric/curvature normalization | `gram2_saturation` |
| B48 | One-channel Schur complement `ad − bc = d(a − b d⁻¹ c)` | `scalar_schur_complement` |
| B51 | Reciprocal quartic reduction in `u = t + 1/t` | `reciprocal_quartic_reduction` |
| B56 | A linear map `ℝ² → ℝ³` is never surjective: a wall meeting the coalescence locus is nontransverse | `b56_combined_derivative_not_surjective` |
| B57 | The indefinite form `x² − y²` has the nonzero null direction `(1, 1)` | `indefinite_null_direction_exists` |
| B60 | `k(n−k) = 1` forces both factors to be one | `tangent_dimension_one_factors` |
| B61 | `(ħ/(α m c))·m = ħ/(α c)` | `bohr_rod` |
| B66 | `det(XᵀX) = (det X)²` | `gram_det_is_square` |
| B68 | If `DΓ = −ΓD` and `Dv = λv`, then `D(Γv) = −λ Γv`; this form does not assume `Γ² = 1` and does not prove `Γv ≠ 0` (B68 above does) | `chiral_eigenvalue_pair` |
| B74 | `g sin²θ = C`, `g ≥ 0`, `sin²θ ≤ 1` give `C ≤ g` | `refraction_turning_barrier` |
| B85 | `(x²−y²)(s²−t²) − (xs−yt)² = −(xt−ys)² ≤ 0` | `rank_one_complex_realpart_det`, `rank_one_complex_realpart_not_definite` |
| B90 | The normal forms `√(t²) = \|t\|`, `(√\|t\|)² = \|t\|`, and a simple crossing changes sign | `hermitian_soft_lapse`, `open_soft_crosses`, `open_lapse_square` |

Bridges proved in the
other repositories: B1 in [iqgt-grassmannian-lean](https://github.com/dicipler-pixel/iqgt-grassmannian-lean), B12 and B38 in [foft-lean](https://github.com/dicipler-pixel/foft-lean), B16
in [price-of-a-direction-lean](https://github.com/dicipler-pixel/price-of-a-direction-lean), B45
and B82 in [spectral-stress-lean](https://github.com/dicipler-pixel/spectral-stress-lean), B61 in
[matter-at-a-scale-lean](https://github.com/dicipler-pixel/matter-at-a-scale-lean). What is not
proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## Extensions and audit (23 November 2026)

[`RelationalAtlas/Extended.lean`](RelationalAtlas/Extended.lean) adds 178 further kernel
declarations, each still a finite statement of one card: B1/B32 in the card's own
normalization, the B13 half-angle monodromy, the B18 deficit bound, B21's `V²+P²+E² = 1`,
B26's Jordan block, the B31 Frobenius identity `‖F‖_F = ‖[Ω,Π]‖_F`, B57's oblique projector,
B66/B85 zero sets, B75's exact cancellation condition, B92's wrap integer, B100's echo circle,
B105's reduced associator, B122's semigroup norm, B129's complementarity budget, B158's
weak-value bound, B190's three-way budget, and B199's traceless trace form `T² = q(T)I` with
`q = 0 ∧ T ≠ 0` exactly the nonzero nilpotents — the wall shared by the spinning key, critical
damping and the ISCO. The module is self-contained, ends with `#print axioms` for every
declaration, and rests only on `propext`, `Classical.choice` and `Quot.sound`.

A second batch lives in [`RelationalAtlas/Extended2.lean`](RelationalAtlas/Extended2.lean) (229 further declarations): B37's finite trace sum, B86's reciprocity witness, B89's vanishing first-order
response, B116's permutation distance, B128's δ+g² ≤ 4, B131's divided-difference bracket, B133's
mixed-channel census, B142's Christoffel data, B148's tensor composition, B155's
diag(cos²ϑ,1) spectrum, B180's factor eight, B202's one-way resolvent, B78's spectral calculus,
B72's off-block projector derivative, B186's quarter-turn sector flip, and B44's five-sector
count with the lift bound. Both extension modules
are checked by `scripts/verify_local.py` under the same rules as the original two.

A third batch, [`RelationalAtlas/Extended3.lean`](RelationalAtlas/Extended3.lean) (262 further
declarations), was asked for each card to state its own displayed formula and then try to break it.
Several sections are refutations followed by the corrected statement: B15's raw comparator is not
subadditive, B132's dichotomy needs `F` symmetric, B44's ledger square is false, B54's `det g > 0`
does not certify a metric, B154 needs a Hermitian `K`, B119's coefficient is the Killing
specialization, B171's hidden block is only line-valued, and B183's ⅛ identity needs unitary edge
blocks rather than merely skew-Hermitian ones. The full list, with the theorem that
settles each, is in [atlas/coverage/LOCAL_KERNEL_AUDIT.md](atlas/coverage/LOCAL_KERNEL_AUDIT.md).

A fourth batch, [`RelationalAtlas/Extended4.lean`](RelationalAtlas/Extended4.lean) (314 further
declarations, 16 cards: B20, B24, B25, B46, B91, B109, B152, B173, B177, B179, B181, B194, B195,
B198, B203, B207), includes three more refutations and the corrections they forced:

- **B91** — `Q ⪰ 0 ⟺ g₁₁ ≥ 0 ∧ 4 det g ≥ |Ω|²` fails at `g₁₁ = 0` (`Q = diag(0,−1)` passes both
  conditions); adding `0 ≤ d` repairs it, and the card's form is exact when `a > 0`.
- **B25** — the card's `χ` is per level; the summed version is exactly twice it at two levels, so
  the per-level value `1/δ²` is supplied separately from the double sum's `2/δ²`.
- **B198** — the auxiliary conjugation carries the wrong sign on `σ_y` (the book energies are
  unaffected).

A fifth batch, [`RelationalAtlas/Extended5.lean`](RelationalAtlas/Extended5.lean) and
[`RelationalAtlas/Extended6.lean`](RelationalAtlas/Extended6.lean) (188 + 19 declarations), closed
the sixteen gaps that stood between the kernels and whole-card certification, and closed two of them
by refutation: B67's unrestricted lift claim is false (a closed loop can fail to lift even when
regular and collision-free, though the isotropy threshold `r ≤ d−2` is exact), and B169's −0.99
correlation floor does not exist (the correlation moves with the precision profile, while the
card's measured −0.999475 stays unverified rather than refuted). The rest are closures: B24 in every
dimension, B145's boundary, B207's extremal hole, B156's pole indices as an exact winding, B158's
equality case, B77's two thresholds, B93's invariance hypothesis, B60's converse, B15's 1/(2√2)
constant shown to belong to √S, B152's spectral clauses, B112's one-zero case, B119's full symbol
and B181's missing join.

A sixth batch, [`RelationalAtlas/Extended7.lean`](RelationalAtlas/Extended7.lean) (579 further
declarations), covers the two-books block B185–B206, and five of its cards needed correction:

- **B185** — nonunitary transport does *not* imply non-stochastic weights: the constant `(1+i)/2`
  matrix has all weights `1/2` and `W` doubly stochastic. The converse is true, so the correct
  statement is an implication.
- **B196** — minimality of the recurrence solution holds at `|c| = 2` as well, so the criterion is
  `|λ| ≥ 2√q`; the boundary witness is graph-realised by a `C₄` adjacency matrix.
- **B200** — the explanation's shift is `−hI`, not `+hI`: `Herm(Z + I) = diag(2,0)` at the
  card's own witness, and the corrected companion identity is proved.
- **B205** — "odd blocks only" is false: in the card-allowed dimer limit an even block carries
  `C_B = ½·I₂`, two half modes.
- **B191** — uncentered linear terms cannot be dropped (one scalar edge gives 16 against 8), and
  uncentered balance (`ρ = 0`) differs from `k/r`-centered balance (`ρ = k/r`).

The rest are proofs: B187's loop-kernel equivalence, B188's two exact minima (`(N/2)(1−cos π/N)`
and `0`), B189's rapidity, B192's bipartiteness criterion in both directions, B193's integer
minimisation with the parity split, B197's zeta pencil, B201's `−32` derivative laws, B204's Schur
factorisation and the ½ protection condition, plus a shared matrix kernel for the block.

Seventh and eighth batches, [`RelationalAtlas/Extended8.lean`](RelationalAtlas/Extended8.lean)
and [`Extended9.lean`](RelationalAtlas/Extended9.lean) (295 + 254 declarations, 26 cards), took the
remaining theorem-grade cards. Three more corrections:

- **B28** — the SLD tensor is `Q = F/4 + C/8`, not `F/4 − iC/8`: at `ρ = diag(3/4,1/4)`,
  `L₁ = σ_x`, `L₂ = σ_y` the card's right side is `1/8` while `Q = i/8`.
- **B121** — the Jordan criterion drops `A₁₂ ≠ 0`: at `t₁=t₂=t₃=1, w=(½,½,0)` the displayed
  equality holds and the transport is `2H`, diagonalizable.
- **B143** — "all rates `ε⁻¹`" fails for the mixed eigenvalues; no `c/ε` lower bound exists.

The rest are proofs across B7, B27, B55, B65, B73, B79, B81, B84, B88, B94, B101, B115, B117,
B118, B126, B147, B150, B151, B157, B172, B176, B182. Batch eight also ran six referee audits of
batch six, which found one error in this repository's own ledger wording (B185) rather than in the
maths.

A ninth batch, [`RelationalAtlas/Extended10.lean`](RelationalAtlas/Extended10.lean) (303 further
declarations, the seven cards still unmapped), was a counterexample hunt rather than a proof batch:
the Atlas grades these cards `conjecture`, so each was transcribed, given the sharpest reading that
is still literal, and attacked. Nothing in the earlier modules was modified.

- **B4 — refuted.** `½‖Π₁−Π₂‖²_F = Σ sin²θᵢ`, which the card calls a theorem, fails without an
  equal-rank hypothesis: `Π₁ = diag(1,0,0)`, `Π₂ = diag(1,1,0)` in ℝ³ give `½` against `0` (or `1`
  with padded `π/2` angles). The repair `½‖Π₁−Π₂‖²_F = Σ_{i≤min(p,q)} sin²θᵢ + |p−q|/2` is proved at
  the level of traces (given `trace P = p`, `trace Q = q`, `trace(PQ) = Σ cos²θᵢ`), and the card's
  identity is exactly the equal-rank case.
- **B49 — refuted, conditionally.** With Yoon's two-bridge torsion formula as input, the torsion on
  the regular figure-eight Riley curve is `∓R_u/2` while either reading of the one-variable Hessian
  gives `R_u` or `R_uu`; regular witnesses at `m = 2` and `m = 3` fail for both readings and both
  torsion signs, and at the branch point `m₀ = (1+i√3)/2, u = −2` the Hessian degenerates while the
  torsion continuation is `0`, not a pole. The correctly normalised Neumann–Zagier theorem is not
  addressed.
- **B62 — refuted.** The unqualified "any real secondary parameter must clear 0.080 dex per galaxy"
  fails: eight synthetic galaxies with one mass and one radius have proxy partial correlation
  exactly `1`, while a separate structural effect of `0.0046 dex` per galaxy carries compactness
  correlation exactly `23/50 = 0.46` and a nonzero recovered slope. The source's SPARC-specific
  numbers are not replayed.
- **B58 — overreach.** The log-det seam identity and its subadditivity hold (`A = B = [4]`,
  coupling `3`, `μ = 9/16`, `det M = 7`); the inference to `C(A∪B) ⊇ C(A) ∪ C(B)` does not, for the
  natural anti-monotone cone: `(1,1/5)` is in both part cones and not in the glued one.
- **B76 — scope.** The count survives: exactly 21 critical points of the blow-up polynomial, all
  nondegenerate, plus three edge points, against `(n−1)² = 16` at `n = 5`. The cited theorem says
  *at least* 24, and at the paper's own `q_ε` the centre is nondegenerate.
- **B53 — provenance and clarification.** The pinned HTML's bare `Δ` should be `Δ⁻¹` (the ledger has
  it right); the pointwise reading is undefined at `ω = (1+i√3)/2`, a unit-modulus zero of `Δ_{3₁}`;
  and the stronger reading "`Δ` determines `A`" is false — `7₄` and `9₂` share `Δ = 4t²−7t+4` but
  have `A(L,1) = (L+1)⁵` and `(L+1)⁷`.
- **B125 — survived.** `Tr₁₁ = 3R` and the second-order coefficients were confirmed three ways: the
  form-space spectrum `R, R/4 (×4), R/6 (×6)`, the unit `S⁴` spectrum `36β + 102β²`, and a
  Lorentzian non-conformally-flat product.

A tenth batch, [`RelationalAtlas/Extended11.lean`](RelationalAtlas/Extended11.lean) (397 further
declarations, the last seven cards graded `theorem` with no kernel), tested a different failure
mode. Every card had two or more members with opposite orders of work — one built the weakest
reading a careless reader would accept as "the card" and refuted it first, the other attacked the
card's own claim first — and each then swapped roles. Two referees re-derived the results
independently. The outcome, per card:

- **B70 — refuted.** The displayed metric dichotomy fails in both directions. `F(x,y) = (x,y²)` has
  a transverse wall kernel, a nonconstant wall image and the quadratic collapsed eigenvalue, yet
  the kernel projector is `diag(0,1)` for every `x`; `F(x,y) = (y−x², xy−x³)` collapses its whole
  locus to a point, the card's own coordinate pole, yet its tangent-kernel projector
  `(1/(1+4x²))[[1,2x],[2x,4x²]]` varies. The two properties the card bundles — constant projector,
  one-point preimage — are independent; what governs the projector is the rotation of the kernel
  direction along the locus. The spectral half survives.
- **B9 — missing hypothesis.** The closed-loop winding is invariant under gauges of zero winding and
  shifts by the gauge's own winding otherwise: on `[[0,z],[z*,0]]` with `z = e^{iθ}` two closed
  representatives of one eigenline have integrals `0` and `1`.
- **B29 — clarification.** The Check's `a₁ = (1/4π)∫R/6` sits at `t⁰` under the displayed power law,
  which the card calls `a₂`; the card's own witness chart plots `1/3` at the constant term. The
  values are right, the indexing is not.
- **B36 — clarification, and a clause proved.** The wall block is defective exactly when the joint
  condition holds *and* the off-diagonal is nonzero; scalar `T` is a diagonalisable boundary. The
  lift `B = J⁻¹AJ` is proved to be a genuine conjugation and to equal `(2t₃)I` at the wall under the
  joint condition — the display's `B(0) = λI`.
- **B11, B140, B164 — survived.** The figure-eight shape and the vanishing correction term; the
  displayed projector bound for circular contours with the perturbed inverse constructed as a
  Neumann series, plus the exact `(1+η)/(2√η)` blowup of the individual idempotents at fixed margin;
  and the Pauli-current identity, proved twice independently for arbitrary spinor and real `A`.

Two scope corrections came out of the same batch. The commoner failure was a real computation
against an invented reading: both B36 `REFUTED` verdicts initially attacked a display belonging to
the historical 93-card edition, and the pinned v7 archive — now obtained from the DOI and verified,
`archive_verified: true` — says the opposite about curvature at that locus. And a referee pass
judged batch nine's B58 cone argument a counterexample to an invented cone rather than to the card,
which is how its record now reads.

Partial or guarded: B24's equality of the two `c₂` forms needs Hermitian `E`; B207 does not treat
the extremal `Q = M`; B46's local HTML and the ledger describe different documents.  Each is
recorded with the theorem that settles it.

What each kernel covers and what it does not is tabulated per card in
[atlas/coverage/CERTIFICATION.md](atlas/coverage/CERTIFICATION.md), generated from the ledger by
`scripts/build_certification.py`: 137 cards have a kernel in this repository, 40 only in a companion
repository, and every card keeps `full_card_certified: false`, which the validator requires.

The full statement audit is in [atlas/coverage/LOCAL_KERNEL_AUDIT.md](atlas/coverage/LOCAL_KERNEL_AUDIT.md):
37/37 ledger declarations elaborate and are axiom-clean, none is false as written, two are
weaker than their names suggest (B32's normalization, B75's "cancels"), the axiom audit now
covers all 37 (five had no `#print axioms` line), and the B146 and B51 computational claims were
recomputed independently — B146 in GAP 4.14.0, B51 against every KnotInfo Alexander polynomial
of degree ≥ 1 with at most 10 crossings. `scripts/verify_local.py` reproduces the elaboration,
axiom and false-control checks without Lake, using the toolchain installed in the VM
(Lean 4.35.0 / Mathlib 4.35.0; the repository still pins v4.34.1 for CI).

## The Atlas itself

The cards, the moves and the version audit live in [`atlas/`](atlas/README.md): the 93-card
edition of 7 September 2026 (open `atlas/cards/index.html` locally), the method and standing-rule
plates transcribed from the volume, and the audit of 14 October 2026 that locates every edition
and tells the three things called "Atlas" apart. The 37 theorems here are the 16 bridge proofs in
`Basic.lean` plus the 21 card kernels in `AtlasFormalCore.lean`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.35.0 and
Mathlib v4.35.0, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and seven deliberately false statements that must fail.

`scripts/ci_local.sh` reproduces the same three steps without GitHub, by copying the installed
Mathlib to a writable directory and pointing a scratch copy of the project at it. The last local
run (25 November 2026, after the ninth batch): `lake build` completed **9059 jobs**, `leanchecker`
replayed all twelve modules including `Extended10`, and `verify.py` reported **2648 theorems** with
the seven controls rejected.

## The paper

*The Operator-First Relational Atlas*, Jeromie Beasley. DOI
[10.5281/zenodo.21972561](https://doi.org/10.5281/zenodo.21972561) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
