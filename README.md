<div align="center">

# The Operator-First Relational Atlas — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-37-2EA043)
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

The ledger maps kernels for 19 cards to this repository and 21 additional cards to seven
companion repositories. The remaining 167 cards are not yet mapped within that audited scope.
These are card counts, not theorem counts or full-card certifications. The local library remains
37 declarations. Proved kernels, empirical witnesses, interpretations and remaining obligations
are recorded separately. The historical 93-card files below remain preserved.

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

## The Atlas itself

The cards, the moves and the version audit live in [`atlas/`](atlas/README.md): the 93-card
edition of 7 September 2026 (open `atlas/cards/index.html` locally), the method and standing-rule
plates transcribed from the volume, and the audit of 14 October 2026 that locates every edition
and tells the three things called "Atlas" apart. The 37 theorems here are the 16 bridge proofs in
`Basic.lean` plus the 21 card kernels in `AtlasFormalCore.lean`.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and seven deliberately false statements that must fail.

## The paper

*The Operator-First Relational Atlas*, Jeromie Beasley. DOI
[10.5281/zenodo.21972561](https://doi.org/10.5281/zenodo.21972561) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
