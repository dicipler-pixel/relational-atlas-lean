<div align="center">

# The Operator-First Relational Atlas — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/relational-atlas-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-16-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21972561-blue)](https://doi.org/10.5281/zenodo.21972561)

Jeromie Beasley

</div>

---

## The idea in one line

The Atlas links its strata by numbered bridges, each graded. This repository takes the bridges
graded THEOREM whose content is finite algebra and checks each one in Lean.

## What is proved

| Bridge | Result | Theorem |
| :--- | :--- | :--- |
| B2 | `H Hᵀ − Hᵀ H = −2[S, K]` for `H = S + K`; `H` is normal exactly when `S` and `K` commute | `normal_commutator`, `normal_iff_commute` |
| B6 | Binary entropy: zero at certainty, symmetric, nonnegative, at most `log 2`, equal to `log 2` at `ν = 1/2` | `binary_entropy` |
| B31 | `F = ΠΩ(1−Π) + (1−Π)ΩΠ` is traceless and vanishes exactly when `[Ω, Π] = 0` | `offBlock_trace`, `offBlock_eq_zero_iff` |
| B39 | `κ sin²θ₁ > 1 ⇔ sin θ₁ > √(1/κ)`; at `θ₂ = π/2 + iy` the sine is `cosh y` and the cosine is purely imaginary | `critical_angle`, `complex_angle_sin`, `complex_angle_cos` |
| B48 | The seam determinant is a Schur complement | `seam_schur` |
| B51 | `at⁴+bt³+ct²+bt+a = t²(au²+bu+(c−2a))`, `u = t + 1/t`; unit-circle roots give `u = 2cos φ ∈ [−2,2]`, and every `u ∈ [−2,2]` comes from a unit-circle `t` | `reciprocal_reduction`, `unit_circle_u`, `u_from_unit_circle` |
| B66 | `det(XᵀX) = (det X)²` | `gram_det` |
| B68 | A chirality `σD = −Dσ` pairs each eigenvalue `λ` with `−λ` | `paired_spectrum` |
| B74 | `g sin²θ = C`, `g ≥ 0` force `g ≥ C`: a degenerate stratum repels | `stratum_repels` |
| B75 | Extremal bands' pair terms share a sign; the middle band's have opposite signs | `middle_cancels` |

The file is [`RelationalAtlas/Basic.lean`](RelationalAtlas/Basic.lean). Bridges proved in the
other repositories: B1 in [iqgt-grassmannian-lean](https://github.com/dicipler-pixel/iqgt-grassmannian-lean), B12 and B38 in [foft-lean](https://github.com/dicipler-pixel/foft-lean), B16
in [price-of-a-direction-lean](https://github.com/dicipler-pixel/price-of-a-direction-lean), B45
and B82 in [spectral-stress-lean](https://github.com/dicipler-pixel/spectral-stress-lean), B61 in
[matter-at-a-scale-lean](https://github.com/dicipler-pixel/matter-at-a-scale-lean). What is not
proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*The Operator-First Relational Atlas*, Jeromie Beasley. DOI
[10.5281/zenodo.21972561](https://doi.org/10.5281/zenodo.21972561) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
