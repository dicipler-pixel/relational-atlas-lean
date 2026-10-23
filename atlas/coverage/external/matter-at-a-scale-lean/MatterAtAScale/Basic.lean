/-
Matter at a Scale: Zero, Span, and the Logarithm Between Them (Jeromie Beasley,
DOI 10.5281/zenodo.22019892): the exact results of Sections 2 and 3.

Units dictionary. All quantities are functions of the epoch through `s = 1 + z > 0`.
* The rigid rod (Eq. 1): the Bohr radius `a₀ = ħ/(αmc)` gives `a₀ m = ħ/(αc)`.
* Theorem 1 (closure): with `ħ, c, α` fixed, atomic redshift `a₀(s) = s a₀(1)` forces
  `m(s) = m(1)/s`; the charge `e² = αħc` is fixed, mass ratios are invariant, and the
  Rydberg–second product `Ry · T` is invariant when atomic times scale as `s`.
* The rejected assignment: if mass and charge both scale as `s` (with `ħ, c` fixed) then
  `α ∝ s²` and `a₀ = ħ²/(me²) ∝ s⁻³`, missing the required `s` by `s⁴`.
* Theorem 2 (gravitational closure): with `M_Pl ∝ 1/s`, `G = ħc/M_Pl² ∝ s²` and
  `α_G = G m²/(ħc) = (m/M_Pl)²` is invariant.

Span (Section 3). Eigenspaces, hence spectral projectors, are unchanged by `K ↦ cK` (`c ≠ 0`,
eigenvalue `λ ↦ cλ`) and by the offset `K ↦ K + a` (`λ ↦ λ + a`); positive `c` preserves the
spectral order and negative `c` reverses it. The self-commutator energy scales as `c⁴` and the
energy as `c²`, so the relative departure from normality `‖[K,K†]‖²/‖K‖⁴` is span-free.
-/
import Mathlib

namespace MatterAtAScale

/-! ## The units dictionary -/

/-- The Bohr radius `a₀ = ħ/(α m c)`. -/
noncomputable def bohr (ħ α m c : ℝ) : ℝ := ħ / (α * m * c)

/-- **The rigid rod (Eq. 1).** `a₀ m = ħ/(αc)`. -/
theorem rigid_rod (ħ α m c : ℝ) (hm : m ≠ 0) : bohr ħ α m c * m = ħ / (α * c) := by
  unfold bohr
  field_simp

/-- **Theorem 1, mass.** With `ħ, α, c` fixed and nonzero, atomic redshift
`a₀(s) = s · a₀(1)` forces `m(s) = m(1)/s`. -/
theorem closure_mass (ħ α c m₁ ms s : ℝ) (hħ : ħ ≠ 0) (hα : α ≠ 0) (hc : c ≠ 0)
    (h₁ : m₁ ≠ 0) (hms : ms ≠ 0) (hs : s ≠ 0)
    (hred : bohr ħ α ms c = s * bohr ħ α m₁ c) : ms = m₁ / s := by
  unfold bohr at hred
  field_simp at hred
  field_simp
  nlinarith [hred]

/-- **Theorem 1, mass ratios.** A common factor leaves `m_p/m_e` unchanged. -/
theorem closure_mass_ratio (mp me k : ℝ) (hk : k ≠ 0) : (k * mp) / (k * me) = mp / me := by
  rw [mul_div_mul_left _ _ hk]

/-- **Theorem 1, Rydberg–second product.** `Ry = ½α²mc²` with `m ↦ m/s` and atomic time
`T ↦ sT` leaves `Ry · T` unchanged. -/
theorem closure_rydberg_second (α m c T s : ℝ) (hs : s ≠ 0) :
    (1 / 2 * α ^ 2 * (m / s) * c ^ 2) * (s * T) = (1 / 2 * α ^ 2 * m * c ^ 2) * T := by
  field_simp

/-- **The rejected assignment, fine structure.** Charge scaling as `s` with `ħ, c` fixed gives
`α = e²/(ħc) ∝ s²`. -/
theorem rejected_alpha (e ħ c s : ℝ) : (s * e) ^ 2 / (ħ * c) = s ^ 2 * (e ^ 2 / (ħ * c)) := by
  ring

/-- **The rejected assignment, atoms.** Mass and charge both scaling as `s` give
`a₀ = ħ²/(me²) ∝ s⁻³`. -/
theorem rejected_bohr (ħ m e s : ℝ) (hs : s ≠ 0) :
    ħ ^ 2 / ((s * m) * (s * e) ^ 2) = s⁻¹ ^ 3 * (ħ ^ 2 / (m * e ^ 2)) := by
  field_simp

/-- **The rejected assignment misses by `s⁴`.** The required `s · a₀` over the obtained
`s⁻³ · a₀` is `s⁴`. -/
theorem rejected_miss (a s : ℝ) (ha : a ≠ 0) (hs : s ≠ 0) :
    (s * a) / (s⁻¹ ^ 3 * a) = s ^ 4 := by
  field_simp

/-- **Theorem 2, gravity.** With `M_Pl ↦ M_Pl/s`, `G = ħc/M_Pl²` scales as `s²`. -/
theorem gravitational_G (ħ c M s : ℝ) (hM : M ≠ 0) (hs : s ≠ 0) :
    ħ * c / (M / s) ^ 2 = s ^ 2 * (ħ * c / M ^ 2) := by
  field_simp

/-- **Theorem 2, the coupling.** `α_G = G m²/(ħc)` with `G = ħc/M_Pl²` equals `(m/M_Pl)²`. -/
theorem alphaG_eq (ħ c M m : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) (hM : M ≠ 0) :
    (ħ * c / M ^ 2) * m ^ 2 / (ħ * c) = (m / M) ^ 2 := by
  field_simp

/-- **Theorem 2, invariance.** Scaling `m` and `M_Pl` together by `1/s` leaves
`α_G = (m/M_Pl)²` unchanged. -/
theorem alphaG_invariant (m M s : ℝ) (hs : s ≠ 0) : ((m / s) / (M / s)) ^ 2 = (m / M) ^ 2 := by
  rw [div_div_div_cancel_right₀ hs]

/-! ## Span: dilation and offset of an operator -/

section Span

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

open Module End

/-- **Lemma 1 (span-blindness).** `K ↦ cK` (`c ≠ 0`) carries the eigenspace at `λ` to the
eigenspace at `cλ` unchanged: spectral projectors do not see a dilation. -/
theorem eigenspace_smul (f : End K V) (c μ : K) (hc : c ≠ 0) :
    eigenspace (c • f) (c * μ) = eigenspace f μ := by
  ext v
  simp only [mem_eigenspace_iff, LinearMap.smul_apply, mul_smul]
  constructor
  · intro h
    exact smul_right_injective V hc h
  · intro h
    rw [h]

/-- **Offset invariance.** `K ↦ K + a` carries the eigenspace at `λ` to the eigenspace at
`λ + a` unchanged. -/
theorem eigenspace_add_scalar (f : End K V) (a μ : K) :
    eigenspace (f + a • 1) (μ + a) = eigenspace f μ := by
  ext v
  simp only [mem_eigenspace_iff, LinearMap.add_apply, LinearMap.smul_apply, one_apply,
    add_smul]
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    rw [h]

end Span

/-- **Lemma 1, spectral order.** A positive dilation preserves the order of eigenvalues; a
negative one reverses it. -/
theorem dilation_order (c μ ν : ℝ) :
    (0 < c → (c * μ < c * ν ↔ μ < ν)) ∧ (c < 0 → (c * μ < c * ν ↔ ν < μ)) := by
  refine ⟨fun hc => ⟨fun h => ?_, fun h => ?_⟩, fun hc => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra h'
    push_neg at h'
    nlinarith
  · nlinarith
  · by_contra h'
    push_neg at h'
    nlinarith
  · nlinarith

section Ratios

open Matrix

variable {n : Type*} [Fintype n]

/-- Frobenius energy `‖X‖² = Re Tr(X X†)`. -/
noncomputable def energy (X : Matrix n n ℂ) : ℝ := (trace (X * Xᴴ)).re

/-- The self-commutator `[K, K†]`. -/
def selfComm (X : Matrix n n ℂ) : Matrix n n ℂ := X * Xᴴ - Xᴴ * X

theorem energy_smul (c : ℝ) (X : Matrix n n ℂ) : energy ((c : ℂ) • X) = c ^ 2 * energy X := by
  unfold energy
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    trace_smul, smul_eq_mul, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem selfComm_smul (c : ℝ) (X : Matrix n n ℂ) :
    selfComm ((c : ℂ) • X) = ((c ^ 2 : ℝ) : ℂ) • selfComm X := by
  unfold selfComm
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    smul_mul_smul_comm, ← smul_sub]
  push_cast
  ring_nf

/-- **Span covariance.** The self-commutator energy scales as `c⁴`. -/
theorem stress_scales (c : ℝ) (X : Matrix n n ℂ) :
    energy (selfComm ((c : ℂ) • X)) = c ^ 4 * energy (selfComm X) := by
  rw [selfComm_smul, energy_smul]
  ring

/-- **Only ratios are observables.** The relative departure from normality
`‖[K,K†]‖²/‖K‖⁴` is unchanged by any dilation `c ≠ 0`. -/
theorem departure_span_free (c : ℝ) (hc : c ≠ 0) (X : Matrix n n ℂ) :
    energy (selfComm ((c : ℂ) • X)) / energy ((c : ℂ) • X) ^ 2 =
      energy (selfComm X) / energy X ^ 2 := by
  rw [stress_scales, energy_smul]
  have hc4 : c ^ 4 ≠ 0 := pow_ne_zero 4 hc
  rw [mul_pow, ← pow_mul]
  norm_num
  rw [mul_div_mul_left _ _ hc4]

end Ratios

end MatterAtAScale
