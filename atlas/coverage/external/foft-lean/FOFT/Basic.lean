/-
Foundational Operator Field Theory on Stratified Manifolds (Jeromie Beasley,
DOI 10.5281/zenodo.21254648, v2.3): the exact finite-dimensional results.

* Theorem 4.1 (Baseline Operator Theorem): `K₀ = −Λ I` commutes with every operator, and
  `[K, K†] = [ΔK, ΔK†]` for `K = K₀ + ΔK`: all non-normality comes from the perturbation.
* Theorem 6.1 (the algebraic core): `K + η I = (η − Λ)(I + X)` with `X = ΔK/(η − Λ)`, and
  `Tr X = 0`, which is why the Mercator series loses its `k = 1` term.
* Theorem 6.2 (Chiral ledger): if `Y` anticommutes with an involution `σ`, every odd moment of
  `Y` and of `X = iY` vanishes; each chiral pair `±λ` contributes `log(1 + λ²)` to the ledger.
* Theorem 8.2 and Proposition 8.4: along the gradient flow `K̇ = −2[C, K]`, `C = [K, K†]`, the
  rate `Tr(K†[C, K]) = Tr C²` is exact; the dual flow `K̇ = −2[C, K†]` has
  `Tr(K†[C, K†]) = 0`, so it conserves `‖K‖²_F`.
* The flow is homogeneous of degree three: `F(cK) = c³ F(K)` for real `c`.
-/
import Mathlib

namespace FOFT

open Matrix ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The self-commutator `C = [K, K†]`. -/
def selfComm (K : Matrix n n ℂ) : Matrix n n ℂ := K * Kᴴ - Kᴴ * K

/-! ## Theorem 4.1: the baseline carries no non-normality -/

/-- **Theorem 4.1 (1).** The isotropic baseline `K₀ = −Λ I` commutes with every operator, so its
flow conjugates every projector to itself. -/
theorem baseline_commutes (Λ : ℝ) (P : Matrix n n ℂ) :
    ((-(Λ : ℂ)) • (1 : Matrix n n ℂ)) * P = P * ((-(Λ : ℂ)) • 1) := by
  simp

/-- **Theorem 4.1 (2).** `[K₀ + ΔK, (K₀ + ΔK)†] = [ΔK, ΔK†]` when `K₀ = −Λ I` with `Λ` real. -/
theorem baseline_selfComm (Λ : ℝ) (D : Matrix n n ℂ) :
    selfComm ((-(Λ : ℂ)) • (1 : Matrix n n ℂ) + D) = selfComm D := by
  have ha : star (-(Λ : ℂ)) = -(Λ : ℂ) := by simp
  unfold selfComm
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, ha]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

/-! ## Theorem 6.1: the regularised ledger -/

/-- **Theorem 6.1, factorisation.** `K + η I = (η − Λ)(I + X)` with `X = ΔK/(η − Λ)`. -/
theorem heff_factor (Λ η : ℂ) (h : η ≠ Λ) (D : Matrix n n ℂ) :
    (-Λ) • (1 : Matrix n n ℂ) + D + η • 1 = (η - Λ) • (1 + (η - Λ)⁻¹ • D) := by
  have h' : η - Λ ≠ 0 := sub_ne_zero.mpr h
  rw [smul_add, smul_smul, mul_inv_cancel₀ h', one_smul, sub_smul]
  module

/-- **Theorem 6.1, the missing `k = 1` term.** A traceless perturbation gives `Tr X = 0`. -/
theorem trace_X_zero (Λ η : ℂ) (D : Matrix n n ℂ) (hD : trace D = 0) :
    trace ((η - Λ)⁻¹ • D) = 0 := by
  rw [trace_smul, hD, smul_zero]

/-! ## Theorem 6.2: the chiral ledger -/

/-- **Theorem 6.2, odd moments.** If `σ² = 1` and `σ Y = −Y σ`, every odd power of `Y` is
traceless. -/
theorem odd_moment_zero (σ Y : Matrix n n ℂ) (hσ : σ * σ = 1) (hσY : σ * Y = -Y * σ)
    (k : ℕ) (hk : Odd k) : trace (Y ^ k) = 0 := by
  have hsemi : SemiconjBy σ Y (-Y) := hσY
  have hpow : σ * Y ^ k = -Y ^ k * σ := by
    have := hsemi.pow_right k
    unfold SemiconjBy at this
    rw [this, hk.neg_pow]
  have hneg : trace (Y ^ k) = -trace (Y ^ k) := by
    calc trace (Y ^ k) = trace (σ * σ * Y ^ k) := by rw [hσ, one_mul]
      _ = trace (σ * (σ * Y ^ k)) := by rw [mul_assoc]
      _ = trace (σ * Y ^ k * σ) := trace_mul_comm _ _
      _ = trace (-(Y ^ k * (σ * σ))) := by rw [hpow, neg_mul, neg_mul, mul_assoc]
      _ = -trace (Y ^ k) := by rw [hσ, mul_one, trace_neg]
  have h2 : (2 : ℂ) * trace (Y ^ k) = 0 := by linear_combination hneg
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- **Theorem 6.2, the skew perturbation.** For `X = iY`, `Tr X^(2m+1) = 0`. -/
theorem odd_moment_zero_X (σ Y : Matrix n n ℂ) (hσ : σ * σ = 1) (hσY : σ * Y = -Y * σ)
    (k : ℕ) (hk : Odd k) : trace ((Complex.I • Y) ^ k) = 0 := by
  rw [smul_pow, trace_smul, odd_moment_zero σ Y hσ hσY k hk, smul_zero]

/-- **Theorem 6.2, one chiral pair.** Eigenvalues `±iλ` of `X` contribute
`log(1 + iλ) + log(1 − iλ) = log(1 + λ²)`, so `Z = ½ Σ_j log(1 + λ_j²)` over the pairs. -/
theorem chiral_pair (lam : ℝ) :
    Complex.log (1 + lam * Complex.I) + Complex.log (1 - lam * Complex.I) =
      (Real.log (1 + lam ^ 2) : ℂ) := by
  have hc : (1 : ℂ) - lam * Complex.I = conj (1 + lam * Complex.I) := by
    apply Complex.ext <;> simp
  have harg : (1 + lam * Complex.I).arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]
    simp
  rw [hc, Complex.log_conj _ harg, Complex.add_conj, Complex.log_re]
  have hn : ‖(1 : ℂ) + lam * Complex.I‖ = √(1 + lam ^ 2) := by
    have := Complex.norm_add_mul_I 1 lam
    simpa using this
  rw [hn, Real.log_sqrt (by positivity)]
  push_cast
  ring

/-! ## Theorem 8.2 and Proposition 8.4: the Henrici budget -/

/-- **Theorem 8.2, exact dissipation.** `Tr(K†[C, K]) = Tr C²`, so along `K̇ = −2[C, K]`,
`d‖K‖²_F/dt = −4 Tr C² = −8Φ`. -/
theorem henrici_rate (K : Matrix n n ℂ) :
    trace (Kᴴ * (selfComm K * K - K * selfComm K)) = trace (selfComm K * selfComm K) := by
  have h1 : trace (Kᴴ * (selfComm K * K)) = trace (K * Kᴴ * selfComm K) := by
    rw [trace_mul_comm Kᴴ (selfComm K * K), mul_assoc, trace_mul_comm (selfComm K)]
  have h2 : trace (Kᴴ * (K * selfComm K)) = trace (Kᴴ * K * selfComm K) := by
    rw [mul_assoc]
  rw [mul_sub, trace_sub, h1, h2, ← trace_sub, ← sub_mul]
  rfl

/-- **Proposition 8.4, the dual flow.** `Tr(K†[C, K†]) = 0` by cyclicity, so
`K̇ = −2[C, K†]` conserves `‖K‖²_F` exactly. -/
theorem dual_flow_conserves (K : Matrix n n ℂ) :
    trace (Kᴴ * (selfComm K * Kᴴ - Kᴴ * selfComm K)) = 0 := by
  rw [mul_sub, trace_sub, trace_mul_comm Kᴴ (selfComm K * Kᴴ), mul_assoc,
    ← mul_assoc Kᴴ Kᴴ (selfComm K), trace_mul_comm (Kᴴ * Kᴴ) (selfComm K), sub_self]

/-! ## Homogeneity of the flow -/

/-- The gradient flow field `F(K) = −2[C, K]`. -/
def flow (K : Matrix n n ℂ) : Matrix n n ℂ := (-2 : ℂ) • (selfComm K * K - K * selfComm K)

theorem selfComm_smul (c : ℝ) (K : Matrix n n ℂ) :
    selfComm ((c : ℂ) • K) = ((c ^ 2 : ℝ) : ℂ) • selfComm K := by
  unfold selfComm
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    smul_mul_smul_comm, ← smul_sub]
  push_cast
  ring_nf

/-- **Homogeneity.** `F(cK) = c³ F(K)`: `K ↦ cK` maps solutions to solutions with time
rescaled by `c²`. -/
theorem flow_smul (c : ℝ) (K : Matrix n n ℂ) :
    flow ((c : ℂ) • K) = ((c ^ 3 : ℝ) : ℂ) • flow K := by
  unfold flow
  rw [selfComm_smul, smul_mul_smul_comm, smul_mul_smul_comm]
  push_cast
  module

end FOFT
