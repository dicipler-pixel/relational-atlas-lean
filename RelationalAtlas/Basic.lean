/-
The Operator-First Relational Atlas (Jeromie Beasley, DOI 10.5281/zenodo.21972561): the bridges
graded THEOREM whose content is finite algebra, machine-checked.

* B2  Normality is exactly commutation: `H Hᵀ − Hᵀ H = −2[S, K]` for `H = S + K`.
* B6  Entropy is membership ambiguity: the binary entropy vanishes at certainty, is symmetric,
      nonnegative, and peaks at `log 2`.
* B31 Change has only one place to go: `F = ΠΩ(1−Π) + (1−Π)ΩΠ` is traceless and vanishes exactly
      when `[Ω, Π] = 0`.
* B39 Past the critical angle: `κ sin²θ₁ > 1 ⇔ sin θ₁ > √(1/κ)`; at `θ₂ = π/2 + iy` the sine is
      `cosh y` and the cosine is purely imaginary.
* B48 The seam is a Schur complement (Mathlib's block determinant, restated).
* B51 The whole classification is one comparison: `at⁴+bt³+ct²+bt+a = t²(au²+bu+(c−2a))` with
      `u = t + 1/t`; a unit-circle `t` gives `u = 2cos φ ∈ [−2, 2]`, and every `u ∈ [−2, 2]` comes
      from a unit-circle `t`.
* B66 The wall is branched: `det(XᵀX) = (det X)²`.
* B68 Paired spectrum: a chirality `σ` with `σD = −Dσ` sends each eigenvalue `λ` to `−λ`.
* B74 A degenerate stratum repels: `g sin²θ = C`, `sin²θ ≤ 1`, `g ≥ 0` force `g ≥ C`.
* B75 The middle of an ordered spectrum cancels: the extremal bands' pair terms share a sign,
      the middle band's have opposite signs.
-/
import Mathlib

namespace RelationalAtlas

open Matrix Real

/-! ## B2: normality is exactly commutation -/

section B2

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **B2.** For `H = S + K` with `S` symmetric and `K` skew, `H Hᵀ − Hᵀ H = −2[S, K]`. -/
theorem normal_commutator (S K : Matrix n n ℝ) (hS : Sᵀ = S) (hK : Kᵀ = -K) :
    (S + K) * (S + K)ᵀ - (S + K)ᵀ * (S + K) = (-2 : ℝ) • (S * K - K * S) := by
  rw [transpose_add, hS, hK]
  simp only [add_mul, mul_add, mul_neg, neg_mul, smul_sub, neg_smul, two_smul]
  abel

/-- **B2.** `H` is normal exactly when its symmetric and skew parts commute. -/
theorem normal_iff_commute (S K : Matrix n n ℝ) (hS : Sᵀ = S) (hK : Kᵀ = -K) :
    (S + K) * (S + K)ᵀ = (S + K)ᵀ * (S + K) ↔ S * K = K * S := by
  rw [← sub_eq_zero, normal_commutator S K hS hK, smul_eq_zero, sub_eq_zero]
  norm_num

end B2

/-! ## B6: binary entropy -/

/-- **B6.** Channels at certainty contribute nothing, the entropy is symmetric under
`ν ↦ 1 − ν`, nonnegative on `[0, 1]`, at most `log 2`, and equal to `log 2` at `ν = 1/2`. -/
theorem binary_entropy (ν : ℝ) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    binEntropy 0 = 0 ∧ binEntropy 1 = 0 ∧ binEntropy (1 - ν) = binEntropy ν ∧
      0 ≤ binEntropy ν ∧ binEntropy ν ≤ log 2 ∧ binEntropy 2⁻¹ = log 2 :=
  ⟨binEntropy_zero, binEntropy_one, binEntropy_one_sub ν, binEntropy_nonneg h0 h1,
    binEntropy_le_log_two, binEntropy_two_inv⟩

/-! ## B31: change has only one place to go -/

section B31

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The off-block part `F(Ω, Π) = ΠΩ(1−Π) + (1−Π)ΩΠ`. -/
def offBlock (Ω P : Matrix n n ℂ) : Matrix n n ℂ := P * Ω * (1 - P) + (1 - P) * Ω * P

/-- **B31.** For a projector `Π`, `Tr F = 0`. -/
theorem offBlock_trace (Ω P : Matrix n n ℂ) (hP : P * P = P) : trace (offBlock Ω P) = 0 := by
  unfold offBlock
  rw [trace_add, trace_mul_comm (P * Ω), trace_mul_comm ((1 - P) * Ω), ← mul_assoc,
    ← mul_assoc]
  rw [show (1 - P) * P = 0 by rw [sub_mul, one_mul, hP, sub_self],
    show P * (1 - P) = 0 by rw [mul_sub, mul_one, hP, sub_self]]
  simp

/-- **B31.** `F = 0` exactly when `[Ω, Π] = 0`. -/
theorem offBlock_eq_zero_iff (Ω P : Matrix n n ℂ) (hP : P * P = P) :
    offBlock Ω P = 0 ↔ Ω * P = P * Ω := by
  unfold offBlock
  constructor
  · intro h
    have hl : P * (P * Ω * (1 - P) + (1 - P) * Ω * P) = 0 := by rw [h, mul_zero]
    have hr : (P * Ω * (1 - P) + (1 - P) * Ω * P) * P = 0 := by rw [h, zero_mul]
    have e1 : P * (P * Ω * (1 - P) + (1 - P) * Ω * P) = P * Ω - P * Ω * P := by
      simp only [mul_add, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, hP]
      abel
    have e2 : (P * Ω * (1 - P) + (1 - P) * Ω * P) * P = Ω * P - P * Ω * P := by
      simp only [add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hP]
      simp only [← mul_assoc, hP]
      abel
    rw [e1, sub_eq_zero] at hl
    rw [e2, sub_eq_zero] at hr
    rw [hl, hr]
  · intro h
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    rw [mul_assoc P Ω P, h, ← mul_assoc, hP]
    abel

end B31

/-! ## B39: past the critical angle -/

/-- **B39, the critical angle.** With `κ > 0` and `sin θ₁ ≥ 0`, the refraction law demands
`sin² θ₂ = κ sin² θ₁ > 1` exactly when `sin θ₁ > √(1/κ)`. -/
theorem critical_angle (κ s : ℝ) (hκ : 0 < κ) (hs : 0 ≤ s) : 1 < κ * s ^ 2 ↔ √(1 / κ) < s := by
  constructor
  · intro h
    have hs' : 0 < s := by
      rcases hs.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at h; norm_num at h
    rw [Real.sqrt_lt' hs', div_lt_iff₀ hκ]
    linarith
  · intro h
    have hs' : 0 < s := lt_of_le_of_lt (Real.sqrt_nonneg _) h
    rw [Real.sqrt_lt' hs', div_lt_iff₀ hκ] at h
    linarith

/-- **B39, the complex angle.** At `θ₂ = π/2 + iy` the sine is `cosh y ≥ 1`. -/
theorem complex_angle_sin (y : ℝ) :
    Complex.sin (π / 2 + y * Complex.I) = (Real.cosh y : ℂ) := by
  rw [add_comm, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

/-- **B39, evanescence.** At `θ₂ = π/2 + iy` the cosine (the normal direction) is purely
imaginary. -/
theorem complex_angle_cos (y : ℝ) : (Complex.cos (π / 2 + y * Complex.I)).re = 0 := by
  rw [add_comm, Complex.cos_add_pi_div_two, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  simp

/-! ## B48: the seam is a Schur complement -/

/-- **B48.** `det [[A, B], [C, D]] = det D · det(A − B D⁻¹ C)` (Mathlib's block determinant). -/
theorem seam_schur {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    [Invertible D] : (fromBlocks A B C D).det = D.det * (A - B * ⅟D * C).det :=
  det_fromBlocks₂₂ A B C D

/-! ## B51: one comparison -/

/-- **B51.** The reciprocal quartic reduces to a quadratic in `u = t + 1/t`. -/
theorem reciprocal_reduction (a b c t : ℂ) (ht : t ≠ 0) :
    a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + b * t + a =
      t ^ 2 * (a * (t + t⁻¹) ^ 2 + b * (t + t⁻¹) + (c - 2 * a)) := by
  field_simp
  ring

/-- **B51, forward.** A root on the unit circle `t = e^{iφ}` gives `u = 2cos φ ∈ [−2, 2]`. -/
theorem unit_circle_u (φ : ℝ) :
    Complex.exp (φ * Complex.I) + (Complex.exp (φ * Complex.I))⁻¹ = ((2 * Real.cos φ : ℝ) : ℂ) ∧
      -2 ≤ 2 * Real.cos φ ∧ 2 * Real.cos φ ≤ 2 := by
  refine ⟨?_, by linarith [Real.neg_one_le_cos φ], by linarith [Real.cos_le_one φ]⟩
  rw [← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- **B51, backward.** Every real `u ∈ [−2, 2]` is `t + 1/t` for some `t` on the unit circle. -/
theorem u_from_unit_circle (u : ℝ) (h1 : -2 ≤ u) (h2 : u ≤ 2) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ t + t⁻¹ = u := by
  have hr : 0 ≤ 1 - u ^ 2 / 4 := by nlinarith
  set t : ℂ := ⟨u / 2, √(1 - u ^ 2 / 4)⟩ with ht
  have hn : Complex.normSq t = 1 := by
    rw [Complex.normSq_apply]
    simp only [ht]
    nlinarith [Real.sq_sqrt hr, Real.mul_self_sqrt hr]
  refine ⟨t, ?_, ?_⟩
  · rw [Complex.norm_def, hn, Real.sqrt_one]
  · rw [Complex.inv_def, hn, inv_one, Complex.ofReal_one, mul_one, Complex.add_conj]
    simp only [ht]
    push_cast
    ring

/-! ## B66, B68, B74, B75 -/

/-- **B66.** The Gram invariant is the square of the determinant. -/
theorem gram_det {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    (Xᵀ * X).det = X.det ^ 2 := by
  rw [det_mul, det_transpose, sq]

/-- **B68.** If `σ² = 1` and `σD = −Dσ`, every eigenvector `v` of `D` for `λ` gives an
eigenvector `σv` for `−λ`. -/
theorem paired_spectrum {n : Type*} [Fintype n] [DecidableEq n] (D σ : Matrix n n ℂ)
    (hσ : σ * σ = 1) (hD : σ * D = -(D * σ)) (v : n → ℂ) (lam : ℂ) (hv : D *ᵥ v = lam • v)
    (hv0 : v ≠ 0) : D *ᵥ (σ *ᵥ v) = (-lam) • (σ *ᵥ v) ∧ σ *ᵥ v ≠ 0 := by
  constructor
  · have hDσ : D * σ = -(σ * D) := by rw [hD, neg_neg]
    rw [mulVec_mulVec, hDσ, neg_mulVec, ← mulVec_mulVec, hv, mulVec_smul, neg_smul]
  · intro h
    apply hv0
    have := congrArg (fun w => σ *ᵥ w) h
    simpa [mulVec_mulVec, hσ] using this

/-- **B74.** The refraction invariant `g sin²θ = C` with `sin²θ ≤ 1` and `g ≥ 0` forces
`g ≥ C`: regions with `g < C` cannot be entered. -/
theorem stratum_repels (g C θ : ℝ) (hg : 0 ≤ g) (h : g * sin θ ^ 2 = C) : C ≤ g := by
  rw [← h]
  have : sin θ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (cos θ)]
  nlinarith

/-- **B75.** For an ordered spectrum `λ₁ < λ₂ < λ₃` and pair terms `s/(λ_b − λ_c)` with `s > 0`,
the extremal bands' two terms share a sign while the middle band's have opposite signs. -/
theorem middle_cancels (l1 l2 l3 s : ℝ) (h12 : l1 < l2) (h23 : l2 < l3) (hs : 0 < s) :
    (s / (l1 - l2) < 0 ∧ s / (l1 - l3) < 0) ∧ (0 < s / (l3 - l1) ∧ 0 < s / (l3 - l2)) ∧
      (s / (l2 - l1) > 0 ∧ s / (l2 - l3) < 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact div_neg_of_pos_of_neg hs (by linarith)
  · exact div_neg_of_pos_of_neg hs (by linarith)
  · exact div_pos hs (by linarith)
  · exact div_pos hs (by linarith)
  · exact div_pos hs (by linarith)
  · exact div_neg_of_pos_of_neg hs (by linarith)

end RelationalAtlas
