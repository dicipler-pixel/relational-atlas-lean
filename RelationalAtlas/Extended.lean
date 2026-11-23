/-
Extended finite kernels for the Operator-First Relational Atlas, beyond the 37
declarations preserved in `Basic.lean` and `AtlasFormalCore.lean`.

Each theorem is a finite algebraic kernel of one card and is labelled by card.
Nothing here certifies a physical reading, a measured exponent, a continuum
limit or a genericity claim.  This file is self-contained (`import Mathlib`) in
the style of the two existing modules; `offBlockExt` repeats the formula of
`RelationalAtlas.offBlock` so that no cross-module import is needed.
-/
import Mathlib

noncomputable section

open Matrix

namespace AtlasFormal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## B31 — the Frobenius norm identity the coverage ledger left open -/

/-- Squared Frobenius norm, written as the real part of `tr (Aᴴ A)`. -/
def frobSq (A : Matrix n n ℂ) : ℝ := (Aᴴ * A).trace.re

/-- The cross terms of `(A + B)ᴴ(A + B)` vanish when `Aᴴ B = 0`. -/
theorem frobSq_add_of_orthogonal (A B : Matrix n n ℂ) (h : Aᴴ * B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  have hBA : Bᴴ * A = 0 := by
    have h' : Bᴴ * A = (Aᴴ * B)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [h', h, conjTranspose_zero]
  simp only [frobSq, conjTranspose_add, add_mul, mul_add, h, hBA, add_zero, zero_add]
  rw [trace_add, Complex.add_re]

/-- The cross terms of `(A − B)ᴴ(A − B)` vanish when `Aᴴ B = 0`. -/
theorem frobSq_sub_of_orthogonal (A B : Matrix n n ℂ) (h : Aᴴ * B = 0) :
    frobSq (A - B) = frobSq A + frobSq B := by
  have hBA : Bᴴ * A = 0 := by
    have h' : Bᴴ * A = (Aᴴ * B)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [h', h, conjTranspose_zero]
  simp only [frobSq, conjTranspose_sub, sub_mul, mul_sub, h, hBA, sub_zero, zero_sub,
    sub_neg_eq_add]
  rw [trace_add, Complex.add_re]

theorem conjTranspose_one_sub (P : Matrix n n ℂ) : (1 - P)ᴴ = 1 - Pᴴ := by
  rw [conjTranspose_sub, conjTranspose_one]

theorem cross_left (P Ω : Matrix n n ℂ) (hP : P * P = P) (hPh : Pᴴ = P) :
    (P * Ω * (1 - P))ᴴ * ((1 - P) * Ω * P) = 0 := by
  have hzero : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_one_sub, hPh]
  rw [show (1 - P) * (Ωᴴ * P) * ((1 - P) * Ω * P)
      = (1 - P) * Ωᴴ * (P * (1 - P)) * Ω * P by noncomm_ring, hzero]
  simp

theorem cross_right (P Ω : Matrix n n ℂ) (hP : P * P = P) (hPh : Pᴴ = P) :
    ((1 - P) * Ω * P)ᴴ * (P * Ω * (1 - P)) = 0 := by
  have hzeroP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_one_sub, hPh]
  rw [show P * (Ωᴴ * (1 - P)) * (P * Ω * (1 - P))
      = P * Ωᴴ * ((1 - P) * P) * Ω * (1 - P) by noncomm_ring, hzeroP]
  simp

/-- The B31 off-block change, the same formula as `RelationalAtlas.offBlock`. -/
def offBlockExt (Ω P : Matrix n n ℂ) : Matrix n n ℂ := P * Ω * (1 - P) + (1 - P) * Ω * P

/-- The commutator is the difference of the two cross-subspace blocks. -/
theorem commutator_eq_offblocks (Ω P : Matrix n n ℂ) :
    Ω * P - P * Ω = (1 - P) * Ω * P - P * Ω * (1 - P) := by
  noncomm_ring

/-- **B31 (norm identity).** For an orthogonal projector `P` and any `Ω`, the
off-block part of the change and the commutator `[Ω, P]` have the same
Frobenius norm: the two cross-subspace blocks are orthogonal, so the commutator's
two terms add in quadrature instead of cancelling.  The card displays
`‖F‖_F = ‖[Ω, Π]‖_F`; this is its exact finite kernel. -/
theorem offBlock_frobSq_eq_commutator (Ω P : Matrix n n ℂ) (hP : P * P = P) (hPh : Pᴴ = P) :
    frobSq (offBlockExt Ω P) = frobSq (Ω * P - P * Ω) := by
  have h1 : (P * Ω * (1 - P))ᴴ * ((1 - P) * Ω * P) = 0 := cross_left P Ω hP hPh
  have h2 : ((1 - P) * Ω * P)ᴴ * (P * Ω * (1 - P)) = 0 := cross_right P Ω hP hPh
  have hF : frobSq (offBlockExt Ω P)
      = frobSq (P * Ω * (1 - P)) + frobSq ((1 - P) * Ω * P) := by
    unfold offBlockExt
    exact frobSq_add_of_orthogonal _ _ h1
  have hC : frobSq (Ω * P - P * Ω)
      = frobSq ((1 - P) * Ω * P) + frobSq (P * Ω * (1 - P)) := by
    rw [commutator_eq_offblocks Ω P]
    exact frobSq_sub_of_orthogonal _ _ h2
  rw [hF, hC, add_comm]

/-! ## B1 / B32 — the bound in the card's own normalization -/

/-- The metric of the card: `g_ij = (1/4) ∂_i n · ∂_j n` for two real tangent
vectors `(a,b)` and `(c,d)`. -/
def cardGram (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(a^2+b^2)/4, (a*c+b*d)/4; (a*c+b*d)/4, (c^2+d^2)/4]

/-- **B1 / B32 (displayed normalization).** With `g = ¼ ∂n·∂n` and
`Ω = ½ n·(∂x n × ∂y n) = (ad − bc)/2` in two real parameters, `4 det g = Ω²`
exactly: the bound of B1 is saturated in two dimensions (B32). -/
theorem card_metric_saturation (a b c d : ℝ) :
    4 * (cardGram a b c d).det = ((a*d - b*c)/2)^2 := by
  rw [cardGram, Matrix.det_fin_two]
  norm_num
  ring

/-! ## B75 — when the middle band's terms actually cancel -/

/-- **B75 (exact cancellation condition).** For an ordered spectrum
`λ₁ < λ₂ < λ₃`, the middle band's two pair terms `w₂₁/(λ₂−λ₁)` and
`w₂₃/(λ₂−λ₃)` sum to zero exactly when the weights balance against the gaps,
`w₂₁(λ₃−λ₂) = w₂₃(λ₂−λ₁)`.  Opposite signs alone do not cancel; the
`middle_cancels` theorem of `Basic.lean` proves only the signs. -/
theorem balanced_middle_terms_cancel (l1 l2 l3 w21 w23 : ℝ)
    (h12 : l1 < l2) (h23 : l2 < l3) :
    w21 / (l2 - l1) + w23 / (l2 - l3) = 0 ↔ w21 * (l3 - l2) = w23 * (l2 - l1) := by
  have h1 : l2 - l1 ≠ 0 := by linarith
  have h2 : l2 - l3 ≠ 0 := by linarith
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    field_simp
    nlinarith

/-- A concrete unequal-gap spectrum where the middle terms have opposite signs
and do not cancel: signs are not cancellation. -/
theorem middle_terms_opposite_but_not_cancelled :
    (1 : ℝ) / (2 - 1) + 1 / (2 - 4) ≠ 0 ∧
      ((1 : ℝ) / (2 - 1) > 0 ∧ (1 : ℝ) / (2 - 4) < 0) := by
  norm_num

/-! ## B66 and B85 — the zero sets the cards name -/

/-- **B66.** `det(XᵀX) = 0` exactly when `det X = 0`, so the two zero sets the
card identifies really coincide. -/
theorem gram_det_zero_iff {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) :
    (Xᵀ * X).det = 0 ↔ X.det = 0 := by
  rw [det_mul, det_transpose]
  exact mul_self_eq_zero

/-- **B85.** The rank-one determinant vanishes exactly on the real-parallel
locus `x t = y s`. -/
theorem rank_one_det_zero_iff (x y s t : ℝ) :
    (x^2 - y^2) * (s^2 - t^2) - (x*s - y*t)^2 = 0 ↔ x*t = y*s := by
  have hneg : (x^2 - y^2) * (s^2 - t^2) - (x*s - y*t)^2 = -(x*t - y*s)^2 := by ring
  rw [hneg, neg_eq_zero, pow_eq_zero_iff (by norm_num), sub_eq_zero]

end AtlasFormal

/-! ## B1 / B32 — Lagrange kernel and the two-parameter saturation

Integrated from `.ultramath/smwtdtx7v/m4/B1Lagrange.lean` (accepted in the formalisation run).
-/

/-!
# B1 / B32 — the two-real-parameter Lagrange kernel

For tangent vectors `a = (a₁,a₂)` and `b = (b₁,b₂)` in `ℝ²`, put
`A = !![a₁,b₁; a₂,b₂]`, `g = Aᵀ A`, and `Ω = 2(a₁b₂-a₂b₁)`.
Lagrange's identity gives `det g = (a₁b₂-a₂b₁)²`, hence the exact saturation
`4 det g = Ω²`.  This is the finite algebraic content of B1 and B32 in the
normalisation of the card; no smooth projector family or two-band Hamiltonian
is needed for this coordinate identity.

The general-rank/higher-dimensional inequality `4 det g ≥ |Ω|²` is a different
argument: it uses Cauchy–Schwarz (equivalently, a two-by-two principal Gram
minor) in the Hermitian tangent space.  It is not asserted to follow merely
from the two-real-parameter identity proved here.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

open Matrix

/-- The two tangent vectors are the columns of this real `2 × 2` matrix. -/
def tangentFrame (a₁ a₂ b₁ b₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a₁, b₁; a₂, b₂]

/-- The unhalved Gram matrix of the two tangent vectors. -/
def gram2 (a₁ a₂ b₁ b₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (tangentFrame a₁ a₂ b₁ b₂)ᵀ * tangentFrame a₁ a₂ b₁ b₂

/-- Twice the oriented area of the two tangent vectors. -/
def omega2 (a₁ a₂ b₁ b₂ : ℝ) : ℝ := 2 * (a₁ * b₂ - a₂ * b₁)

/-- Lagrange's identity, in precisely the coordinates used below. -/
theorem lagrange_identity (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁^2 + a₂^2) * (b₁^2 + b₂^2) =
      (a₁*b₁ + a₂*b₂)^2 + (a₁*b₂ - a₂*b₁)^2 := by
  ring

/-- The entries of `gram2` are the three Euclidean inner products. -/
theorem gram2_entries (a₁ a₂ b₁ b₂ : ℝ) :
    gram2 a₁ a₂ b₁ b₂ =
      !![a₁^2 + a₂^2, a₁*b₁ + a₂*b₂;
         a₁*b₁ + a₂*b₂, b₁^2 + b₂^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram2, tangentFrame, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- In two real dimensions the Gram determinant is exactly the squared area. -/
theorem gram2_det_eq (a₁ a₂ b₁ b₂ : ℝ) :
    (gram2 a₁ a₂ b₁ b₂).det = (a₁*b₂ - a₂*b₁)^2 := by
  rw [gram2_entries, Matrix.det_fin_two_of]
  nlinarith [lagrange_identity a₁ a₂ b₁ b₂]

/-- Positivity of the determinant is visible from the same identity. -/
theorem gram2_det_nonneg (a₁ a₂ b₁ b₂ : ℝ) :
    0 ≤ (gram2 a₁ a₂ b₁ b₂).det := by
  rw [gram2_det_eq]
  exact sq_nonneg _

/-- **B1/B32 saturation.**  If `g` is the stated Gram matrix and `Ω` twice
its oriented area, then `4 det g = Ω²`; there is no slack in this two-real-
parameter case. -/
theorem b1_two_parameter_saturation
    (a₁ a₂ b₁ b₂ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ)
    (hg : g = gram2 a₁ a₂ b₁ b₂) (hΩ : Ω = omega2 a₁ a₂ b₁ b₂) :
    4 * g.det = Ω^2 := by
  subst g
  subst Ω
  rw [gram2_det_eq]
  unfold omega2
  ring

/-- **B1's metric-control inequality**, here with equality by saturation. -/
theorem b1_curvature_le_metric
    (a₁ a₂ b₁ b₂ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ)
    (hg : g = gram2 a₁ a₂ b₁ b₂) (hΩ : Ω = omega2 a₁ a₂ b₁ b₂) :
    Ω^2 ≤ 4 * g.det :=
  (b1_two_parameter_saturation a₁ a₂ b₁ b₂ g Ω hg hΩ).ge

/-- The displayed B1 form with `|Ω|²`; for real `Ω` it equals `Ω²`. -/
theorem b1_abs_curvature_le_metric
    (a₁ a₂ b₁ b₂ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ)
    (hg : g = gram2 a₁ a₂ b₁ b₂) (hΩ : Ω = omega2 a₁ a₂ b₁ b₂) :
    |Ω|^2 ≤ 4 * g.det := by
  simpa only [sq_abs] using b1_curvature_le_metric a₁ a₂ b₁ b₂ g Ω hg hΩ

/-- **B32's displayed saturation**, `|Ω| = 2√(det g)`. -/
theorem b32_two_parameter_saturation
    (a₁ a₂ b₁ b₂ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ)
    (hg : g = gram2 a₁ a₂ b₁ b₂) (hΩ : Ω = omega2 a₁ a₂ b₁ b₂) :
    |Ω| = 2 * Real.sqrt g.det := by
  subst g
  subst Ω
  rw [gram2_det_eq]
  simp [omega2, abs_mul, Real.sqrt_sq_eq_abs]

/-- A concrete nondegenerate instance: the standard orthonormal frame has
`g = I`, `Ω = 2`, and the general saturation theorem fires with `4 = 4`.
The nonzero second conjunct rules out a vacuous zero-curvature witness. -/
example :
    (4 : ℝ) * (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = (2 : ℝ)^2 ∧
      (2 : ℝ) ≠ 0 := by
  constructor
  · refine b1_two_parameter_saturation 1 0 0 1 _ 2 ?_ ?_
    · rw [gram2_entries]
      norm_num
    · norm_num [omega2]
  · norm_num

end AtlasFormal

#print axioms AtlasFormal.lagrange_identity
#print axioms AtlasFormal.gram2_entries
#print axioms AtlasFormal.gram2_det_eq
#print axioms AtlasFormal.gram2_det_nonneg
#print axioms AtlasFormal.b1_two_parameter_saturation
#print axioms AtlasFormal.b1_curvature_le_metric
#print axioms AtlasFormal.b1_abs_curvature_le_metric
#print axioms AtlasFormal.b32_two_parameter_saturation

/-! ## B18 — the logarithmic dimension-deficit bound

Integrated from `.ultramath/smwtdtx7v/m9/B18Deficit.lean` (accepted in the formalisation run).
-/

/-!
# B18 — the logarithmic dimension-deficit bound

This file proves the finite arithmetic content of Atlas card B18.  The card's
`n - d` is renamed `n` here, as in the task specification.  Its support sets,
δ-nets, straight-tube counting, trackability threshold, and concentration
alternative are geometric inputs and are not formalized.

The sole arithmetic input is `1 ≤ C₀ * a^n`: demand `a^n` against capacity
`C₀`.  Since `0 < a < 1`, the cutoff depth `Real.log (1 / a)` is positive.
Taking logarithms gives both the displayed bound and its exact equality case.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal
namespace B18

/-- The cutoff-depth logarithm is minus the cutoff logarithm. -/
theorem log_cutoff_depth {a : ℝ} (ha : 0 < a) :
    Real.log (1 / a) = -Real.log a := by
  rw [Real.log_div one_ne_zero ha.ne', Real.log_one, zero_sub]

/-- Taking logarithms of the capacity hypothesis, in the sign convention
`Real.log (1 / a) = -Real.log a`. -/
theorem capacity_log_lower_bound {a C₀ : ℝ} {n : ℕ}
    (ha : 0 < a) (hC₀ : 0 < C₀) (hcap : 1 ≤ C₀ * a ^ n) :
    0 ≤ Real.log C₀ - (n : ℝ) * Real.log (1 / a) := by
  have hprod : 0 < C₀ * a ^ n := lt_of_lt_of_le zero_lt_one hcap
  have hlog : Real.log 1 ≤ Real.log (C₀ * a ^ n) :=
    (Real.log_le_log_iff zero_lt_one hprod).2 hcap
  rw [Real.log_mul hC₀.ne' (pow_ne_zero n ha.ne'), Real.log_pow,
    Real.log_one] at hlog
  rw [log_cutoff_depth ha]
  simpa [mul_neg, sub_neg_eq_add] using hlog

/-- **B18 (deficit bound).**  For `0 < a < 1`, positive capacity `C₀`, and
`1 ≤ C₀ * a^n`, the renamed deficit `n` satisfies the card's displayed formula
`n ≤ log C₀ / log (1 / a)`. -/
theorem capacity_deficit_bound {a C₀ : ℝ} {n : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hC₀ : 0 < C₀)
    (hcap : 1 ≤ C₀ * a ^ n) :
    (n : ℝ) ≤ Real.log C₀ / Real.log (1 / a) := by
  have hden : 0 < Real.log (1 / a) := by
    rw [log_cutoff_depth ha]
    exact neg_pos.mpr (Real.log_neg ha ha1)
  apply (le_div_iff₀ hden).2
  have hlog := capacity_log_lower_bound ha hC₀ hcap
  nlinarith

/-- **B18 (sharpness).**  Under the same hypotheses, equality in the displayed
bound holds exactly when the capacity inequality is saturated:
`C₀ * a^n = 1`. -/
theorem capacity_deficit_eq_iff {a C₀ : ℝ} {n : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hC₀ : 0 < C₀)
    (hcap : 1 ≤ C₀ * a ^ n) :
    (n : ℝ) = Real.log C₀ / Real.log (1 / a) ↔ C₀ * a ^ n = 1 := by
  have hden : 0 < Real.log (1 / a) := by
    rw [log_cutoff_depth ha]
    exact neg_pos.mpr (Real.log_neg ha ha1)
  have hprod : 0 < C₀ * a ^ n := lt_of_lt_of_le zero_lt_one hcap
  rw [eq_div_iff hden.ne']
  have hlog : Real.log (C₀ * a ^ n) =
      Real.log C₀ - (n : ℝ) * Real.log (1 / a) := by
    rw [Real.log_mul hC₀.ne' (pow_ne_zero n ha.ne'), Real.log_pow,
      log_cutoff_depth ha]
    ring
  constructor
  · intro heq
    apply Real.eq_one_of_pos_of_log_eq_zero hprod
    rw [hlog]
    nlinarith
  · intro heq
    have hz : Real.log (C₀ * a ^ n) = 0 := by rw [heq, Real.log_one]
    rw [hlog] at hz
    nlinarith

/-- A concrete saturation instance: `a = 1/2`, `C₀ = 4`, `n = 2`.
It satisfies every hypothesis and fires the inequality theorem; the companion
equality below shows that this instance lies on the card's equality locus. -/
example : (2 : ℝ) ≤ Real.log 4 / Real.log (1 / (1 / 2 : ℝ)) := by
  apply capacity_deficit_bound (a := 1 / 2) (C₀ := 4) (n := 2)
  all_goals norm_num

example : (2 : ℝ) = Real.log 4 / Real.log (1 / (1 / 2 : ℝ)) := by
  apply (capacity_deficit_eq_iff (a := 1 / 2) (C₀ := 4) (n := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  norm_num

end B18
end AtlasFormal

#print axioms AtlasFormal.B18.log_cutoff_depth
#print axioms AtlasFormal.B18.capacity_log_lower_bound
#print axioms AtlasFormal.B18.capacity_deficit_bound
#print axioms AtlasFormal.B18.capacity_deficit_eq_iff

/-! ## B57 — zero length and moving: the oblique projector witness

Integrated from `.ultramath/smwtdtx7v/m15/B57TraceForm.lean` (accepted in the formalisation run).
-/

/-!
# B57 -- Zero length, and still moving

Finite real-matrix kernel of the Operator-First Relational Atlas card B57.

On the tangent space to the idempotents, with a symmetric (Hermitian, in the
real case) tangent `T`, the trace form `trace (T * T)` is positive definite.
For the displayed oblique projector, the same trace form has a nonzero null
tangent.  Thus `g(t,t) = 0` cannot coexist with `∂tΠ ≠ 0` in the symmetric
case, and the explicit second example realises exactly that coexistence after
symmetry is dropped.

The biorthogonal metric's factor and normalisation are conventions.  The
invariant algebraic content formalised here is the positivity, respectively
vanishing, of the trace form.  No curve, derivative, wall geometry, or
finite-difference assertion from the full card is proved.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas.B57

open Matrix

/-- **B57, symmetric tangent space.**  If `Π` is an orthogonal projector and
`T` is a nonzero symmetric tangent, then the quadratic trace form is strictly
positive.  Algebraically the proof uses only `Tᵀ = T` and `T ≠ 0`; the other
three hypotheses faithfully record the orthogonal-projector tangent space. -/
theorem orthogonal_tangent_trace_pos {n : Type*} [Fintype n] [DecidableEq n]
    (P T : Matrix n n ℝ) (hP : P * P = P) (hPsymm : Pᵀ = P)
    (hTsymm : Tᵀ = T) (htangent : P * T + T * P = T) (hT : T ≠ 0) :
    0 < Matrix.trace (T * T) := by
  have hnonneg : 0 ≤ Matrix.trace (Tᴴ * T) :=
    (Matrix.posSemidef_conjTranspose_mul_self T).trace_nonneg
  have hne : Matrix.trace (Tᴴ * T) ≠ 0 := by
    intro hzero
    exact hT (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero)
  have hTT : T * T = Tᴴ * T := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hTsymm]
  rw [hTT]
  exact lt_of_le_of_ne hnonneg hne.symm

/-- The oblique projector in B57's concrete two-dimensional witness. -/
def obliquePi : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

/-- A nonzero symmetric-free tangent to `obliquePi`. -/
def obliqueT : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The witness is idempotent. -/
theorem obliquePi_idempotent : obliquePi * obliquePi = obliquePi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliquePi, Matrix.mul_apply, Fin.sum_univ_two]

/-- The witness is not an orthogonal projector: it is not symmetric. -/
theorem obliquePi_not_symmetric : obliquePiᵀ ≠ obliquePi := by
  intro h
  have hij := congrFun (congrFun h 0) 1
  norm_num [obliquePi, Matrix.transpose_apply] at hij

/-- The nonzero matrix `obliqueT` satisfies the linearised idempotence equation. -/
theorem obliqueT_tangent :
    obliquePi * obliqueT + obliqueT * obliquePi = obliqueT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliquePi, obliqueT, Matrix.mul_apply, Fin.sum_univ_two]

/-- The oblique tangent is genuinely nonzero. -/
theorem obliqueT_ne_zero : obliqueT ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h 0) 1
  norm_num [obliqueT] at hij

/-- **B57, oblique null direction.**  This tangent is nonzero although its
quadratic trace length is exactly zero. -/
theorem obliqueT_null : Matrix.trace (obliqueT * obliqueT) = 0 := by
  norm_num [obliqueT, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- A concrete symmetric-projector instance satisfying every hypothesis of
`orthogonal_tangent_trace_pos` and firing its conclusion. -/
example :
    0 < Matrix.trace ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      !![0, 1; 1, 0]) := by
  apply orthogonal_tangent_trace_pos !![1, 0; 0, 0] !![0, 1; 1, 0]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have hij := congrFun (congrFun h 0) 1
    norm_num at hij

/-- The concrete oblique hypotheses can be satisfied simultaneously with zero
trace length. -/
example :
    obliquePi * obliquePi = obliquePi ∧ obliquePiᵀ ≠ obliquePi ∧
      obliquePi * obliqueT + obliqueT * obliquePi = obliqueT ∧
      obliqueT ≠ 0 ∧ Matrix.trace (obliqueT * obliqueT) = 0 :=
  ⟨obliquePi_idempotent, obliquePi_not_symmetric, obliqueT_tangent,
    obliqueT_ne_zero, obliqueT_null⟩

end RelationalAtlas.B57

#print axioms RelationalAtlas.B57.orthogonal_tangent_trace_pos
#print axioms RelationalAtlas.B57.obliquePi_idempotent
#print axioms RelationalAtlas.B57.obliquePi_not_symmetric
#print axioms RelationalAtlas.B57.obliqueT_tangent
#print axioms RelationalAtlas.B57.obliqueT_ne_zero
#print axioms RelationalAtlas.B57.obliqueT_null

/-! ## B26 — coalescence is not defectiveness

Integrated from `.ultramath/smwtdtx7v/m1/B26Defective.lean` (accepted in the formalisation run).
-/

/-!
# B26 — Coalescence alone is not enough

This file proves the finite algebraic kernel of Atlas card B26.  A non-scalar
2×2 Jordan block has a repeated eigenvalue but is defective, whereas a scalar
matrix has the same repeated characteristic polynomial and is diagonalizable.
No asymptotic statement about `κ * sqrt δ` is made here.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas

open Matrix Polynomial

/-- The non-scalar real Jordan block with diagonal entry `lam`. -/
def jordanBlock₂ (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![lam, 1; 0, lam]

/-- B26: the characteristic polynomial of the Jordan block is `(X - lam)^2`. -/
theorem jordanBlock₂_charpoly (lam : ℝ) :
    (jordanBlock₂ lam).charpoly = (X - C lam) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [jordanBlock₂, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- B26: no real invertible change of basis diagonalizes the Jordan block. -/
theorem jordanBlock₂_not_diagonalizable (lam : ℝ) :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit P.det ∧ (P⁻¹ * jordanBlock₂ lam * P).IsDiag := by
  rintro ⟨P, hP, hdiag⟩
  let A : Matrix (Fin 2) (Fin 2) ℝ := P⁻¹ * jordanBlock₂ lam * P
  let d : Fin 2 → ℝ := Matrix.diag A
  have hA : diagonal d = A := (Matrix.isDiag_iff_diagonal_diag A).mp hdiag
  have htrace : A.trace = (jordanBlock₂ lam).trace := by
    dsimp [A]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP,
      Matrix.one_mul]
  have hdet_inv : P⁻¹.det * P.det = 1 := Matrix.det_nonsing_inv_mul_det P hP
  have hdet : A.det = (jordanBlock₂ lam).det := by
    calc
      A.det = (P⁻¹.det * (jordanBlock₂ lam).det) * P.det := by
        simp only [A, Matrix.det_mul]
      _ = (jordanBlock₂ lam).det * (P⁻¹.det * P.det) := by ring
      _ = (jordanBlock₂ lam).det := by rw [hdet_inv, mul_one]
  have hsum : d 0 + d 1 = 2 * lam := by
    rw [← hA] at htrace
    simpa [jordanBlock₂, Matrix.trace, Fin.sum_univ_two, two_mul] using htrace
  have hprod : d 0 * d 1 = lam ^ 2 := by
    rw [← hA] at hdet
    simpa [jordanBlock₂, Matrix.det_diagonal, Fin.prod_univ_two,
      Matrix.det_fin_two, pow_two] using hdet
  have hsquare : (d 0 - d 1) ^ 2 = 0 := by
    calc
      (d 0 - d 1) ^ 2 = (d 0 + d 1) ^ 2 - 4 * (d 0 * d 1) := by ring
      _ = 0 := by rw [hsum, hprod]; ring
  have heq : d 0 = d 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  have hd0 : d 0 = lam := by nlinarith
  have hd1 : d 1 = lam := by rw [← heq]; exact hd0
  have hscalar : A = lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd0, hd1, Matrix.one_apply]
  have hconjugate := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => P * M * P⁻¹) hscalar
  have hconjugate' : P * (P⁻¹ * jordanBlock₂ lam) =
      lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa [A, Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP] using hconjugate
  have hJ : jordanBlock₂ lam = lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.mul_nonsing_inv_cancel_left P (jordanBlock₂ lam) hP] at hconjugate'
    exact hconjugate'
  have hentry := congrFun (congrFun hJ 0) 1
  norm_num [jordanBlock₂, Matrix.one_apply] at hentry

/-- B26: the exact normality commutator of the Jordan block. -/
theorem jordanBlock₂_normality_defect (lam : ℝ) :
    jordanBlock₂ lam * (jordanBlock₂ lam)ᵀ - (jordanBlock₂ lam)ᵀ * jordanBlock₂ lam =
      !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanBlock₂, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- In particular, the Jordan block is not normal. -/
theorem jordanBlock₂_not_normal (lam : ℝ) :
    jordanBlock₂ lam * (jordanBlock₂ lam)ᵀ - (jordanBlock₂ lam)ᵀ * jordanBlock₂ lam ≠ 0 := by
  rw [jordanBlock₂_normality_defect]
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num at hentry

/-- The scalar matrix has the same coalesced characteristic polynomial. -/
theorem scalar₂_charpoly (lam : ℝ) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ)).charpoly = (X - C lam) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.one_apply,
    Polynomial.C_ofNat]
  ring

/-- Converse reading of B26: scalar coalescence is diagonalizable, witnessed by `P = 1`. -/
theorem scalar₂_diagonalizable (lam : ℝ) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit P.det ∧ (P⁻¹ * (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * P).IsDiag := by
  refine ⟨1, by simp, ?_⟩
  intro i j hij
  simp [Matrix.one_apply, hij]

/-- A concrete instance: the nilpotent Jordan block at zero is defective and non-normal. -/
example :
    (jordanBlock₂ 0).charpoly = X ^ 2 ∧
    (¬ ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      IsUnit P.det ∧ (P⁻¹ * jordanBlock₂ 0 * P).IsDiag) ∧
    jordanBlock₂ 0 * (jordanBlock₂ 0)ᵀ - (jordanBlock₂ 0)ᵀ * jordanBlock₂ 0 ≠ 0 := by
  refine ⟨?_, jordanBlock₂_not_diagonalizable 0, jordanBlock₂_not_normal 0⟩
  simpa using jordanBlock₂_charpoly 0

end RelationalAtlas

#print axioms RelationalAtlas.jordanBlock₂_charpoly
#print axioms RelationalAtlas.jordanBlock₂_not_diagonalizable
#print axioms RelationalAtlas.jordanBlock₂_normality_defect
#print axioms RelationalAtlas.jordanBlock₂_not_normal
#print axioms RelationalAtlas.scalar₂_charpoly
#print axioms RelationalAtlas.scalar₂_diagonalizable

/-! ## B13 — one loop swaps the square-root pair, two restore it

Integrated from `.ultramath/smwtdtx7v/m5/B13Monodromy.lean` (accepted in the formalisation run).
-/

/-!
# B13 — going around swaps the square-root pair

This file formalizes the finite algebraic kernel of Atlas card B13 for the
continuity-tracked labels
`λ(θ) = √r * exp (θ I / 2)` on the circle `z(θ) = r * exp (θ I)`, where
`r > 0`.  The two labels are exactly the roots of the characteristic polynomial
of `H(θ) = [[0, 1], [z(θ), 0]]`.  One circuit in `z` interchanges the labels;
two circuits restore them.  The matrix family itself already returns after one
circuit.

The published card also displays a winding-number formula for the discriminant.
That analytic assertion, winding numbers, and the discriminant integral are not
part of this finite kernel.  Nor does this file make any assertion about an
eigenvector sign or Berry phase.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

open Polynomial

/-- The nonzero complex parameter on the circle of radius `r`. -/
def b13Z (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The continuous square-root branch obtained by halving the angle. -/
def b13Lambda (r θ : ℝ) : ℂ :=
  (Real.sqrt r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I / 2)

/-- The two-level family whose eigenvalue discriminant is `4 * b13Z r θ`. -/
def b13H (r θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; b13Z r θ, 0]

/-- Squaring the half-angle label gives the parameter on the original circle. -/
theorem b13_lambda_sq (r θ : ℝ) (hr : 0 < r) :
    b13Lambda r θ ^ 2 = b13Z r θ := by
  have hsqrt : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  unfold b13Lambda b13Z
  calc
    ((Real.sqrt r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I / 2)) ^ 2 =
        (Real.sqrt r : ℂ) ^ 2 *
          (Complex.exp ((θ : ℂ) * Complex.I / 2) *
            Complex.exp ((θ : ℂ) * Complex.I / 2)) := by ring
    _ = (r : ℂ) *
          (Complex.exp ((θ : ℂ) * Complex.I / 2) *
            Complex.exp ((θ : ℂ) * Complex.I / 2)) := by rw [hsqrt]
    _ = (r : ℂ) * Complex.exp
          (((θ : ℂ) * Complex.I / 2) + ((θ : ℂ) * Complex.I / 2)) := by
      rw [Complex.exp_add]
    _ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      congr 2
      ring

/-- For `r > 0`, the two displayed labels are all the square roots of `z`.
There are no other roots. -/
theorem b13_root_iff (r θ : ℝ) (hr : 0 < r) (w : ℂ) :
    w ^ 2 = b13Z r θ ↔ w = b13Lambda r θ ∨ w = -b13Lambda r θ := by
  rw [← b13_lambda_sq r θ hr]
  constructor
  · intro h
    have hfactor : (w - b13Lambda r θ) * (w + b13Lambda r θ) = 0 := by
      calc
        (w - b13Lambda r θ) * (w + b13Lambda r θ) =
            w ^ 2 - b13Lambda r θ ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr h
    rcases mul_eq_zero.mp hfactor with hw | hw
    · exact Or.inl (sub_eq_zero.mp hw)
    · right
      linear_combination hw
  · rintro (rfl | rfl) <;> ring

/-- The selected square-root label is nonzero when `r > 0`. -/
theorem b13_lambda_ne_zero (r θ : ℝ) (hr : 0 < r) : b13Lambda r θ ≠ 0 := by
  unfold b13Lambda
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne')
    (Complex.exp_ne_zero _)

/-- The two roots really are distinct; the root-pair statement is not degenerate. -/
theorem b13_lambda_ne_neg (r θ : ℝ) (hr : 0 < r) :
    b13Lambda r θ ≠ -b13Lambda r θ := by
  intro h
  apply b13_lambda_ne_zero r θ hr
  have htwo : (2 : ℂ) * b13Lambda r θ = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The characteristic polynomial of `H` is exactly `X² - z`. -/
theorem b13_charpoly (r θ : ℝ) :
    (b13H r θ).charpoly = X ^ 2 - C (b13Z r θ) := by
  rw [Matrix.charpoly_fin_two]
  simp [b13H, Matrix.trace_fin_two, Matrix.det_fin_two, sub_eq_add_neg]

/-- In factored form, the characteristic roots are precisely `λ` and `-λ`. -/
theorem b13_charpoly_factor (r θ : ℝ) (hr : 0 < r) :
    (b13H r θ).charpoly = (X - C (b13Lambda r θ)) * (X - C (-b13Lambda r θ)) := by
  rw [b13_charpoly, ← b13_lambda_sq r θ hr]
  simp only [map_neg, map_pow]
  ring

/-- Characteristic-polynomial form of the exhaustive root-pair statement. -/
theorem b13_charpoly_root_iff (r θ : ℝ) (hr : 0 < r) (w : ℂ) :
    Polynomial.eval w (b13H r θ).charpoly = 0 ↔
      w = b13Lambda r θ ∨ w = -b13Lambda r θ := by
  rw [b13_charpoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero]
  exact b13_root_iff r θ hr w

/-- Advancing the original parameter by one `2π` circuit advances the
half-angle by `π`, hence negates the continuously tracked square root. -/
theorem b13_lambda_add_two_pi (r θ : ℝ) :
    b13Lambda r (θ + 2 * Real.pi) = -b13Lambda r θ := by
  unfold b13Lambda
  have harg : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 =
      (θ : ℂ) * Complex.I / 2 + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add_pi_mul_I]
  ring

/-- After one circuit, the ordered pair `(λ, -λ)` is swapped. -/
theorem b13_one_loop_swaps (r θ : ℝ) :
    (b13Lambda r (θ + 2 * Real.pi), -b13Lambda r (θ + 2 * Real.pi)) =
      (-b13Lambda r θ, b13Lambda r θ) := by
  rw [b13_lambda_add_two_pi]
  simp only [neg_neg]

/-- Two circuits restore the original continuously tracked square root. -/
theorem b13_lambda_add_four_pi (r θ : ℝ) :
    b13Lambda r (θ + 4 * Real.pi) = b13Lambda r θ := by
  rw [show θ + 4 * Real.pi = (θ + 2 * Real.pi) + 2 * Real.pi by ring,
    b13_lambda_add_two_pi, b13_lambda_add_two_pi, neg_neg]

/-- After two circuits, the whole ordered pair returns. -/
theorem b13_two_loops_restore (r θ : ℝ) :
    (b13Lambda r (θ + 4 * Real.pi), -b13Lambda r (θ + 4 * Real.pi)) =
      (b13Lambda r θ, -b13Lambda r θ) := by
  rw [b13_lambda_add_four_pi]

/-- The parameter `z` is periodic with period `2π`, unlike its half-angle label. -/
theorem b13_z_add_two_pi (r θ : ℝ) : b13Z r (θ + 2 * Real.pi) = b13Z r θ := by
  unfold b13Z
  have harg : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The matrix family returns after the first circuit, while its eigenvalue
labels are interchanged (`b13_one_loop_swaps`). -/
theorem b13_family_add_two_pi (r θ : ℝ) :
    b13H r (θ + 2 * Real.pi) = b13H r θ := by
  unfold b13H
  rw [b13_z_add_two_pi]

/-- A concrete non-vacuous instance: radius one, initial angle zero.  The two
roots are `1` and `-1`; one loop sends the selected root `1` to `-1`, two loops
return it to `1`, and the matrix returns after one loop. -/
example :
    b13Lambda 1 0 = 1 ∧
    (1 : ℂ) ^ 2 = b13Z 1 0 ∧
    (∀ w : ℂ, w ^ 2 = b13Z 1 0 ↔ w = 1 ∨ w = -1) ∧
    b13Lambda 1 (2 * Real.pi) = -1 ∧
    b13Lambda 1 (4 * Real.pi) = 1 ∧
    b13H 1 (2 * Real.pi) = b13H 1 0 := by
  have hr : (0 : ℝ) < 1 := by norm_num
  have hL : b13Lambda 1 0 = 1 := by
    norm_num [b13Lambda]
  have hsq := b13_lambda_sq 1 0 hr
  rw [hL] at hsq
  have hroots : ∀ w : ℂ, w ^ 2 = b13Z 1 0 ↔ w = 1 ∨ w = -1 := by
    intro w
    simpa [hL] using b13_root_iff 1 0 hr w
  have hone : b13Lambda 1 (2 * Real.pi) = -1 := by
    simpa [hL] using b13_lambda_add_two_pi 1 0
  have htwo : b13Lambda 1 (4 * Real.pi) = 1 := by
    simpa [hL] using b13_lambda_add_four_pi 1 0
  exact ⟨hL, hsq, hroots, hone, htwo, by simpa using b13_family_add_two_pi 1 0⟩

end AtlasFormal

#print axioms AtlasFormal.b13_lambda_sq
#print axioms AtlasFormal.b13_root_iff
#print axioms AtlasFormal.b13_lambda_ne_zero
#print axioms AtlasFormal.b13_lambda_ne_neg
#print axioms AtlasFormal.b13_charpoly
#print axioms AtlasFormal.b13_charpoly_factor
#print axioms AtlasFormal.b13_charpoly_root_iff
#print axioms AtlasFormal.b13_lambda_add_two_pi
#print axioms AtlasFormal.b13_one_loop_swaps
#print axioms AtlasFormal.b13_lambda_add_four_pi
#print axioms AtlasFormal.b13_two_loops_restore
#print axioms AtlasFormal.b13_z_add_two_pi
#print axioms AtlasFormal.b13_family_add_two_pi

/-! ## B21 — predictability, visibility and concurrence

Integrated from `.ultramath/smwtdtx7v/m11/B21Triality.lean` (accepted in the formalisation run).
-/

/-!
# B21 — predictability, visibility and concurrence

For a normalized two-qubit pure state
`|ψ⟩ = a|00⟩ + b|01⟩ + c|10⟩ + d|11⟩`, tracing out the second qubit gives
`ρ₀₀ = |a|² + |b|²`, `ρ₁₁ = |c|² + |d|²`, and
`ρ₀₁ = a * conj c + b * conj d`.  We use the standard conventions
`P = ρ₀₀ - ρ₁₁`, `V = 2 |ρ₀₁|`, and `E = 2 |a d - b c|`, where `E` is
Wootters' concurrence for a pure two-qubit state.  These conventions, absent
from the short card, make the displayed `V² + P² + E² = 1` explicit.

Only the finite algebraic conservation law is proved here.  The card's name
"census" for `E`, its boundary interpretation, and its measured rank-15 versus
rank-20 assertion are not formalized.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas

open scoped ComplexConjugate

/-- Predictability of the first qubit: the population imbalance of its reduced state. -/
def b21Predictability (a b c d : ℂ) : ℝ :=
  (Complex.normSq a + Complex.normSq b) - (Complex.normSq c + Complex.normSq d)

/-- Visibility: twice the modulus of the reduced state's off-diagonal entry. -/
def b21Visibility (a b c d : ℂ) : ℝ :=
  2 * ‖a * conj c + b * conj d‖

/-- Entanglement `E`, using pure-state concurrence as required by card B21. -/
def b21Entanglement (a b c d : ℂ) : ℝ :=
  2 * ‖a * d - b * c‖

/-- **B21.** For every normalized two-qubit pure state, visibility,
predictability, and concurrence satisfy the displayed three-way budget
`V² + P² + E² = 1`.

The proof is exact complex algebra.  In particular, no Schmidt-coordinate or
real-coefficient assumption is added. -/
theorem b21_triality (a b c d : ℂ)
    (hnormalized : Complex.normSq a + Complex.normSq b +
      Complex.normSq c + Complex.normSq d = 1) :
    b21Visibility a b c d ^ 2 + b21Predictability a b c d ^ 2 +
      b21Entanglement a b c d ^ 2 = 1 := by
  have hvisibility : ‖a * conj c + b * conj d‖ ^ 2 =
      Complex.normSq (a * conj c + b * conj d) :=
    Complex.sq_norm _
  have hentanglement : ‖a * d - b * c‖ ^ 2 =
      Complex.normSq (a * d - b * c) :=
    Complex.sq_norm _
  calc
    b21Visibility a b c d ^ 2 + b21Predictability a b c d ^ 2 +
        b21Entanglement a b c d ^ 2 =
        (Complex.normSq a + Complex.normSq b + Complex.normSq c +
          Complex.normSq d) ^ 2 := by
      simp only [b21Visibility, b21Predictability, b21Entanglement]
      rw [show (2 * ‖a * conj c + b * conj d‖) ^ 2 =
          4 * ‖a * conj c + b * conj d‖ ^ 2 by ring,
        show (2 * ‖a * d - b * c‖) ^ 2 = 4 * ‖a * d - b * c‖ ^ 2 by ring,
        hvisibility, hentanglement]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring
    _ = 1 := by rw [hnormalized]; norm_num

example : b21Predictability (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) = -(7 / 25 : ℝ) := by
  norm_num [b21Predictability, Complex.normSq_apply]

example : b21Visibility (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) = 0 := by
  norm_num [b21Visibility]

example : b21Entanglement (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) = 24 / 25 := by
  rw [b21Entanglement]
  norm_num [Complex.norm_def, Complex.normSq_apply]

/-- A concrete normalized, genuinely entangled instance fires B21 with no
square-root normalization.  Here `P = -7/25`, `V = 0`, and `E = 24/25`. -/
example :
    b21Visibility (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) ^ 2 +
      b21Predictability (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) ^ 2 +
      b21Entanglement (3 / 5 : ℂ) 0 0 (4 / 5 : ℂ) ^ 2 = 1 := by
  apply b21_triality
  norm_num [Complex.normSq_apply]

end RelationalAtlas

#print axioms RelationalAtlas.b21_triality

/-! ## B129 — the two-path complementarity budget and the marker Gram

Integrated from `.ultramath/smwtdtx7v/m8/B129Complementarity.lean` (accepted in the formalisation run).
-/

/-!
# B129 — pure-path complementarity and the marker Gram determinant

This is a self-contained finite algebraic kernel for Atlas card B129.  For
normalized complex amplitudes `z, w`, put

* `D = normSq z - normSq w` (population distinguishability), and
* `V = 2 * ‖z * w‖` (equal-prior path coherence, hence visibility).

Then `D² + V² = 1`.  The marker Gram matrix `[[1,v],[star v,1]]` has complex
determinant `1 - ‖v‖²`.  With the equal-prior coherence `v = 2 * star z * w`,
its norm is exactly `V`, so `det G = D²`, as on the card.

Normalization warning: replacing this `v` by the unscaled product `star z * w`
does **not** prove the displayed Gram identification and in fact makes it false.
The theorem `unscaled_overlap_counterexample` below gives a normalized rational
counterexample.  The published card defines `v` as the overlap of two *marker*
states, not as an arbitrary unscaled product of path amplitudes; our
`pathCoherence` is the convention consistent with `V = 2 * ‖z*w‖` and equal
path priors.  No optimal-discrimination theorem, partial trace, or mixed-state
construction is formalized here.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal
namespace B129

/-- Population distinguishability of two normalized path amplitudes. -/
def pathD (z w : ℂ) : ℝ := Complex.normSq z - Complex.normSq w

/-- Visibility for equal path priors, written as the modulus of path coherence. -/
def pathV (z w : ℂ) : ℝ := 2 * ‖z * w‖

/-- The complex coherence whose modulus is `pathV`; its phase does not affect
any of the real formulas below. -/
def pathCoherence (z w : ℂ) : ℂ := 2 * star z * w

/-- The two-state marker Gram matrix from the card, with conjugate-transpose
symmetry and unit diagonal. -/
def markerGram (v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, v; star v, 1]

/-- The budget before imposing normalization. -/
theorem complementarity_eq_sum_sq (z w : ℂ) :
    pathD z w ^ 2 + pathV z w ^ 2 =
      (Complex.normSq z + Complex.normSq w) ^ 2 := by
  unfold pathD pathV
  rw [mul_pow, Complex.sq_norm, Complex.normSq_mul]
  ring

/-- B129's exact pure-state budget `D² + V² = 1`. -/
theorem complementarity_squared (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    pathD z w ^ 2 + pathV z w ^ 2 = 1 := by
  rw [complementarity_eq_sum_sq, h]
  norm_num

/-- Algebraic form of the interior budget for subnormalized amplitudes.
For genuinely mixed markers, the identification of these scalar formulas with
a partial trace is an additional physical/modeling step not made here. -/
theorem subnormalized_complementarity (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w ≤ 1) :
    pathD z w ^ 2 + pathV z w ^ 2 ≤ 1 := by
  rw [complementarity_eq_sum_sq]
  have hs : 0 ≤ Complex.normSq z + Complex.normSq w :=
    add_nonneg (Complex.normSq_nonneg z) (Complex.normSq_nonneg w)
  nlinarith [mul_nonneg hs (sub_nonneg.mpr h)]

/-- The determinant of the marker Gram matrix is real and equals
`1 - ‖v‖²`. -/
theorem markerGram_det (v : ℂ) :
    (markerGram v).det = ((1 - ‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [markerGram, Matrix.det_fin_two_of]
  simp [Complex.mul_conj']

/-- Pure-marker distinguishability in the optimal-discrimination convention.
The Helstrom/optimal-measurement theorem behind this definition is outside this
algebraic kernel. -/
def gramD (v : ℂ) : ℝ := Real.sqrt (1 - ‖v‖ ^ 2)

/-- Visibility is the modulus of the normalized marker overlap. -/
def gramV (v : ℂ) : ℝ := ‖v‖

/-- Squared pure-marker distinguishability is exactly the Gram determinant's
real value. -/
theorem gramD_sq (v : ℂ) (hv : ‖v‖ ≤ 1) :
    gramD v ^ 2 = 1 - ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by nlinarith [sq_nonneg ‖v‖, norm_nonneg v])

/-- Direct normalized-marker form of B129:
`D = sqrt (1 - |v|²)`, `V = |v|`, hence `D² + V² = 1`. -/
theorem marker_complementarity (v : ℂ) (hv : ‖v‖ ≤ 1) :
    gramD v ^ 2 + gramV v ^ 2 = 1 := by
  rw [gramD_sq v hv]
  simp [gramV]

/-- The same pure-marker quantities give `det G = D²` without mentioning path
amplitudes. -/
theorem marker_gram_det (v : ℂ) (hv : ‖v‖ ≤ 1) :
    (markerGram v).det = (↑(gramD v ^ 2) : ℂ) := by
  rw [markerGram_det, gramD_sq v hv]

/-- The chosen coherence has modulus precisely `V`; the equal-prior factor `2`
is essential here. -/
theorem pathCoherence_norm (z w : ℂ) :
    ‖pathCoherence z w‖ = pathV z w := by
  simp [pathCoherence, pathV, mul_assoc]

/-- Real form of `det G = D²`, using `v = 2 * star z * w`. -/
theorem gram_det_real_identity (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    1 - ‖pathCoherence z w‖ ^ 2 = pathD z w ^ 2 := by
  rw [pathCoherence_norm]
  nlinarith [complementarity_squared z w h]

/-- Normalization gives a genuine normalized marker overlap: its modulus is at
most one. -/
theorem pathCoherence_norm_le_one (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    ‖pathCoherence z w‖ ≤ 1 := by
  have hV : 0 ≤ pathV z w := by
    unfold pathV
    positivity
  rw [pathCoherence_norm]
  nlinarith [sq_nonneg (pathD z w), complementarity_squared z w h]

/-- In the amplitude model, the pure-marker `gramD` is the absolute population
imbalance.  Squaring removes the arbitrary labeling sign of `pathD`. -/
theorem gramD_pathCoherence (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    gramD (pathCoherence z w) = |pathD z w| := by
  unfold gramD
  rw [gram_det_real_identity z w h, Real.sqrt_sq_eq_abs]

/-- B129's Gram reading: determinant, complement of squared visibility, and
squared distinguishability are one and the same quantity. -/
theorem complementarity_gram (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    (markerGram (pathCoherence z w)).det = (↑(pathD z w ^ 2) : ℂ) := by
  rw [markerGram_det, gram_det_real_identity z w h]

/-- A nondegenerate rational normalized pair: its amplitudes are both nonzero,
so this witness exercises both terms in the complementarity identity. -/
def witnessZ : ℂ := 3 / 5
/-- The second amplitude of the rational normalized witness. -/
def witnessW : ℂ := 4 / 5

theorem witness_normalized : Complex.normSq witnessZ + Complex.normSq witnessW = 1 := by
  norm_num [witnessZ, witnessW, Complex.normSq_apply]

example : pathD witnessZ witnessW ^ 2 + pathV witnessZ witnessW ^ 2 = 1 :=
  complementarity_squared witnessZ witnessW witness_normalized

example :
    (markerGram (pathCoherence witnessZ witnessW)).det =
      (↑(pathD witnessZ witnessW ^ 2) : ℂ) :=
  complementarity_gram witnessZ witnessW witness_normalized

example :
    gramD (pathCoherence witnessZ witnessW) ^ 2 +
      gramV (pathCoherence witnessZ witnessW) ^ 2 = 1 :=
  marker_complementarity _
    (pathCoherence_norm_le_one witnessZ witnessW witness_normalized)

/-- The literal unscaled identification `v = star z * w` is false.  At
`z = 3/5`, `w = 4/5`, the left side is `481/625`, whereas `D² = 49/625`.
Thus the factor/convention in `pathCoherence` is not a cosmetic change. -/
theorem unscaled_overlap_counterexample :
    Complex.normSq witnessZ + Complex.normSq witnessW = 1 ∧
      1 - ‖star witnessZ * witnessW‖ ^ 2 ≠
        (Complex.normSq witnessZ - Complex.normSq witnessW) ^ 2 := by
  refine ⟨witness_normalized, ?_⟩
  rw [Complex.sq_norm]
  norm_num [witnessZ, witnessW, Complex.normSq_apply]

end B129
end AtlasFormal

#print axioms AtlasFormal.B129.complementarity_eq_sum_sq
#print axioms AtlasFormal.B129.complementarity_squared
#print axioms AtlasFormal.B129.subnormalized_complementarity
#print axioms AtlasFormal.B129.markerGram_det
#print axioms AtlasFormal.B129.gramD_sq
#print axioms AtlasFormal.B129.marker_complementarity
#print axioms AtlasFormal.B129.marker_gram_det
#print axioms AtlasFormal.B129.pathCoherence_norm
#print axioms AtlasFormal.B129.gram_det_real_identity
#print axioms AtlasFormal.B129.pathCoherence_norm_le_one
#print axioms AtlasFormal.B129.gramD_pathCoherence
#print axioms AtlasFormal.B129.complementarity_gram
#print axioms AtlasFormal.B129.witness_normalized
#print axioms AtlasFormal.B129.unscaled_overlap_counterexample

/-! ## B158 — a large weak value is paid for in success probability

Integrated from `.ultramath/smwtdtx7v/m7/B158WeakValue.lean` (accepted in the formalisation run).
-/

/-!
# B158 — a large weak value is paid for in success probability

This file formalizes the finite Hilbert-space kernel of Atlas card B158.  For
normalized `i` and `f`, with `⟪f,i⟫ ≠ 0`, and a symmetric (Hermitian) linear
operator `A`, define

* `A_w = ⟪f,A i⟫ / ⟪f,i⟫`;
* `p₀ = ‖⟪f,i⟫‖²`;
* the second moment `⟪i,A²i⟫ = ⟪i,A (A i)⟫`.

The displayed bound is `p₀ ‖A_w‖² ≤ Re ⟪i,A (A i)⟫`.  The proof is exactly
Cauchy–Schwarz applied to `f` and `A i`, after cancelling the nonzero weak-value
denominator.  Self-adjointness identifies the second moment with `‖A i‖²`.
The postselection dynamics and finite-strength pointer response are not treated.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas
namespace B158

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Algebra behind `p₀ |A_w|²`: the nonzero overlap cancels the denominator. -/
theorem postselected_weak_value_sq (f i : E) (A : E →ₗ[ℂ] E)
    (h : ⟪f, i⟫_ℂ ≠ 0) :
    ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 =
      ‖⟪f, A i⟫_ℂ‖ ^ 2 := by
  have hn : ‖⟪f, i⟫_ℂ‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [norm_div]
  field_simp

/-- The second moment of a symmetric operator is the squared norm of `A i`. -/
theorem second_moment_eq_norm_sq (i : E) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (⟪i, A (A i)⟫_ℂ).re = ‖A i‖ ^ 2 := by
  rw [← hA i (A i)]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A i)

/-- **B158, Theorem P2.**  For normalized states and a nonzero postselection
overlap, `p₀ |A_w|² ≤ ⟨i|A²|i⟩`.  Here `LinearMap.IsSymmetric` is Hermiticity,
and taking the real part is the scalar second-moment reading.

The unit-norm assumption on `i` is retained exactly as on the card, although
this particular inequality remains true without it.  The unit norm of `f` is
used in Cauchy–Schwarz. -/
theorem weak_value_bound (f i : E) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (_hi : ‖i‖ = 1) (hf : ‖f‖ = 1) (h : ⟪f, i⟫_ℂ ≠ 0) :
    ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 ≤
      (⟪i, A (A i)⟫_ℂ).re := by
  rw [postselected_weak_value_sq f i A h, second_moment_eq_norm_sq i A hA]
  have hcs : ‖⟪f, A i⟫_ℂ‖ ≤ ‖A i‖ := by
    have hle := norm_inner_le_norm (𝕜 := ℂ) f (A i)
    rwa [hf, one_mul] at hle
  nlinarith [norm_nonneg (⟪f, A i⟫_ℂ : ℂ)]

/-! ### A concrete anomalous weak value

The Pauli-x matrix has eigenvalues `1` and `-1`.  With
`i = (1,0)` and `f = (3/5,4/5)`, one has `A i = (0,1)`, hence
`A_w = (4/5)/(3/5) = 4/3`.  The weak value is greater than `1`,
while `p₀ |A_w|² = 16/25 ≤ 1 = ⟨i|A²|i⟩`. -/
section ConcreteExample

abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The Pauli-x matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-x as a linear map on the two-dimensional Hilbert space. -/
def A0 : Qubit →ₗ[ℂ] Qubit := sigmaX.toEuclideanLin

/-- The preselected state `(1,0)`. -/
def i0 : Qubit := !₂[1, 0]

/-- The normalized postselected state `(3/5,4/5)`. -/
def f0 : Qubit := !₂[(3 : ℂ) / 5, 4 / 5]

theorem A0_isSymmetric : A0.IsSymmetric := by
  rw [A0, Matrix.isSymmetric_toEuclideanLin_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.conjTranspose_apply]

theorem i0_norm : ‖i0‖ = 1 := by
  norm_num [EuclideanSpace.norm_eq, i0, Fin.sum_univ_two]

theorem f0_norm : ‖f0‖ = 1 := by
  norm_num [EuclideanSpace.norm_eq, f0, Fin.sum_univ_two]

theorem overlap0 : ⟪f0, i0⟫_ℂ = (3 : ℂ) / 5 := by
  norm_num [PiLp.inner_apply, f0, i0, Fin.sum_univ_two]
  simp only [starRingEnd_apply, star_ofNat]

theorem A0_i0 : A0 i0 = !₂[0, 1] := by
  ext j
  fin_cases j <;>
    norm_num [A0, sigmaX, i0, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- Applying the observable twice returns the initial state (`sigmaX² = 1`). -/
theorem A0_A0_i0 : A0 (A0 i0) = i0 := by
  rw [A0_i0]
  ext j
  fin_cases j <;>
    norm_num [A0, sigmaX, i0, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The numerator of the weak value in the concrete instance. -/
theorem numerator0 : ⟪f0, A0 i0⟫_ℂ = (4 : ℂ) / 5 := by
  rw [A0_i0]
  norm_num [PiLp.inner_apply, f0, Fin.sum_univ_two]
  simp only [starRingEnd_apply, star_ofNat]

/-- The weak value is `4/3`, outside the real interval `[-1,1]` containing
the two eigenvalues of Pauli-x. -/
theorem weak_value0 : ⟪f0, A0 i0⟫_ℂ / ⟪f0, i0⟫_ℂ = (4 : ℂ) / 3 := by
  rw [numerator0, overlap0]
  norm_num

/-- The probability-weighted squared weak value is exactly `16/25`. -/
theorem weighted_square0 :
    ‖⟪f0, i0⟫_ℂ‖ ^ 2 * ‖⟪f0, A0 i0⟫_ℂ / ⟪f0, i0⟫_ℂ‖ ^ 2 =
      (16 : ℝ) / 25 := by
  rw [weak_value0, overlap0]
  norm_num [Complex.norm_def, Complex.normSq_apply]

/-- The second moment is exactly one. -/
theorem second_moment0 : (⟪i0, A0 (A0 i0)⟫_ℂ).re = 1 := by
  rw [A0_A0_i0]
  simp [i0_norm]

/-- This instance really satisfies the hypotheses and fires the general
success-probability bound. -/
theorem two_level_witness :
    ‖⟪f0, i0⟫_ℂ‖ ^ 2 * ‖⟪f0, A0 i0⟫_ℂ / ⟪f0, i0⟫_ℂ‖ ^ 2 ≤
      (⟪i0, A0 (A0 i0)⟫_ℂ).re := by
  apply weak_value_bound f0 i0 A0 A0_isSymmetric i0_norm f0_norm
  rw [overlap0]
  norm_num

/-- The same concrete application, evaluated on both sides: the anomalous weak
value `4/3` still has probability-weighted square only `16/25`. -/
example : (16 : ℝ) / 25 ≤ 1 := by
  rw [← weighted_square0, ← second_moment0]
  exact two_level_witness

end ConcreteExample

end B158
end RelationalAtlas

#print axioms RelationalAtlas.B158.postselected_weak_value_sq
#print axioms RelationalAtlas.B158.second_moment_eq_norm_sq
#print axioms RelationalAtlas.B158.weak_value_bound
#print axioms RelationalAtlas.B158.A0_isSymmetric
#print axioms RelationalAtlas.B158.i0_norm
#print axioms RelationalAtlas.B158.f0_norm
#print axioms RelationalAtlas.B158.overlap0
#print axioms RelationalAtlas.B158.A0_i0
#print axioms RelationalAtlas.B158.A0_A0_i0
#print axioms RelationalAtlas.B158.numerator0
#print axioms RelationalAtlas.B158.weak_value0
#print axioms RelationalAtlas.B158.weighted_square0
#print axioms RelationalAtlas.B158.second_moment0
#print axioms RelationalAtlas.B158.two_level_witness

/-! ## B60 — one complex line forces saturation, and complex parallelism is the criterion

Integrated from `.ultramath/smwtdtx7v/m13/B60Saturation.lean` (accepted in the formalisation run).
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

/-!
# B60 — saturation and one-complex-line tangent geometry

For coordinate vectors `u v : Fin n → ℂ` we use the conjugate-first convention
`Q u v = ∑ j, conj (u j) * v j`.  The real quantum metric is `Re Q` and the
curvature normalization is `Ω = 2 Im (Q u v)`, so the card's displayed bound is
`|Ω|² = 4 det g` at saturation.  The two projected tangent vectors are the input
data; no claim about a physical band family is made here.

Scope: arbitrary finite dimension is covered for the forward parallel-pair theorem.
The exact cross-product/if-and-only-if criterion is proved in two coordinates (the
card's two parameter directions, not a restriction to two levels).  The actual
projector `(1-Π)`, Hermitian band-family hypotheses, and the published kagome
example are outside this finite coordinate kernel; the converse is instead
refuted by an explicit three-coordinate algebraic witness with nonzero curvature.
-/

/-- Squared norm of a finite complex coordinate vector. -/
def b60NormSq {n : ℕ} (u : Fin n → ℂ) : ℝ :=
  ∑ j, Complex.normSq (u j)

/-- Hermitian overlap, conjugate-linear in its first argument. -/
def b60Overlap {n : ℕ} (u v : Fin n → ℂ) : ℂ :=
  ∑ j, (starRingEnd ℂ) (u j) * v j

/-- The two-direction real Gram/quantum-metric matrix. -/
def b60Gram {n : ℕ} (u v : Fin n → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b60NormSq u, (b60Overlap u v).re;
     (b60Overlap u v).re, b60NormSq v]

/-- Curvature in the normalization for which saturation is `|Ω|² = 4 det g`. -/
def b60Omega {n : ℕ} (u v : Fin n → ℂ) : ℝ :=
  2 * (b60Overlap u v).im

/-- `v` lies on the complex line spanned by `u`. -/
def B60ComplexParallel {n : ℕ} (u v : Fin n → ℂ) : Prop :=
  ∃ c : ℂ, v = c • u

/-- The planar cross product detecting failure of complex parallelism in two
coordinates. -/
def b60Cross (u v : Fin 2 → ℂ) : ℂ :=
  u 0 * v 1 - u 1 * v 0

lemma b60Overlap_self {n : ℕ} (u : Fin n → ℂ) :
    b60Overlap u u = (b60NormSq u : ℂ) := by
  simp only [b60Overlap, b60NormSq, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self]

lemma b60NormSq_smul {n : ℕ} (c : ℂ) (u : Fin n → ℂ) :
    b60NormSq (c • u) = Complex.normSq c * b60NormSq u := by
  simp only [b60NormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]

lemma b60Overlap_smul_right {n : ℕ} (c : ℂ) (u : Fin n → ℂ) :
    b60Overlap u (c • u) = c * (b60NormSq u : ℂ) := by
  simp only [b60Overlap, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j, (starRingEnd ℂ) (u j) * (c * u j)) =
        ∑ j, c * ((starRingEnd ℂ) (u j) * u j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = c * ∑ j, (starRingEnd ℂ) (u j) * u j := by rw [Finset.mul_sum]
    _ = c * b60Overlap u u := by rfl
    _ = c * (b60NormSq u : ℂ) := by rw [b60Overlap_self]

/-- A complex-line pair saturates in every finite ambient dimension. -/
theorem b60_saturation_of_complexParallel {n : ℕ} {u v : Fin n → ℂ}
    (h : B60ComplexParallel u v) :
    |b60Omega u v| ^ 2 = 4 * (b60Gram u v).det := by
  rcases h with ⟨c, rfl⟩
  rw [sq_abs]
  simp [b60Gram, b60Omega, b60NormSq_smul, b60Overlap_smul_right,
    Matrix.det_fin_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- In two coordinates, the exact slack in `4 det g − Ω²` is four times the
squared cross product.  This is a direct finite Lagrange/Cauchy–Schwarz identity,
not an additional positivity hypothesis. -/
theorem b60_saturation_defect (u v : Fin 2 → ℂ) :
    4 * (b60Gram u v).det = (b60Omega u v) ^ 2 +
      4 * Complex.normSq (b60Cross u v) := by
  simp [b60Gram, b60Omega, b60NormSq, b60Overlap, b60Cross,
    Matrix.det_fin_two, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Saturation is exactly the vanishing of the complex cross product. -/
theorem b60_saturation_iff_cross_eq_zero (u v : Fin 2 → ℂ) :
    |b60Omega u v| ^ 2 = 4 * (b60Gram u v).det ↔ b60Cross u v = 0 := by
  rw [sq_abs, b60_saturation_defect]
  constructor
  · intro h
    have hs : Complex.normSq (b60Cross u v) = 0 := by
      have hn := Complex.normSq_nonneg (b60Cross u v)
      nlinarith
    exact Complex.normSq_eq_zero.mp hs
  · intro h
    rw [h, Complex.normSq_zero]
    ring

/-- For nonzero `u`, the planar cross-product criterion really is complex
parallelism.  The hypothesis `u ≠ 0` removes the degenerate case `u = 0`,
`v ≠ 0`, where saturation holds although no scalar `c` has `v = c • u`. -/
lemma b60ComplexParallel_of_cross_eq_zero {u v : Fin 2 → ℂ}
    (hu : u ≠ 0) (hcross : b60Cross u v = 0) :
    B60ComplexParallel u v := by
  have huv : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp hcross
  rcases eq_or_ne (u 0) 0 with hu0 | hu0
  · have hu1 : u 1 ≠ 0 := by
      intro hu1
      apply hu
      funext j
      fin_cases j <;> simp [hu0, hu1]
    have hu1v0 : u 1 * v 0 = 0 := by
      simpa [hu0] using huv.symm
    have hv0 : v 0 = 0 := (mul_eq_zero.mp hu1v0).resolve_left hu1
    refine ⟨v 1 / u 1, ?_⟩
    funext j
    fin_cases j
    · change v 0 = (v 1 / u 1) * u 0
      simp [hu0, hv0]
    · change v 1 = (v 1 / u 1) * u 1
      field_simp [hu1]
  · refine ⟨v 0 / u 0, ?_⟩
    funext j
    fin_cases j
    · change v 0 = (v 0 / u 0) * u 0
      field_simp [hu0]
    · change v 1 = (v 0 / u 0) * u 1
      field_simp [hu0]
      linear_combination huv

/-- **B60 equality criterion.** Away from the zero first tangent, saturation is
exactly complex parallelism of the two projected tangent vectors. -/
theorem b60_saturation_iff_complexParallel {u v : Fin 2 → ℂ} (hu : u ≠ 0) :
    |b60Omega u v| ^ 2 = 4 * (b60Gram u v).det ↔ B60ComplexParallel u v := by
  constructor
  · intro h
    exact b60ComplexParallel_of_cross_eq_zero hu
      ((b60_saturation_iff_cross_eq_zero u v).mp h)
  · exact b60_saturation_of_complexParallel

/-- Arithmetic in the card: `k(n-k)=1` forces both `k=1` and `n=2`. -/
theorem b60_dimension_one_forces_two_levels {n k : ℕ} (h : k * (n - k) = 1) :
    k = 1 ∧ n - k = 1 ∧ n = 2 := by
  have hk : k = 1 := Nat.eq_one_of_mul_eq_one_right h
  have hq : n - k = 1 := Nat.eq_one_of_mul_eq_one_left h
  exact ⟨hk, hq, by omega⟩

/-- **B60, the displayed two-level implication.** When `k(n-k)=1`, the preceding
arithmetic gives `k=1` and `n=2`.  On that one complex line the two projected
tangents are represented by their coordinates `a b : ℂ` along one fixed unit
basis vector, hence by `Fin 1 → ℂ`.  No extra parallel-pair hypothesis is needed:
this coordinate type is precisely the rank-one model, and the conclusion is the
card's `|Ω|² = 4 det g`.  Zero coordinates are allowed. -/
theorem b60_two_levels_force_saturation {n k : ℕ} (hnk : k * (n - k) = 1)
    (a b : ℂ) :
    k = 1 ∧ n = 2 ∧
      |b60Omega (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)| ^ 2 =
        4 * (b60Gram (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).det := by
  have hdim := b60_dimension_one_forces_two_levels hnk
  refine ⟨hdim.1, hdim.2.2, ?_⟩
  rw [sq_abs]
  simp [b60Gram, b60Omega, b60NormSq, b60Overlap, Matrix.det_fin_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The two-coordinate saturation identity also gives the unsaturated bound. -/
theorem b60_curvature_le_metric (u v : Fin 2 → ℂ) :
    |b60Omega u v| ^ 2 ≤ 4 * (b60Gram u v).det := by
  rw [sq_abs, b60_saturation_defect]
  nlinarith [Complex.normSq_nonneg (b60Cross u v)]

/-- A concrete nondegenerate two-level instance has line coordinates `a=1` and
`b=I`.  It has `det g = 1`, `Ω = 2`, and the displayed theorem fires with
`k=1`, `n=2` and `1*(2-1)=1`. -/
example :
    |b60Omega (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => Complex.I)| ^ 2 =
      4 * (b60Gram (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => Complex.I)).det := by
  exact (b60_two_levels_force_saturation (n := 2) (k := 1)
    (by norm_num) 1 Complex.I).2.2

/-- The card's converse is false even with nonzero curvature.  In a three-level,
`tangent-dimension-two` reading (`n=3`, `k=2`, so `k(n-k)=2`), the symmetric
parallel pair `u=(1,1,0)`, `v=Iu` has `Ω=4` and saturates. -/
theorem b60_saturation_does_not_imply_two_levels :
    ∃ n k : ℕ, ∃ u v : Fin 3 → ℂ,
      (|b60Omega u v| ^ 2 = 4 * (b60Gram u v).det) ∧
      k * (n - k) ≠ 1 ∧ b60Omega u v ≠ 0 := by
  let u : Fin 3 → ℂ := ![1, 1, 0]
  let v : Fin 3 → ℂ := ![Complex.I, Complex.I, 0]
  have hparallel : B60ComplexParallel u v := by
    refine ⟨Complex.I, ?_⟩
    funext j
    fin_cases j <;> simp [u, v, Pi.smul_apply, smul_eq_mul]
  have homega : b60Omega u v = 4 := by
    norm_num [b60Omega, b60Overlap, u, v, Fin.sum_univ_three,
      Complex.normSq_apply]
  refine ⟨3, 2, u, v, b60_saturation_of_complexParallel hparallel,
    by norm_num, ?_⟩
  rw [homega]
  norm_num

end AtlasFormal

#print axioms AtlasFormal.b60Overlap_self
#print axioms AtlasFormal.b60NormSq_smul
#print axioms AtlasFormal.b60Overlap_smul_right
#print axioms AtlasFormal.b60_saturation_of_complexParallel
#print axioms AtlasFormal.b60_saturation_defect
#print axioms AtlasFormal.b60_saturation_iff_cross_eq_zero
#print axioms AtlasFormal.b60ComplexParallel_of_cross_eq_zero
#print axioms AtlasFormal.b60_saturation_iff_complexParallel
#print axioms AtlasFormal.b60_dimension_one_forces_two_levels
#print axioms AtlasFormal.b60_two_levels_force_saturation
#print axioms AtlasFormal.b60_curvature_le_metric
#print axioms AtlasFormal.b60_saturation_does_not_imply_two_levels

/-! ## B87 — which symmetry forbids the linear coupling

Integrated from `.ultramath/smwtdtx7v/m3/B87Crossing.lean` (accepted in the formalisation run).
-/

/-!
# B87 — symmetry selection and the quadratic/conical normal forms

This file formalizes the finite algebraic kernel of B87. A traceless real
symmetric `2 × 2` matrix is written as `traceless u v = !![u,v;v,-u]`.
Conjugation by a planar rotation rotates the pair `(u,v)` through *twice* the
angle. Consequently a displacement has rotation weight one while the
traceless perturbation has weight two.

For an arbitrary real-linear first-order coupling we use the `90°` consequence
of continuous `SO(2)` equivariance to prove that all four coefficients vanish.
By contrast, the explicit Jahn--Teller coupling `jahnTeller x y = traceless x
(-y)` is equivariant for the `120°` (`Z₃`) action and has eigenvalues `±r` in
polar coordinates. The protected diagonal normal form has eigenvalues
`cos²ϑ` and `1`, hence gap `1-cos²ϑ = sin²ϑ`.

Thus the proved content is the card's selection rule and its exact quadratic
and conical gap normal forms. We do **not** assert the false generic statement
that every point-fixing symmetry forbids a linear term: the `Z₃` example below
is a counterexample to that reading. Berry/eigenline holonomy, line-field
indices, asymptotic ratios, measured numerical constants and continuum
symmetry classification are outside this finite file.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

open Matrix Real
open Polynomial

/-- The two coordinates of a traceless symmetric real `2 × 2` matrix. -/
def traceless (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u, v; v, -u]

/-- Planar rotation by `θ`. -/
def rotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-- The general real-linear map from displacement `(x,y)` to a traceless
symmetric perturbation. -/
def linearTraceless (a b c d x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  traceless (a*x + b*y) (c*x + d*y)

/-- The explicit nonzero linear Jahn--Teller coupling. -/
def jahnTeller (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := traceless x (-y)

/-- The protected diagonal normal form, with eigenvalues `cos²ϑ` and `1`. -/
def protectedFamily (ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos ϑ ^ 2, 0; 0, 1]

/-- Conjugation of a traceless symmetric matrix by `rotation θ` has rotation
weight two: `(u,v)` is rotated by `2θ`. -/
theorem rotation_traceless (θ u v : ℝ) :
    rotation θ * traceless u v * (rotation θ)ᵀ =
      traceless (cos (2*θ)*u - sin (2*θ)*v) (sin (2*θ)*u + cos (2*θ)*v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, traceless, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_two_mul', Real.sin_two_mul] <;> ring

/-- At `90°`, the displacement has weight one and the traceless matrix has
weight two, hence the latter is negated. -/
theorem rotation90_traceless (u v : ℝ) :
    rotation (π/2) * traceless u v * (rotation (π/2))ᵀ = -traceless u v := by
  rw [rotation_traceless]
  have h : 2 * (π/2) = π := by ring
  rw [h, Real.cos_pi, Real.sin_pi]
  simp [traceless]

/-- The explicit displacement transformation used below is multiplication by
the `90°` rotation matrix. -/
theorem rotation90_displacement (x y : ℝ) :
    rotation (π/2) *ᵥ ![x, y] = ![-y, x] := by
  ext i
  fin_cases i <;> simp [rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **B87 selection rule (continuous rotation).** If a real-linear coupling
from the weight-one displacement to the weight-two traceless matrix is
equivariant under the `90°` action, all its coefficients vanish. This single
angle is a consequence of full `SO(2)` equivariance, so the conclusion holds
under the card's continuous-symmetry hypothesis. -/
theorem so2_linear_term_forbidden (a b c d : ℝ)
    (h : ∀ x y : ℝ, linearTraceless a b c d (-y) x =
      rotation (π/2) * linearTraceless a b c d x y * (rotation (π/2))ᵀ) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h' : ∀ x y : ℝ, linearTraceless a b c d (-y) x =
      -linearTraceless a b c d x y := by
    intro x y
    rw [h]
    unfold linearTraceless
    rw [rotation_traceless]
    have hp : 2 * (π/2) = π := by ring
    rw [hp, Real.cos_pi, Real.sin_pi]
    simp [traceless]
  have h10 := h' 1 0
  have h01 := h' 0 1
  have h10u := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h10
  have h10v := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h10
  have h01u := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h01
  have h01v := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h01
  simp [linearTraceless, traceless] at h10u h10v h01u h01v
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Therefore the whole first-order perturbation, not merely its coefficients,
vanishes in the continuously rotation-invariant case. -/
theorem so2_linear_term_eq_zero (a b c d : ℝ)
    (h : ∀ x y : ℝ, linearTraceless a b c d (-y) x =
      rotation (π/2) * linearTraceless a b c d x y * (rotation (π/2))ᵀ)
    (x y : ℝ) : linearTraceless a b c d x y = 0 := by
  rcases so2_linear_term_forbidden a b c d h with ⟨rfl, rfl, rfl, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linearTraceless, traceless]

/-- Exact cosine of the `Z₃` rotation angle. -/
lemma cos_z3_turn : cos (2*π/3) = -1/2 := by
  rw [show 2*π/3 = 2*(π/3) by ring, Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num

/-- Exact sine of the `Z₃` rotation angle. -/
lemma sin_z3_turn : sin (2*π/3) = √3/2 := by
  rw [show 2*π/3 = 2*(π/3) by ring, Real.sin_two_mul,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

/-- Cosine of twice the `Z₃` rotation angle. -/
lemma cos_z3_double_turn : cos (2*(2*π/3)) = -1/2 := by
  rw [Real.cos_two_mul, cos_z3_turn]
  norm_num

/-- Sine of twice the `Z₃` rotation angle. -/
lemma sin_z3_double_turn : sin (2*(2*π/3)) = -√3/2 := by
  rw [Real.sin_two_mul, sin_z3_turn, cos_z3_turn]
  ring

/-- **B87, the allowed branch.** The nonzero linear Jahn--Teller coupling is
equivariant under the `120°` action: its source rotates through `120°`, while
its traceless target rotates through `240°`. Thus `Z₃` alone does not forbid
the linear term; the actual transformation weights matter. -/
theorem z3_linear_term_allowed (x y : ℝ) :
    jahnTeller (cos (2*π/3)*x - sin (2*π/3)*y)
        (sin (2*π/3)*x + cos (2*π/3)*y) =
      rotation (2*π/3) * jahnTeller x y * (rotation (2*π/3))ᵀ := by
  unfold jahnTeller
  rw [rotation_traceless]
  congr 1 <;>
    simp [cos_z3_turn, sin_z3_turn, cos_z3_double_turn, sin_z3_double_turn] <;> ring

/-- The characteristic polynomial of a traceless symmetric `2 × 2` matrix
factors over the reals, with eigenvalues `±√(u²+v²)`. -/
theorem traceless_charpoly (u v : ℝ) :
    (traceless u v).charpoly =
      (X - C (√(u^2 + v^2))) * (X + C (√(u^2 + v^2))) := by
  have hs : (√(u^2 + v^2))^2 = u^2 + v^2 :=
    Real.sq_sqrt (by positivity)
  rw [Matrix.charpoly_fin_two]
  simp [traceless, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
  have hsC : (C (√(u^2+v^2)) : ℝ[X]) * C (√(u^2+v^2)) =
      C (u*u) + C v * C v := by
    rw [← C_mul, ← C_mul, ← C_add]
    congr 1
    nlinarith
  have huC : (C u : ℝ[X])^2 = C (u*u) := by
    rw [sq, ← C_mul]
  linear_combination hsC - huC

/-- **B87 conical normal form.** On the Jahn--Teller family in polar
coordinates `(x,y)=(r cosφ,r sinφ)`, the two eigenvalues are exactly `±r`
(for `r ≥ 0`), so the spectral gap `r-(-r)` is exactly `2r`, linear in the
radius. -/
theorem conical_gap (r φ : ℝ) (hr : 0 ≤ r) :
    (jahnTeller (r*cos φ) (r*sin φ)).charpoly = (X - C r) * (X + C r) ∧
      r - (-r) = 2*r := by
  constructor
  · rw [show jahnTeller (r*cos φ) (r*sin φ) =
        traceless (r*cos φ) (-(r*sin φ)) by rfl]
    have hradius : √((r*cos φ)^2 + (r*sin φ)^2) = r := by
      have hsum : (r*cos φ)^2 + (r*sin φ)^2 = r^2 := by
        nlinarith [Real.sin_sq_add_cos_sq φ]
      rw [hsum, Real.sqrt_sq hr]
    simpa [hradius] using traceless_charpoly (r*cos φ) (-(r*sin φ))
  · ring

/-- The characteristic polynomial of the protected diagonal family is the
product corresponding to its two displayed diagonal eigenvalues. -/
theorem protectedFamily_charpoly (ϑ : ℝ) :
    (protectedFamily ϑ).charpoly = (X - C (cos ϑ^2)) * (X - C 1) := by
  rw [Matrix.charpoly_fin_two]
  simp [protectedFamily, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- **B87 protected quadratic gap.** The gap between the diagonal eigenvalues
`1` and `cos²ϑ` is exactly `sin²ϑ`; in particular it has no linear term at the
degeneracy `ϑ=0`. -/
theorem protected_gap (ϑ : ℝ) : 1 - cos ϑ^2 = sin ϑ^2 := by
  linear_combination -(Real.sin_sq_add_cos_sq ϑ)

/-- At the degeneracy the protected family is the scalar identity matrix. -/
theorem protectedFamily_degenerate : protectedFamily 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [protectedFamily]

/-- A concrete nontrivial conical instance: the allowed linear family at
`(x,y)=(3,4)` has eigenvalues `±5`, hence gap `10`. -/
example : (jahnTeller 3 4).charpoly = (X - C (5:ℝ)) * (X + C (5:ℝ)) := by
  have hs : √((3:ℝ)^2 + 4^2) = 5 := by
    rw [show (3:ℝ)^2 + 4^2 = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]
  simpa [jahnTeller, hs] using traceless_charpoly 3 (-4)

/-- A concrete protected instance at `ϑ=π/2` has gap one. -/
example : 1 - cos (π/2)^2 = (1:ℝ) := by
  rw [protected_gap]
  norm_num

/-- The `SO(2)` selection theorem has satisfiable hypotheses and fires on a
nonzero displacement. -/
example : linearTraceless 0 0 0 0 (1:ℝ) 2 = 0 := by
  apply so2_linear_term_eq_zero
  intro x y
  have hz (s t : ℝ) : linearTraceless 0 0 0 0 s t = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [linearTraceless, traceless]
  rw [hz, hz]
  simp

end AtlasFormal

#print axioms AtlasFormal.rotation_traceless
#print axioms AtlasFormal.rotation90_traceless
#print axioms AtlasFormal.rotation90_displacement
#print axioms AtlasFormal.so2_linear_term_forbidden
#print axioms AtlasFormal.so2_linear_term_eq_zero
#print axioms AtlasFormal.cos_z3_turn
#print axioms AtlasFormal.sin_z3_turn
#print axioms AtlasFormal.cos_z3_double_turn
#print axioms AtlasFormal.sin_z3_double_turn
#print axioms AtlasFormal.z3_linear_term_allowed
#print axioms AtlasFormal.traceless_charpoly
#print axioms AtlasFormal.conical_gap
#print axioms AtlasFormal.protectedFamily_charpoly
#print axioms AtlasFormal.protected_gap
#print axioms AtlasFormal.protectedFamily_degenerate

/-! ## B92 — the determinant keeps the sum of the phases and one wrap integer

Integrated from `.ultramath/smwtdtx7v/m2/B92PhaseDeterminant.lean` (accepted in the formalisation run).
-/

/-!
# B92 — the determinant discards exactly one wrap

The published formula is `w = (1 / (2π)) ∑ j, arg λj ∈ ℤ` when `det R = 1`.
Here `λ` is any finite list of complex numbers whose product is `R.det` (for
example, the eigenvalues with algebraic multiplicity).  No diagonalizability or
unit-modulus hypothesis is needed for this algebraic statement.

The second displayed identity, `det R = exp (Tr log R)`, is proved below in the
diagonal normal form, using the principal complex logarithm entrywise.  The
card's path continuity, branch tracking, and the physical interpretation of the
integer are not formalized.  In particular, this is a finite algebraic kernel,
not a theorem about lifting eigenvalue branches along a path.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

open scoped BigOperators
open Matrix

/-- The principal-argument wrap invariant from B92. -/
def phaseWrap {ι : Type*} [Fintype ι] (lam : ι → ℂ) : ℝ :=
  (∑ i, Complex.arg (lam i)) / (2 * Real.pi)

/-- A finite product is the exponential of the sum of principal logarithms. -/
theorem prod_eq_exp_sum_log {ι : Type*} [Fintype ι] (lam : ι → ℂ)
    (hlam : ∀ i, lam i ≠ 0) :
    (∏ i, lam i) = Complex.exp (∑ i, Complex.log (lam i)) := by
  calc
    (∏ i, lam i) = ∏ i, Complex.exp (Complex.log (lam i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Complex.exp_log (hlam i)).symm
    _ = Complex.exp (∑ i, Complex.log (lam i)) := by
      symm
      simpa using (Complex.exp_sum Finset.univ (fun i => Complex.log (lam i)))

/-- If the product is one, the sum of principal arguments is an integral
multiple of `2π`.  This is the finite algebraic content of B92. -/
theorem sum_arg_eq_int_mul_two_pi_of_prod_eq_one {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hprod : (∏ i, lam i) = 1) :
    ∃ w : ℤ, (∑ i, Complex.arg (lam i)) = (w : ℝ) * (2 * Real.pi) := by
  have hp0 : (∏ i, lam i) ≠ 0 := by simp [hprod]
  have hlam : ∀ i, lam i ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hp0) i (Finset.mem_univ i)
  have hexp : Complex.exp (∑ i, Complex.log (lam i)) = 1 := by
    rw [← prod_eq_exp_sum_log lam hlam, hprod]
  obtain ⟨w, hw⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨w, ?_⟩
  have him := congrArg Complex.im hw
  simpa [Complex.log_im, mul_comm, mul_left_comm, mul_assoc] using him

/-- **B92.** If `det R = 1` and `λ` multiplies to `det R`, then
`(2π)⁻¹ ∑ j, arg λj` is an integer. -/
theorem b92_determinant_discards_wrap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (lam : ι → ℂ)
    (hprod : R.det = ∏ i, lam i) (hdet : R.det = 1) :
    ∃ w : ℤ, phaseWrap lam = (w : ℝ) := by
  have hp : (∏ i, lam i) = 1 := by rw [← hprod, hdet]
  obtain ⟨w, hw⟩ := sum_arg_eq_int_mul_two_pi_of_prod_eq_one lam hp
  refine ⟨w, ?_⟩
  unfold phaseWrap
  rw [hw]
  field_simp [Real.pi_ne_zero]

/-- The other displayed B92 identity, in diagonal normal form:
`det R = exp (Tr log R)` for entrywise principal logarithms. -/
theorem det_diagonal_eq_exp_trace_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) :
    (Matrix.diagonal lam).det =
      Complex.exp (Matrix.trace (Matrix.diagonal (fun i => Complex.log (lam i)))) := by
  rw [Matrix.det_diagonal, Matrix.trace_diagonal]
  exact prod_eq_exp_sum_log lam hlam

/-- A concrete instance firing the general determinant theorem: the diagonal
`4 × 4` matrix with every eigenvalue `I` has determinant one. -/
example : ∃ w : ℤ, phaseWrap (fun _ : Fin 4 => Complex.I) = (w : ℝ) := by
  apply b92_determinant_discards_wrap
    (Matrix.diagonal (fun _ : Fin 4 => Complex.I)) (fun _ => Complex.I)
    Matrix.det_diagonal
  simp [Matrix.det_diagonal]

/-- The same witness has wrap number one, not zero, while its determinant is
one.  Thus the conclusion above is non-vacuous and exhibits the lost wrap. -/
example : phaseWrap (fun _ : Fin 4 => Complex.I) = (1 : ℝ) := by
  unfold phaseWrap
  simp [Complex.arg_I]
  field_simp [Real.pi_ne_zero]
  norm_num

end AtlasFormal

#print axioms AtlasFormal.prod_eq_exp_sum_log
#print axioms AtlasFormal.sum_arg_eq_int_mul_two_pi_of_prod_eq_one
#print axioms AtlasFormal.b92_determinant_discards_wrap
#print axioms AtlasFormal.det_diagonal_eq_exp_trace_log

/-! ## B100 — the echo crosses a circle, not a radius cutoff

Integrated from `.ultramath/smwtdtx7v/m6/B100EchoCircle.lean` (accepted in the formalisation run).
-/

/-!
# B100 — the echo crosses a circle, not a radius cutoff

This is the finite complex-algebra kernel of Jeromie Beasley's Atlas card B100.
For
`r = (a + x) / (1 + a*x)`, `A = 1 - |a|^4`, and `C = conj a * (1 - a^2)`,
we prove the *combined* decision theorem

  `|r|^2 > |a|^2  ↔  |x - xc| > |xc|`,   where `xc = -conj C / A`.

The hypotheses are exactly the finite ones on the card: `|a| < 1` (which makes
`A > 0`) and `1 + a*x ≠ 0`.  The left inequality is written with
`Complex.normSq`, i.e. with squared moduli.  The right inequality is written
with norms, exactly as on the published card; `echo_gt_bulk_sq_iff` also records
the version in which both sides are squared.

The optical interpretation of `a` and `x`, wavelength, film thickness, detection
thresholds, and homogeneous-film optics are not formalized.  In particular, this
is an exact Möbius-transformation/circle theorem, not a measured reflectance law.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas

open Complex

/-- The positive circle coefficient `A = 1 - |a|^4`. -/
def echoA (a : ℂ) : ℝ := 1 - Complex.normSq a ^ 2

/-- The linear circle coefficient `C = conj a * (1 - a^2)`. -/
def echoC (a : ℂ) : ℂ := (starRingEnd ℂ) a * (1 - a * a)

/-- Centre of the circle, written in real and imaginary coordinates.
`centre_eq` below identifies this with `-conj C / A`. -/
noncomputable def centre (A : ℝ) (C : ℂ) : ℂ := ⟨-C.re / A, C.im / A⟩

/-- The published centre `xc = -conj C / A`. -/
noncomputable def echoCentre (a : ℂ) : ℂ := centre (echoA a) (echoC a)

/-- **B100, exact reflectance difference.**
`|r|² - |a|² = (A|x|² + 2 Re(Cx)) / |1 + ax|²`. -/
theorem echo_circle (a x : ℂ) (h : 1 + a * x ≠ 0) :
    normSq ((a + x) / (1 + a * x)) - normSq a =
      ((1 - normSq a ^ 2) * normSq x +
        2 * ((starRingEnd ℂ) a * (1 - a * a) * x).re) / normSq (1 + a * x) := by
  have hn : normSq (1 + a * x) ≠ 0 := by
    intro h0
    exact h (normSq_eq_zero.mp h0)
  rw [normSq_div, eq_div_iff hn, sub_mul, div_mul_cancel₀ _ hn]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, one_re, one_im,
    sub_re, sub_im, conj_re, conj_im]
  ring

/-- Coordinate centre formula in the conventional complex form. -/
theorem centre_eq (A : ℝ) (_hA : A ≠ 0) (C : ℂ) :
    centre A C = -(starRingEnd ℂ) C / (A : ℂ) := by
  apply Complex.ext <;> simp [centre, div_ofReal_re, div_ofReal_im]

/-- The circle identity `A(|x-xc|²-|xc|²) = A|x|² + 2 Re(Cx)`. -/
theorem circle_identity (A : ℝ) (hA : A ≠ 0) (C x : ℂ) :
    A * (normSq (x - centre A C) - normSq (centre A C)) =
      A * normSq x + 2 * (C * x).re := by
  simp only [centre, normSq_apply, sub_re, sub_im, mul_re]
  field_simp
  ring

/-- For `A > 0`, positivity of the reflectance numerator is precisely the
strict exterior of the circle. -/
theorem circle_criterion (A : ℝ) (hA : 0 < A) (C x : ℂ) :
    0 < A * normSq x + 2 * (C * x).re ↔
      normSq (centre A C) < normSq (x - centre A C) := by
  rw [← circle_identity A hA.ne' C x, mul_pos_iff_of_pos_left hA, sub_pos]

/-- The boundary circle passes through the origin. -/
theorem circle_through_origin (A : ℝ) (C : ℂ) :
    normSq (0 - centre A C) = normSq (centre A C) := by
  rw [zero_sub, normSq_neg]

/-- `|a| < 1` gives the positive coefficient required by the circle criterion. -/
theorem echoA_pos_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) : 0 < echoA a := by
  have h1 : ‖a‖ ^ 2 < (1 : ℝ) := by
    simpa [pow_two] using mul_self_lt_mul_self (norm_nonneg a) ha
  have h4 : (‖a‖ ^ 2) ^ 2 < (1 : ℝ) := by
    simpa [pow_two] using mul_self_lt_mul_self (sq_nonneg ‖a‖) h1
  unfold echoA
  rw [Complex.normSq_eq_norm_sq]
  linarith

/-- **B100, squared circle form.**  Exceeding the bulk reflectance is equivalent
to the strict exterior inequality with squared moduli on both sides. -/
theorem echo_gt_bulk_sq_iff (a x : ℂ) (ha : ‖a‖ < 1) (h : 1 + a * x ≠ 0) :
    normSq a < normSq ((a + x) / (1 + a * x)) ↔
      normSq (echoCentre a) < normSq (x - echoCentre a) := by
  have hn : 0 < normSq (1 + a * x) := normSq_pos.mpr h
  have hnum :
      normSq a < normSq ((a + x) / (1 + a * x)) ↔
        0 < (1 - normSq a ^ 2) * normSq x +
          2 * ((starRingEnd ℂ) a * (1 - a * a) * x).re := by
    rw [← sub_pos, echo_circle a x h]
    exact div_pos_iff_of_pos_right hn
  exact hnum.trans (circle_criterion (echoA a) (echoA_pos_of_norm_lt_one ha) (echoC a) x)

/-- Squared-modulus strict inequalities are norm strict inequalities. -/
theorem normSq_lt_normSq_iff_norm_lt (z w : ℂ) :
    normSq z < normSq w ↔ ‖z‖ < ‖w‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact sq_lt_sq₀ (norm_nonneg z) (norm_nonneg w)

/-- **B100, the card's displayed decision formula.**
For `r = (a+x)/(1+ax)` and `xc = -conj C/A`,
`|r|² > |a|² ↔ |x-xc| > |xc|`. -/
theorem echo_gt_bulk_iff (a x : ℂ) (ha : ‖a‖ < 1) (h : 1 + a * x ≠ 0) :
    normSq ((a + x) / (1 + a * x)) > normSq a ↔
      ‖x - echoCentre a‖ > ‖echoCentre a‖ := by
  exact (echo_gt_bulk_sq_iff a x ha h).trans (normSq_lt_normSq_iff_norm_lt _ _)

/-- The `xc` used in the decision theorem has the card's formula
`-conj(conj a * (1-a²)) / (1-|a|⁴)`. -/
theorem echoCentre_eq (a : ℂ) (ha : ‖a‖ < 1) :
    echoCentre a = -(starRingEnd ℂ) (echoC a) / (echoA a : ℂ) := by
  exact centre_eq (echoA a) (echoA_pos_of_norm_lt_one ha).ne' (echoC a)

/-- **One radius cannot decide.**  The two echoes `x = 1/5` and `x = -1/5`
have equal modulus for `a = 1/2`, but raise and lower the reflectance respectively. -/
theorem one_radius_cannot_decide :
    ((1 / 2 + 1 / 5) / (1 + 1 / 2 * (1 / 5)) : ℝ) ^ 2 = 49 / 121 ∧
      (1 / 2 : ℝ) ^ 2 < 49 / 121 ∧
      ((1 / 2 - 1 / 5) / (1 - 1 / 2 * (1 / 5)) : ℝ) ^ 2 = 1 / 9 ∧
      (1 / 9 : ℝ) < (1 / 2 : ℝ) ^ 2 := by
  norm_num

/-- A concrete non-vacuous instance: `a = 1/2` and `x = 1/5` satisfy both
hypotheses and fire `echo_gt_bulk_iff` on the strict (outside) side. -/
theorem b100_concrete_witness :
    ∃ a x : ℂ, ‖a‖ < 1 ∧ 1 + a * x ≠ 0 ∧
      normSq ((a + x) / (1 + a * x)) > normSq a ∧
      ‖x - echoCentre a‖ > ‖echoCentre a‖ := by
  let a : ℂ := ((1 / 2 : ℝ) : ℂ)
  let x : ℂ := ((1 / 5 : ℝ) : ℂ)
  have ha : ‖a‖ < 1 := by
    dsimp [a]
    norm_num
  have h : 1 + a * x ≠ 0 := by
    dsimp [a, x]
    norm_num
  have hbulk : normSq ((a + x) / (1 + a * x)) > normSq a := by
    dsimp [a, x]
    norm_num [normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨a, x, ha, h, hbulk, (echo_gt_bulk_iff a x ha h).mp hbulk⟩

/-- The same concrete instance, presented as an explicit `example`:
`a = 1/2` and `x = 1/5`. -/
example :
    let a : ℂ := ((1 / 2 : ℝ) : ℂ)
    let x : ℂ := ((1 / 5 : ℝ) : ℂ)
    ‖a‖ < 1 ∧ 1 + a * x ≠ 0 ∧
      normSq ((a + x) / (1 + a * x)) > normSq a ∧
      ‖x - echoCentre a‖ > ‖echoCentre a‖ := by
  dsimp only
  have ha : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by norm_num
  have h : 1 + ((1 / 2 : ℝ) : ℂ) * ((1 / 5 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hbulk :
      normSq ((((1 / 2 : ℝ) : ℂ) + ((1 / 5 : ℝ) : ℂ)) /
        (1 + ((1 / 2 : ℝ) : ℂ) * ((1 / 5 : ℝ) : ℂ))) >
          normSq ((1 / 2 : ℝ) : ℂ) := by
    norm_num [normSq_apply, Complex.div_re, Complex.div_im]
  exact ⟨ha, h, hbulk, (echo_gt_bulk_iff _ _ ha h).mp hbulk⟩

end RelationalAtlas

#print axioms RelationalAtlas.echo_circle
#print axioms RelationalAtlas.centre_eq
#print axioms RelationalAtlas.circle_identity
#print axioms RelationalAtlas.circle_criterion
#print axioms RelationalAtlas.circle_through_origin
#print axioms RelationalAtlas.echoA_pos_of_norm_lt_one
#print axioms RelationalAtlas.echo_gt_bulk_sq_iff
#print axioms RelationalAtlas.normSq_lt_normSq_iff_norm_lt
#print axioms RelationalAtlas.echo_gt_bulk_iff
#print axioms RelationalAtlas.echoCentre_eq
#print axioms RelationalAtlas.one_radius_cannot_decide
#print axioms RelationalAtlas.b100_concrete_witness

/-! ## B105 — the discarded products return as the associator

Integrated from `.ultramath/smwtdtx7v/m10/B105ReducedAssociator.lean` (accepted in the formalisation run).
-/

/-!
# B105 — discarded products return as an associator

This file formalizes the finite algebraic kernel of Atlas card B105.  In an
associative ring `R`, the reduced product is `x ⋆ y = P (x*y)` and the discarded
part is `Q x = x - P x` (so `Q = I - P`).  The main theorem below is exactly

  `(x ⋆ y) ⋆ z - x ⋆ (y ⋆ z) = P (x*Q(y*z) - Q(x*y)*z)`.

The card states that `P` is a projection and checks `P²=P`.  Accordingly the
card-level theorem includes idempotence as a hypothesis.  Algebraic expansion
of the displayed identity itself uses only additivity of `P`; no stronger
linearity or multiplicativity is assumed.

No claim is made about a physical reduction procedure, a topology, or convergence.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal
namespace B105

/-- The reduced product obtained by retaining only the `P`-part of an ambient
associative product. -/
def reducedProduct {R : Type*} [Ring R] (P : R →+ R) (x y : R) : R :=
  P (x * y)

/-- The complementary/discarded part `Q x = (I-P)x`. -/
def discardedPart {R : Type*} [Ring R] (P : R →+ R) (x : R) : R :=
  x - P x

/-- **B105, exact reduced-product associator.**  If `P` is an additive
idempotent on an associative ring, then the two parenthesizations of its reduced
product differ by precisely the two discarded intermediate products re-entering
through `P`.

The hypothesis `hP` is the card's explicit `P²=P` condition.  It is deliberately
retained even though the algebraic expansion does not need to rewrite with it.
-/
theorem reduced_associator {R : Type*} [Ring R] (P : R →+ R)
    (_hP : ∀ a, P (P a) = P a) (x y z : R) :
    reducedProduct P (reducedProduct P x y) z -
        reducedProduct P x (reducedProduct P y z) =
      P (x * discardedPart P (y * z) - discardedPart P (x * y) * z) := by
  unfold reducedProduct discardedPart
  rw [← map_sub]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- A concrete additive projection onto the diagonal of `ℝ × ℝ`, where the
ambient product is pointwise multiplication. -/
def diagonalAverageProjection : (ℝ × ℝ) →+ (ℝ × ℝ) where
  toFun p := ((p.1 + p.2) / 2, (p.1 + p.2) / 2)
  map_zero' := by norm_num
  map_add' p q := by
    ext <;> simp <;> ring

/-- Non-vacuity: the projection satisfies the card's `P²=P` hypothesis, and the
main theorem fires with a strictly nonzero defect.  For
`x=(1,2)`, `y=(1,0)`, `z=(0,1)`, both sides of its displayed identity equal
`(1/4,1/4)`.  In particular, this is not an associative-product tautology with
an always-zero conclusion. -/
example :
    reducedProduct diagonalAverageProjection
          (reducedProduct diagonalAverageProjection (1, 2) (1, 0)) (0, 1) -
        reducedProduct diagonalAverageProjection (1, 2)
          (reducedProduct diagonalAverageProjection (1, 0) (0, 1)) =
      ((1 / 4 : ℝ), (1 / 4 : ℝ)) ∧
    ((1 / 4 : ℝ), (1 / 4 : ℝ)) ≠ 0 := by
  have hP : ∀ p : ℝ × ℝ,
      diagonalAverageProjection (diagonalAverageProjection p) =
        diagonalAverageProjection p := by
    rintro ⟨a, b⟩
    ext <;> simp [diagonalAverageProjection]
  have h := reduced_associator diagonalAverageProjection hP
    (1, 2) (1, 0) (0, 1)
  constructor
  · rw [h]
    norm_num [discardedPart, diagonalAverageProjection]
  · intro hzero
    have hfirst := congrArg Prod.fst hzero
    norm_num at hfirst

end B105
end AtlasFormal

#print axioms AtlasFormal.B105.reduced_associator

/-! ## B190 — the three-way budget of a scalar edge

Integrated from `.ultramath/smwtdtx7v/m12/B190.lean` (accepted in the formalisation run).
-/

/-!
# B190 — the edge complementarity identity

For an edge with real inner-product end vectors `a` and `b`, put
`s = ‖a‖² + ‖b‖²` and use the two book energies
`E⁺ = ‖a + b‖²`, `E⁻ = ‖a - b‖²`.  This is the normalization in B190's
"Why it holds" section.  Hermitian matrix blocks are included by taking their
real Frobenius inner product; the graph and the unitary transport only produce
the pair `(a,b)` and are not needed for the algebraic identity.

The displayed identity is exactly
`Pe² + Ve² + Le² = 1`.  I formalize `Le²` directly, rather than choosing a sign
for `Le`.  Common-rescaling invariance, random-edge witnesses, and the physical
Jakob–Bergou interpretation are outside this kernel and are not claimed here.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal.B190

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The common scale `s = ‖a‖² + ‖b‖²`. -/
def s (a b : E) : ℝ := ‖a‖ ^ 2 + ‖b‖ ^ 2

/-- The parallel-book energy `E⁺ = ‖a+b‖²`. -/
def Eplus (a b : E) : ℝ := ‖a + b‖ ^ 2

/-- The antiparallel-book energy `E⁻ = ‖a-b‖²`. -/
def Eminus (a b : E) : ℝ := ‖a - b‖ ^ 2

/-- B190 predictability: `Pe = (‖a‖² - ‖b‖²) / s`. -/
def Pe (a b : E) : ℝ := (‖a‖ ^ 2 - ‖b‖ ^ 2) / s a b

/-- B190 visibility: `Ve = (E⁺ - E⁻) / (E⁺ + E⁻)`. -/
def Ve (a b : E) : ℝ := (Eplus a b - Eminus a b) / (Eplus a b + Eminus a b)

/-- B190's squared concurrence, the normalized two-vector Gram determinant. -/
def LeSq (a b : E) : ℝ :=
  4 * (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2) / (s a b) ^ 2

/-- The polarization identity for B190's two books. -/
theorem book_energy_sub (a b : E) :
    Eplus a b - Eminus a b = 4 * ⟪a, b⟫_ℝ := by
  rw [Eplus, Eminus, norm_add_sq_real, norm_sub_sq_real]
  ring

/-- The book-energy budget is `E⁺ + E⁻ = 2s`. -/
theorem book_energy_add (a b : E) : Eplus a b + Eminus a b = 2 * s a b := by
  rw [Eplus, Eminus, s, norm_add_sq_real, norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ E] in
/-- At least one nonzero end gives B190's check `s > 0`. -/
theorem s_pos (a b : E) (h : a ≠ 0 ∨ b ≠ 0) : 0 < s a b := by
  unfold s
  rcases h with ha | hb
  · have ha' : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
    nlinarith [sq_nonneg ‖b‖]
  · have hb' : 0 < ‖b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
    nlinarith [sq_nonneg ‖a‖]

/-- Consequently, visibility is the normalized overlap `Ve = 2⟨a,b⟩/s`. -/
theorem Ve_eq_two_inner_div (a b : E) (hs : 0 < s a b) :
    Ve a b = 2 * ⟪a, b⟫_ℝ / s a b := by
  rw [Ve, book_energy_sub, book_energy_add]
  field_simp [hs.ne']
  ring

/-- **B190 complementarity.**  With `s > 0`, the card's three displayed
quantities satisfy `Pe² + Ve² + Le² = 1`. -/
theorem complementarity (a b : E) (hs : 0 < s a b) :
    Pe a b ^ 2 + Ve a b ^ 2 + LeSq a b = 1 := by
  rw [Ve_eq_two_inner_div a b hs]
  unfold Pe LeSq
  field_simp [hs.ne']
  unfold s
  ring

/-- The Gram-determinant numerator is nonnegative by Cauchy–Schwarz. -/
theorem gram_numerator_nonneg (a b : E) :
    0 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 := by
  have hcs : |⟪a, b⟫_ℝ| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have hsq : |⟪a, b⟫_ℝ| ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [sq_abs, mul_pow] at hsq
  exact sub_nonneg.mpr hsq

/-- In particular, B190's squared concurrence is nonnegative. -/
theorem LeSq_nonneg (a b : E) : 0 ≤ LeSq a b := by
  unfold LeSq
  exact div_nonneg (mul_nonneg (by norm_num) (gram_numerator_nonneg a b))
    (sq_nonneg _)

/-- **Corrected equality case.**  If the left end is nonzero, `Le² = 0` exactly
when `b` is a real scalar multiple of `a`.  The hypothesis `a ≠ 0` is needed:
the published shorthand omits the boundary case `a = 0`, `b ≠ 0`. -/
theorem LeSq_eq_zero_iff (a b : E) (ha : a ≠ 0) :
    LeSq a b = 0 ↔ ∃ r : ℝ, b = r • a := by
  have hs : 0 < s a b := s_pos a b (Or.inl ha)
  constructor
  · intro h
    have hdet : ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 = 0 := by
      unfold LeSq at h
      field_simp [hs.ne'] at h
      nlinarith
    have hsquares : |⟪a, b⟫_ℝ| ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
      rw [sq_abs, mul_pow]
      nlinarith
    have heq : |⟪a, b⟫_ℝ| = ‖a‖ * ‖b‖ :=
      (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsquares
    have hdep : a = 0 ∨ ∃ r : ℝ, b = r • a :=
      ((norm_inner_eq_norm_tfae ℝ a b).out 1 3).mp (by
        simpa [Real.norm_eq_abs] using heq)
    exact hdep.resolve_left ha
  · rintro ⟨r, rfl⟩
    simp only [LeSq, norm_smul, Real.norm_eq_abs, real_inner_smul_self_right,
      mul_pow, sq_abs]
    ring

/-- The unqualified printed assertion "`Le = 0` iff `b` is a real multiple of
`a`" is false at the permitted boundary `a = 0`, `b ≠ 0`. -/
theorem zero_left_end_counterexample :
    0 < s (0 : ℝ) 1 ∧ LeSq (0 : ℝ) 1 = 0 ∧
      ¬ ∃ r : ℝ, (1 : ℝ) = r • (0 : ℝ) := by
  refine ⟨by norm_num [s], by norm_num [LeSq, s, inner], ?_⟩
  rintro ⟨r, hr⟩
  norm_num at hr

/-- A concrete non-scalar edge: all three contributions are nonzero. -/
theorem complex_edge_values :
    Pe (1 : ℂ) (1 + Complex.I) = -1 / 3 ∧
    Ve (1 : ℂ) (1 + Complex.I) = 2 / 3 ∧
    LeSq (1 : ℂ) (1 + Complex.I) = 4 / 9 := by
  norm_num [Pe, Ve, LeSq, Eplus, Eminus, s, Complex.sq_norm,
    Complex.normSq_apply, inner]

/-- This concrete instance satisfies the card's check and fires the main
complementarity theorem. -/
example : Pe (1 : ℂ) (1 + Complex.I) ^ 2 + Ve (1 : ℂ) (1 + Complex.I) ^ 2 +
    LeSq (1 : ℂ) (1 + Complex.I) = 1 := by
  apply complementarity
  norm_num [s, Complex.sq_norm, Complex.normSq_apply]

end AtlasFormal.B190

#print axioms AtlasFormal.B190.book_energy_sub
#print axioms AtlasFormal.B190.book_energy_add
#print axioms AtlasFormal.B190.s_pos
#print axioms AtlasFormal.B190.Ve_eq_two_inner_div
#print axioms AtlasFormal.B190.complementarity
#print axioms AtlasFormal.B190.gram_numerator_nonneg
#print axioms AtlasFormal.B190.LeSq_nonneg
#print axioms AtlasFormal.B190.LeSq_eq_zero_iff
#print axioms AtlasFormal.B190.zero_left_end_counterexample
#print axioms AtlasFormal.B190.complex_edge_values

/-! ## B199 — the balanced trace form and the nonzero nilpotent

Integrated from `.ultramath/smwtdtx7v/m14/B199BalancedNilpotent.lean` (accepted in the formalisation run).
-/

/-!
# B199 — the balanced trace form and nonzero nilpotents

This file formalizes the finite algebraic kernel of Atlas card B199.  Every real
traceless `2 × 2` matrix satisfies `T² = q(T) • I`, where `q(T)` is one half of
the difference between the squared Frobenius norms of its symmetric and skew
parts.  Moreover, `q(T) = 0` is equivalent to `T² = 0`; consequently `q(T) = 0`
and `T ≠ 0` is exactly the nonzero nilpotent assertion.

The dimension, scalar field, and trace-zero hypotheses are essential and are
stated explicitly.  The oscillator theorem below concerns the *traceless part*
of the usual generator.  No growth/turning interpretation, matrix exponential,
critical-damping asymptotic, ISCO assertion, or other continuum claim is proved.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal
namespace B199

open Matrix

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℝ

/-- Squared Frobenius norm of a real `2 × 2` matrix, written without a square root. -/
def frobNormSq (T : Mat₂) : ℝ := ∑ i, ∑ j, (T i j) ^ 2

/-- For a real matrix, `Herm T` in the card is its symmetric part. -/
def hermPart (T : Mat₂) : Mat₂ := (2 : ℝ)⁻¹ • (T + T.transpose)

/-- For a real matrix, `Skew T` in the card is its skew-symmetric part. -/
def skewPart (T : Mat₂) : Mat₂ := (2 : ℝ)⁻¹ • (T - T.transpose)

/-- The card's trace form `q(T) = ½(‖Herm T‖² - ‖Skew T‖²)`. -/
def traceFormQ (T : Mat₂) : ℝ :=
  (frobNormSq (hermPart T) - frobNormSq (skewPart T)) / 2

/-- Coordinate formula for the trace form (also valid without tracelessness). -/
theorem traceFormQ_apply (T : Mat₂) :
    traceFormQ T = (T 0 0) ^ 2 / 2 + (T 1 1) ^ 2 / 2 + T 0 1 * T 1 0 := by
  simp [traceFormQ, frobNormSq, hermPart, skewPart, Fin.sum_univ_two]
  ring

/-- In the traceless case the coordinate formula is `a² + bc`. -/
theorem traceFormQ_of_trace_eq_zero (T : Mat₂) (hT : Matrix.trace T = 0) :
    traceFormQ T = (T 0 0) ^ 2 + T 0 1 * T 1 0 := by
  rw [traceFormQ_apply]
  rw [Matrix.trace_fin_two] at hT
  have hd : T 1 1 = -T 0 0 := by linarith
  rw [hd]
  ring

/-- **B199's displayed formula.**  A real traceless `2 × 2` matrix satisfies
`T² = q(T)I`, with `q` defined by the symmetric/skew Frobenius norms. -/
theorem traceless_sq_eq_traceFormQ (T : Mat₂) (hT : Matrix.trace T = 0) :
    T ^ 2 = traceFormQ T • (1 : Mat₂) := by
  rw [traceFormQ_of_trace_eq_zero T hT]
  rw [Matrix.trace_fin_two] at hT
  have hd : T 1 1 = -T 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hd] <;> ring

/-- The wall condition is exactly square-zero, with no nonzero assumption needed. -/
theorem traceFormQ_eq_zero_iff_sq_eq_zero (T : Mat₂) (hT : Matrix.trace T = 0) :
    traceFormQ T = 0 ↔ T ^ 2 = 0 := by
  constructor
  · intro hq
    rw [traceless_sq_eq_traceFormQ T hT, hq, zero_smul]
  · intro hs
    have h := congrArg (fun M : Mat₂ => M 0 0) (traceless_sq_eq_traceFormQ T hT)
    rw [hs] at h
    simpa using h.symm

/-- **B199's nonzero-wall characterization.**  Under the card's real, dimension-two,
traceless hypotheses, `q(T) = 0` and `T ≠ 0` iff `T` is a nonzero nilpotent.
The reverse implication uses that the trace of a nilpotent real matrix is zero. -/
theorem balanced_iff_nonzero_nilpotent (T : Mat₂) (hT : Matrix.trace T = 0) :
    (traceFormQ T = 0 ∧ T ≠ 0) ↔ (T ≠ 0 ∧ IsNilpotent T) := by
  constructor
  · rintro ⟨hq, hne⟩
    exact ⟨hne, 2, (traceFormQ_eq_zero_iff_sq_eq_zero T hT).mp hq⟩
  · rintro ⟨hne, hnil⟩
    refine ⟨?_, hne⟩
    have hnil2 : IsNilpotent (T ^ 2) := hnil.pow_of_pos (by norm_num)
    have htrace2 : Matrix.trace (T ^ 2) = 0 :=
      (Matrix.isNilpotent_trace_of_isNilpotent hnil2).eq_zero
    have hs := congrArg Matrix.trace (traceless_sq_eq_traceFormQ T hT)
    rw [htrace2] at hs
    simp [Matrix.trace_smul, Matrix.trace_one] at hs
    linarith

/-- The card's symmetric-versus-rotation normal form, with `q = h² - r²`. -/
def keyMatrix (h r : ℝ) : Mat₂ := !![h, r; -r, -h]

theorem keyMatrix_trace (h r : ℝ) : Matrix.trace (keyMatrix h r) = 0 := by
  simp [keyMatrix]

theorem keyMatrix_traceFormQ (h r : ℝ) : traceFormQ (keyMatrix h r) = h ^ 2 - r ^ 2 := by
  rw [traceFormQ_of_trace_eq_zero _ (keyMatrix_trace h r)]
  simp [keyMatrix]
  ring

/-- The normal-form specialization of B199: `T² = (h²-r²)I`. -/
theorem keyMatrix_sq (h r : ℝ) :
    (keyMatrix h r) ^ 2 = (h ^ 2 - r ^ 2) • (1 : Mat₂) := by
  rw [traceless_sq_eq_traceFormQ _ (keyMatrix_trace h r), keyMatrix_traceFormQ]

/-- Traceless part of `[[0, 1], [-ω², -2ωζ]]`, namely
`[[ωζ, 1], [-ω², -ωζ]]`. -/
def oscillatorPart (ω ζ : ℝ) : Mat₂ := !![ω * ζ, 1; -ω ^ 2, -(ω * ζ)]

theorem oscillatorPart_trace (ω ζ : ℝ) : Matrix.trace (oscillatorPart ω ζ) = 0 := by
  simp [oscillatorPart]

/-- The card's oscillator formula `q = ω²(ζ²-1)`. -/
theorem oscillatorPart_traceFormQ (ω ζ : ℝ) :
    traceFormQ (oscillatorPart ω ζ) = ω ^ 2 * (ζ ^ 2 - 1) := by
  rw [traceFormQ_of_trace_eq_zero _ (oscillatorPart_trace ω ζ)]
  simp [oscillatorPart]
  ring

/-- The orbit block displayed on the card. -/
def orbitMatrix (κ : ℝ) : Mat₂ := !![0, 1; -κ ^ 2, 0]

theorem orbitMatrix_trace (κ : ℝ) : Matrix.trace (orbitMatrix κ) = 0 := by
  simp [orbitMatrix]

theorem orbitMatrix_traceFormQ (κ : ℝ) : traceFormQ (orbitMatrix κ) = -κ ^ 2 := by
  rw [traceFormQ_of_trace_eq_zero _ (orbitMatrix_trace κ)]
  simp [orbitMatrix]

/-- Concrete non-vacuous wall instance: the balanced key matrix at `h = r = 1`
satisfies the left side of the equivalence because it is nonzero and nilpotent. -/
example : traceFormQ (keyMatrix 1 1) = 0 ∧ keyMatrix 1 1 ≠ 0 := by
  apply (balanced_iff_nonzero_nilpotent _ (keyMatrix_trace 1 1)).mpr
  constructor
  · intro hz
    have hentry := congrArg (fun M : Mat₂ => M 0 0) hz
    norm_num [keyMatrix] at hentry
  · refine ⟨2, ?_⟩
    rw [keyMatrix_sq]
    norm_num

/-- A non-wall instance fires the displayed square formula with nonzero `q = 3`. -/
example : (keyMatrix 2 1) ^ 2 = (3 : ℝ) • (1 : Mat₂) := by
  rw [keyMatrix_sq]
  norm_num

end B199
end AtlasFormal

#print axioms AtlasFormal.B199.traceFormQ_apply
#print axioms AtlasFormal.B199.traceFormQ_of_trace_eq_zero
#print axioms AtlasFormal.B199.traceless_sq_eq_traceFormQ
#print axioms AtlasFormal.B199.traceFormQ_eq_zero_iff_sq_eq_zero
#print axioms AtlasFormal.B199.balanced_iff_nonzero_nilpotent
#print axioms AtlasFormal.B199.keyMatrix_trace
#print axioms AtlasFormal.B199.keyMatrix_traceFormQ
#print axioms AtlasFormal.B199.keyMatrix_sq
#print axioms AtlasFormal.B199.oscillatorPart_trace
#print axioms AtlasFormal.B199.oscillatorPart_traceFormQ
#print axioms AtlasFormal.B199.orbitMatrix_trace
#print axioms AtlasFormal.B199.orbitMatrix_traceFormQ

/-! ## B122 — the exact norm of the defective-block semigroup

Integrated from `.ultramath/smwtdtx7v/m16/B122SemigroupNorm.lean` (accepted in the formalisation run).
-/

/-
B122 (Jeromie Beasley, Operator-First Relational Atlas): the finite spectral-norm
kernel.  All matrix norms in this file are the L2 operator (largest singular
value) norms, not entrywise or Frobenius norms.

The published display is
  ‖exp(-t J)‖ = exp(-bt) * (sqrt(4 + μ²t²) + |μ|t)/2,
  J = [[b, μ], [0, b]].
For real t, the theorem below writes |μ*t|.  When 0 ≤ t this reduces to the
published |μ|t.  The factor is also proved to be the unique global solution of
X'(t)=-X(t)J with X(0)=I, so no matrix-exponential series calculation is needed.
The transient-growth threshold κ > 2, its maximizing time, and Mmax are not
formalized here.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal

open Matrix Real

/-- The strictly upper-triangular 2 by 2 nilpotent. -/
def b122N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- `I+sN`, the unscaled Jordan semigroup factor. -/
def b122A (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := 1 + s • b122N

/-- Its larger singular value. -/
def b122Q (s : ℝ) : ℝ := (Real.sqrt (4 + s^2) + |s|) / 2

/-- Its smaller singular value; `b122Q s * b122Qinv s = 1`. -/
def b122Qinv (s : ℝ) : ℝ := (Real.sqrt (4 + s^2) - |s|) / 2

lemma b122A_entries (s : ℝ) : b122A s = !![1, s; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b122A, b122N]

lemma b122_sqrt_sq (s : ℝ) : Real.sqrt (4 + s^2)^2 = 4 + s^2 :=
  Real.sq_sqrt (by positivity)

lemma b122_abs_le_sqrt (s : ℝ) : |s| ≤ Real.sqrt (4 + s^2) := by
  rw [show |s| = Real.sqrt (s^2) by rw [Real.sqrt_sq_eq_abs]]
  exact Real.sqrt_le_sqrt (by linarith)

lemma b122_two_le_sqrt (s : ℝ) : 2 ≤ Real.sqrt (4 + s^2) := by
  rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq] <;> norm_num]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])

lemma b122Q_pos (s : ℝ) : 0 < b122Q s := by
  have h := Real.sqrt_pos.2 (show 0 < 4 + s^2 by positivity)
  unfold b122Q
  positivity

lemma b122Q_nonneg (s : ℝ) : 0 ≤ b122Q s := (b122Q_pos s).le

lemma b122_one_le_Q (s : ℝ) : 1 ≤ b122Q s := by
  have h := b122_two_le_sqrt s
  have ha := abs_nonneg s
  unfold b122Q
  linarith

lemma b122Qinv_nonneg (s : ℝ) : 0 ≤ b122Qinv s := by
  have h := b122_abs_le_sqrt s
  unfold b122Qinv
  linarith

lemma b122Q_mul_Qinv (s : ℝ) : b122Q s * b122Qinv s = 1 := by
  have h := b122_sqrt_sq s
  have ha := sq_abs s
  unfold b122Q b122Qinv
  nlinarith

lemma b122Qinv_le_one (s : ℝ) : b122Qinv s ≤ 1 := by
  have hp := b122Q_mul_Qinv s
  have hq := b122_one_le_Q s
  have hn := b122Qinv_nonneg s
  nlinarith

lemma b122Qinv_le_Q (s : ℝ) : b122Qinv s ≤ b122Q s :=
  (b122Qinv_le_one s).trans (b122_one_le_Q s)

lemma b122_eigenvalue_sum (s : ℝ) :
    b122Q s^2 + b122Qinv s^2 = 2 + s^2 := by
  have h := b122_sqrt_sq s
  have ha := sq_abs s
  unfold b122Q b122Qinv
  nlinarith

lemma b122_eigenvalue_product (s : ℝ) :
    b122Q s^2 * b122Qinv s^2 = 1 := by
  have h := b122Q_mul_Qinv s
  nlinarith

/-- The two singular values multiply to one and their squares sum to `2+s²`. -/
lemma b122_larger_root (s : ℝ) :
    (b122Q s^2)^2 - (2 + s^2) * b122Q s^2 + 1 = 0 := by
  have hs := b122_eigenvalue_sum s
  have hp := b122_eigenvalue_product s
  linear_combination b122Q s^2 * hs - hp

/-- The squared singular value.  Notice the `2`: the optional fallback identity
in the task statement has `1+s²` instead of `2+s²`, but that auxiliary formula
is false at `s=1`.  The card's unsquared norm formula itself is correct. -/
lemma b122Q_sq (s : ℝ) :
    b122Q s^2 = (2 + s^2 + |s| * Real.sqrt (4 + s^2)) / 2 := by
  have h := b122_sqrt_sq s
  have ha := sq_abs s
  unfold b122Q
  calc
    ((Real.sqrt (4 + s^2) + |s|) / 2)^2 =
        (Real.sqrt (4 + s^2)^2 + 2 * |s| * Real.sqrt (4 + s^2) + |s|^2) / 4 := by
          ring
    _ = (2 + s^2 + |s| * Real.sqrt (4 + s^2)) / 2 := by
      rw [h, ha]
      ring

/-- The Gram matrix of `I+sN`. -/
lemma b122_gram (s : ℝ) :
    (b122A s)ᵀ * b122A s = !![1, s; s, 1 + s^2] := by
  rw [b122A_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Characteristic polynomial of the Gram matrix, factored by the squares of the
larger and smaller singular values. -/
lemma b122_gram_charpoly (s : ℝ) :
    ((b122A s)ᵀ * b122A s).charpoly =
      (Polynomial.X - Polynomial.C (b122Q s^2)) *
        (Polynomial.X - Polynomial.C (b122Qinv s^2)) := by
  rw [b122_gram, Matrix.charpoly_fin_two]
  have htr : (!![1, s; s, 1 + s^2] : Matrix (Fin 2) (Fin 2) ℝ).trace = 2+s^2 := by
    simp [Matrix.trace, Fin.sum_univ_two]
    ring
  have hdet : (!![1, s; s, 1 + s^2] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    simp [Matrix.det_fin_two]
    ring
  rw [htr, hdet, ← b122_eigenvalue_sum s, ← b122_eigenvalue_product s]
  simp only [map_add, map_mul, map_one]
  ring

/-- A two-variable quadratic with zero discriminant and nonnegative diagonal is
nonnegative.  This elementary form avoids any sign split on the off-diagonal. -/
lemma b122_quadratic_nonneg {a b d x y : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a * d = b^2) :
    0 ≤ a*x^2 + 2*b*x*y + d*y^2 := by
  by_cases ha0 : a = 0
  · subst a
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    simp [hb]
    positivity
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hkey : a * (a*x^2 + 2*b*x*y + d*y^2) = (a*x + b*y)^2 := by
      calc
        a * (a*x^2 + 2*b*x*y + d*y^2) =
            (a*x + b*y)^2 + (a*d-b^2)*y^2 := by ring
        _ = (a*x + b*y)^2 := by rw [had]; ring
    have hnonneg : 0 ≤ a * (a*x^2 + 2*b*x*y + d*y^2) := by
      rw [hkey]
      positivity
    exact nonneg_of_mul_nonneg_right hnonneg ha'

/-! ## The Jordan initial-value problem

Uniqueness is proved coordinatewise via `ODE_solution_unique_univ`.  The two
off-diagonal entries solve one forced and one zero scalar equation; the two
diagonal entries solve `f'=-bf`.  This avoids expanding an exponential series. -/
section B122ScalarODE

/-- The generator `J=[[b,μ],[0,b]]`. -/
def b122J (b μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b,μ;0,b]

/-- The displayed closed factor `e^{-bt}(I-μtN)`. -/
def b122Semigroup (b μ : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (-(b*t)) • (1 - (μ*t) • b122N)

/-- The closed factor has the identity initial condition. -/
lemma b122_semigroup_zero (b μ : ℝ) : b122Semigroup b μ 0 = 1 := by
  simp [b122Semigroup]

lemma b122_entry_derivative {b μ : ℝ} (X : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hX : ∀ t, HasDerivAt X (-X t * b122J b μ) t) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun u => X u i j) ((-X t * b122J b μ) i j) t := by
  exact (hasDerivAt_pi.mp ((hasDerivAt_pi.mp (hX t)) i)) j

/-- The closed factor solves `X'=-XJ`, proved entry by entry. -/
lemma b122_semigroup_hasDerivAt (b μ t : ℝ) :
    HasDerivAt (b122Semigroup b μ) (-b122Semigroup b μ t * b122J b μ) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  fin_cases i <;> fin_cases j
  · have hlin : HasDerivAt (fun u : ℝ => -(b*u)) (-b) t := by
      simpa [neg_mul] using (hasDerivAt_id t).const_mul (-b)
    have hE : HasDerivAt (fun u : ℝ => Real.exp (-(b*u)))
        (-b * Real.exp (-(b*t))) t := by
      convert hlin.exp using 1 <;> ring
    simpa [b122Semigroup, b122N, b122J, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm] using hE
  · have hlin : HasDerivAt (fun u : ℝ => -(b*u)) (-b) t := by
      simpa [neg_mul] using (hasDerivAt_id t).const_mul (-b)
    have hE : HasDerivAt (fun u : ℝ => Real.exp (-(b*u)))
        (-b * Real.exp (-(b*t))) t := by
      convert hlin.exp using 1 <;> ring
    have hμ : HasDerivAt (fun u : ℝ => μ*u) μ t := by
      simpa using (hasDerivAt_id t).const_mul μ
    have hmul := hE.mul (hμ.neg)
    convert hmul using 1
    · funext u
      simp [b122Semigroup, b122N]
    · simp [b122Semigroup, b122N, b122J, Matrix.mul_apply, Fin.sum_univ_two]
      ring
  · simpa [b122Semigroup, b122N, b122J, Matrix.mul_apply, Fin.sum_univ_two] using
      (hasDerivAt_const t (0 : ℝ))
  · have hlin : HasDerivAt (fun u : ℝ => -(b*u)) (-b) t := by
      simpa [neg_mul] using (hasDerivAt_id t).const_mul (-b)
    have hE : HasDerivAt (fun u : ℝ => Real.exp (-(b*u)))
        (-b * Real.exp (-(b*t))) t := by
      convert hlin.exp using 1 <;> ring
    simpa [b122Semigroup, b122N, b122J, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm] using hE

lemma b122_scalar_lipschitz (b : ℝ) : ∀ t : ℝ, LipschitzOnWith ‖(-b : ℝ)‖₊
    (fun x : ℝ => -b*x) Set.univ := by
  intro t
  apply LipschitzWith.lipschitzOnWith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  calc
    ‖-b*x - (-b*y)‖ = ‖(-b)*(x-y)‖ := by congr 1; ring
    _ ≤ (‖(-b : ℝ)‖₊ : ℝ) * ‖x-y‖ := by simp [norm_mul]

lemma b122_scalar_exp_unique (b c : ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (-b*f t) t) (hf0 : f 0 = c) :
    f = fun t => c * Real.exp (-(b*t)) := by
  have hlin (t : ℝ) : HasDerivAt (fun u : ℝ => -(b*u)) (-b) t := by
    simpa [neg_mul] using (hasDerivAt_id t).const_mul (-b)
  have hE (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (-(b*u)))
      (-b * Real.exp (-(b*t))) t := by
    convert (hlin t).exp using 1 <;> ring
  apply ODE_solution_unique_univ (v := fun _ x => -b*x) (s := fun _ => Set.univ)
    (t₀ := 0) (K := ‖(-b : ℝ)‖₊) (b122_scalar_lipschitz b)
  · intro t
    exact ⟨hf t, Set.mem_univ _⟩
  · intro t
    constructor
    · convert (hE t).const_mul c using 1 <;> ring
    · exact Set.mem_univ _
  · simp [hf0]

lemma b122_scalar_forced_unique (b μ : ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (-μ*Real.exp (-(b*t)) - b*f t) t) (hf0 : f 0 = 0) :
    f = fun t => -(μ*t) * Real.exp (-(b*t)) := by
  have hlin (t : ℝ) : HasDerivAt (fun u : ℝ => -(b*u)) (-b) t := by
    simpa [neg_mul] using (hasDerivAt_id t).const_mul (-b)
  have hE (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (-(b*u)))
      (-b * Real.exp (-(b*t))) t := by
    convert (hlin t).exp using 1 <;> ring
  have hμ (t : ℝ) : HasDerivAt (fun u : ℝ => μ*u) μ t := by
    simpa using (hasDerivAt_id t).const_mul μ
  apply ODE_solution_unique_univ
    (v := fun t x => -μ*Real.exp (-(b*t)) - b*x) (s := fun _ => Set.univ)
    (t₀ := 0) (K := ‖(-b : ℝ)‖₊)
  · intro t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm]
    calc
      ‖(-μ*Real.exp (-(b*t))-b*x) - (-μ*Real.exp (-(b*t))-b*y)‖ =
          ‖(-b)*(x-y)‖ := by congr 1; ring
      _ ≤ (‖(-b : ℝ)‖₊ : ℝ) * ‖x-y‖ := by simp [norm_mul]
  · intro t
    exact ⟨hf t, Set.mem_univ _⟩
  · intro t
    constructor
    · convert ((hμ t).mul (hE t)).neg using 1
      · funext u
        simp [mul_comm]
      · ring
    · exact Set.mem_univ _
  · simp [hf0]

/-- **ODE characterization of the Jordan exponential.**  Every global solution
of `X'=-XJ` with `X(0)=I` equals the displayed closed factor. -/
lemma b122_semigroup_unique (b μ : ℝ) (X : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hX : ∀ t, HasDerivAt X (-X t * b122J b μ) t) (hX0 : X 0 = 1) :
    X = b122Semigroup b μ := by
  have h00 : (fun t => X t 0 0) = fun t => 1 * Real.exp (-(b*t)) := by
    apply b122_scalar_exp_unique b 1
    · intro t
      simpa [b122J, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using b122_entry_derivative X hX t 0 0
    · have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℝ => Y 0 0) hX0
      simpa using h
  have h10 : (fun t => X t 1 0) = fun t => 0 * Real.exp (-(b*t)) := by
    apply b122_scalar_exp_unique b 0
    · intro t
      simpa [b122J, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using b122_entry_derivative X hX t 1 0
    · have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℝ => Y 1 0) hX0
      simpa using h
  have h00' (t : ℝ) : X t 0 0 = Real.exp (-(b*t)) := by
    have h := congrFun h00 t
    simpa using h
  have h10' (t : ℝ) : X t 1 0 = 0 := by
    have h := congrFun h10 t
    simpa using h
  have h01 : (fun t => X t 0 1) = fun t => -(μ*t) * Real.exp (-(b*t)) := by
    apply b122_scalar_forced_unique b μ
    · intro t
      convert b122_entry_derivative X hX t 0 1 using 1 <;>
        simp [b122J, Matrix.mul_apply, Fin.sum_univ_two, h00' t] <;> ring
    · have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℝ => Y 0 1) hX0
      simpa using h
  have h11 : (fun t => X t 1 1) = fun t => 1 * Real.exp (-(b*t)) := by
    apply b122_scalar_exp_unique b 1
    · intro t
      simpa [b122J, Matrix.mul_apply, Fin.sum_univ_two, h10' t, mul_comm] using b122_entry_derivative X hX t 1 1
    · have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℝ => Y 1 1) hX0
      simpa using h
  have h01' (t : ℝ) : X t 0 1 = -(μ*t) * Real.exp (-(b*t)) := congrFun h01 t
  have h11' (t : ℝ) : X t 1 1 = Real.exp (-(b*t)) := by
    have h := congrFun h11 t
    simpa using h
  funext t
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [b122Semigroup, b122N] using h00' t
  · simp [b122Semigroup, b122N]
    rw [h01' t]
    ring
  · simpa [b122Semigroup, b122N] using h10' t
  · simpa [b122Semigroup, b122N] using h11' t


end B122ScalarODE

open scoped Matrix.Norms.L2Operator

/-- Squared Euclidean length after applying `I+sN`, in coordinates. -/
lemma b122_norm_shift_apply_sq (s : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s) x‖^2 = (x 0 + s*x 1)^2 + (x 1)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [Matrix.mulVec, Fin.sum_univ_two, b122A_entries, Matrix.vecHead, Matrix.vecTail]

/-- Rayleigh upper bound: `q²` majorizes the Gram quadratic form. -/
lemma b122_rayleigh_bound (s x y : ℝ) :
    (x + s*y)^2 + y^2 ≤ b122Q s^2 * (x^2 + y^2) := by
  have hq := b122_one_le_Q s
  have hm := b122Qinv_le_one s
  have hm0 := b122Qinv_nonneg s
  have ha : 0 ≤ b122Q s^2 - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by linarith : 0 ≤ b122Q s + 1)]
  have hd : 0 ≤ 1 - b122Qinv s^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (by linarith : 0 ≤ b122Qinv s + 1)]
  have had : (b122Q s^2 - 1) * (1 - b122Qinv s^2) = (-s)^2 := by
    have hs := b122_eigenvalue_sum s
    have hp := b122_eigenvalue_product s
    nlinarith
  have h := b122_quadratic_nonneg (x := x) (y := y) ha hd had
  have hid : b122Q s^2 * (x^2+y^2) - ((x+s*y)^2+y^2) =
      (b122Q s^2-1)*x^2 - 2*s*x*y + (1-b122Qinv s^2)*y^2 := by
    linear_combination y^2 * b122_eigenvalue_sum s
  linarith

lemma b122Q_zero : b122Q 0 = 1 := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold b122Q
  norm_num [h4]

/-- The larger Gram eigenvalue has a nonzero eigenvector.  The second component
`q²-1` also works at nonzero `s`; at `s=0` we use the first coordinate vector. -/
lemma b122_larger_eigenvector (s : ℝ) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      ((b122A s)ᵀ * b122A s) *ᵥ v = b122Q s^2 • v := by
  by_cases hs : s = 0
  · subst s
    refine ⟨![1, 0], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      norm_num at h0
    · rw [b122_gram, b122Q_zero]
      ext i
      fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two]
  · refine ⟨![s, b122Q s^2-1], ?_, ?_⟩
    · intro h
      apply hs
      have h0 := congrFun h 0
      simpa using h0
    · rw [b122_gram]
      ext i
      fin_cases i
      · simp [Matrix.mulVec, Fin.sum_univ_two]
        ring
      · simp [Matrix.mulVec, Fin.sum_univ_two]
        linear_combination -b122_larger_root s

lemma b122_opNorm_upper (s : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s)‖ ≤ b122Q s := by
  apply ContinuousLinearMap.opNorm_le_bound _ (b122Q_nonneg s)
  intro x
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (b122Q_nonneg s) (norm_nonneg _)),
    b122_norm_shift_apply_sq, mul_pow, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact b122_rayleigh_bound s (x 0) (x 1)

lemma b122_opNorm_lower (s : ℝ) :
    b122Q s ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s)‖ := by
  obtain ⟨v, hv0, hv⟩ := b122_larger_eigenvector s
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 v
  have hx0 : x ≠ 0 := by
    simpa [x] using hv0
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hquad : (v 0 + s*v 1)^2 + (v 1)^2 = b122Q s^2 * ((v 0)^2 + (v 1)^2) := by
    have h := congrArg (fun w : Fin 2 → ℝ => v ⬝ᵥ w) hv
    simp [b122_gram, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h
    linear_combination h
  have hTxsq : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s) x‖^2 =
      (b122Q s * ‖x‖)^2 := by
    rw [mul_pow, b122_norm_shift_apply_sq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact hquad
  have hTxnorm : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s) x‖ = b122Q s * ‖x‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (b122Q_nonneg s) (norm_nonneg _))).mp hTxsq
  have hle := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (b122A s)).le_opNorm x
  rw [hTxnorm] at hle
  exact le_of_mul_le_mul_right hle hxpos

/-- **B122, unscaled semigroup norm.**  The L2 operator norm of `I+sN` is the
larger singular value `(sqrt(4+s²)+|s|)/2`. -/
theorem b122_shift_opNorm (s : ℝ) :
    ‖b122A s‖ = (Real.sqrt (4+s^2) + |s|) / 2 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  exact le_antisymm (b122_opNorm_upper s) (b122_opNorm_lower s)

/-- **B122, the displayed semigroup norm.**  The hypothesis `0 < b` is the
card's standing decay hypothesis; algebraically the rescaling identity needs no
positivity. -/
theorem b122_semigroup_norm (b μ t : ℝ) (_hb : 0 < b) :
    ‖Real.exp (-(b*t)) • (1 - (μ*t) • b122N)‖ =
      Real.exp (-(b*t)) * ((Real.sqrt (4 + (μ*t)^2) + |μ*t|) / 2) := by
  have hA : 1 - (μ*t) • b122N = b122A (-(μ*t)) := by
    simp [b122A, sub_eq_add_neg]
  rw [hA, norm_smul, b122_shift_opNorm]
  simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_neg]

/-- The concrete value `s=1` is nonzero and hence makes the norm formula a
nontrivial, satisfiable instance, not a vacuous universal assertion. -/
example : ‖b122A 1‖ = (Real.sqrt 5 + 1) / 2 := by
  rw [b122_shift_opNorm]
  norm_num

/-- A concrete decaying Jordan block: `b=1`, `μ=1`, `t=1`. -/
example : ‖Real.exp (-(1*1)) • (1 - ((1*1 : ℝ)) • b122N)‖ =
    Real.exp (-(1*1)) * ((Real.sqrt (4 + (1*1 : ℝ)^2) + |1*1|) / 2) :=
  b122_semigroup_norm 1 1 1 (by norm_num)

/-- The same card formula for the named unique ODE solution. -/
theorem b122_semigroup_norm_named (b μ t : ℝ) (hb : 0 < b) :
    ‖b122Semigroup b μ t‖ =
      Real.exp (-(b*t)) * ((Real.sqrt (4 + (μ*t)^2) + |μ*t|) / 2) :=
  b122_semigroup_norm b μ t hb

end AtlasFormal

#print axioms AtlasFormal.b122A_entries
#print axioms AtlasFormal.b122_sqrt_sq
#print axioms AtlasFormal.b122_abs_le_sqrt
#print axioms AtlasFormal.b122_two_le_sqrt
#print axioms AtlasFormal.b122Q_pos
#print axioms AtlasFormal.b122Q_nonneg
#print axioms AtlasFormal.b122_one_le_Q
#print axioms AtlasFormal.b122Qinv_nonneg
#print axioms AtlasFormal.b122Q_mul_Qinv
#print axioms AtlasFormal.b122Qinv_le_one
#print axioms AtlasFormal.b122Qinv_le_Q
#print axioms AtlasFormal.b122_eigenvalue_sum
#print axioms AtlasFormal.b122_eigenvalue_product
#print axioms AtlasFormal.b122_larger_root
#print axioms AtlasFormal.b122Q_sq
#print axioms AtlasFormal.b122_gram
#print axioms AtlasFormal.b122_gram_charpoly
#print axioms AtlasFormal.b122_quadratic_nonneg
#print axioms AtlasFormal.b122_entry_derivative
#print axioms AtlasFormal.b122_semigroup_zero
#print axioms AtlasFormal.b122_semigroup_hasDerivAt
#print axioms AtlasFormal.b122_scalar_lipschitz
#print axioms AtlasFormal.b122_scalar_exp_unique
#print axioms AtlasFormal.b122_scalar_forced_unique
#print axioms AtlasFormal.b122_semigroup_unique
#print axioms AtlasFormal.b122_norm_shift_apply_sq
#print axioms AtlasFormal.b122_rayleigh_bound
#print axioms AtlasFormal.b122Q_zero
#print axioms AtlasFormal.b122_larger_eigenvector
#print axioms AtlasFormal.b122_opNorm_upper
#print axioms AtlasFormal.b122_opNorm_lower
#print axioms AtlasFormal.b122_shift_opNorm
#print axioms AtlasFormal.b122_semigroup_norm
#print axioms AtlasFormal.b122_semigroup_norm_named

/-! Axiom audit for the hand-written section above. -/
#print axioms AtlasFormal.frobSq_add_of_orthogonal
#print axioms AtlasFormal.frobSq_sub_of_orthogonal
#print axioms AtlasFormal.conjTranspose_one_sub
#print axioms AtlasFormal.cross_left
#print axioms AtlasFormal.cross_right
#print axioms AtlasFormal.commutator_eq_offblocks
#print axioms AtlasFormal.offBlock_frobSq_eq_commutator
#print axioms AtlasFormal.card_metric_saturation
#print axioms AtlasFormal.balanced_middle_terms_cancel
#print axioms AtlasFormal.middle_terms_opposite_but_not_cancelled
#print axioms AtlasFormal.gram_det_zero_iff
#print axioms AtlasFormal.rank_one_det_zero_iff
