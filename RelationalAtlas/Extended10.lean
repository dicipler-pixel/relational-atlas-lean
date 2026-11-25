/-
Ninth batch: a counterexample hunt on the seven remaining conjectures.

The Atlas does not claim these cards as theorems, and this batch was not sent to prove
them. Each member transcribed the card's displayed claim, took the sharpest reading that
is still literal, and attacked it. Six of the seven cards came back either refuted or
bounded; the file records, per card, exactly which reading failed and what survives.

Each contribution is reproduced verbatim except for its import line and is wrapped in its
own `section ... end`, so that no file-level `open` leaks into the next contribution.
Nothing in the earlier modules is modified.
-/
import Mathlib


/-! ## B4 — the mixed-rank projector identity fails; the equal-rank repair

Integrated from `.ultramath/smww885zp/m5/B4.lean`.
-/

section
open scoped BigOperators Matrix.Norms.Frobenius
open Matrix

namespace B4Counterexample

/-- Projection onto `span {e₀}` in `ℝ³`. -/
def P₁ : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 0, 0]

/-- Projection onto `span {e₀,e₁}` in `ℝ³`. -/
def P₂ : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 1, 0]

/-- An orthogonal projector in real coordinates. -/
def IsOrthoProjector (P : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  Pᵀ = P ∧ P * P = P

/-- Entrywise squared Frobenius norm. -/
def frobeniusSq (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Mathlib's Frobenius norm agrees with the entrywise squared norm. -/
lemma norm_sq_eq_entry_sum (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

lemma frobeniusSq_eq_norm_sq (A : Matrix (Fin 3) (Fin 3) ℝ) :
    frobeniusSq A = ‖A‖ ^ 2 := by
  rw [norm_sq_eq_entry_sum]
  simp [frobeniusSq, Real.norm_eq_abs, sq_abs]

lemma P₁_isOrthoProjector : IsOrthoProjector P₁ := by
  constructor
  · simp [P₁]
  · simp [P₁, diagonal_mul_diagonal]
    intro i
    fin_cases i <;> norm_num

lemma P₂_isOrthoProjector : IsOrthoProjector P₂ := by
  constructor
  · simp [P₂]
  · simp [P₂, diagonal_mul_diagonal]
    intro i
    fin_cases i <;> norm_num

lemma P₁_rank : P₁.rank = 1 := by
  classical
  rw [P₁, rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![(1 : ℝ), 0, 0] : Fin 3 → ℝ) x ≠ 0)).card = 1
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![(1 : ℝ), 0, 0] : Fin 3 → ℝ) x ≠ 0)) = {0} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

lemma P₂_rank : P₂.rank = 2 := by
  classical
  rw [P₂, rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![(1 : ℝ), 1, 0] : Fin 3 → ℝ) x ≠ 0)).card = 2
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![(1 : ℝ), 1, 0] : Fin 3 → ℝ) x ≠ 0)) = {0, 1} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

lemma projector_distance : frobeniusSq (P₁ - P₂) / 2 = 1 / 2 := by
  norm_num [frobeniusSq, P₁, P₂, Fin.sum_univ_three, diagonal]

lemma projector_distance_norm : ‖P₁ - P₂‖ ^ 2 / 2 = 1 / 2 := by
  rw [← frobeniusSq_eq_norm_sq]
  exact projector_distance

/-- The smaller range is contained in the larger one. -/
lemma cross_projection : P₂ * P₁ = P₁ := by
  simp [P₁, P₂, diagonal_mul_diagonal]
  intro i
  fin_cases i <;> norm_num

/-- The cross-Gram matrix is `P₁`.  Its squared nonzero singular value is
therefore `1`; since `P₁` has rank one, the sole principal cosine is `1`. -/
lemma cross_gram : (P₂ * P₁)ᵀ * (P₂ * P₁) = P₁ := by
  rw [cross_projection, P₁_isOrthoProjector.1, P₁_isOrthoProjector.2]

/-- Unit generator of the rank-one range. -/
def e₀ : Fin 3 → ℝ := ![1, 0, 0]

lemma e₀_unit : ∑ i, e₀ i * e₀ i = 1 := by
  norm_num [e₀, Fin.sum_univ_three]

lemma P₂_fixes_e₀ : P₂.mulVec e₀ = e₀ := by
  funext i
  fin_cases i <;> norm_num [P₂, e₀, mulVec, dotProduct, Fin.sum_univ_three, diagonal]

/-- With the usual `min (rank P₁) (rank P₂)` principal-angle list,
the cross-Gram calculation gives the sole angle `arccos 1 = 0`. -/
noncomputable def anglesMin : Fin 1 → ℝ := ![Real.arccos 1]

/-- If principal angles are instead padded to `max (rank P₁) (rank P₂)`,
the extra angle is the usual right angle. -/
noncomputable def anglesMax : Fin 2 → ℝ := ![Real.arccos 1, Real.pi / 2]

lemma sum_sin_sq_anglesMin : ∑ i, Real.sin (anglesMin i) ^ 2 = 0 := by
  simp [anglesMin]

lemma sum_sin_sq_anglesMax : ∑ i, Real.sin (anglesMax i) ^ 2 = 1 := by
  norm_num [anglesMax, Fin.sum_univ_two, Real.sin_pi_div_two]

/-- The literal unrestricted B4 identity fails for the standard short list. -/
theorem B4_false_min_principal_angles :
    frobeniusSq (P₁ - P₂) / 2 ≠ ∑ i, Real.sin (anglesMin i) ^ 2 := by
  rw [projector_distance, sum_sin_sq_anglesMin]
  norm_num

/-- Padding with the customary extra right angle does not repair it either. -/
theorem B4_false_padded_principal_angles :
    frobeniusSq (P₁ - P₂) / 2 ≠ ∑ i, Real.sin (anglesMax i) ^ 2 := by
  rw [projector_distance, sum_sin_sq_anglesMax]
  norm_num

/-- The same counterexample, using the exact notation of the card. -/
theorem B4_display_false :
    ‖P₁ - P₂‖ ^ 2 / 2 ≠ ∑ i, Real.sin (anglesMin i) ^ 2 := by
  rw [projector_distance_norm, sum_sin_sq_anglesMin]
  norm_num

/-- The unhalved identity exposes the repair: the rank deficiency contributes
`1`, while the short-list squared sines contribute `0`. -/
theorem corrected_identity_at_witness :
    ‖P₁ - P₂‖ ^ 2 = 2 * (∑ i, Real.sin (anglesMin i) ^ 2) +
      ((P₂.rank : ℝ) - (P₁.rank : ℝ)) := by
  rw [← frobeniusSq_eq_norm_sq, sum_sin_sq_anglesMin, P₁_rank, P₂_rank]
  have h := projector_distance
  norm_num at h ⊢
  exact h

#print axioms P₁_isOrthoProjector
#print axioms P₂_isOrthoProjector
#print axioms P₁_rank
#print axioms P₂_rank
#print axioms frobeniusSq_eq_norm_sq
#print axioms projector_distance
#print axioms projector_distance_norm
#print axioms cross_projection
#print axioms cross_gram
#print axioms e₀_unit
#print axioms P₂_fixes_e₀
#print axioms B4_false_min_principal_angles
#print axioms B4_false_padded_principal_angles
#print axioms B4_display_false
#print axioms corrected_identity_at_witness

end B4Counterexample
end


/-! ## B4 — the surviving equal-rank Frobenius identity

Integrated from `.ultramath/smww885zp/m3/B4EqualRank.lean`.
-/

section
/-!
# B4: the equal-rank principal-angle identity

The card has no rank hypothesis.  This file isolates the exact trace/SVD kernel
which makes the identity valid for equal ranks, and gives a fully explicit
planar family of rank-one orthogonal projectors satisfying it.  It also proves
the elementary squaring step in the refraction law; no identification between
that law and a higher-rank Grassmannian distance is assumed.
-/

open scoped BigOperators Matrix.Norms.Frobenius
open Matrix

namespace B4EqualRank

set_option autoImplicit false

/-- A real symmetric idempotent matrix. -/
def IsOrthoProjector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) : Prop := Pᵀ = P ∧ P * P = P

/-- Squared Frobenius norm, written without a square root. -/
def frobSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ := (Aᵀ * A).trace

/-- The trace expansion is unconditional on ranks. -/
theorem frobSq_sub_projectors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℝ) (hP : IsOrthoProjector P) (hQ : IsOrthoProjector Q) :
    frobSq (P - Q) = P.trace + Q.trace - 2 * (P * Q).trace := by
  unfold frobSq
  rw [Matrix.transpose_sub, hP.1, hQ.1]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_add]
  rw [hP.2, hQ.2, Matrix.trace_mul_comm Q P]
  ring

#print axioms frobSq_sub_projectors

/-- The trace formula is the entrywise squared norm. -/
theorem frobSq_eq_entry_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    frobSq A = ∑ i : ι, ∑ j : ι, (A i j) ^ 2 := by
  simp [frobSq, Matrix.trace, Matrix.mul_apply, pow_two]
  rw [Finset.sum_comm]

#print axioms frobSq_eq_entry_sum

/-- `frobSq` is exactly the square of Mathlib's Frobenius norm. -/
theorem frobSq_eq_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : frobSq A = ‖A‖ ^ 2 := by
  have h : 0 ≤ ∑ i : ι, ∑ j : ι, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num
  rw [frobSq_eq_entry_sum]

#print axioms frobSq_eq_norm_sq

/-- The trigonometric sum in terms of the common rank. -/
theorem sum_sin_sq_sub {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : ℕ) (θ : κ → ℝ) (hrκ : (r : ℝ) = ∑ i : κ, 1) :
    (∑ i : κ, (Real.sin (θ i)) ^ 2) =
      (r : ℝ) - ∑ i : κ, (Real.cos (θ i)) ^ 2 := by
  calc
    (∑ i : κ, (Real.sin (θ i)) ^ 2) =
        ∑ i : κ, ((1 : ℝ) - (Real.cos (θ i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sin_sq]
    _ = (∑ i : κ, (1 : ℝ)) - ∑ i : κ, (Real.cos (θ i)) ^ 2 := by
      rw [Finset.sum_sub_distrib]
    _ = (r : ℝ) - ∑ i : κ, (Real.cos (θ i)) ^ 2 := by rw [← hrκ]

#print axioms sum_sin_sq_sub

/-- Algebraic equal-rank kernel.  The last hypothesis is the SVD trace
characterisation of the principal cosines; it is not an assumption of the
conclusion. -/
theorem equalRank_trace_kernel {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P Q : Matrix ι ι ℝ)
    (hP : IsOrthoProjector P) (hQ : IsOrthoProjector Q)
    (r : ℕ) (θ : κ → ℝ)
    (hrP : P.trace = (r : ℝ)) (hrQ : Q.trace = (r : ℝ))
    (hrκ : (r : ℝ) = ∑ i : κ, 1)
    (hcos : (P * Q).trace = ∑ i : κ, (Real.cos (θ i)) ^ 2) :
    frobSq (P - Q) / 2 = ∑ i : κ, (Real.sin (θ i)) ^ 2 := by
  rw [frobSq_sub_projectors P Q hP hQ, hrP, hrQ, hcos,
    sum_sin_sq_sub r θ hrκ]
  ring

#print axioms equalRank_trace_kernel

/-- The same calculation exposes the unequal-rank defect. -/
theorem unequalRank_trace_formula {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P Q : Matrix ι ι ℝ)
    (hP : IsOrthoProjector P) (hQ : IsOrthoProjector Q)
    (p q : ℕ) (θ : κ → ℝ)
    (hrP : P.trace = (p : ℝ)) (hrQ : Q.trace = (q : ℝ))
    (hpκ : (p : ℝ) = ∑ i : κ, 1)
    (hcos : (P * Q).trace = ∑ i : κ, (Real.cos (θ i)) ^ 2) :
    frobSq (P - Q) / 2 = (∑ i : κ, (Real.sin (θ i)) ^ 2) +
      (((q : ℝ) - (p : ℝ)) / 2) := by
  rw [frobSq_sub_projectors P Q hP hQ, hrP, hrQ, hcos,
    sum_sin_sq_sub p θ hpκ]
  ring

#print axioms unequalRank_trace_formula

/-- Projection onto the line at angle `θ` in the real plane. -/
noncomputable def lineProjector (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(Real.cos θ)^2, Real.cos θ * Real.sin θ;
     Real.cos θ * Real.sin θ, (Real.sin θ)^2]

 theorem lineProjector_isOrthoProjector (θ : ℝ) :
    IsOrthoProjector (lineProjector θ) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [lineProjector]
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [lineProjector, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (Real.cos θ)^2 * (Real.sin_sq_add_cos_sq θ)
    · simp [lineProjector, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (Real.cos θ * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    · simp [lineProjector, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (Real.cos θ * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    · simp [lineProjector, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (Real.sin θ)^2 * (Real.sin_sq_add_cos_sq θ)

#print axioms lineProjector_isOrthoProjector

 theorem lineProjector_trace (θ : ℝ) : (lineProjector θ).trace = 1 := by
  simp [lineProjector, Matrix.trace, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

#print axioms lineProjector_trace

/-- The cross trace is the squared principal cosine. -/
theorem lineProjector_cross_trace (θ : ℝ) :
    (lineProjector 0 * lineProjector θ).trace = (Real.cos θ)^2 := by
  simp [lineProjector, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

#print axioms lineProjector_cross_trace

/-- Explicit B4 identity for every planar angle. -/
theorem lineProjector_B4 (θ : ℝ) :
    frobSq (lineProjector 0 - lineProjector θ) / 2 = (Real.sin θ)^2 := by
  rw [frobSq_sub_projectors _ _
    (lineProjector_isOrthoProjector 0) (lineProjector_isOrthoProjector θ),
    lineProjector_trace, lineProjector_trace, lineProjector_cross_trace]
  rw [Real.sin_sq]
  ring

#print axioms lineProjector_B4

/-- The card's displayed norm identity, for every planar line angle. -/
theorem lineProjector_B4_display (θ : ℝ) :
    ‖lineProjector 0 - lineProjector θ‖ ^ 2 / 2 = (Real.sin θ)^2 := by
  rw [← frobSq_eq_norm_sq]
  exact lineProjector_B4 θ

#print axioms lineProjector_B4_display

/-- The same identity follows from the generic equal-rank trace kernel. -/
theorem lineProjector_B4_from_kernel (θ : ℝ) :
    frobSq (lineProjector 0 - lineProjector θ) / 2 =
      ∑ i : Fin 1, (Real.sin ((fun _ => θ) i)) ^ 2 := by
  apply equalRank_trace_kernel _ _
    (lineProjector_isOrthoProjector 0) (lineProjector_isOrthoProjector θ)
    1 (fun _ : Fin 1 => θ)
  · norm_num; exact lineProjector_trace 0
  · norm_num; exact lineProjector_trace θ
  · simp
  · simpa using lineProjector_cross_trace θ

#print axioms lineProjector_B4_from_kernel

/-- The boundary case `θ = 0` is not a counterexample: both sides vanish. -/
theorem equal_lines_boundary :
    frobSq (lineProjector 0 - lineProjector 0) / 2 = 0 := by
  simpa using lineProjector_B4 0

#print axioms equal_lines_boundary

/-- Squaring a first-power refraction relation is exact. -/
theorem refraction_square_step (a₁ a₂ R₁ R₂ θ₁ θ₂ : ℝ)
    (hR₁ : R₁ = a₁ ^ 2) (hR₂ : R₂ = a₂ ^ 2)
    (hstationary : a₁ * Real.sin θ₁ = a₂ * Real.sin θ₂) :
    R₁ * (Real.sin θ₁)^2 = R₂ * (Real.sin θ₂)^2 := by
  calc
    R₁ * (Real.sin θ₁)^2 = (a₁ * Real.sin θ₁)^2 := by rw [hR₁]; ring
    _ = (a₂ * Real.sin θ₂)^2 := by rw [hstationary]
    _ = R₂ * (Real.sin θ₂)^2 := by rw [hR₂]; ring

#print axioms refraction_square_step

end B4EqualRank
end


/-! ## B49 — Riley-family counterexample to the Hessian/torsion identification

Integrated from `.ultramath/smww885zp/m2/B49.lean`.
-/

section
/-
B49: a finite computation for the figure-eight Riley curve.

Coordinates follow the general two-bridge adjoint-torsion formula: x=m^2+m^(-2)
and R=u^2+(3-x)(u+1).  The one-variable potential V has V_u=R, hence its
1-by-1 Hessian determinant is R_u.  For the figure-eight knot (p,q)=(5,3),
Yoon's formula (up to its global sign ambiguity) is

  T = R_u * (1+2u+u^2-m^2*u) /
      (2*(m^2-1)*(u+1)*(u+2-m^2)).
-/
namespace B49Counterexample
noncomputable section

/-- Figure-eight Riley polynomial in the `(m,u)` coordinates. -/
def R (m u : ℝ) : ℝ := u ^ 2 + (3 - m ^ 2 - (m ^ 2)⁻¹) * (u + 1)

/-- Jacobian in the deformation variable; also the scalar Hessian `V_uu`. -/
def dRdu (m u : ℝ) : ℝ := 2 * u + 3 - m ^ 2 - (m ^ 2)⁻¹

/-- Meridian Jacobian of the Riley polynomial. -/
def dRdm (m u : ℝ) : ℝ := -2 * (m - (m ^ 3)⁻¹) * (u + 1)

/-- An antiderivative, in `u`, of the Riley polynomial. -/
def potential (m u : ℝ) : ℝ :=
  u ^ 3 / 3 + (3 - m ^ 2 - (m ^ 2)⁻¹) * (u ^ 2 / 2 + u)

lemma hasDerivAt_potential (m u : ℝ) :
    HasDerivAt (fun t : ℝ => potential m t) (R m u) u := by
  unfold potential R
  convert (hasDerivAt_pow 3 u).div_const 3 |>.add
    ((((hasDerivAt_pow 2 u).div_const 2).add (hasDerivAt_id u)).const_mul
      (3 - m ^ 2 - (m ^ 2)⁻¹)) using 1 <;> (try funext t) <;> simp [id] <;> ring

lemma hasDerivAt_R (m u : ℝ) :
    HasDerivAt (fun t : ℝ => R m t) (dRdu m u) u := by
  unfold R dRdu
  convert (hasDerivAt_pow 2 u).add
    (((hasDerivAt_id u).add_const 1).const_mul (3 - m ^ 2 - (m ^ 2)⁻¹)) using 1 <;> (try funext t) <;> simp [id] <;> ring

lemma potential_first_derivative (m : ℝ) :
    deriv (fun t : ℝ => potential m t) = fun t => R m t := by
  funext u
  exact (hasDerivAt_potential m u).deriv

lemma potential_hessian (m u : ℝ) :
    deriv (deriv (fun t : ℝ => potential m t)) u = dRdu m u := by
  rw [potential_first_derivative]
  exact (hasDerivAt_R m u).deriv

/-- Adjoint Reidemeister torsion, with Yoon's global `±` suppressed. -/
def torsion (m u : ℝ) : ℝ :=
  dRdu m u * (1 + 2 * u + u ^ 2 - m ^ 2 * u) /
    (2 * (m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2))

/-- The explicit finite witness. -/
def u0 : ℝ := (5 + Real.sqrt 105) / 8

lemma sqrt_105_pos : 0 < Real.sqrt 105 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt_105_sq : (Real.sqrt 105) ^ 2 = 105 := Real.sq_sqrt (by norm_num)

lemma u0_pos : 0 < u0 := by
  dsimp [u0]
  positivity

lemma u0_ne_zero : u0 ≠ 0 := ne_of_gt u0_pos

lemma u0_poly : 4 * u0 ^ 2 - 5 * u0 - 5 = 0 := by
  have h := sqrt_105_sq
  dsimp [u0]
  nlinarith

lemma figure_eight_R : R 2 u0 = 0 := by
  have h := u0_poly
  dsimp [R]
  norm_num
  nlinarith

lemma dRdu_value : dRdu 2 u0 = Real.sqrt 105 / 4 := by
  dsimp [dRdu, u0]
  norm_num
  ring

lemma dRdu_nonzero : dRdu 2 u0 ≠ 0 := by
  rw [dRdu_value]
  have h := sqrt_105_pos
  positivity

lemma dRdm_nonzero : dRdm 2 u0 ≠ 0 := by
  have h := u0_pos
  dsimp [dRdm, u0]
  norm_num
  positivity

lemma u0_ne_neg_one : u0 + 1 ≠ 0 := by
  have h := u0_pos
  linarith

lemma u0_ne_two : u0 - 2 ≠ 0 := by
  intro h
  have heq : u0 = 2 := by linarith
  have hp := u0_poly
  rw [heq] at hp
  norm_num at hp

/-- On the whole regular figure-eight Riley curve, torsion is `-R_u/2`. -/
lemma torsion_on_curve {m u : ℝ} (hR : R m u = 0) (hm0 : m ≠ 0)
    (hm : m ^ 2 - 1 ≠ 0) (hu : u + 1 ≠ 0) (hv : u + 2 - m ^ 2 ≠ 0) :
    torsion m u = -dRdu m u / 2 := by
  have hw : 1 + 2 * u + u ^ 2 - m ^ 2 * u =
      -((m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2)) + m ^ 2 * R m u := by
    dsimp [R]
    field_simp [hm0] <;> ring
  rw [hR] at hw
  have hw' : 1 + 2 * u + u ^ 2 - m ^ 2 * u =
      -((m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2)) := by
    nlinarith
  have hden : (m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hm hu) hv
  dsimp [torsion]
  rw [hw']
  field_simp [hden]

lemma hessian_cannot_equal_torsion_on_regular_curve {m u : ℝ}
    (hR : R m u = 0) (hm0 : m ≠ 0) (hm : m ^ 2 - 1 ≠ 0) (hu : u + 1 ≠ 0)
    (hv : u + 2 - m ^ 2 ≠ 0) (hJ : dRdu m u ≠ 0) :
    dRdu m u ≠ torsion m u ∧ dRdu m u ≠ -torsion m u := by
  rw [torsion_on_curve hR hm0 hm hu hv]
  constructor <;> intro heq <;> apply hJ <;> nlinarith

lemma torsion_factor :
    (u0 - 1) ^ 2 / (6 * (u0 + 1) * (u0 - 2)) = -1 / 2 := by
  have hden : 6 * (u0 + 1) * (u0 - 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) u0_ne_neg_one) u0_ne_two
  rw [div_eq_iff hden]
  have hp := u0_poly
  nlinarith

lemma torsion_at_two :
    torsion 2 u0 = -dRdu 2 u0 / 2 := by
  have hform : torsion 2 u0 =
      dRdu 2 u0 * (u0 - 1) ^ 2 / (6 * (u0 + 1) * (u0 - 2)) := by
    dsimp [torsion]
    norm_num
    ring
  rw [hform]
  calc
    dRdu 2 u0 * (u0 - 1) ^ 2 / (6 * (u0 + 1) * (u0 - 2)) =
        dRdu 2 u0 * ((u0 - 1) ^ 2 / (6 * (u0 + 1) * (u0 - 2))) := by ring
    _ = dRdu 2 u0 * (-1 / 2) := by rw [torsion_factor]
    _ = -dRdu 2 u0 / 2 := by ring

lemma torsion_value : torsion 2 u0 = -Real.sqrt 105 / 8 := by
  rw [torsion_at_two, dRdu_value]
  ring

/-- The literal displayed equality fails for the torsion sign chosen above. -/
lemma hessian_ne_torsion : dRdu 2 u0 ≠ torsion 2 u0 := by
  rw [dRdu_value, torsion_value]
  have h := sqrt_105_pos
  intro heq
  linarith

/-- It also fails after reversing Yoon's global sign. -/
lemma hessian_ne_neg_torsion : dRdu 2 u0 ≠ -torsion 2 u0 := by
  rw [dRdu_value, torsion_value]
  have h := sqrt_105_pos
  intro heq
  linarith

/-- All finite hypotheses and both sign versions of the failed conclusion. -/
theorem b49_regular_counterexample :
    2 ≠ 0 ∧ (2 : ℝ) ≠ 1 ∧ (2 : ℝ) ≠ -1 ∧ u0 ≠ 0 ∧
      R 2 u0 = 0 ∧ dRdu 2 u0 ≠ 0 ∧ dRdm 2 u0 ≠ 0 ∧
      dRdu 2 u0 ≠ torsion 2 u0 ∧ dRdu 2 u0 ≠ -torsion 2 u0 := by
  exact ⟨by norm_num, by norm_num, by norm_num, u0_ne_zero,
    figure_eight_R, dRdu_nonzero, dRdm_nonzero,
    hessian_ne_torsion, hessian_ne_neg_torsion⟩

/-- The discriminant double root at `x=-1` also has zero (not nonzero) Jacobian. -/
lemma branch_discriminant_and_jacobian :
    ((-1 : ℝ) + 1) * ((-1 : ℝ) - 3) = 0 ∧
      (-2 : ℝ) ^ 2 + (3 - (-1 : ℝ)) * (-2 + 1) = 0 ∧
      2 * (-2 : ℝ) + 3 - (-1 : ℝ) = 0 := by
  norm_num

#print axioms hasDerivAt_potential
#print axioms hasDerivAt_R
#print axioms potential_first_derivative
#print axioms potential_hessian
#print axioms sqrt_105_pos
#print axioms sqrt_105_sq
#print axioms u0_pos
#print axioms u0_ne_zero
#print axioms u0_poly
#print axioms figure_eight_R
#print axioms dRdu_value
#print axioms dRdu_nonzero
#print axioms dRdm_nonzero
#print axioms u0_ne_neg_one
#print axioms u0_ne_two
#print axioms torsion_on_curve
#print axioms hessian_cannot_equal_torsion_on_regular_curve
#print axioms torsion_factor
#print axioms torsion_at_two
#print axioms torsion_value
#print axioms hessian_ne_torsion
#print axioms hessian_ne_neg_torsion
#print axioms b49_regular_counterexample
#print axioms branch_discriminant_and_jacobian

end
end B49Counterexample
end


/-! ## B49 — the literal potential reading, and the smoothing point

Integrated from `.ultramath/smww885zp/m9/B49_literal.lean`.
-/

section
/-
B49, ledger-literal reading: the Riley polynomial R itself is the
one-variable potential in u.  Thus its scalar Hessian determinant is R_uu.

For the figure-eight two-bridge knot, R is obtained from
  w = g1 * g2^(-1) * g1^(-1) * g2,
  rho(g1) = [[m,1],[0,m^(-1)]],
  rho(g2) = [[m,0],[-u,m^(-1)]],
by R = w11 - (m-m^(-1))*w12.  Yoon's two-bridge adjoint-torsion formula
(arXiv:2009.12051, Theorems 1.1 and 3.1), specialised to (p,q,k)=(5,3,3),
is the function `torsion` below, up to its global sign.
-/
namespace B49Literal
noncomputable section

/-- Figure-eight Riley polynomial, regarded literally as the potential in `u`. -/
def R (m u : ℝ) : ℝ := u ^ 2 + (3 - m ^ 2 - (m ^ 2)⁻¹) * (u + 1)

/-- The antiderivative convention `V_u=R`, included to test the other natural reading. -/
def primitivePotential (m u : ℝ) : ℝ :=
  u ^ 3 / 3 + (3 - m ^ 2 - (m ^ 2)⁻¹) * (u ^ 2 / 2 + u)

/-- The Jacobian in the deformation variable. -/
def dRdu (m u : ℝ) : ℝ := 2 * u + 3 - m ^ 2 - (m ^ 2)⁻¹

/-- The meridian Jacobian. -/
def dRdm (m u : ℝ) : ℝ := -2 * (m - (m ^ 3)⁻¹) * (u + 1)

/-- Discriminant of the quadratic `R` in `u`. -/
def discR (m : ℝ) : ℝ :=
  (3 - m ^ 2 - (m ^ 2)⁻¹) ^ 2 - 4 * (3 - m ^ 2 - (m ^ 2)⁻¹)

/-- Yoon's adjoint torsion formula with its global `±` suppressed. -/
def torsion (m u : ℝ) : ℝ :=
  dRdu m u * (1 + 2 * u + u ^ 2 - m ^ 2 * u) /
    (2 * (m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2))

lemma hasDerivAt_primitivePotential (m u : ℝ) :
    HasDerivAt (fun t : ℝ => primitivePotential m t) (R m u) u := by
  unfold primitivePotential R
  convert (hasDerivAt_pow 3 u).div_const 3 |>.add
    ((((hasDerivAt_pow 2 u).div_const 2).add (hasDerivAt_id u)).const_mul
      (3 - m ^ 2 - (m ^ 2)⁻¹)) using 1 <;>
    (try funext t) <;> simp [id] <;> ring

lemma primitive_first_derivative (m : ℝ) :
    deriv (fun t : ℝ => primitivePotential m t) = fun t => R m t := by
  funext u
  exact (hasDerivAt_primitivePotential m u).deriv

lemma hasDerivAt_R (m u : ℝ) :
    HasDerivAt (fun t : ℝ => R m t) (dRdu m u) u := by
  unfold R dRdu
  convert (hasDerivAt_pow 2 u).add
    (((hasDerivAt_id u).add_const 1).const_mul
      (3 - m ^ 2 - (m ^ 2)⁻¹)) using 1 <;>
    (try funext t) <;> simp [id] <;> ring

lemma hasDerivAt_dRdu (m u : ℝ) :
    HasDerivAt (fun t : ℝ => dRdu m t) 2 u := by
  unfold dRdu
  convert ((hasDerivAt_id u).const_mul (2 : ℝ)).add_const
    (3 - m ^ 2 - (m ^ 2)⁻¹) using 1 <;>
    (try funext t) <;> simp [id] <;> ring

lemma riley_first_derivative (m : ℝ) :
    deriv (fun t : ℝ => R m t) = fun t => dRdu m t := by
  funext u
  exact (hasDerivAt_R m u).deriv

/-- For the antiderivative convention, the scalar Hessian determinant is `R_u`. -/
theorem primitive_hessian (m u : ℝ) :
    deriv (deriv (fun t : ℝ => primitivePotential m t)) u = dRdu m u := by
  rw [primitive_first_derivative]
  exact (hasDerivAt_R m u).deriv

/-- For the literal potential `V=R`, the one-by-one Hessian determinant is 2. -/
theorem riley_hessian (m u : ℝ) :
    deriv (deriv (fun t : ℝ => R m t)) u = 2 := by
  rw [riley_first_derivative]
  exact (hasDerivAt_dRdu m u).deriv

/-- Algebraic reduction of Yoon's formula on the regular Riley curve. -/
lemma torsion_on_curve {m u : ℝ} (hR : R m u = 0) (hm0 : m ≠ 0)
    (hm : m ^ 2 - 1 ≠ 0) (hu : u + 1 ≠ 0) (hv : u + 2 - m ^ 2 ≠ 0) :
    torsion m u = -dRdu m u / 2 := by
  have hw : 1 + 2 * u + u ^ 2 - m ^ 2 * u =
      -((m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2)) + m ^ 2 * R m u := by
    dsimp [R]
    field_simp [hm0] <;> ring
  rw [hR] at hw
  have hw' : 1 + 2 * u + u ^ 2 - m ^ 2 * u =
      -((m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2)) := by
    nlinarith
  have hden : (m ^ 2 - 1) * (u + 1) * (u + 2 - m ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hm hu) hv
  dsimp [torsion]
  rw [hw']
  field_simp [hden]

/-- A regular witness different from the one in the other swarm direction. -/
def u₁ : ℝ := (55 + Real.sqrt 5005) / 18

lemma sqrt_5005_pos : 0 < Real.sqrt 5005 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt_5005_sq : (Real.sqrt 5005) ^ 2 = 5005 := Real.sq_sqrt (by norm_num)

lemma u₁_pos : 0 < u₁ := by
  dsimp [u₁]
  positivity

lemma u₁_ne_zero : u₁ ≠ 0 := ne_of_gt u₁_pos

lemma u₁_poly : 9 * u₁ ^ 2 - 55 * u₁ - 55 = 0 := by
  have h := sqrt_5005_sq
  dsimp [u₁]
  nlinarith

lemma witness_R : R 3 u₁ = 0 := by
  have h := u₁_poly
  dsimp [R]
  norm_num
  nlinarith

lemma witness_dRdu : dRdu 3 u₁ = Real.sqrt 5005 / 9 := by
  dsimp [dRdu, u₁]
  norm_num
  ring

lemma witness_dRdu_nonzero : dRdu 3 u₁ ≠ 0 := by
  rw [witness_dRdu]
  have h := sqrt_5005_pos
  positivity

lemma witness_dRdm_nonzero : dRdm 3 u₁ ≠ 0 := by
  have h := u₁_pos
  dsimp [dRdm]
  norm_num
  positivity

lemma witness_discriminant : discR 3 = 5005 / 81 := by
  dsimp [discR]
  norm_num

lemma witness_discriminant_nonzero : discR 3 ≠ 0 := by
  rw [witness_discriminant]
  norm_num

lemma u₁_ne_neg_one : u₁ + 1 ≠ 0 := by
  have h := u₁_pos
  linarith

lemma u₁_ne_seven : u₁ ≠ 7 := by
  intro h
  have hp := u₁_poly
  rw [h] at hp
  norm_num at hp

lemma witness_last_denominator_factor : u₁ + 2 - (3 : ℝ) ^ 2 ≠ 0 := by
  have heq : u₁ + 2 - (3 : ℝ) ^ 2 = u₁ - 7 := by norm_num; ring
  rw [heq]
  exact sub_ne_zero.mpr u₁_ne_seven

lemma witness_torsion : torsion 3 u₁ = -Real.sqrt 5005 / 18 := by
  rw [torsion_on_curve witness_R (by norm_num) (by norm_num)
    u₁_ne_neg_one witness_last_denominator_factor, witness_dRdu]
  ring

/-- The displayed equality fails for Yoon's chosen sign. -/
theorem hessian_ne_torsion : 2 ≠ torsion 3 u₁ := by
  rw [witness_torsion]
  have h := sqrt_5005_pos
  linarith

/-- The displayed equality also fails after reversing the global torsion sign. -/
theorem hessian_ne_neg_torsion : 2 ≠ -torsion 3 u₁ := by
  rw [witness_torsion]
  have h := sqrt_5005_pos
  intro heq
  have hs : Real.sqrt 5005 = 36 := by nlinarith
  have hsquare := sqrt_5005_sq
  nlinarith

/-- The same point also refutes the display under the antiderivative convention. -/
theorem primitive_hessian_ne_torsion : dRdu 3 u₁ ≠ torsion 3 u₁ := by
  rw [witness_torsion, witness_dRdu]
  have h := sqrt_5005_pos
  linarith

theorem primitive_hessian_ne_neg_torsion : dRdu 3 u₁ ≠ -torsion 3 u₁ := by
  rw [witness_torsion, witness_dRdu]
  have h := sqrt_5005_pos
  intro heq
  nlinarith

/-- Every finite regularity hypothesis and both sign versions of the failure. -/
theorem b49_literal_counterexample :
    (3 : ℝ) ≠ 0 ∧ (3 : ℝ) ≠ 1 ∧ (3 : ℝ) ≠ -1 ∧ u₁ ≠ 0 ∧
      R 3 u₁ = 0 ∧ discR 3 ≠ 0 ∧ dRdu 3 u₁ ≠ 0 ∧ dRdm 3 u₁ ≠ 0 ∧
      deriv (deriv (fun t : ℝ => R 3 t)) u₁ = 2 ∧
      torsion 3 u₁ = -Real.sqrt 5005 / 18 ∧
      2 ≠ torsion 3 u₁ ∧ 2 ≠ -torsion 3 u₁ := by
  exact ⟨by norm_num, by norm_num, by norm_num, u₁_ne_zero,
    witness_R, witness_discriminant_nonzero, witness_dRdu_nonzero,
    witness_dRdm_nonzero, riley_hessian 3 u₁, witness_torsion,
    hessian_ne_torsion, hessian_ne_neg_torsion⟩

/-- The conclusion fails at the witness under either potential convention. -/
theorem b49_both_potential_readings :
    (deriv (deriv (fun t : ℝ => R 3 t)) u₁ = 2 ∧
      2 ≠ torsion 3 u₁ ∧ 2 ≠ -torsion 3 u₁) ∧
    (deriv (deriv (fun t : ℝ => primitivePotential 3 t)) u₁ = dRdu 3 u₁ ∧
      dRdu 3 u₁ ≠ torsion 3 u₁ ∧ dRdu 3 u₁ ≠ -torsion 3 u₁) := by
  exact ⟨⟨riley_hessian 3 u₁, hessian_ne_torsion, hessian_ne_neg_torsion⟩,
    primitive_hessian 3 u₁, primitive_hessian_ne_torsion,
    primitive_hessian_ne_neg_torsion⟩

#print axioms hasDerivAt_primitivePotential
#print axioms primitive_first_derivative
#print axioms primitive_hessian
#print axioms hasDerivAt_R
#print axioms hasDerivAt_dRdu
#print axioms riley_first_derivative
#print axioms riley_hessian
#print axioms torsion_on_curve
#print axioms sqrt_5005_pos
#print axioms sqrt_5005_sq
#print axioms u₁_pos
#print axioms u₁_ne_zero
#print axioms u₁_poly
#print axioms witness_R
#print axioms witness_dRdu
#print axioms witness_dRdu_nonzero
#print axioms witness_dRdm_nonzero
#print axioms witness_discriminant
#print axioms witness_discriminant_nonzero
#print axioms u₁_ne_neg_one
#print axioms u₁_ne_seven
#print axioms witness_last_denominator_factor
#print axioms witness_torsion
#print axioms hessian_ne_torsion
#print axioms hessian_ne_neg_torsion
#print axioms primitive_hessian_ne_torsion
#print axioms primitive_hessian_ne_neg_torsion
#print axioms b49_literal_counterexample
#print axioms b49_both_potential_readings

end
end B49Literal
end


/-! ## B49 — the branch point is a torsion zero, not a torsion pole

Integrated from `.ultramath/smww885zp/m4/B49.lean`.
-/

section
open scoped ComplexConjugate

namespace B49

/-- A square root of -3 in the complex numbers. -/
noncomputable def s0 : ℂ := Complex.I * (Real.sqrt 3 : ℂ)

lemma s0_sq : s0 ^ 2 = -3 := by
  have h : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  simp [s0, mul_pow, Complex.I_sq, h]

/-- The primitive sixth root of unity used in the counterexample. -/
noncomputable def m0 : ℂ := (1 + s0) / 2

lemma m0_sq_sub_add : m0 ^ 2 - m0 + 1 = 0 := by
  unfold m0
  linear_combination (1 / 4 : ℂ) * s0_sq

lemma m0_sq : m0 ^ 2 = m0 - 1 := by
  linear_combination m0_sq_sub_add

lemma m0_ne_zero : m0 ≠ 0 := by
  intro h
  have h' := m0_sq_sub_add
  rw [h] at h'
  norm_num at h'

lemma m0_inv : m0⁻¹ = 1 - m0 := by
  field_simp [m0_ne_zero]
  linear_combination m0_sq_sub_add

lemma m0_inv_sq : (m0 ^ 2)⁻¹ = -m0 := by
  rw [← inv_pow, m0_inv]
  calc
    (1 - m0) ^ 2 = m0 ^ 2 - 2 * m0 + 1 := by ring
    _ = (m0 - 1) - 2 * m0 + 1 := by rw [m0_sq]
    _ = -m0 := by ring

lemma m0_ne_one : m0 ≠ 1 := by
  intro h
  have h' := m0_sq_sub_add
  rw [h] at h'
  norm_num at h'

lemma m0_ne_neg_one : m0 ≠ -1 := by
  intro h
  have h' := m0_sq_sub_add
  rw [h] at h'
  norm_num at h'

lemma m0_cubed : m0 ^ 3 = -1 := by
  calc
    m0 ^ 3 = m0 * m0 ^ 2 := by ring
    _ = m0 * (m0 - 1) := by rw [m0_sq]
    _ = -1 := by linear_combination m0_sq_sub_add

lemma m0_four : m0 ^ 4 = -m0 := by
  calc
    m0 ^ 4 = m0 * m0 ^ 3 := by ring
    _ = -m0 := by rw [m0_cubed]; ring

lemma m0_inv_cubed : (m0 ^ 3)⁻¹ = -1 := by
  rw [m0_cubed]
  norm_num

lemma m0_inv_four : (m0 ^ 4)⁻¹ = m0 ^ 2 := by
  rw [m0_four]
  simp [m0_inv, m0_sq]

lemma s0_ne_zero : s0 ≠ 0 := by
  have hreal : Real.sqrt 3 ≠ 0 := by
    positivity
  have hc : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast hreal
  exact mul_ne_zero Complex.I_ne_zero hc

/-- The meridian trace squared minus two at the witness. -/
lemma m0_Q : m0 ^ 2 + (m0 ^ 2)⁻¹ = -1 := by
  rw [m0_inv_sq, m0_sq]
  ring

lemma m0_sq_sub_inv_sq : m0 ^ 2 - (m0 ^ 2)⁻¹ = s0 := by
  rw [m0_inv_sq, m0_sq]
  unfold m0
  ring

/-- GKY's figure-eight character-curve equation (with y = -u). -/
noncomputable def rileyF (y m : ℂ) : ℂ :=
  (y - 1) * (m ^ 2 + (m ^ 2)⁻¹) + y ^ 2 - 3 * y + 3

/-- Its partial derivative in the representation variable y. -/
noncomputable def rileyFy (y m : ℂ) : ℂ :=
  m ^ 2 + (m ^ 2)⁻¹ + 2 * y - 3

/-- Its partial derivative in the meridian eigenvalue m. -/
noncomputable def rileyFm (y m : ℂ) : ℂ :=
  (y - 1) * (2 * m - 2 * (m ^ 3)⁻¹)

/-- At the witness the Riley polynomial is literally a square. -/
theorem rileyF_double_square (y : ℂ) : rileyF y m0 = (y - 2) ^ 2 := by
  simp only [rileyF, m0_Q]
  ring

theorem witness_on_riley_curve : rileyF 2 m0 = 0 := by
  rw [rileyF_double_square]
  norm_num

theorem witness_riley_degenerate : rileyFy 2 m0 = 0 := by
  simp only [rileyFy, m0_Q]
  ring

theorem witness_riley_smooth_in_meridian : rileyFm 2 m0 ≠ 0 := by
  simp only [rileyFm, m0_inv_cubed]
  have h : m0 + 1 ≠ 0 := by
    intro h
    apply m0_ne_neg_one
    calc
      m0 = (m0 + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  apply mul_ne_zero
  · norm_num
  · convert mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) h using 1 <;> ring

/-- The canonical-longitude eigenvalue on the figure-eight Riley curve. -/
noncomputable def longitudeEigenvalue (y m : ℂ) : ℂ :=
  -(m ^ 2)⁻¹ * (y - 3) * (y - 1) ^ 2 - (m ^ 4)⁻¹ * (y ^ 2 - 3 * y + 1)

theorem witness_longitude_eigenvalue : longitudeEigenvalue 2 m0 = -1 := by
  unfold longitudeEigenvalue
  rw [m0_inv_sq, m0_inv_four, m0_sq]
  ring

/-- The figure-eight A-polynomial used by Gang--Kim--Yoon. -/
noncomputable def Apoly (l m : ℂ) : ℂ :=
  l + l⁻¹ + (-(m ^ 4)⁻¹ + (m ^ 2)⁻¹ + 2 + m ^ 2 - m ^ 4)

/-- Its l-partial. -/
noncomputable def ApolyDl (l : ℂ) : ℂ := 1 - (l ^ 2)⁻¹

/-- Its m-partial, in factored form. -/
noncomputable def ApolyDm (m : ℂ) : ℂ :=
  -2 * m⁻¹ * (2 * (m ^ 2 + (m ^ 2)⁻¹) - 1) * (m ^ 2 - (m ^ 2)⁻¹)

/-- The factored m-partial is the actual derivative of the m-dependent part
of `Apoly`; this also checks that no inverse-power convention was dropped. -/
theorem ApolyDm_eq_expanded (m : ℂ) (hm : m ≠ 0) :
    ApolyDm m = 4 * (m ^ 5)⁻¹ - 2 * (m ^ 3)⁻¹ + 2 * m - 4 * m ^ 3 := by
  simp only [ApolyDm]
  field_simp [hm]
  ring

/-- Longitude torsion with one fixed choice of the otherwise free sign. -/
noncomputable def longitudeTorsion (m : ℂ) : ℂ :=
  -(2 * (m ^ 2 + (m ^ 2)⁻¹) - 1)

/-- The longitude-to-meridian torsion conversion formula. -/
noncomputable def meridianTorsion (l m : ℂ) : ℂ :=
  -(l / m) * (ApolyDl l / ApolyDm m) * longitudeTorsion m

theorem witness_on_A_polynomial : Apoly (-1) m0 = 0 := by
  unfold Apoly
  rw [m0_inv_four, m0_inv_sq]
  rw [m0_four, m0_sq]
  norm_num
  ring

theorem witness_A_l_zero : ApolyDl (-1 : ℂ) = 0 := by
  norm_num [ApolyDl]

theorem witness_A_m_nonzero : ApolyDm m0 ≠ 0 := by
  simp only [ApolyDm, m0_Q, m0_sq_sub_inv_sq]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (inv_ne_zero m0_ne_zero)) (by norm_num))
    s0_ne_zero

theorem witness_longitude_torsion_value : longitudeTorsion m0 = 3 := by
  norm_num [longitudeTorsion, m0_Q]

/-- The literal pole claim is the exact opposite of the rational continuation:
at this smooth meridian branch point the meridian torsion has a zero. -/
theorem witness_meridian_torsion_zero : meridianTorsion (-1) m0 = 0 := by
  simp [meridianTorsion, witness_A_l_zero]

end B49

#print axioms B49.s0_sq
#print axioms B49.m0_sq_sub_add
#print axioms B49.m0_sq
#print axioms B49.m0_ne_zero
#print axioms B49.m0_inv
#print axioms B49.m0_inv_sq
#print axioms B49.m0_ne_one
#print axioms B49.m0_ne_neg_one
#print axioms B49.m0_cubed
#print axioms B49.m0_four
#print axioms B49.m0_inv_cubed
#print axioms B49.m0_inv_four
#print axioms B49.s0_ne_zero
#print axioms B49.m0_Q
#print axioms B49.m0_sq_sub_inv_sq
#print axioms B49.rileyF_double_square
#print axioms B49.witness_on_riley_curve
#print axioms B49.witness_riley_degenerate
#print axioms B49.witness_riley_smooth_in_meridian
#print axioms B49.witness_longitude_eigenvalue
#print axioms B49.ApolyDm_eq_expanded
#print axioms B49.witness_on_A_polynomial
#print axioms B49.witness_A_l_zero
#print axioms B49.witness_A_m_nonzero
#print axioms B49.witness_longitude_torsion_value
#print axioms B49.witness_meridian_torsion_zero
end


/-! ## B53 — coloured Jones data for 3_1 under the AJ normalisation

Integrated from `.ultramath/smww885zp/m15/B53.lean`.
-/

section
/-!
# Finite checks for card B53

The knot-theoretic inputs are Habiro's sum for the left-handed trefoil and
Garoufalidis's first-order recurrence. This file checks the resulting small
colour polynomial algebra and the classical (q = 1) recurrence algebra. It
does not assert the Melvin--Morton theorem or construct knots in Lean.
-/

open scoped Polynomial
open Polynomial

namespace B53

/-- The second normalized coloured Jones polynomial of the left trefoil. -/
def trefoilJonesTwo (q : ℚ) : ℚ := q + q ^ 3 - q ^ 4

/-- The k = 0,1 terms of Habiro's sum at colour N = 2; terms with k ≥ 2 vanish. -/
def trefoilJonesTwoHabiro (q : ℚ) : ℚ :=
  1 - q ^ 4 * (1 - q ^ (-3 : ℤ)) * (1 - q ^ (-1 : ℤ))

/-- Evaluation of Habiro's sum at the second colour. -/
theorem trefoilJonesTwo_eq_habiro {q : ℚ} (hq : q ≠ 0) :
    trefoilJonesTwoHabiro q = trefoilJonesTwo q := by
  simp only [trefoilJonesTwoHabiro, trefoilJonesTwo]
  rw [zpow_neg, zpow_neg]
  norm_num only [zpow_ofNat]
  field_simp
  ring

#print axioms trefoilJonesTwo_eq_habiro

/-- The same second-colour value, as a polynomial (no Laurent inverse needed). -/
noncomputable def trefoilJonesTwoPoly : ℚ[X] := X + X ^ 3 - X ^ 4

theorem trefoilJonesTwoPoly_eval_one : trefoilJonesTwoPoly.eval 1 = 1 := by
  norm_num [trefoilJonesTwoPoly]

#print axioms trefoilJonesTwoPoly_eval_one

theorem trefoilJonesTwoPoly_first_moment :
    (derivative trefoilJonesTwoPoly).eval 1 = 0 := by
  simp [trefoilJonesTwoPoly]
  norm_num

#print axioms trefoilJonesTwoPoly_first_moment

theorem trefoilJonesTwoPoly_second_moment :
    (derivative (derivative trefoilJonesTwoPoly)).eval 1 = -6 := by
  simp [trefoilJonesTwoPoly]
  norm_num

#print axioms trefoilJonesTwoPoly_second_moment

/--
The coefficient of h² in J₂(e^(h/2)). For a Laurent polynomial Σ c_d q^d,
the coefficient is (Σ c_d d²)/(2N²); here the exponents are 1,3,-4 and N=2.
-/
theorem trefoil_second_colour_h2_coefficient :
    ((1 : ℚ) ^ 2 + 3 ^ 2 - 4 ^ 2) / (2 * (2 : ℚ) ^ 2) = -3 / 4 := by
  norm_num

#print axioms trefoil_second_colour_h2_coefficient

/-- The coefficient of h² in Δ_3₁(e^h) = e^h - 1 + e^(-h). -/
theorem trefoil_alexander_h2_coefficient :
    ((1 : ℚ) ^ 2 + (-1) ^ 2) / 2 = 1 := by
  norm_num

#print axioms trefoil_alexander_h2_coefficient

/-- Δ(e^h) has no linear term. -/
theorem trefoil_alexander_h1_coefficient :
    ((1 : ℚ) + (-1)) / 1 = 0 := by
  norm_num

#print axioms trefoil_alexander_h1_coefficient

/-- The h² coefficient in 1/Δ_3₁(e^h), using 1/Δ = 1-h²+O(h³). -/
theorem trefoil_inverse_alexander_h2_coefficient :
    -((1 : ℚ) ^ 2 + (-1) ^ 2) / 2 = -1 := by
  norm_num

#print axioms trefoil_inverse_alexander_h2_coefficient

/-- Finite N=2 is not the MMR limit, but that is not a counterexample to it. -/
theorem second_colour_is_not_leading_line :
    ((1 : ℚ) ^ 2 + 3 ^ 2 - 4 ^ 2) / (2 * (2 : ℚ) ^ 2) ≠
      -((1 : ℚ) ^ 2 + (-1) ^ 2) / 2 := by
  norm_num

#print axioms second_colour_is_not_leading_line

/--
Eliminate the inhomogeneous term in the q=1 trefoil recurrence

  J(n) + Q³ J(n-1) = Q(Q+1).

This produces the second-order homogeneous recurrence whose symbol is the
A-polynomial, including the abelian L-1 factor.
-/
theorem eliminate_inhomogeneous_trefoil_recurrence
    {R : Type*} [CommRing R] (Q : R) (J : ℤ → R)
    (h : ∀ n : ℤ, J n + Q ^ 3 * J (n - 1) = Q * (Q + 1)) (n : ℤ) :
    J (n + 1) + (Q ^ 3 - 1) * J n - Q ^ 3 * J (n - 1) = 0 := by
  have h₀ := h n
  have h₁ := h (n + 1)
  have hmid : n + 1 - 1 = n := by omega
  rw [hmid] at h₁
  linear_combination h₁ - h₀

#print axioms eliminate_inhomogeneous_trefoil_recurrence

/-- With Q=M², the homogeneous symbol is exactly (L-1)(L+M⁶). -/
theorem trefoil_A_polynomial_factorization {R : Type*} [CommRing R] (L M : R) :
    L ^ 2 + (M ^ 6 - 1) * L - M ^ 6 = (L - 1) * (L + M ^ 6) := by
  ring

#print axioms trefoil_A_polynomial_factorization

/-- The same recurrence written under Q=M² and L=E. -/
theorem trefoil_classical_recurrence_is_A
    {R : Type*} [CommRing R] (M : R) (J : ℤ → R)
    (h : ∀ n : ℤ, J n + (M ^ 2) ^ 3 * J (n - 1) =
      M ^ 2 * (M ^ 2 + 1)) (n : ℤ) :
    J (n + 1) + ((M ^ 2) ^ 3 - 1) * J n - (M ^ 2) ^ 3 * J (n - 1) = 0 := by
  exact eliminate_inhomogeneous_trefoil_recurrence (M ^ 2) J h n

#print axioms trefoil_classical_recurrence_is_A

/-- The second derivative at q=1 of A_n(q)=q^(n-1)(q^(2n-1)-1)/(q^n-1),
with the removable singularity filled by the geometric-sum quotient. -/
def trefoilASecondAtOne (n : ℚ) : ℚ :=
  (2*n - 1) * (n - 1) * (15*n - 23) / (6*n)

/-- The second derivative at q=1 of B_n(q)=q^(3n-1)(q^(n-1)-1)/(q^n-1),
again after filling its removable singularity. -/
def trefoilBSecondAtOne (n : ℚ) : ℚ :=
  (n - 1) * (54*n^2 - 73*n + 23) / (6*n)

/-- The explicit A''-B'' calculation used in differentiating Habiro's recurrence. -/
theorem trefoil_second_derivative_difference {n : ℚ} (hn : n ≠ 0) :
    trefoilASecondAtOne n - trefoilBSecondAtOne n = -4*n^2 + 6*n - 2 := by
  simp only [trefoilASecondAtOne, trefoilBSecondAtOne]
  field_simp
  ring

#print axioms trefoil_second_derivative_difference

/--
Induction for second moments, using the recurrence obtained by twice
differentiating J_n=A_n-B_nJ_{n-1} and writing s_n=J_n''(1).
All knot-theoretic content is confined to the two explicit hypotheses.
-/
theorem trefoil_all_colour_second_moments
    (s : ℕ → ℚ)
    (hs₁ : s 1 = 0)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      s n = trefoilASecondAtOne n - trefoilBSecondAtOne n -
        ((n : ℚ) - 1) / n * s (n - 1)) :
    ∀ n : ℕ, s (n + 1) = -2 * (((n + 1 : ℕ) : ℚ)^2 - 1) := by
  intro n
  induction n with
  | zero => simpa using hs₁
  | succ n ih =>
      rw [hrec (n + 2) (by omega)]
      have hprev : n + 2 - 1 = n + 1 := by omega
      rw [hprev, ih]
      have hn : ((n : ℚ) + 2) ≠ 0 := by positivity
      push_cast
      rw [trefoil_second_derivative_difference hn]
      field_simp
      ring

#print axioms trefoil_all_colour_second_moments

/-- The exact finite-N h² coefficient: -1+1/N², not merely its limit. -/
theorem trefoil_h2_coefficient_all_colours
    (s : ℕ → ℚ)
    (hs₁ : s 1 = 0)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      s n = trefoilASecondAtOne n - trefoilBSecondAtOne n -
        ((n : ℚ) - 1) / n * s (n - 1)) (n : ℕ) :
    s (n + 1) / (2 * ((n + 1 : ℕ) : ℚ)^2) =
      -1 + 1 / ((n + 1 : ℕ) : ℚ)^2 := by
  rw [trefoil_all_colour_second_moments s hs₁ hrec n]
  have hn : (((n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp
  ring

#print axioms trefoil_h2_coefficient_all_colours

open Filter Topology

/-- Hence the second Melvin--Morton coefficient is the limit -1. -/
theorem trefoil_h2_coefficient_tendsto
    (s : ℕ → ℚ)
    (hs₁ : s 1 = 0)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      s n = trefoilASecondAtOne n - trefoilBSecondAtOne n -
        ((n : ℚ) - 1) / n * s (n - 1)) :
    Tendsto (fun n : ℕ => s (n + 1) / (2 * ((n + 1 : ℕ) : ℚ)^2)) atTop (𝓝 (-1)) := by
  have h₁ : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℚ))) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℚ))
  have h₂ : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℚ)^2)) atTop (𝓝 0) := by
    simpa [div_pow] using h₁.pow 2
  have heq : (fun n : ℕ => s (n + 1) / (2 * ((n + 1 : ℕ) : ℚ)^2)) =
      (fun n : ℕ => -1 + 1 / (((n + 1 : ℕ) : ℚ)^2)) := by
    funext n
    exact trefoil_h2_coefficient_all_colours s hs₁ hrec n
  rw [heq]
  simpa using h₂.const_add (-1 : ℚ)

#print axioms trefoil_h2_coefficient_tendsto

end B53
end


/-! ## B53 — the h^2 coefficient limit and its second derivative

Integrated from `.ultramath/smww885zp/m15/B53Analysis.lean`.
-/

section
namespace B53Analysis

lemma hasDerivAt_exp_const_mul (c x : ℝ) :
    HasDerivAt (fun h : ℝ => Real.exp (c * h)) (c * Real.exp (c * x)) x := by
  have hc : HasDerivAt (fun h : ℝ => c * h) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  convert hc.exp using 1 <;> ring

noncomputable def j2scaled (N h : ℝ) : ℝ :=
  Real.exp ((1/N) * h) + Real.exp ((3/N) * h) - Real.exp ((4/N) * h)

noncomputable def j2scaledDeriv (N x : ℝ) : ℝ :=
  (1/N) * Real.exp ((1/N) * x) + (3/N) * Real.exp ((3/N) * x) -
    (4/N) * Real.exp ((4/N) * x)

lemma hasDerivAt_j2scaled (N x : ℝ) :
    HasDerivAt (j2scaled N) (j2scaledDeriv N x) x := by
  exact ((hasDerivAt_exp_const_mul (1/N) x).add
    (hasDerivAt_exp_const_mul (3/N) x)).sub (hasDerivAt_exp_const_mul (4/N) x)

lemma deriv_j2scaled (N : ℝ) : deriv (j2scaled N) = j2scaledDeriv N := by
  funext x
  exact (hasDerivAt_j2scaled N x).deriv

lemma hasDerivAt_j2scaledDeriv (N x : ℝ) :
    HasDerivAt (j2scaledDeriv N)
      ((1/N) * ((1/N) * Real.exp ((1/N) * x)) +
       (3/N) * ((3/N) * Real.exp ((3/N) * x)) -
       (4/N) * ((4/N) * Real.exp ((4/N) * x))) x := by
  exact ((hasDerivAt_exp_const_mul (1/N) x).const_mul (1/N) |>.add
    ((hasDerivAt_exp_const_mul (3/N) x).const_mul (3/N))).sub
      ((hasDerivAt_exp_const_mul (4/N) x).const_mul (4/N))

lemma j2scaled_second_deriv (N : ℝ) :
    deriv (deriv (j2scaled N)) 0 = -6 / N^2 := by
  rw [deriv_j2scaled]
  convert (hasDerivAt_j2scaledDeriv N 0).deriv using 1
  norm_num
  ring

lemma j2scaled_first_deriv (N : ℝ) : deriv (j2scaled N) 0 = 0 := by
  convert (hasDerivAt_j2scaled N 0).deriv using 1
  norm_num [j2scaledDeriv]
  ring

/-- Δ_3₁(e^h), written with scalar multipliers for convenient differentiation. -/
noncomputable def deltaExp (h : ℝ) : ℝ :=
  Real.exp (1 * h) - 1 + Real.exp ((-1) * h)

noncomputable def deltaDeriv (x : ℝ) : ℝ :=
  1 * Real.exp (1 * x) + (-1) * Real.exp ((-1) * x)

lemma hasDerivAt_deltaExp (x : ℝ) :
    HasDerivAt deltaExp (deltaDeriv x) x := by
  exact ((hasDerivAt_exp_const_mul 1 x).sub_const 1).add
    (hasDerivAt_exp_const_mul (-1) x)

lemma deriv_deltaExp : deriv deltaExp = deltaDeriv := by
  funext x
  exact (hasDerivAt_deltaExp x).deriv

lemma hasDerivAt_deltaDeriv (x : ℝ) :
    HasDerivAt deltaDeriv
      (1 * (1 * Real.exp (1*x)) + (-1) * ((-1) * Real.exp ((-1)*x))) x := by
  exact (hasDerivAt_exp_const_mul 1 x).const_mul 1 |>.add
    ((hasDerivAt_exp_const_mul (-1) x).const_mul (-1))

lemma deltaExp_first_deriv : deriv deltaExp 0 = 0 := by
  convert (hasDerivAt_deltaExp 0).deriv using 1
  norm_num [deltaDeriv]

lemma deltaExp_second_deriv : deriv (deriv deltaExp) 0 = 2 := by
  rw [deriv_deltaExp]
  convert (hasDerivAt_deltaDeriv 0).deriv using 1
  norm_num

lemma deltaExp_eq (h : ℝ) : deltaExp h = Real.exp h - 1 + Real.exp (-h) := by
  simp [deltaExp]

lemma deltaExp_pos (h : ℝ) : 0 < deltaExp h := by
  have hc := Real.one_le_cosh h
  rw [Real.cosh_eq] at hc
  simp only [deltaExp, one_mul, neg_mul]
  linarith

noncomputable def invDeltaExp (h : ℝ) : ℝ := (deltaExp h)⁻¹

noncomputable def invDeltaDeriv (x : ℝ) : ℝ :=
  -deltaDeriv x / (deltaExp x)^2

lemma hasDerivAt_invDeltaExp (x : ℝ) :
    HasDerivAt invDeltaExp (invDeltaDeriv x) x := by
  exact (hasDerivAt_deltaExp x).inv (ne_of_gt (deltaExp_pos x))

lemma deriv_invDeltaExp : deriv invDeltaExp = invDeltaDeriv := by
  funext x
  exact (hasDerivAt_invDeltaExp x).deriv

lemma hasDerivAt_invDeltaDeriv_zero :
    HasDerivAt invDeltaDeriv (-2) 0 := by
  have hn := (hasDerivAt_deltaDeriv 0).neg
  have hd := (hasDerivAt_deltaExp 0).mul (hasDerivAt_deltaExp 0)
  have hz : deltaExp 0 * deltaExp 0 ≠ 0 := ne_of_gt (mul_pos (deltaExp_pos 0) (deltaExp_pos 0))
  convert hn.div hd hz using 1
  · ext x
    simp [invDeltaDeriv, pow_two]
  · norm_num [deltaDeriv, deltaExp]

lemma invDeltaExp_first_deriv : deriv invDeltaExp 0 = 0 := by
  convert (hasDerivAt_invDeltaExp 0).deriv using 1
  norm_num [invDeltaDeriv, deltaDeriv]

lemma invDeltaExp_second_deriv : deriv (deriv invDeltaExp) 0 = -2 := by
  rw [deriv_invDeltaExp]
  exact hasDerivAt_invDeltaDeriv_zero.deriv

#print axioms hasDerivAt_exp_const_mul
#print axioms hasDerivAt_j2scaled
#print axioms deriv_j2scaled
#print axioms hasDerivAt_j2scaledDeriv
#print axioms j2scaled_second_deriv
#print axioms j2scaled_first_deriv
#print axioms hasDerivAt_deltaExp
#print axioms deriv_deltaExp
#print axioms hasDerivAt_deltaDeriv
#print axioms deltaExp_first_deriv
#print axioms deltaExp_second_deriv
#print axioms deltaExp_eq
#print axioms deltaExp_pos
#print axioms hasDerivAt_invDeltaExp
#print axioms deriv_invDeltaExp
#print axioms hasDerivAt_invDeltaDeriv_zero
#print axioms invDeltaExp_first_deriv
#print axioms invDeltaExp_second_deriv

end B53Analysis
end


/-! ## B53 — the domain obstruction at a root of the Alexander polynomial

Integrated from `.ultramath/smww885zp/m16/B53Domain.lean`.
-/

section
/-!
# B53: domain test for the reciprocal Conway/Alexander shadow

The trefoil has Conway polynomial `1 + z^2`. This file isolates the finite
algebra behind testing the reciprocal at a zero of that polynomial. It
intentionally does not define coloured Jones polynomials or assert MMR.
-/

open scoped BigOperators

namespace B53Domain

/-- The Conway polynomial of the (right- or left-handed) trefoil. -/
def conwayTrefoil (z : ℂ) : ℂ := 1 + z ^ 2

@[simp] theorem conwayTrefoil_zero : conwayTrefoil 0 = 1 := by
  norm_num [conwayTrefoil]

/-- A concrete zero of the trefoil Conway polynomial. -/
@[simp] theorem conwayTrefoil_I : conwayTrefoil Complex.I = 0 := by
  simp [conwayTrefoil, Complex.I_sq]

/-- No finite complex number is a multiplicative inverse at that zero. -/
theorem no_finite_inverse_at_trefoil_root :
    ¬ ∃ w : ℂ, conwayTrefoil Complex.I * w = 1 := by
  rintro ⟨w, hw⟩
  rw [conwayTrefoil_I, zero_mul] at hw
  exact zero_ne_one hw

/-- The local geometric series for the reciprocal Conway polynomial.
The explicit hypothesis is the pointwise convergence condition missing from
any reading of `J_N → 1/Δ` as an unrestricted numerical assertion. -/
theorem hasSum_inverse_conwayTrefoil (z : ℂ) (hz : ‖-(z ^ 2)‖ < 1) :
    HasSum (fun n : ℕ => (-(z ^ 2)) ^ n) (conwayTrefoil z)⁻¹ := by
  simpa [conwayTrefoil, sub_neg_eq_add] using
    (hasSum_geometric_of_norm_lt_one (ξ := -(z ^ 2)) hz)

/-- At the zero `z = i`, that same geometric series is not summable. -/
theorem not_summable_inverse_conwayTrefoil_at_root :
    ¬ Summable (fun n : ℕ => (-(Complex.I ^ 2)) ^ n) := by
  have hroot : (-(Complex.I ^ 2) : ℂ) = 1 := by
    rw [Complex.I_sq]
    norm_num
  rw [hroot]
  simpa using
    (not_congr (summable_geometric_iff_norm_lt_one (ξ := (1 : ℂ))))

/-- Every term at the root is one, so ordinary summation cannot repair it. -/
theorem inverse_series_term_at_root (n : ℕ) :
    (-(Complex.I ^ 2)) ^ n = 1 := by
  rw [show (-(Complex.I ^ 2) : ℂ) = 1 by rw [Complex.I_sq]; norm_num]
  exact one_pow n

/-- The symmetric Alexander polynomial of the trefoil, as tabulated by
Knot Atlas. -/
noncomputable def alexanderTrefoil (t : ℂ) : ℂ := t + t⁻¹ - 1

/-- An explicit primitive-sixth-root choice. -/
noncomputable def trefoilAlexanderRoot : ℂ :=
  (1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

theorem trefoilAlexanderRoot_polynomial :
    trefoilAlexanderRoot ^ 2 - trefoilAlexanderRoot + 1 = 0 := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  dsimp [trefoilAlexanderRoot]
  ring_nf
  simp [Complex.I_sq, hs]
  ring

theorem trefoilAlexanderRoot_ne_zero : trefoilAlexanderRoot ≠ 0 := by
  intro h
  have hr : trefoilAlexanderRoot.re = 0 := by rw [h]; rfl
  norm_num [trefoilAlexanderRoot, Complex.normSq_apply] at hr

/-- The witness is on the unit circle, not merely somewhere in `ℂ`. -/
theorem trefoilAlexanderRoot_normSq : trefoilAlexanderRoot.normSq = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [trefoilAlexanderRoot, Complex.normSq_apply]
  ring_nf

/-- The Alexander root has norm one. -/
theorem trefoilAlexanderRoot_norm : ‖trefoilAlexanderRoot‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← Complex.normSq_eq_norm_sq]
  simp [trefoilAlexanderRoot, Complex.normSq_apply]
  ring_nf

@[simp] theorem alexanderTrefoil_at_root : alexanderTrefoil trefoilAlexanderRoot = 0 := by
  rw [show alexanderTrefoil trefoilAlexanderRoot =
      (trefoilAlexanderRoot ^ 2 - trefoilAlexanderRoot + 1) / trefoilAlexanderRoot by
    dsimp [alexanderTrefoil]
    field_simp [trefoilAlexanderRoot_ne_zero]
    ring]
  rw [trefoilAlexanderRoot_polynomial]
  norm_num

/-- Even after restricting to the unit circle, the reciprocal cannot be a
total finite complex-valued function. -/
theorem trefoil_no_total_reciprocal_on_circle :
    ¬ ∃ V : ℂ → ℂ, ∀ t, ‖t‖ = 1 → alexanderTrefoil t * V t = 1 := by
  rintro ⟨V, hV⟩
  have h := hV trefoilAlexanderRoot trefoilAlexanderRoot_norm
  rw [alexanderTrefoil_at_root, zero_mul] at h
  exact zero_ne_one h

/-- The symmetric Alexander polynomial of the twist knot `6_1` (Stevedore),
as tabulated by Knot Atlas. -/
noncomputable def alexanderStevedore (t : ℝ) : ℝ := -2 * t + 5 - 2 / t

@[simp] theorem alexanderStevedore_one : alexanderStevedore 1 = 1 := by
  norm_num [alexanderStevedore]

/-- A real zero of an Alexander polynomial in the card's stated twist-knot
class. -/
@[simp] theorem alexanderStevedore_two : alexanderStevedore 2 = 0 := by
  norm_num [alexanderStevedore]

/-- Consequently no total real-valued function can be its reciprocal at every
point, without restricting the domain or allowing an extended value. -/
theorem stevedore_no_total_reciprocal :
    ¬ ∃ V : ℝ → ℝ, ∀ t, alexanderStevedore t * V t = 1 := by
  rintro ⟨V, hV⟩
  have h := hV 2
  rw [alexanderStevedore_two, zero_mul] at h
  exact zero_ne_one h

@[simp] theorem alexanderStevedore_three : alexanderStevedore 3 = -5 / 3 := by
  norm_num [alexanderStevedore]

/-- At a regular point, the ledger's reciprocal and the HTML's bare
Alexander polynomial are unequal targets. -/
theorem stevedore_reciprocal_differs_at_three :
    (alexanderStevedore 3)⁻¹ ≠ alexanderStevedore 3 := by
  norm_num

/-- The HTML's bare `Δ` target and the ledger/MMR reciprocal target cannot
both describe the same leading coefficient at this regular point. The two
hypotheses are kept explicit: the first is the cited MMR shadow, the second
is the literal HTML display. -/
theorem mmr_reciprocal_and_html_bare_polynomial_incompatible (V : ℝ)
    (hMMR : V = (alexanderStevedore 3)⁻¹)
    (hHTML : V = alexanderStevedore 3) : False := by
  rw [hMMR] at hHTML
  exact stevedore_reciprocal_differs_at_three hHTML

end B53Domain

#print axioms B53Domain.conwayTrefoil_zero
#print axioms B53Domain.conwayTrefoil_I
#print axioms B53Domain.no_finite_inverse_at_trefoil_root
#print axioms B53Domain.hasSum_inverse_conwayTrefoil
#print axioms B53Domain.not_summable_inverse_conwayTrefoil_at_root
#print axioms B53Domain.inverse_series_term_at_root
#print axioms B53Domain.trefoilAlexanderRoot_polynomial
#print axioms B53Domain.trefoilAlexanderRoot_ne_zero
#print axioms B53Domain.trefoilAlexanderRoot_normSq
#print axioms B53Domain.trefoilAlexanderRoot_norm
#print axioms B53Domain.alexanderTrefoil_at_root
#print axioms B53Domain.trefoil_no_total_reciprocal_on_circle
#print axioms B53Domain.alexanderStevedore_one
#print axioms B53Domain.alexanderStevedore_two
#print axioms B53Domain.stevedore_no_total_reciprocal
#print axioms B53Domain.alexanderStevedore_three
#print axioms B53Domain.stevedore_reciprocal_differs_at_three
#print axioms B53Domain.mmr_reciprocal_and_html_bare_polynomial_incompatible
end


/-! ## B53 — 7_4 and 9_2 share the Alexander polynomial but not the A-polynomial

Integrated from `.ultramath/smww885zp/m14/B53.lean`.
-/

section
/-!
# B53: the Alexander polynomial does not determine the A-polynomial

Arithmetic certificate for the two-bridge knots 7_4 = S(15,11) and
9_2 = S(15,7).  The A-polynomial expressions below are transcribed from
Jim Hoste's table at
https://knotinfo.org/descriptions/a_polys_table_two_bridge.html
(entries `{7, {11, 15}}` and `{9, {7, 15}}`).

The identification of the knots and the topological meaning of these
polynomials are external input, not a Lean development of knot theory.
Their Alexander polynomials were independently recomputed from the PD
codes by SnapPy 3.3.2 and SageMath 10.8; both give 4*t^2 - 7*t + 4 after
choosing the normalized (non-Laurent) representative.
-/

namespace B53

/-- Normalized Alexander polynomial shared by 7_4 and 9_2. -/
def delta74 (t : ℝ) : ℝ := 4 * t^2 - 7 * t + 4

/-- Normalized Alexander polynomial shared by 7_4 and 9_2. -/
def delta92 (t : ℝ) : ℝ := 4 - 7 * t + 4 * t^2

/-- Hoste's nonabelian A-polynomial factor for 7_4 = S(15,11). -/
def a74 (L M : ℝ) : ℝ :=
  1 - 3*L + 3*L^2 - L^3 + 7*L*M^2 - 10*L^2*M^2 + 3*L^3*M^2 + 4*L*M^4 + 3*L^2*M^4 - 3*L^3*M^4 - 6*L*M^6 + 21*L^2*M^6 - 2*L^3*M^6 + L*M^8 - 3*L^2*M^8 + 10*L^3*M^8 + L^4*M^8 + 3*L*M^10 - 17*L^2*M^10 + 6*L^3*M^10 - 2*L^4*M^10 - 2*L*M^12 + 6*L^2*M^12 - 17*L^3*M^12 + 3*L^4*M^12 + L*M^14 + 10*L^2*M^14 - 3*L^3*M^14 + L^4*M^14 - 2*L^2*M^16 + 21*L^3*M^16 - 6*L^4*M^16 - 3*L^2*M^18 + 3*L^3*M^18 + 4*L^4*M^18 + 3*L^2*M^20 - 10*L^3*M^20 + 7*L^4*M^20 - L^2*M^22 + 3*L^3*M^22 - 3*L^4*M^22 + L^5*M^22

/-- Hoste's nonabelian A-polynomial factor for 9_2 = S(15,7). -/
def a92 (L M : ℝ) : ℝ :=
  1 - 3*L + 3*L^2 - L^3 + 6*L*M^2 - 12*L^2*M^2 + 6*L^3*M^2 + 4*L*M^4 + 5*L^2*M^4 - 12*L^3*M^4 + 3*L^4*M^4 + 15*L^2*M^6 + 2*L^3*M^6 - 13*L^4*M^6 + 10*L^2*M^8 + 5*L^3*M^8 + 9*L^4*M^8 - 3*L^5*M^8 + 15*L^3*M^10 + 16*L^4*M^10 + 8*L^5*M^10 + 20*L^3*M^12 + L^6*M^12 - 15*L^4*M^14 - 5*L^5*M^14 - L^6*M^14 - L*M^16 - 5*L^2*M^16 - 15*L^3*M^16 + L*M^18 + 20*L^4*M^18 + 8*L^2*M^20 + 16*L^3*M^20 + 15*L^4*M^20 - 3*L^2*M^22 + 9*L^3*M^22 + 5*L^4*M^22 + 10*L^5*M^22 - 13*L^3*M^24 + 2*L^4*M^24 + 15*L^5*M^24 + 3*L^3*M^26 - 12*L^4*M^26 + 5*L^5*M^26 + 4*L^6*M^26 + 6*L^4*M^28 - 12*L^5*M^28 + 6*L^6*M^28 - L^4*M^30 + 3*L^5*M^30 - 3*L^6*M^30 + L^7*M^30

theorem alexander_coincidence : delta74 = delta92 := by
  funext t
  simp [delta74, delta92]
  ring

theorem alexander74_normalized : delta74 1 = 1 := by
  norm_num [delta74]

theorem alexander92_normalized : delta92 1 = 1 := by
  norm_num [delta92]

/-- The M=1 specialisation of the 7_4 A-polynomial. -/
theorem a74_at_m_one (L : ℝ) : a74 L 1 = (L + 1)^5 := by
  simp [a74]
  ring

/-- The M=1 specialisation of the 9_2 A-polynomial. -/
theorem a92_at_m_one (L : ℝ) : a92 L 1 = (L + 1)^7 := by
  simp [a92]
  ring

theorem a74_witness_value : a74 2 1 = 243 := by
  rw [a74_at_m_one]
  norm_num

theorem a92_witness_value : a92 2 1 = 2187 := by
  rw [a92_at_m_one]
  norm_num

theorem witness_A_values_differ : a74 2 1 ≠ a92 2 1 := by
  rw [a74_witness_value, a92_witness_value]
  norm_num

/-- There is no function of the normalized Alexander polynomial alone
which returns both A-polynomials. -/
theorem no_A_function_of_Alexander
    (G : (ℝ → ℝ) → (ℝ → ℝ → ℝ))
    (h74 : a74 = G delta74)
    (h92 : a92 = G delta92) : False := by
  have h : a74 = a92 := by
    calc
      a74 = G delta74 := h74
      _ = G delta92 := by rw [alexander_coincidence]
      _ = a92 := h92.symm
  have hv := congrFun (congrFun h 2) 1
  rw [a74_witness_value, a92_witness_value] at hv
  norm_num at hv

open scoped LaurentPolynomial
open LaurentPolynomial

/-- The quotient of the two M=1 specialisations, as a Laurent polynomial. -/
noncomputable def quotientAtMOne : ℝ[T;T⁻¹] := (T 1 + 1)^2

theorem specialisation_quotient :
    (T 1 + 1 : ℝ[T;T⁻¹])^7 = (T 1 + 1)^5 * quotientAtMOne := by
  simp [quotientAtMOne]
  ring

/-- The quotient is not a Laurent-polynomial unit.  Thus the mismatch
cannot be removed by a monomial/sign normalisation. -/
theorem quotientAtMOne_not_isUnit : ¬ IsUnit quotientAtMOne := by
  rw [isUnit_iff_exists_inv]
  rintro ⟨q, hq⟩
  let x : ℝˣ := -1
  have h := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℝ) x) hq
  norm_num [quotientAtMOne, x] at h

#print axioms alexander_coincidence
#print axioms alexander74_normalized
#print axioms alexander92_normalized
#print axioms a74_at_m_one
#print axioms a92_at_m_one
#print axioms a74_witness_value
#print axioms a92_witness_value
#print axioms witness_A_values_differ
#print axioms no_A_function_of_Alexander
#print axioms specialisation_quotient
#print axioms quotientAtMOne_not_isUnit

end B53
end


/-! ## B58 — the log-det seam identity, and the cone inference that fails

Integrated from `.ultramath/smww885zp/m10/B58.lean`.
-/

section
/-!
# B58: subadditivity does not imply the displayed cone inclusion

The scalar blocks are `partA = partB = [4]`, coupled by `3`. The glued
operator is `[[4, 3], [3, 4]]`. Thus its determinant is `7`, and the Schur
parameter is `9 / 16`. All the obstruction-ledger hypotheses hold.

The cone `cone o = {(x,y) | x ≥ 0, |y| * exp o ≤ x}` is invariant under
nonnegative scaling and anti-monotone in the obstruction `o`; on its `x = 1`
cross-section, a positive slope `t` is admissible exactly when `log t + o ≤ 0`.
This is therefore the natural reading in which a larger obstruction narrows
the cone. Nevertheless the direction `(1, 1 / 5)` is admissible for either
separate block, but not for the glued block.
-/

namespace RelationalAtlas.B58

open scoped Matrix

/-- The first positive one-by-one block. -/
def partA : Matrix (Fin 1) (Fin 1) ℝ := !![4]

/-- The second positive one-by-one block. -/
def partB : Matrix (Fin 1) (Fin 1) ℝ := !![4]

/-- The scalar interface coupling. -/
def coupling : ℝ := 3

/-- The explicitly glued two-by-two operator. -/
def glued : Matrix (Fin 2) (Fin 2) ℝ :=
  !![partA 0 0, coupling; coupling, partB 0 0]

/-- Log-determinant obstruction of a finite real square matrix. -/
noncomputable def O {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : ℝ := Real.log M.det

/-- The eigenvalue parameter in the one-interface Schur formula. -/
noncomputable def interfaceMu : ℝ := coupling ^ 2 / (partA.det * partB.det)

/-- A scale-invariant admissible cone determined by an obstruction value. -/
noncomputable def cone (o : ℝ) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | 0 ≤ z.1 ∧ |z.2| * Real.exp o ≤ z.1}

/-- The counterexample direction, stable under positive rescaling. -/
noncomputable def witness : ℝ × ℝ := (1, 1 / 5)

@[simp] theorem partA_det : partA.det = 4 := by
  norm_num [partA, Matrix.det_fin_two]

@[simp] theorem partB_det : partB.det = 4 := by
  norm_num [partB, Matrix.det_fin_two]

@[simp] theorem glued_det : glued.det = 7 := by
  norm_num [glued, partA, partB, coupling, Matrix.det_fin_two]

@[simp] theorem partA00 : partA 0 0 = 4 := by norm_num [partA]

@[simp] theorem partB00 : partB 0 0 = 4 := by norm_num [partB]

theorem partA_posDef : partA.PosDef := by
  have h : partA = (4 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [partA, Matrix.ofNat_apply]
  rw [h]
  exact Matrix.PosDef.ofNat 4

theorem partB_posDef : partB.PosDef := by
  have h : partB = (4 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [partB, Matrix.ofNat_apply]
  rw [h]
  exact Matrix.PosDef.ofNat 4

/-- Positive definiteness by `glued = I + 3 vvᵀ`, with `v = (1,1)`. -/
theorem glued_posDef : glued.PosDef := by
  let v : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]
  have hpd : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := Matrix.PosDef.one
  have hps : ((3 : ℝ) • (vᴴ * v)).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self v).smul (by norm_num)
  have hsum := hpd.add_posSemidef hps
  have h : glued = (1 : Matrix (Fin 2) (Fin 2) ℝ) + (3 : ℝ) • (vᴴ * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glued, partA, partB, coupling, v, Matrix.mul_apply] <;> norm_num
  rw [h]
  exact hsum

/-- A concrete bound on the coupling, and the strict Schur bound. -/
theorem coupling_bounded : |coupling| ≤ 3 ∧ coupling ^ 2 < partA.det * partB.det := by
  norm_num [coupling]

@[simp] theorem interfaceMu_value : interfaceMu = 9 / 16 := by
  norm_num [interfaceMu, coupling]

theorem interfaceMu_nonneg : 0 ≤ interfaceMu := by norm_num [interfaceMu_value]

theorem interfaceMu_lt_one : interfaceMu < 1 := by norm_num [interfaceMu_value]

/-- The exact determinant form of the scalar Schur-complement identity. -/
theorem schur_det_identity :
    glued.det = partA.det * partB.det * (1 - interfaceMu) := by
  norm_num [interfaceMu, coupling]

/-- The exact logarithmic seam ledger from the card. -/
theorem obstruction_ledger :
    O glued = O partA + O partB + Real.log (1 - interfaceMu) := by
  unfold O
  rw [schur_det_identity]
  rw [Real.log_mul (by norm_num : partA.det * partB.det ≠ 0)
    (by norm_num [interfaceMu_value] : (1 - interfaceMu) ≠ 0)]
  rw [Real.log_mul (by norm_num : partA.det ≠ 0) (by norm_num : partB.det ≠ 0)]

/-- The interface correction is nonpositive. -/
theorem interface_term_nonpos : Real.log (1 - interfaceMu) ≤ 0 := by
  apply Real.log_nonpos <;> norm_num [interfaceMu_value]

/-- In particular, the stated log-determinant subadditivity holds. -/
theorem obstruction_subadditive : O glued ≤ O partA + O partB := by
  rw [obstruction_ledger]
  linarith [interface_term_nonpos]

/-- The cone really is anti-monotone in obstruction. -/
theorem cone_antitone {o₁ o₂ : ℝ} (h : o₁ ≤ o₂) : cone o₂ ⊆ cone o₁ := by
  intro x hx
  refine ⟨hx.1, le_trans ?_ hx.2⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) (abs_nonneg x.2)

/-- These admissible regions are cones in the literal scale-invariant sense. -/
theorem cone_smul {a : ℝ} (ha : 0 ≤ a) {o : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ cone o) : a • z ∈ cone o := by
  rcases z with ⟨x, y⟩
  change 0 ≤ x ∧ |y| * Real.exp o ≤ x at hz
  change 0 ≤ a * x ∧ |a * y| * Real.exp o ≤ a * x
  rw [abs_mul, abs_of_nonneg ha, mul_assoc]
  exact ⟨mul_nonneg ha hz.1, mul_le_mul_of_nonneg_left hz.2 ha⟩

/-- On the `x = 1` cross-section, a positive slope `t` is admissible exactly
when `log t + o ≤ 0`. -/
theorem positive_slope_mem_cone_iff {t o : ℝ} (ht : 0 < t) :
    (1, t) ∈ cone o ↔ Real.log t + o ≤ 0 := by
  have hp : 0 < t * Real.exp o := mul_pos ht (Real.exp_pos o)
  change (0 ≤ (1 : ℝ) ∧ |t| * Real.exp o ≤ 1) ↔ Real.log t + o ≤ 0
  rw [and_iff_right (by norm_num : (0 : ℝ) ≤ 1), abs_of_pos ht]
  calc
    t * Real.exp o ≤ 1 ↔ Real.log (t * Real.exp o) ≤ 0 :=
      (Real.log_nonpos_iff hp.le).symm
    _ ↔ Real.log t + o ≤ 0 := by
      rw [Real.log_mul ht.ne' (Real.exp_ne_zero o), Real.log_exp]

/-- The glued obstruction exceeds either individual obstruction, although it
is below their sum. -/
theorem obstruction_exceeds_parts : O partA < O glued ∧ O partB < O glued := by
  simp only [O, partA_det, partB_det, glued_det]
  exact ⟨Real.log_lt_log (by norm_num) (by norm_num),
    Real.log_lt_log (by norm_num) (by norm_num)⟩

/-- The same direction is admissible for the first separate block. -/
theorem witness_mem_partA : witness ∈ cone (O partA) := by
  norm_num [witness, cone, O, Real.exp_log]

/-- The same direction is admissible for the second separate block. -/
theorem witness_mem_partB : witness ∈ cone (O partB) := by
  norm_num [witness, cone, O, Real.exp_log]

/-- It is not admissible for the glued operator. -/
theorem witness_not_mem_glued : witness ∉ cone (O glued) := by
  norm_num [witness, cone, O, Real.exp_log]

/-- **Counterexample to B58's displayed cone implication.** Every operator,
Schur, boundedness and subadditivity hypothesis above holds, but the
conclusion's union is not contained in the composite cone. -/
theorem cone_inclusion_fails :
    ¬ cone (O glued) ⊇ cone (O partA) ∪ cone (O partB) := by
  intro h
  apply witness_not_mem_glued
  apply h
  exact Or.inl witness_mem_partA

/-- All witnesses and checks in one statement. -/
theorem b58_counterexample :
    partA.PosDef ∧ partB.PosDef ∧ glued.PosDef ∧
      |coupling| ≤ 3 ∧ coupling ^ 2 < partA.det * partB.det ∧
      0 ≤ interfaceMu ∧ interfaceMu < 1 ∧
      O glued = O partA + O partB + Real.log (1 - interfaceMu) ∧
      O glued ≤ O partA + O partB ∧
      ¬ cone (O glued) ⊇ cone (O partA) ∪ cone (O partB) := by
  exact ⟨partA_posDef, partB_posDef, glued_posDef,
    coupling_bounded.1, coupling_bounded.2,
    interfaceMu_nonneg, interfaceMu_lt_one,
    obstruction_ledger, obstruction_subadditive, cone_inclusion_fails⟩

#print axioms partA_det
#print axioms partB_det
#print axioms glued_det
#print axioms partA00
#print axioms partB00
#print axioms partA_posDef
#print axioms partB_posDef
#print axioms glued_posDef
#print axioms coupling_bounded
#print axioms interfaceMu_value
#print axioms interfaceMu_nonneg
#print axioms interfaceMu_lt_one
#print axioms schur_det_identity
#print axioms obstruction_ledger
#print axioms interface_term_nonpos
#print axioms obstruction_subadditive
#print axioms cone_antitone
#print axioms cone_smul
#print axioms positive_slope_mem_cone_iff
#print axioms obstruction_exceeds_parts
#print axioms witness_mem_partA
#print axioms witness_mem_partB
#print axioms witness_not_mem_glued
#print axioms cone_inclusion_fails
#print axioms b58_counterexample

end RelationalAtlas.B58
end


/-! ## B62 — the exact partial-correlation algebra under linear mass control

Integrated from `.ultramath/smww885zp/m11/B62.lean`.
-/

section
/-!
# B62: partial correlation of two power-law size proxies

For centred log-variables `m` and `r`, put `x = m - a*r` and
`y = m - b*r`.  The parameters below are
`vm = Cov(m,m)`, `vr = Cov(r,r)`, and `c = Cov(m,r)`.
The definitions are the ordinary covariance formulae for `x` and `y`,
followed by the usual formula for partial correlation after linearly
controlling for `m`.
-/

namespace B62

noncomputable section

/-- The part of `Var r` left after linear regression on `m`. -/
def residualVar (vm vr c : ℝ) : ℝ := vr - c ^ 2 / vm

/-- Numerator of the partial correlation of `m-a*r` and `m-b*r` given `m`. -/
def partialNum (vm vr c a b : ℝ) : ℝ :=
  vm + a * b * vr - (a + b) * c - (vm - a * c) * (vm - b * c) / vm

/-- Residual variance of `m-a*r` after linear regression on `m`. -/
def proxyResidualVar (vm vr c a : ℝ) : ℝ :=
  vm + a ^ 2 * vr - 2 * a * c - (vm - a * c) ^ 2 / vm

/-- Residual standard deviation of a proxy after linear mass control. -/
def proxyResidualSD (vm vr c a : ℝ) : ℝ :=
  Real.sqrt (proxyResidualVar vm vr c a)

/-- The ordinary partial-correlation formula, with variances and covariances
computed from `x=m-a*r`, `y=m-b*r`. -/
def partialCorr (vm vr c a b : ℝ) : ℝ :=
  partialNum vm vr c a b /
    Real.sqrt (proxyResidualVar vm vr c a * proxyResidualVar vm vr c b)

lemma partialNum_eq (vm vr c a b : ℝ) (hvm : vm ≠ 0) :
    partialNum vm vr c a b = a * b * residualVar vm vr c := by
  unfold partialNum residualVar
  field_simp [hvm]
  ring

lemma proxyResidualVar_eq (vm vr c a : ℝ) (hvm : vm ≠ 0) :
    proxyResidualVar vm vr c a = a ^ 2 * residualVar vm vr c := by
  unfold proxyResidualVar residualVar
  field_simp [hvm]
  ring

/-- For nonzero exponents of the same sign, the partial correlation is
exactly one.  The only nondegeneracy conditions are positive mass variance,
nonvanishing radius residual, and `a*b>0`. -/
theorem partialCorr_eq_one (vm vr c a b : ℝ)
    (hvm : vm ≠ 0) (hab : 0 < a * b) (hD : 0 < residualVar vm vr c) :
    partialCorr vm vr c a b = 1 := by
  rw [partialCorr, partialNum_eq vm vr c a b hvm,
    proxyResidualVar_eq vm vr c a hvm, proxyResidualVar_eq vm vr c b hvm]
  have hprod : 0 < a * b * residualVar vm vr c := mul_pos hab hD
  have hsq : (a ^ 2 * residualVar vm vr c) * (b ^ 2 * residualVar vm vr c) =
      (a * b * residualVar vm vr c) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq (le_of_lt hprod)]
  exact div_self (ne_of_gt hprod)

/-- With opposite-sign exponents the same computation gives exactly minus one. -/
theorem partialCorr_eq_neg_one (vm vr c a b : ℝ)
    (hvm : vm ≠ 0) (hab : a * b < 0) (hD : 0 < residualVar vm vr c) :
    partialCorr vm vr c a b = -1 := by
  rw [partialCorr, partialNum_eq vm vr c a b hvm,
    proxyResidualVar_eq vm vr c a hvm, proxyResidualVar_eq vm vr c b hvm]
  have hprod : a * b * residualVar vm vr c < 0 := mul_neg_of_neg_of_pos hab hD
  have hsq : (a ^ 2 * residualVar vm vr c) * (b ^ 2 * residualVar vm vr c) =
      (a * b * residualVar vm vr c) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_neg hprod]
  have hne : a * b * residualVar vm vr c ≠ 0 := ne_of_lt hprod
  rw [div_neg, div_self hne]

/-- A zero exponent gives a zero residual variance, so partial correlation is
undefined rather than one. -/
lemma zero_exponent_residualVar (vm vr c : ℝ) (hvm : vm ≠ 0) :
    proxyResidualVar vm vr c 0 = 0 := by
  unfold proxyResidualVar
  field_simp [hvm]
  ring

/-- If radius is an exact linear function of mass, both residuals vanish. -/
lemma zero_radius_residual_proxyVar (vm c a : ℝ) (hvm : vm ≠ 0) :
    proxyResidualVar vm (c ^ 2 / vm) c a = 0 := by
  rw [proxyResidualVar_eq vm (c ^ 2 / vm) c a hvm]
  simp [residualVar]

/-- For the conventional compactness exponent `3/2` and surface-density
exponent `2`, the partial correlation is exactly one, not merely close to one.
The preceding theorem also covers every other pair of positive exponents. -/
theorem compactness_surfaceDensity_partialCorr (vm vr c : ℝ)
    (hvm : vm ≠ 0) (hD : 0 < residualVar vm vr c) :
    partialCorr vm vr c (3 / 2) 2 = 1 := by
  apply partialCorr_eq_one
  · exact hvm
  · norm_num
  · exact hD

/-- The residual radius variance can be arbitrarily small while the partial
correlation remains exactly one.  Thus no positive residual-variance floor is
a consequence of the power-law model alone. -/
theorem partialCorr_one_with_small_residual (ε a b : ℝ)
    (hε : 0 < ε) (hab : 0 < a * b) :
    partialCorr 1 (1 + ε ^ 2) 1 a b = 1 ∧
      residualVar 1 (1 + ε ^ 2) 1 = ε ^ 2 := by
  have hD : residualVar 1 (1 + ε ^ 2) 1 = ε ^ 2 := by
    unfold residualVar
    norm_num
  constructor
  · apply partialCorr_eq_one
    · norm_num
    · exact hab
    · rw [hD]
      positivity
  · exact hD

/-- Explicit small-residual instance: the radius residual variance is
`1/1000000`, while the two card proxies still have partial correlation one. -/
theorem explicit_small_residual_witness :
    partialCorr 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) 2 = 1 ∧
      residualVar 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 = 1 / 1000000 := by
  have h := partialCorr_one_with_small_residual (1 / 1000 : ℝ) (3 / 2) 2
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- In the explicit instance, both proxy residual standard deviations are in
the model's log units and are below `0.080`; nevertheless the partial
correlation is exactly one.  This refutes a universal `0.080` lower bound as a
consequence of the algebraic Carry hypotheses, not an empirical measurement. -/
theorem explicit_scatter_below_universal_floor :
    partialCorr 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) 2 = 1 ∧
      proxyResidualSD 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) = 3 / 2000 ∧
      proxyResidualSD 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 2 = 1 / 500 ∧
      (3 / 2000 : ℝ) < 8 / 100 ∧ (1 / 500 : ℝ) < 8 / 100 := by
  have hD : residualVar 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 = 1 / 1000000 := by
    norm_num [residualVar]
  have hvar15 : proxyResidualVar 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) =
      (3 / 2000 : ℝ) ^ 2 := by
    rw [proxyResidualVar_eq _ _ _ _ (by norm_num), hD]
    norm_num
  have hvar2 : proxyResidualVar 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 2 =
      (1 / 500 : ℝ) ^ 2 := by
    rw [proxyResidualVar_eq _ _ _ _ (by norm_num), hD]
    norm_num
  refine ⟨explicit_small_residual_witness.1, ?_, ?_, by norm_num, by norm_num⟩
  · rw [proxyResidualSD, hvar15, Real.sqrt_sq (by norm_num)]
  · rw [proxyResidualSD, hvar2, Real.sqrt_sq (by norm_num)]

/-- Population mean and covariance for four equally weighted observations. -/
def mean4 (x : Fin 4 → ℝ) : ℝ := (∑ i, x i) / 4

def cov4 (x y : Fin 4 → ℝ) : ℝ :=
  (∑ i, (x i - mean4 x) * (y i - mean4 y)) / 4

/-- A four-galaxy log-mass sample taking the values `1,1,-1,-1`. -/
def finiteMass : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- Log-radius is mass plus an independent balanced perturbation of
amplitude `1/1000` on the same four points. -/
def finiteRadius : Fin 4 → ℝ :=
  ![1 + 1 / 1000, 1 - 1 / 1000, -1 + 1 / 1000, -1 - 1 / 1000]

/-- The abstract covariance triple used above is realised exactly by four
observations.  Consequently the small-scatter witness uses actual power-law
proxies `10^m / (10^r)^a`, not an inadmissible covariance matrix. -/
theorem finite_sample_realisation :
    mean4 finiteMass = 0 ∧ mean4 finiteRadius = 0 ∧
      cov4 finiteMass finiteMass = 1 ∧
      cov4 finiteMass finiteRadius = 1 ∧
      cov4 finiteRadius finiteRadius = 1 + (1 / 1000 : ℝ) ^ 2 ∧
      partialCorr 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) 2 = 1 ∧
      proxyResidualSD 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 (3 / 2) < 8 / 100 ∧
      proxyResidualSD 1 (1 + (1 / 1000 : ℝ) ^ 2) 1 2 < 8 / 100 := by
  have hmom : mean4 finiteMass = 0 ∧ mean4 finiteRadius = 0 ∧
      cov4 finiteMass finiteMass = 1 ∧
      cov4 finiteMass finiteRadius = 1 ∧
      cov4 finiteRadius finiteRadius = 1 + (1 / 1000 : ℝ) ^ 2 := by
    norm_num [mean4, cov4, finiteMass, finiteRadius, Fin.sum_univ_four]
  obtain ⟨hmm, hrm, hmm2, hmr, hrr⟩ := hmom
  obtain ⟨hpc, hsd15, hsd2, hlt15, hlt2⟩ := explicit_scatter_below_universal_floor
  exact ⟨hmm, hrm, hmm2, hmr, hrr, hpc, hsd15 ▸ hlt15, hsd2 ▸ hlt2⟩

end
end B62

#print axioms B62.partialNum_eq
#print axioms B62.proxyResidualVar_eq
#print axioms B62.partialCorr_eq_one
#print axioms B62.partialCorr_eq_neg_one
#print axioms B62.zero_exponent_residualVar
#print axioms B62.zero_radius_residual_proxyVar
#print axioms B62.compactness_surfaceDensity_partialCorr
#print axioms B62.partialCorr_one_with_small_residual
#print axioms B62.explicit_small_residual_witness
#print axioms B62.explicit_scatter_below_universal_floor
#print axioms B62.finite_sample_realisation
end


/-! ## B62 — an eight-galaxy countermodel to the unconditional 0.080 dex floor

Integrated from `.ultramath/smww885zp/m1/B62_empirical.lean`.
-/

section
/-!
# B62: an eight-galaxy synthetic extraction model

The two structural proxies use one and the same radius.  An independent RAR
residual is constructed with correlation `23/50 = 0.46` with compactness
after linear mass control.  All observations are in base-10 logarithmic units.
-/

namespace B62Empirical

noncomputable section

/-- Population mean of eight equally weighted galaxies. -/
def mean8 (x : Fin 8 → ℝ) : ℝ := (∑ i, x i) / 8

/-- Population covariance of eight equally weighted galaxies. -/
def cov8 (x y : Fin 8 → ℝ) : ℝ :=
  (∑ i, (x i - mean8 x) * (y i - mean8 y)) / 8

/-- Covariance left after linearly controlling for `m`. -/
def partialNum8 (m x y : Fin 8 → ℝ) : ℝ :=
  cov8 x y - cov8 x m * cov8 y m / cov8 m m

/-- Variance of `x` left after linearly controlling for `m`. -/
def residualVar8 (m x : Fin 8 → ℝ) : ℝ :=
  cov8 x x - cov8 x m ^ 2 / cov8 m m

/-- Partial correlation after ordinary linear mass control (with intercept). -/
def partialCorr8 (m x y : Fin 8 → ℝ) : ℝ :=
  partialNum8 m x y / Real.sqrt (residualVar8 m x * residualVar8 m y)

/-- Residual standard deviation after linear mass control. -/
def residualSD8 (m x : Fin 8 → ℝ) : ℝ := Real.sqrt (residualVar8 m x)

/-- The mass column is one of the nonconstant Hadamard columns. -/
def mass : Fin 8 → ℝ := ![1, -1, 1, -1, -1, 1, -1, 1]

/-- `5` times the alternating Hadamard column. -/
def sizePattern : Fin 8 → ℝ := ![5, -5, 5, -5, 5, -5, 5, -5]

/-- A centred residual pattern.  Its coefficients are chosen so that
`||sizePattern||² = 200`, `||rarPattern||² = 800`, and their dot product is
`184`; consequently their correlation is `184/400 = 23/50`. -/
def rarPattern : Fin 8 → ℝ :=
  ![78/5, 2, 54/5, 6, -8/5, -76/5, -32/5, -56/5]

/-- Log compactness, omitting only the fixed `log (G/c²)` offset. -/
def logCompact (ε : ℝ) : Fin 8 → ℝ := fun i => mass i + ε * sizePattern i

/-- Log surface density, using exactly the same log radius `-ε*sizePattern`
as compactness and omitting only the fixed `log π` offset. -/
def logSurface (ε : ℝ) : Fin 8 → ℝ := fun i => mass i + 2 * ε * sizePattern i

/-- A synthetic RAR residual; it is orthogonal to mass but not to size. -/
def rarResidual (ε : ℝ) : Fin 8 → ℝ := fun i => ε * rarPattern i

/-- The component of the RAR residual explained by mass-controlled compactness. -/
def structuralEffect (ε : ℝ) : Fin 8 → ℝ := fun i => (23/25) * ε * sizePattern i

/-- The orthogonal remainder in the synthetic residual model. -/
def remainingResidual (ε : ℝ) : Fin 8 → ℝ := fun i =>
  rarResidual ε i - structuralEffect ε i

lemma rar_eq_structural_add_remaining (ε : ℝ) :
    rarResidual ε = fun i => structuralEffect ε i + remainingResidual ε i := by
  funext i
  simp [rarResidual, structuralEffect, remainingResidual]

lemma cov_mass_mass : cov8 mass mass = 1 := by
  norm_num [cov8, mean8, mass, Fin.sum_univ_eight]

lemma cov_mass_compact (ε : ℝ) : cov8 mass (logCompact ε) = 1 := by
  norm_num [cov8, mean8, mass, logCompact, sizePattern, Fin.sum_univ_eight]
  ring

lemma cov_compact_compact (ε : ℝ) :
    cov8 (logCompact ε) (logCompact ε) = 1 + 25 * ε ^ 2 := by
  norm_num [cov8, mean8, mass, logCompact, sizePattern, Fin.sum_univ_eight]
  ring

lemma cov_mass_surface (ε : ℝ) : cov8 mass (logSurface ε) = 1 := by
  norm_num [cov8, mean8, mass, logSurface, sizePattern, Fin.sum_univ_eight]
  ring

lemma cov_surface_surface (ε : ℝ) :
    cov8 (logSurface ε) (logSurface ε) = 1 + 100 * ε ^ 2 := by
  norm_num [cov8, mean8, mass, logSurface, sizePattern, Fin.sum_univ_eight]
  ring

lemma cov_compact_surface (ε : ℝ) :
    cov8 (logCompact ε) (logSurface ε) = 1 + 50 * ε ^ 2 := by
  norm_num [cov8, mean8, mass, logCompact, logSurface, sizePattern,
    Fin.sum_univ_eight]
  ring

lemma cov_mass_rar (ε : ℝ) : cov8 mass (rarResidual ε) = 0 := by
  norm_num [cov8, mean8, mass, rarResidual, rarPattern, Fin.sum_univ_eight]
  ring

lemma cov_compact_rar (ε : ℝ) :
    cov8 (logCompact ε) (rarResidual ε) = 23 * ε ^ 2 := by
  norm_num [cov8, mean8, mass, logCompact, rarResidual, sizePattern, rarPattern,
    Fin.sum_univ_eight]
  ring

lemma cov_rar_rar (ε : ℝ) :
    cov8 (rarResidual ε) (rarResidual ε) = 100 * ε ^ 2 := by
  norm_num [cov8, mean8, rarResidual, rarPattern, Fin.sum_univ_eight]
  ring

lemma cov_comm (x y : Fin 8 → ℝ) : cov8 x y = cov8 y x := by
  unfold cov8
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring


lemma partial_compact_surface (ε : ℝ) :
    partialNum8 mass (logCompact ε) (logSurface ε) = 50 * ε ^ 2 := by
  unfold partialNum8
  rw [cov_comm (logCompact ε) mass, cov_comm (logSurface ε) mass,
    cov_compact_surface, cov_mass_compact, cov_mass_surface, cov_mass_mass]
  norm_num only [one_mul, div_one]
  ring

lemma residualVar_compact (ε : ℝ) :
    residualVar8 mass (logCompact ε) = 25 * ε ^ 2 := by
  unfold residualVar8
  rw [cov_comm (logCompact ε) mass, cov_compact_compact, cov_mass_compact,
    cov_mass_mass]
  norm_num only [one_pow, div_one]
  ring

lemma residualVar_surface (ε : ℝ) :
    residualVar8 mass (logSurface ε) = 100 * ε ^ 2 := by
  unfold residualVar8
  rw [cov_comm (logSurface ε) mass, cov_surface_surface, cov_mass_surface,
    cov_mass_mass]
  norm_num only [one_pow, div_one]
  ring

lemma residualVar_rar (ε : ℝ) :
    residualVar8 mass (rarResidual ε) = 100 * ε ^ 2 := by
  unfold residualVar8
  rw [cov_comm (rarResidual ε) mass, cov_rar_rar, cov_mass_rar, cov_mass_mass]
  norm_num

lemma partial_compact_rar (ε : ℝ) :
    partialNum8 mass (logCompact ε) (rarResidual ε) = 23 * ε ^ 2 := by
  unfold partialNum8
  rw [cov_comm (logCompact ε) mass, cov_comm (rarResidual ε) mass,
    cov_compact_rar, cov_mass_compact, cov_mass_rar, cov_mass_mass]
  norm_num only [mul_zero, zero_div, sub_zero]

/-- The two power-law proxies are perfectly correlated after mass control.
This is the exact algebraic kernel of the first clause. -/
theorem compact_surface_partialCorr (ε : ℝ) (hε : ε ≠ 0) :
    partialCorr8 mass (logCompact ε) (logSurface ε) = 1 := by
  rw [partialCorr8, partial_compact_surface, residualVar_compact,
    residualVar_surface]
  have hs : (25 * ε ^ 2) * (100 * ε ^ 2) = (50 * ε ^ 2) ^ 2 := by ring
  rw [hs, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 50 * ε ^ 2)]
  have hpos : (0 : ℝ) < 50 * ε ^ 2 := by
    have hsquare : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
    positivity
  exact div_self (ne_of_gt hpos)

/-- A separate RAR residual can have the card's localized correlation `0.46`
with compactness while the preceding proxy correlation remains exactly one. -/
theorem compact_rar_partialCorr (ε : ℝ) (hε : ε ≠ 0) :
    partialCorr8 mass (logCompact ε) (rarResidual ε) = 23/50 := by
  rw [partialCorr8, partial_compact_rar, residualVar_compact, residualVar_rar]
  have hs : (25 * ε ^ 2) * (100 * ε ^ 2) = (50 * ε ^ 2) ^ 2 := by ring
  rw [hs, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 50 * ε ^ 2)]
  field_simp [hε]

/-- The nonzero structural slope is visible in the finite covariance data at
every nonzero scale; there is no scale cutoff in the algebra. -/
theorem recovered_secondary_slope (ε : ℝ) (hε : ε ≠ 0) :
    partialNum8 mass (logCompact ε) (rarResidual ε) /
      residualVar8 mass (logCompact ε) = 23/25 := by
  rw [partial_compact_rar, residualVar_compact]
  field_simp [hε]

lemma residualSD_rar (ε : ℝ) (hε : 0 ≤ ε) :
    residualSD8 mass (rarResidual ε) = 10 * ε := by
  rw [residualSD8, residualVar_rar]
  have hs : 100 * ε ^ 2 = (10 * ε) ^ 2 := by ring
  rw [hs, Real.sqrt_sq (by positivity)]

theorem explicit_rar_scatter_below_floor :
    residualSD8 mass (rarResidual (1/1000)) = 1/100 ∧
      (1/100 : ℝ) < 8/100 := by
  rw [residualSD_rar (1/1000) (by norm_num)]
  norm_num

/-- The structural effect has amplitude `0.0046` at every galaxy in the small
synthetic example, below the unconditional `0.080` threshold stated on B62. -/
theorem structural_effect_below_floor_per_galaxy :
    ∀ i, |structuralEffect (1/1000) i| < 8/100 := by
  intro i
  fin_cases i <;> norm_num [structuralEffect, sizePattern, abs_of_nonneg,
    abs_of_nonpos]

/-- The structural slope is nonzero and the fitted correlation is not merely
"approximately one". -/
theorem explicit_secondary_signal :
    partialNum8 mass (logCompact (1/1000)) (rarResidual (1/1000)) /
        residualVar8 mass (logCompact (1/1000)) = 23/25 ∧
      partialCorr8 mass (logCompact (1/1000)) (rarResidual (1/1000)) = 23/50 ∧
      (23/25 : ℝ) ≠ 0 := by
  exact ⟨recovered_secondary_slope (1/1000) (by norm_num),
    compact_rar_partialCorr (1/1000) (by norm_num), by norm_num⟩


lemma cov_structural_remaining (ε : ℝ) :
    cov8 (structuralEffect ε) (remainingResidual ε) = 0 := by
  norm_num [cov8, mean8, structuralEffect, remainingResidual, rarResidual,
    sizePattern, rarPattern, Fin.sum_univ_eight]
  ring

/-- Base-10 exponentiation gives positive synthetic galaxy observables. -/
def dex (x : ℝ) : ℝ := (10 : ℝ) ^ x

lemma dex_pos (x : ℝ) : 0 < dex x := Real.rpow_pos_of_pos (by norm_num) x

lemma logb_dex (x : ℝ) : Real.logb 10 (dex x) = x := by
  unfold dex
  rw [Real.logb_rpow] <;> norm_num

lemma dex_div (a b : ℝ) : dex a / dex b = dex (a-b) :=
  (Real.rpow_sub (by norm_num) a b).symm

lemma dex_sq (a : ℝ) : (dex a) ^ 2 = dex (2*a) := by
  unfold dex
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
  congr 1
  ring

/-- Positive baryonic masses. -/
def galaxyMass (i : Fin 8) : ℝ := dex (mass i)

/-- The one common effective radius used by both proxies. -/
def galaxyRadius (ε : ℝ) (i : Fin 8) : ℝ := dex (-(ε * sizePattern i))

/-- Compactness up to its fixed physical prefactor `G/c²`. -/
def compactProxy (ε : ℝ) (i : Fin 8) : ℝ := galaxyMass i / galaxyRadius ε i

/-- Baryonic surface density up to its fixed geometric prefactor `1/π`. -/
def surfaceProxy (ε : ℝ) (i : Fin 8) : ℝ := galaxyMass i / (galaxyRadius ε i)^2

theorem galaxyMass_pos (i : Fin 8) : 0 < galaxyMass i := dex_pos _

theorem galaxyRadius_pos (ε : ℝ) (i : Fin 8) : 0 < galaxyRadius ε i := dex_pos _

/-- The formal compactness data really are `log10 (M/R)`. -/
theorem logb_compactProxy (ε : ℝ) (i : Fin 8) :
    Real.logb 10 (compactProxy ε i) = logCompact ε i := by
  unfold compactProxy galaxyMass galaxyRadius
  rw [dex_div, logb_dex]
  unfold logCompact
  ring

/-- The formal surface-density data really are `log10 (M/R²)`, with the same
mass and radius as in the preceding theorem. -/
theorem logb_surfaceProxy (ε : ℝ) (i : Fin 8) :
    Real.logb 10 (surfaceProxy ε i) = logSurface ε i := by
  unfold surfaceProxy galaxyMass galaxyRadius
  rw [dex_sq, dex_div, logb_dex]
  unfold logSurface
  ring

theorem structural_effect_nonzero (ε : ℝ) (hε : ε ≠ 0) (i : Fin 8) :
    structuralEffect ε i ≠ 0 := by
  fin_cases i <;> norm_num [structuralEffect, sizePattern, hε]

theorem rar_residual_below_floor_per_galaxy :
    ∀ i, |rarResidual (1/1000) i| < 8/100 := by
  intro i
  fin_cases i <;> norm_num [rarResidual, rarPattern, abs_of_nonneg,
    abs_of_nonpos]

/-- Complete finite witness against an unconditional algebraic `0.080 dex`
floor: actual common-radius power-law proxies, exact unit proxy partial
correlation, a nonzero small structural component, and exact `r = 0.46`. -/
theorem unconditional_floor_countermodel :
    (∀ i, 0 < galaxyMass i) ∧
    (∀ i, 0 < galaxyRadius (1/1000) i) ∧
    (∀ i, Real.logb 10 (compactProxy (1/1000) i) = logCompact (1/1000) i) ∧
    (∀ i, Real.logb 10 (surfaceProxy (1/1000) i) = logSurface (1/1000) i) ∧
    partialCorr8 mass (logCompact (1/1000)) (logSurface (1/1000)) = 1 ∧
    partialCorr8 mass (logCompact (1/1000)) (rarResidual (1/1000)) = 23/50 ∧
    (∀ i, structuralEffect (1/1000) i ≠ 0) ∧
    (∀ i, |structuralEffect (1/1000) i| < 8/100) := by
  exact ⟨galaxyMass_pos, galaxyRadius_pos (1/1000),
    logb_compactProxy (1/1000), logb_surfaceProxy (1/1000),
    compact_surface_partialCorr (1/1000) (by norm_num),
    compact_rar_partialCorr (1/1000) (by norm_num),
    structural_effect_nonzero (1/1000) (by norm_num),
    structural_effect_below_floor_per_galaxy⟩


end
end B62Empirical

#print axioms B62Empirical.rar_eq_structural_add_remaining
#print axioms B62Empirical.cov_mass_mass
#print axioms B62Empirical.cov_mass_compact
#print axioms B62Empirical.cov_compact_compact
#print axioms B62Empirical.cov_mass_surface
#print axioms B62Empirical.cov_surface_surface
#print axioms B62Empirical.cov_compact_surface
#print axioms B62Empirical.cov_mass_rar
#print axioms B62Empirical.cov_compact_rar
#print axioms B62Empirical.cov_rar_rar
#print axioms B62Empirical.cov_comm
#print axioms B62Empirical.partial_compact_surface
#print axioms B62Empirical.residualVar_compact
#print axioms B62Empirical.residualVar_surface
#print axioms B62Empirical.residualVar_rar
#print axioms B62Empirical.partial_compact_rar
#print axioms B62Empirical.compact_surface_partialCorr
#print axioms B62Empirical.compact_rar_partialCorr
#print axioms B62Empirical.recovered_secondary_slope
#print axioms B62Empirical.residualSD_rar
#print axioms B62Empirical.explicit_rar_scatter_below_floor
#print axioms B62Empirical.structural_effect_below_floor_per_galaxy
#print axioms B62Empirical.explicit_secondary_signal
#print axioms B62Empirical.cov_structural_remaining
#print axioms B62Empirical.dex_pos
#print axioms B62Empirical.logb_dex
#print axioms B62Empirical.dex_div
#print axioms B62Empirical.dex_sq
#print axioms B62Empirical.galaxyMass_pos
#print axioms B62Empirical.galaxyRadius_pos
#print axioms B62Empirical.logb_compactProxy
#print axioms B62Empirical.logb_surfaceProxy
#print axioms B62Empirical.structural_effect_nonzero
#print axioms B62Empirical.rar_residual_below_floor_per_galaxy
#print axioms B62Empirical.unconditional_floor_countermodel
end


/-! ## B76 — the five-charge critical-point count

Integrated from `.ultramath/smww885zp/m12/B76.lean`.
-/

section
/-!
# B76: the exact algebraic kernel of the 21-point unfolding

The card's five-charge construction has the blow-up potential
`Phi0 = (5/32) H2 + (15/8) H3 + (3/16) H4`.
This file certifies the real algebraic branches of its critical-point
calculation and the nonvanishing of the Hessian determinant on the
nonzero-radius branches. No numerical approximation is used.
-/

open Real

namespace B76

noncomputable section

def H2 (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 - 2 * z ^ 2
def H3 (x y z : ℝ) : ℝ := x ^ 3 - 3 * x * y ^ 2
def H4 (x y z : ℝ) : ℝ :=
  3 * (x ^ 2 + y ^ 2) ^ 2 - 24 * (x ^ 2 + y ^ 2) * z ^ 2 + 8 * z ^ 4

def Phi0 (x y z : ℝ) : ℝ :=
  (5 / 32) * H2 x y z + (15 / 8) * H3 x y z + (3 / 16) * H4 x y z

/-- The blow-up potential in cylindrical coordinates, where `c` will be
`cos (3 * theta)`. -/
def Phi0r (r z c : ℝ) : ℝ :=
  (1 / 32) * (18 * r ^ 4 + 60 * r ^ 3 * c - 144 * r ^ 2 * z ^ 2 +
    5 * r ^ 2 + 48 * z ^ 4 - 10 * z ^ 2)

lemma cylindrical_radius_sq (r θ : ℝ) :
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
  calc
    (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

lemma cylindrical_cubic (r θ z : ℝ) :
    H3 (r * Real.cos θ) (r * Real.sin θ) z = r ^ 3 * Real.cos (3 * θ) := by
  simp only [H3]
  rw [Real.cos_three_mul]
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    (r * Real.cos θ) ^ 3 -
          3 * (r * Real.cos θ) * (r * Real.sin θ) ^ 2 =
        r ^ 3 * (Real.cos θ ^ 3 - 3 * Real.cos θ * Real.sin θ ^ 2) := by ring
    _ = r ^ 3 * (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) := by rw [hs]; ring

/-- Exact passage from the displayed Cartesian polynomial to its
cylindrical form. -/
theorem Phi0_polar (r θ z : ℝ) :
    Phi0 (r * Real.cos θ) (r * Real.sin θ) z = Phi0r r z (Real.cos (3 * θ)) := by
  simp only [Phi0, Phi0r, H2, H4, cylindrical_radius_sq, cylindrical_cubic]
  ring

open Polynomial

/-- `Phi0r` as a polynomial in the radial coordinate. -/
def radialPoly (z c : ℝ) : ℝ[X] :=
  C (18 / 32) * X ^ 4 + C ((60 * c) / 32) * X ^ 3 +
    C ((-144 * z ^ 2 + 5) / 32) * X ^ 2 + C ((48 * z ^ 4 - 10 * z ^ 2) / 32)

lemma radialPoly_eval (r z c : ℝ) : (radialPoly z c).eval r = Phi0r r z c := by
  simp [radialPoly, Phi0r]
  ring

/-- The displayed radial equation is the actual partial derivative. -/
theorem hasDerivAt_Phi0r_radial (r z c : ℝ) :
    HasDerivAt (fun t => Phi0r t z c)
      (r / 16 * (36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5)) r := by
  have h := (radialPoly z c).hasDerivAt r
  have he : (radialPoly z c).derivative.eval r =
      r / 16 * (36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5) := by
    simp [radialPoly, derivative_add, derivative_mul, derivative_C]
    ring
  have hf : (fun t => Phi0r t z c) = (fun t => (radialPoly z c).eval t) := by
    funext t
    exact (radialPoly_eval t z c).symm
  rw [hf]
  rwa [he] at h

theorem deriv_Phi0r_radial (r z c : ℝ) :
    deriv (fun t => Phi0r t z c) r =
      r / 16 * (36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5) :=
  (hasDerivAt_Phi0r_radial r z c).deriv

/-- `Phi0r` as a polynomial in the axial coordinate. -/
def axialPoly (r c : ℝ) : ℝ[X] :=
  C (48 / 32) * X ^ 4 + C ((-144 * r ^ 2 - 10) / 32) * X ^ 2 +
    C ((18 * r ^ 4 + 60 * r ^ 3 * c + 5 * r ^ 2) / 32)

lemma axialPoly_eval (r z c : ℝ) : (axialPoly r c).eval z = Phi0r r z c := by
  simp [axialPoly, Phi0r]
  ring

/-- The displayed axial equation is the actual partial derivative. -/
theorem hasDerivAt_Phi0r_axial (r z c : ℝ) :
    HasDerivAt (fun t => Phi0r r t c)
      (z / 8 * (48 * z ^ 2 - 72 * r ^ 2 - 5)) z := by
  have h := (axialPoly r c).hasDerivAt z
  have he : (axialPoly r c).derivative.eval z =
      z / 8 * (48 * z ^ 2 - 72 * r ^ 2 - 5) := by
    simp [axialPoly, derivative_add, derivative_mul, derivative_C]
    ring
  have hf : (fun t => Phi0r r t c) = (fun t => (axialPoly r c).eval t) := by
    funext t
    exact (axialPoly_eval r t c).symm
  rw [hf]
  rwa [he] at h

theorem deriv_Phi0r_axial (r z c : ℝ) :
    deriv (fun t => Phi0r r t c) z =
      z / 8 * (48 * z ^ 2 - 72 * r ^ 2 - 5) :=
  (hasDerivAt_Phi0r_axial r z c).deriv

/-- The angular equation follows by the chain rule from
`r^3 cos (3 * theta)`. -/
theorem hasDerivAt_Phi0r_angular (r θ z : ℝ) :
    HasDerivAt (fun t => Phi0r r z (Real.cos (3 * t)))
      (-(45 * r ^ 3 / 8) * Real.sin (3 * θ)) θ := by
  have ht : HasDerivAt (fun t : ℝ => 3 * t) 3 θ := by
    simpa using (hasDerivAt_id θ).const_mul (3 : ℝ)
  have hc : HasDerivAt (fun t : ℝ => Real.cos (3 * t))
      (-Real.sin (3 * θ) * 3) θ := ht.cos
  have hf : (fun t => Phi0r r z (Real.cos (3 * t))) =
      (fun t => (60 * r ^ 3 / 32) * Real.cos (3 * t) +
        (1 / 32) * (18 * r ^ 4 - 144 * r ^ 2 * z ^ 2 + 5 * r ^ 2 +
          48 * z ^ 4 - 10 * z ^ 2)) := by
    funext t
    simp only [Phi0r]
    ring
  rw [hf]
  convert (hc.const_mul (60 * r ^ 3 / 32)).add_const
    ((1 / 32) * (18 * r ^ 4 - 144 * r ^ 2 * z ^ 2 + 5 * r ^ 2 +
      48 * z ^ 4 - 10 * z ^ 2)) using 1 <;> ring

theorem deriv_Phi0r_angular (r θ z : ℝ) :
    deriv (fun t => Phi0r r z (Real.cos (3 * t))) θ =
      -(45 * r ^ 3 / 8) * Real.sin (3 * θ) :=
  (hasDerivAt_Phi0r_angular r θ z).deriv

/-- At a non-axial critical point the angular equation makes
`cos (3 * theta)` equal to one of these two signs. -/
theorem angular_signs {θ : ℝ} (hθ : Real.sin (3 * θ) = 0) :
    Real.cos (3 * θ) = 1 ∨ Real.cos (3 * θ) = -1 := by
  have h := Real.sin_sq_add_cos_sq (3 * θ)
  rw [hθ] at h
  exact sq_eq_one_iff.mp (by nlinarith)

/-- The two equations after removing the nonzero radial and axial
factors. Their real branches are exactly those below. -/
theorem nonzero_radius_branches {r z c : ℝ} (hr : 0 < r)
    (hc : c = 1 ∨ c = -1)
    (hrad : r * (36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5) = 0)
    (hz : z * (48 * z ^ 2 - 72 * r ^ 2 - 5) = 0) :
    (c = 1 ∧
      ((r = 1 / 3 ∧ z ^ 2 = 13 / 48) ∨ (r = 1 / 6 ∧ z ^ 2 = 7 / 48))) ∨
    (c = -1 ∧ z = 0 ∧
      (r = (15 + Real.sqrt 205) / 12 ∨ r = (15 - Real.sqrt 205) / 12)) := by
  have hA : 36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5 = 0 :=
    (mul_eq_zero.mp hrad).resolve_left (ne_of_gt hr)
  have hs : (Real.sqrt 205) ^ 2 = 205 := Real.sq_sqrt (by norm_num)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hz with hz0 | hB
  · subst z
    rcases hc with rfl | rfl
    · exfalso
      nlinarith [sq_nonneg r]
    · right
      refine ⟨rfl, rfl, ?_⟩
      have hprod : (r - (15 + Real.sqrt 205) / 12) *
          (r - (15 - Real.sqrt 205) / 12) = 0 := by
        nlinarith [hA, hs]
      rcases mul_eq_zero.mp hprod with hp | hm
      · left
        linarith
      · right
        linarith
  · have hcubic : 18 * r ^ 2 - 9 * r * c + 1 = 0 := by
      nlinarith [hA, hB]
    rcases hc with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hprod : (3 * r - 1) * (6 * r - 1) = 0 := by
        nlinarith [hcubic]
      rcases mul_eq_zero.mp hprod with h3 | h6
      · left
        constructor
        · linarith
        · nlinarith [hB, h3]
      · right
        constructor
        · linarith
        · nlinarith [hB, h6]
    · exfalso
      nlinarith [sq_nonneg r]

/-- Derivative-zero form of the complete nonzero-radius classification.
For `r > 0`, these three equations are equivalent to vanishing of the
Cartesian gradient in cylindrical coordinates. -/
theorem nonzero_radius_critical_branches {r θ z : ℝ} (hr : 0 < r)
    (hrad : deriv (fun t => Phi0r t z (Real.cos (3 * θ))) r = 0)
    (hang : deriv (fun t => Phi0r r z (Real.cos (3 * t))) θ = 0)
    (hz : deriv (fun t => Phi0r r t (Real.cos (3 * θ))) z = 0) :
    (Real.cos (3 * θ) = 1 ∧
      ((r = 1 / 3 ∧ z ^ 2 = 13 / 48) ∨ (r = 1 / 6 ∧ z ^ 2 = 7 / 48))) ∨
    (Real.cos (3 * θ) = -1 ∧ z = 0 ∧
      (r = (15 + Real.sqrt 205) / 12 ∨ r = (15 - Real.sqrt 205) / 12)) := by
  rw [deriv_Phi0r_radial] at hrad
  rw [deriv_Phi0r_angular] at hang
  rw [deriv_Phi0r_axial] at hz
  have hsin : Real.sin (3 * θ) = 0 := by
    have hcoef : -(45 * r ^ 3 / 8) ≠ 0 :=
      neg_ne_zero.mpr (ne_of_gt (by positivity : 0 < 45 * r ^ 3 / 8))
    exact (mul_eq_zero.mp hang).resolve_left hcoef
  apply nonzero_radius_branches hr (angular_signs hsin)
  · nlinarith [hrad]
  · nlinarith [hz]

/-- The `r = 0` radial coordinate collapses to three physical points:
the origin and two axial points. -/
theorem zero_radius_branches {z : ℝ}
    (hz : z * (48 * z ^ 2 - 5) = 0) :
    z = 0 ∨ z ^ 2 = 5 / 48 := by
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hz with h | h
  · exact Or.inl h
  · exact Or.inr (by nlinarith)

/-- The angular Hessian eigenvalue at a nondegenerate angular branch. -/
def angularCurv (r c : ℝ) : ℝ := -(135 / 8) * r * c

/-- Radial second derivative at a nonzero-radius critical point. -/
def radialCurv (r c : ℝ) : ℝ := (r / 16) * (72 * r + 90 * c)

def mixedCurv (r z : ℝ) : ℝ := -18 * r * z

def axialCurv (r z : ℝ) : ℝ := 18 * z ^ 2 - 9 * r ^ 2 - 5 / 8

/-- The cylindrical Hessian determinant is nonzero on every branch with
`r > 0`. Together with the angular multiplicities (three for `c = 1`
and three for `c = -1`) this accounts for the 6 planar and 12 off-planar
points. -/
theorem hessian_det_ne_zero_of_pos_radius {r z c : ℝ} (hr : 0 < r)
    (hc : c = 1 ∨ c = -1)
    (hrad : r * (36 * r ^ 2 + 90 * r * c - 144 * z ^ 2 + 5) = 0)
    (hz : z * (48 * z ^ 2 - 72 * r ^ 2 - 5) = 0) :
    angularCurv r c *
      (radialCurv r c * axialCurv r z - mixedCurv r z ^ 2) ≠ 0 := by
  have hang : angularCurv r c ≠ 0 := by
    rcases hc with rfl | rfl <;> simp [angularCurv, ne_of_gt hr]
  apply mul_ne_zero hang
  have hbranches := nonzero_radius_branches hr hc hrad hz
  have hs : 0 < Real.sqrt 205 := Real.sqrt_pos.2 (by norm_num)
  rcases hbranches with hoff | hplanar
  · rcases hoff with ⟨rfl, hro | hro⟩
    · rcases hro with ⟨hr3, hz13⟩
      have hdet : radialCurv r 1 * axialCurv r z - mixedCurv r z ^ 2 < 0 := by
        simp only [radialCurv, axialCurv, mixedCurv]
        rw [hr3]
        nlinarith [hz13]
      exact ne_of_lt hdet
    · rcases hro with ⟨hr6, hz7⟩
      have hdet : 0 < radialCurv r 1 * axialCurv r z - mixedCurv r z ^ 2 := by
        simp only [radialCurv, axialCurv, mixedCurv]
        rw [hr6]
        nlinarith [hz7]
      exact ne_of_gt hdet
  · rcases hplanar with ⟨hcneg, rfl, hrout | hrin⟩
    · subst c
      have hroutpos : 0 < (15 + Real.sqrt 205) / 12 := by positivity
      have hR : 0 < radialCurv r (-1) := by
        rw [hrout]
        simp only [radialCurv]
        apply mul_pos
        · positivity
        · nlinarith
      have hZ : axialCurv r 0 < 0 := by
        simp only [axialCurv]
        nlinarith [sq_nonneg r]
      have hdet : radialCurv r (-1) * axialCurv r 0 - mixedCurv r 0 ^ 2 < 0 := by
        simpa [mixedCurv] using mul_neg_of_pos_of_neg hR hZ
      exact ne_of_lt hdet
    · subst c
      have hrinpos : 0 < (15 - Real.sqrt 205) / 12 := by
        rw [← hrin]
        exact hr
      have hR : radialCurv r (-1) < 0 := by
        rw [hrin]
        simp only [radialCurv]
        apply mul_neg_of_pos_of_neg
        · positivity
        · nlinarith
      have hZ : axialCurv r 0 < 0 := by
        simp only [axialCurv]
        nlinarith [sq_nonneg r]
      have hdet : 0 < radialCurv r (-1) * axialCurv r 0 - mixedCurv r 0 ^ 2 := by
        have h := mul_pos_of_neg_of_neg hR hZ
        simpa [mixedCurv] using h
      exact ne_of_gt hdet

/-- The two collapsed radial cases have these nonzero Hessian
eigenvalue products, respectively at the origin and on the axis. -/
theorem origin_hessian_det_ne_zero :
    (5 / 16 : ℝ) * (5 / 16) * (-5 / 8) ≠ 0 := by norm_num

theorem axis_hessian_det_ne_zero :
    (-5 / 8 : ℝ) * (-5 / 8) * (5 / 4) ≠ 0 := by norm_num

/-- Cardinality of the exact local enumeration: origin, two axial,
three angular copies of each of two planar radii, and three angular
copies of each of two radii with two axial signs. -/
theorem local_point_count : 1 + 2 + 3 * 2 + 3 * 2 * 2 = 21 := by norm_num

#print axioms cylindrical_radius_sq
#print axioms cylindrical_cubic
#print axioms Phi0_polar
#print axioms radialPoly_eval
#print axioms hasDerivAt_Phi0r_radial
#print axioms deriv_Phi0r_radial
#print axioms axialPoly_eval
#print axioms hasDerivAt_Phi0r_axial
#print axioms deriv_Phi0r_axial
#print axioms hasDerivAt_Phi0r_angular
#print axioms deriv_Phi0r_angular
#print axioms angular_signs
#print axioms nonzero_radius_branches
#print axioms nonzero_radius_critical_branches
#print axioms zero_radius_branches
#print axioms hessian_det_ne_zero_of_pos_radius
#print axioms origin_hessian_det_ne_zero
#print axioms axis_hessian_det_ne_zero
#print axioms local_point_count

end
end B76
end


/-! ## B76 — the centre is nondegenerate at the stated q_eps

Integrated from `.ultramath/smww885zp/m6/B76Global.lean`.
-/

section
/-!
# B76: exact finite arithmetic for the source's displayed numerical example

This file deliberately proves only exact rational facts.  The companion root search
is numerical and is not used as a formal existence or exhaustiveness certificate.
-/

namespace B76Global

/-- The perturbation size used in the numerical example in the primary source. -/
def eps : ℚ := 1 / 6

/-- The two equal axial charges in the Arathoon--Ball--Kvalheim construction. -/
def axialCharge (e : ℚ) : ℚ := (3 / 4) * e ^ 3 - (5 / 32) * e ^ 5

/-- At `ε = 1/6`, the common axial charge is exactly `859/248832`. -/
theorem axialCharge_eps : axialCharge eps = 859 / 248832 := by
  norm_num [axialCharge, eps]

/-- In particular, both added charges are strictly positive in that example. -/
theorem axialCharge_eps_pos : 0 < axialCharge eps := by
  rw [axialCharge_eps]
  norm_num

/-- The displayed Maxwell-bound arithmetic is correct at five sources. -/
theorem maxwell_arithmetic : (24 : ℕ) > (5 - 1) ^ 2 := by
  norm_num

/-- The central-family census and the addition of the three persistent edge points. -/
theorem central_and_total_census :
    1 + 2 + 6 + 12 = 21 ∧ 3 + (1 + 2 + 6 + 12) = 24 := by
  norm_num

end B76Global

#print axioms B76Global.axialCharge_eps
#print axioms B76Global.axialCharge_eps_pos
#print axioms B76Global.maxwell_arithmetic
#print axioms B76Global.central_and_total_census
end


/-! ## B125 — the trace-log expansion coefficient

Integrated from `.ultramath/smww885zp/m8/B125.lean`.
-/

section
open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace B125

/-- The error after the degree-two Taylor polynomial of `-log (1 - c*x)` is cubic. -/
lemma negLog_one_sub_sub_taylor_isBigO (c : ℝ) :
    (fun x : ℝ => -Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (2 * |c| ^ 3)
  have hcont : ContinuousAt (fun x : ℝ => |x * c|) 0 := by fun_prop
  have ht : Tendsto (fun x : ℝ => |x * c|) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto
  have hev : ∀ᶠ x : ℝ in 𝓝 0, |x * c| < (1 / 2 : ℝ) :=
    ht.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hev] with x hx
  have hx1 : |x * c| < (1 : ℝ) := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 2
  norm_num [Finset.sum_range_succ] at h
  have hden : (1 / 2 : ℝ) ≤ 1 - |x * c| := by linarith
  have hdenpos : (0 : ℝ) < 1 - |x * c| := by linarith
  have hcube : (0 : ℝ) ≤ |x * c| ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden hcube
  simp only [Real.norm_eq_abs]
  calc
    |-Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2| =
        |-( -Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2)| :=
      (abs_neg _).symm
    _ = |(x * c) + (x * c) ^ 2 / 2 + Real.log (1 - x * c)| := by
      congr 1
      ring
    _ ≤ |x * c| ^ 3 / (1 - |x * c|) := by
      simpa [mul_comm] using h
    _ ≤ 2 * |x * c| ^ 3 := by
      apply (div_le_iff₀ hdenpos).2
      nlinarith
    _ = 2 * |c| ^ 3 * |x ^ 3| := by
      simp only [abs_mul, abs_pow]
      ring

/-- Finite diagonal model of the trace-log on form space. -/
def traceLog {n : ℕ} (d : Fin n → ℝ) (x : ℝ) : ℝ :=
  -∑ i, Real.log (1 - x * d i)

/-- Summing the scalar remainder gives the trace-log Taylor expansion. -/
lemma traceLog_sub_taylor_isBigO {n : ℕ} (d : Fin n → ℝ) :
    (fun x : ℝ => traceLog d x - x * (∑ i, d i) -
      x ^ 2 / 2 * (∑ i, d i ^ 2)) =O[𝓝 0] (fun x : ℝ => x ^ 3) := by
  have h0 : (∑ i : Fin n, fun x : ℝ =>
      (-Real.log (1 - x * d i) - x * d i - (x * d i) ^ 2 / 2)) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) :=
    Asymptotics.IsBigO.sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => negLog_one_sub_sub_taylor_isBigO (d i))
  have h : (fun x : ℝ => ∑ i : Fin n,
      (-Real.log (1 - x * d i) - x * d i - (x * d i) ^ 2 / 2)) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
    apply h0.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
    simp
  apply h.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
  simp only [traceLog, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, mul_pow]
  have hquad : (∑ i, x ^ 2 * d i ^ 2 / 2) = x ^ 2 / 2 * (∑ i, d i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hquad]

/-- Spectrum of `R ⊕ Ric ⊕ Riem` for the unit round four-sphere, on
`Λ⁰ ⊕ Λ¹ ⊕ Λ²`, of dimensions `1 + 4 + 6 = 11`. -/
def sphereSpectrum : Fin 11 → ℝ :=
  ![12, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2]

lemma sphereSpectrum_sum : (∑ i, sphereSpectrum i) = 36 := by
  norm_num [sphereSpectrum, Fin.sum_univ_succ]

lemma sphereSpectrum_sq_sum : (∑ i, sphereSpectrum i ^ 2) = 204 := by
  norm_num [sphereSpectrum, Fin.sum_univ_succ]

/-- The displayed coefficients on the unit round four-sphere: `R = 12`,
`Ric² = 36`, and `Riem² = 24`. -/
lemma sphere_traceLog_coefficients :
    (∑ i, sphereSpectrum i) = 3 * 12 ∧
    (∑ i, sphereSpectrum i ^ 2) = 12 ^ 2 + 36 + 24 := by
  rw [sphereSpectrum_sum, sphereSpectrum_sq_sum]
  norm_num

/-- The unit round four-sphere satisfies the card's displayed expansion. -/
theorem sphere_traceLog_expansion :
    (fun x : ℝ => traceLog sphereSpectrum x -
      (3 * x * 12 + x ^ 2 / 2 * (12 ^ 2 + 36 + 24))) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  have h := traceLog_sub_taylor_isBigO sphereSpectrum
  rw [sphereSpectrum_sum, sphereSpectrum_sq_sum] at h
  apply h.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
  ring

/-- The card's normalized constant-curvature spectrum, with scalar parameter `R`. -/
def constantCurvatureSpectrum (R : ℝ) : Fin 11 → ℝ :=
  ![R, R / 4, R / 4, R / 4, R / 4, R / 6, R / 6, R / 6, R / 6, R / 6, R / 6]

lemma constantCurvatureSpectrum_sum (R : ℝ) :
    (∑ i, constantCurvatureSpectrum R i) = 3 * R := by
  norm_num [constantCurvatureSpectrum, Fin.sum_univ_succ] <;> ring

lemma constantCurvatureSpectrum_sq_sum (R : ℝ) :
    (∑ i, constantCurvatureSpectrum R i ^ 2) = 17 / 12 * R ^ 2 := by
  norm_num [constantCurvatureSpectrum, Fin.sum_univ_succ] <;> ring

lemma traceLog_constantCurvature (R x : ℝ) :
    traceLog (constantCurvatureSpectrum R) x =
      -Real.log (1 - x * R) - 4 * Real.log (1 - x * (R / 4)) -
        6 * Real.log (1 - x * (R / 6)) := by
  simp [traceLog, constantCurvatureSpectrum, Fin.sum_univ_succ]
  ring

/-- The card's full constant-curvature witness, for arbitrary `R`. -/
theorem constantCurvature_traceLog_expansion (R : ℝ) :
    (fun x : ℝ => traceLog (constantCurvatureSpectrum R) x -
      (3 * x * R + x ^ 2 / 2 * (R ^ 2 + R ^ 2 / 4 + R ^ 2 / 6))) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  have h := traceLog_sub_taylor_isBigO (constantCurvatureSpectrum R)
  rw [constantCurvatureSpectrum_sum, constantCurvatureSpectrum_sq_sum] at h
  apply h.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
  ring

/-- With the card's value of `β` and `ℓP² = G`, the scalar-curvature
coefficient in `-ℓP⁻⁴ Tr log (I - βR)` is `1 / (16πG)`. -/
theorem einstein_coefficient (ellP G : ℝ) (hG : G = ellP ^ 2) (hellP : ellP ≠ 0) :
    ellP ^ (-4 : ℤ) * (3 * (ellP ^ 2 / (48 * Real.pi))) =
      1 / (16 * Real.pi * G) := by
  rw [hG]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hp2 : ellP ^ 2 ≠ 0 := pow_ne_zero 2 hellP
  rw [zpow_neg]
  field_simp
  ring

end B125

#print axioms B125.negLog_one_sub_sub_taylor_isBigO
#print axioms B125.traceLog_sub_taylor_isBigO
#print axioms B125.sphereSpectrum_sum
#print axioms B125.sphereSpectrum_sq_sum
#print axioms B125.sphere_traceLog_coefficients
#print axioms B125.sphere_traceLog_expansion
#print axioms B125.constantCurvatureSpectrum_sum
#print axioms B125.constantCurvatureSpectrum_sq_sum
#print axioms B125.traceLog_constantCurvature
#print axioms B125.constantCurvature_traceLog_expansion
#print axioms B125.einstein_coefficient
end
end


/-! ## B125 — the 11-dimensional form-space spectrum: Tr = 3R

Integrated from `.ultramath/smww885zp/m13/B125Kernel.lean`.
-/

section
open scoped BigOperators Topology
open Filter Asymptotics

noncomputable section

namespace B125Kernel

/-- The eleven form-sector eigenvalues on the unit round four-sphere,
in the full-contraction normalisation used explicitly by card B125. -/
def sphereSpectrum : Fin 11 → ℝ :=
  ![12, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2]

lemma sphereSpectrum_sum : (∑ i, sphereSpectrum i) = 36 := by
  norm_num [sphereSpectrum, Fin.sum_univ_succ]

lemma sphereSpectrum_sq_sum : (∑ i, sphereSpectrum i ^ 2) = 204 := by
  norm_num [sphereSpectrum, Fin.sum_univ_succ]

/-- The card's first two displayed trace coefficients hold for this witness:
`36 = 3 * 12` and `204 = 12² + 36 + 24`. -/
theorem sphere_matches_display :
    (∑ i, sphereSpectrum i) = 3 * 12 ∧
    (∑ i, sphereSpectrum i ^ 2) = 12 ^ 2 + 36 + 24 := by
  rw [sphereSpectrum_sum, sphereSpectrum_sq_sum]
  norm_num

def delta (i j : Fin 4) : ℝ := if i = j then 1 else 0

/-- Unit constant-curvature Riemann tensor in an orthonormal frame. -/
def ccRiem (i j k l : Fin 4) : ℝ :=
  delta i k * delta j l - delta i l * delta j k

def ccRic (j l : Fin 4) : ℝ := ∑ i, ccRiem i j i l

def ccScalar : ℝ := ∑ j, ccRic j j

lemma ccRic_value (j l : Fin 4) : ccRic j l = 3 * delta j l := by
  fin_cases j <;> fin_cases l <;>
    norm_num [ccRic, ccRiem, delta, Fin.sum_univ_succ]

lemma ccScalar_value : ccScalar = 12 := by
  norm_num [ccScalar, ccRic, ccRiem, delta, Fin.sum_univ_succ]

lemma ccRic_squared_trace : (∑ j, ∑ l, ccRic j l * ccRic l j) = 36 := by
  norm_num [ccRic, ccRiem, delta, Fin.sum_univ_succ]

lemma ccRiem_squared_norm :
    (∑ i, ∑ j, ∑ k, ∑ l, (ccRiem i j k l) ^ 2) = 24 := by
  norm_num [ccRiem, delta, Fin.sum_univ_succ]

def formPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![((0 : Fin 4), (1 : Fin 4)),
    ((0 : Fin 4), (2 : Fin 4)),
    ((0 : Fin 4), (3 : Fin 4)),
    ((1 : Fin 4), (2 : Fin 4)),
    ((1 : Fin 4), (3 : Fin 4)),
    ((2 : Fin 4), (3 : Fin 4))]

/-- Full-contraction Riemann endomorphism on ordered-pair coordinates for Λ². -/
def ccFormOp (p q : Fin 6) : ℝ :=
  2 * ccRiem (formPairs p).1 (formPairs p).2 (formPairs q).1 (formPairs q).2

lemma ccFormOp_value (p q : Fin 6) : ccFormOp p q = if p = q then 2 else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [ccFormOp, formPairs, ccRiem, delta]

lemma ccFormOp_trace : (∑ p, ccFormOp p p) = 12 := by
  norm_num [ccFormOp, formPairs, ccRiem, delta, Fin.sum_univ_succ]

lemma ccFormOp_squared_trace : (∑ p, ∑ q, ccFormOp p q * ccFormOp q p) = 24 := by
  norm_num [ccFormOp, formPairs, ccRiem, delta, Fin.sum_univ_succ]

lemma cc_total_trace : ccScalar + (∑ j, ccRic j j) + (∑ p, ccFormOp p p) = 36 := by
  rw [ccScalar_value, ccFormOp_trace]
  norm_num [ccRic, ccRiem, delta, Fin.sum_univ_succ]

lemma cc_total_squared_trace :
    ccScalar ^ 2 + (∑ j, ∑ l, ccRic j l * ccRic l j) +
      (∑ p, ∑ q, ccFormOp p q * ccFormOp q p) = 204 := by
  rw [ccScalar_value, ccRic_squared_trace, ccFormOp_squared_trace]
  norm_num


/-- The particular Planck length, Newton constant, and small parameter in
our verification.  In natural units `G = ℓP²`, as in the card's witness. -/
def ellP : ℝ := 1
def newtonG : ℝ := 1
def beta : ℝ := ellP ^ 2 / (48 * Real.pi)

lemma beta_value : beta = 1 / (48 * Real.pi) := by
  norm_num [beta, ellP]

lemma beta_pos : 0 < beta := by
  rw [beta_value]
  positivity

lemma spectrum_nonneg (i : Fin 11) : 0 ≤ sphereSpectrum i := by
  fin_cases i <;> norm_num [sphereSpectrum]

lemma spectrum_le_twelve (i : Fin 11) : sphereSpectrum i ≤ 12 := by
  fin_cases i <;> norm_num [sphereSpectrum]

/-- `I - βℝ` is strictly positive on every eigenvalue, so the real
logarithm is on the principal analytic branch requested by the card. -/
theorem logarithm_branch (i : Fin 11) : |beta * sphereSpectrum i| < 1 := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hnonneg : 0 ≤ beta * sphereSpectrum i :=
    mul_nonneg beta_pos.le (spectrum_nonneg i)
  rw [abs_of_nonneg hnonneg]
  calc
    beta * sphereSpectrum i ≤ beta * 12 :=
      mul_le_mul_of_nonneg_left (spectrum_le_twelve i) beta_pos.le
    _ = 1 / (4 * Real.pi) := by
      rw [beta_value]
      field_simp
      ring
    _ < 1 := by
      rw [div_lt_one (by positivity)]
      linarith


/-- The remainder after the degree-two Taylor polynomial of `-log(1-cx)`. -/
lemma negLog_residual_isBigO (c : ℝ) :
    (fun x : ℝ => -Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (2 * |c| ^ 3)
  have hcont : ContinuousAt (fun x : ℝ => |x * c|) 0 := by fun_prop
  have ht : Tendsto (fun x : ℝ => |x * c|) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto
  have hev : ∀ᶠ x : ℝ in 𝓝 0, |x * c| < (1 / 2 : ℝ) :=
    ht.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hev] with x hx
  have hx1 : |x * c| < (1 : ℝ) := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 2
  norm_num [Finset.sum_range_succ] at h
  have hden : (1 / 2 : ℝ) ≤ 1 - |x * c| := by linarith
  have hdenpos : (0 : ℝ) < 1 - |x * c| := by linarith
  have hcube : (0 : ℝ) ≤ |x * c| ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden hcube
  simp only [Real.norm_eq_abs]
  calc
    |-Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2| =
        |-( -Real.log (1 - x * c) - x * c - (x * c) ^ 2 / 2)| :=
      (abs_neg _).symm
    _ = |(x * c) + (x * c) ^ 2 / 2 + Real.log (1 - x * c)| := by
      congr 1
      ring
    _ ≤ |x * c| ^ 3 / (1 - |x * c|) := by
      simpa [mul_comm] using h
    _ ≤ 2 * |x * c| ^ 3 := by
      apply (div_le_iff₀ hdenpos).2
      nlinarith
    _ = 2 * |c| ^ 3 * |x ^ 3| := by
      simp only [abs_mul, abs_pow]
      ring

/-- Finite diagonal model of the trace-log on form space. -/
def traceLog {n : ℕ} (d : Fin n → ℝ) (x : ℝ) : ℝ :=
  -∑ i, Real.log (1 - x * d i)

lemma traceLog_sub_taylor_isBigO {n : ℕ} (d : Fin n → ℝ) :
    (fun x : ℝ => traceLog d x - x * (∑ i, d i) -
      x ^ 2 / 2 * (∑ i, d i ^ 2)) =O[𝓝 0] (fun x : ℝ => x ^ 3) := by
  have h0 : (∑ i : Fin n, fun x : ℝ =>
      (-Real.log (1 - x * d i) - x * d i - (x * d i) ^ 2 / 2)) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) :=
    Asymptotics.IsBigO.sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => negLog_residual_isBigO (d i))
  have h : (fun x : ℝ => ∑ i : Fin n,
      (-Real.log (1 - x * d i) - x * d i - (x * d i) ^ 2 / 2)) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
    apply h0.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
    simp
  apply h.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
  simp only [traceLog, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, mul_pow]
  have hquad : (∑ i, x ^ 2 * d i ^ 2 / 2) = x ^ 2 / 2 * (∑ i, d i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hquad]

/-- The displayed trace-log expansion is valid for the unit-sphere witness. -/
theorem sphere_traceLog_expansion :
    (fun x : ℝ => traceLog sphereSpectrum x -
      (3 * x * 12 + x ^ 2 / 2 * (12 ^ 2 + 36 + 24))) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  have h := traceLog_sub_taylor_isBigO sphereSpectrum
  rw [sphereSpectrum_sum, sphereSpectrum_sq_sum] at h
  apply h.congr' (Eventually.of_forall (fun x => ?_)) (EventuallyEq.rfl)
  ring

/-- The general positive scalar coefficient after substituting the expansion
of `-Tr log` into the action `-ℓP⁻⁴ ∫ Tr log`. -/
theorem planck_beta_matches_EH (ell G : ℝ) (hG : G = ell ^ 2) (hell : ell ≠ 0) :
    ell ^ (-4 : ℤ) * (3 * (ell ^ 2 / (48 * Real.pi))) =
      1 / (16 * Real.pi * G) := by
  rw [hG]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hp2 : ell ^ 2 ≠ 0 := pow_ne_zero 2 hell
  rw [zpow_neg]
  field_simp
  ring

/-- The scalar-curvature coefficient in the displayed action at the unit
four-sphere.  The inner minus is the coefficient of `Tr log`; the outer minus
is the explicit sign in `S_B`. -/
def actionRCoefficient : ℝ := -ellP ^ (-4 : ℤ) * (-(3 * beta * 12))

/-- The displayed positive Einstein--Hilbert scalar-curvature coefficient. -/
def einsteinHilbertRCoefficient : ℝ := (1 / (16 * Real.pi * newtonG)) * 12

theorem action_coefficient_value :
    actionRCoefficient = 3 / (4 * Real.pi) := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [actionRCoefficient, beta_value]
  norm_num [ellP]
  field_simp
  ring

theorem einstein_coefficient_value :
    einsteinHilbertRCoefficient = 3 / (4 * Real.pi) := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [einsteinHilbertRCoefficient]
  norm_num [newtonG]
  field_simp
  ring

/-- Both displayed signs are needed, and with them the proposed value of β
reproduces the positive Einstein--Hilbert coefficient. -/
theorem einstein_normalisation_consistency :
    actionRCoefficient = einsteinHilbertRCoefficient ∧
    0 < actionRCoefficient := by
  rw [action_coefficient_value, einstein_coefficient_value]
  have hpos : (0 : ℝ) < 3 / (4 * Real.pi) := by positivity
  exact ⟨rfl, hpos⟩

end B125Kernel

#print axioms B125Kernel.sphereSpectrum_sum
#print axioms B125Kernel.sphereSpectrum_sq_sum
#print axioms B125Kernel.sphere_matches_display
#print axioms B125Kernel.ccRic_value
#print axioms B125Kernel.ccScalar_value
#print axioms B125Kernel.ccRic_squared_trace
#print axioms B125Kernel.ccRiem_squared_norm
#print axioms B125Kernel.ccFormOp_value
#print axioms B125Kernel.ccFormOp_trace
#print axioms B125Kernel.ccFormOp_squared_trace
#print axioms B125Kernel.cc_total_trace
#print axioms B125Kernel.cc_total_squared_trace
#print axioms B125Kernel.beta_value
#print axioms B125Kernel.beta_pos
#print axioms B125Kernel.spectrum_nonneg
#print axioms B125Kernel.spectrum_le_twelve
#print axioms B125Kernel.logarithm_branch
#print axioms B125Kernel.negLog_residual_isBigO
#print axioms B125Kernel.traceLog_sub_taylor_isBigO
#print axioms B125Kernel.sphere_traceLog_expansion
#print axioms B125Kernel.action_coefficient_value
#print axioms B125Kernel.einstein_coefficient_value
#print axioms B125Kernel.planck_beta_matches_EH
#print axioms B125Kernel.einstein_normalisation_consistency
end
end


/-! ## B125 — an independent non-conformally-flat product witness

Integrated from `.ultramath/smww885zp/m7/B125Product.lean`.
-/

section
open scoped BigOperators
open Finset

namespace B125

/-- The eleven eigenvalues of the card's operator on
`Λ⁰ ⊕ Λ¹ ⊕ Λ²` for a product of two two-dimensional constant-curvature
factors of sectional curvatures `k` and `l`.  The same trace formulae hold
in either signature; the concrete example below is Lorentzian.

The convention is the one in the card: on 2-forms the operator is
`ℛ_{μν}^{ρσ}`, without a factor `1/2` in its contraction with a 2-form.
-/
def productSpectrum (k l : ℝ) : List ℝ :=
  [2 * k + 2 * l, k, k, l, l, 2 * k, 2 * l, 0, 0, 0, 0]

/-- The scalar curvature of the product. -/
def scalar (k l : ℝ) : ℝ := 2 * k + 2 * l

/-- The squared norm of the Ricci tensor of the product. -/
def ricciSq (k l : ℝ) : ℝ := 2 * k ^ 2 + 2 * l ^ 2

/-- The squared norm of the Riemann tensor of the product. -/
def riemannSq (k l : ℝ) : ℝ := 4 * k ^ 2 + 4 * l ^ 2

theorem productSpectrum_length (k l : ℝ) :
    (productSpectrum k l).length = 11 := by
  rfl

/-- The first trace over all eleven form directions is exactly `3R`. -/
theorem trace_product (k l : ℝ) :
    (productSpectrum k l).sum = 3 * scalar k l := by
  simp [productSpectrum, scalar]
  ring

/-- The second trace is the card's displayed sum of quadratic curvature
invariants.  In particular, the 2-form block has no extra factor. -/
theorem trace_sq_product (k l : ℝ) :
    ((productSpectrum k l).map fun x => x ^ 2).sum =
      scalar k l ^ 2 + ricciSq k l + riemannSq k l := by
  simp [productSpectrum, scalar, ricciSq, riemannSq]
  ring

/-- The card's prose description of the quadratic term as Gauss--Bonnet
plus five times the squared Ricci norm is algebraically identical to its
displayed formula. -/
theorem quadratic_is_gauss_bonnet_plus_five_ricci (k l : ℝ) :
    scalar k l ^ 2 + ricciSq k l + riemannSq k l =
      (riemannSq k l - 4 * ricciSq k l + scalar k l ^ 2) +
        5 * ricciSq k l := by
  ring

/-- The residual after the first two terms of `-log (1-x)`. -/
noncomputable def logRemainder (x : ℝ) : ℝ :=
  -Real.log (1 - x) - x - x ^ 2 / 2

/-- Exact finite trace-log expansion, with no analytic hypothesis needed:
all the tail is retained in the last sum. -/
theorem traceLog_expansion (xs : List ℝ) (beta : ℝ) :
    -(xs.map fun x => Real.log (1 - beta * x)).sum =
      beta * xs.sum + beta ^ 2 / 2 * (xs.map fun x => x ^ 2).sum +
        (xs.map fun x => logRemainder (beta * x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [neg_add, ih]
      simp only [logRemainder]
      ring

theorem abs_logRemainder_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |logRemainder x| ≤ 2 * |x| ^ 3 := by
  have hx1 : |x| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 2
  have hbound : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |x|)).2
    have hpow : 0 ≤ |x| ^ 3 := by positivity
    have hprod : 0 ≤ |x| ^ 3 * (1 - 2 * |x|) :=
      mul_nonneg hpow (by linarith)
    nlinarith
  have heq : logRemainder x =
      -((∑ i ∈ range 2, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)) := by
    simp [logRemainder, sum_range_succ]
    ring
  have hsimplify :
      |(∑ i ∈ range 2, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)| =
        |logRemainder x| := by
    rw [heq, abs_neg]
  rw [← hsimplify]
  exact h.trans hbound

/-- A uniform cubic bound for the complete finite trace-log tail. -/
theorem abs_traceLog_remainder_le (xs : List ℝ) (beta : ℝ)
    (hsmall : ∀ x ∈ xs, |beta * x| ≤ 1 / 2) :
    |(xs.map fun x => logRemainder (beta * x)).sum| ≤
      2 * |beta| ^ 3 * (xs.map fun x => |x| ^ 3).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : |beta * x| ≤ 1 / 2 := hsmall x (by simp)
      have hxs : ∀ y ∈ xs, |beta * y| ≤ 1 / 2 := by
        intro y hy
        exact hsmall y (by simp [hy])
      have hi := ih hxs
      simp only [List.map_cons, List.sum_cons]
      calc
        |logRemainder (beta * x) +
            (xs.map fun y => logRemainder (beta * y)).sum| ≤
            |logRemainder (beta * x)| +
              |(xs.map fun y => logRemainder (beta * y)).sum| := abs_add_le _ _
        _ ≤ 2 * |beta * x| ^ 3 +
              2 * |beta| ^ 3 * (xs.map fun y => |y| ^ 3).sum :=
          add_le_add (abs_logRemainder_le hx) hi
        _ = 2 * |beta| ^ 3 * (|x| ^ 3 + (xs.map fun y => |y| ^ 3).sum) := by
          rw [abs_mul, mul_pow]
          ring

/-- The displayed second-order identity on the product test, retaining its
remainder explicitly. -/
theorem product_traceLog_expansion (k l beta : ℝ) :
    -((productSpectrum k l).map fun x => Real.log (1 - beta * x)).sum =
      3 * beta * scalar k l +
        beta ^ 2 / 2 * (scalar k l ^ 2 + ricciSq k l + riemannSq k l) +
        ((productSpectrum k l).map fun x => logRemainder (beta * x)).sum := by
  rw [traceLog_expansion, trace_product, trace_sq_product]
  ring

/-- Concrete non-conformally-flat Lorentzian test:
`dS²(1) × S²(2)`, whose sectional curvatures are `1` and `1/4`. -/
theorem numeric_product_first_coefficient :
    3 * scalar 1 (1 / 4 : ℝ) = 15 / 2 := by
  norm_num [scalar]

theorem numeric_product_second_coefficient :
    scalar 1 (1 / 4 : ℝ) ^ 2 + ricciSq 1 (1 / 4 : ℝ) +
      riemannSq 1 (1 / 4 : ℝ) = 101 / 8 := by
  norm_num [scalar, ricciSq, riemannSq]

theorem numeric_product_cubic_norm_sum :
    ((productSpectrum 1 (1 / 4 : ℝ)).map fun x => |x| ^ 3).sum = 825 / 32 := by
  norm_num [productSpectrum]

/-- For this example, `|beta| ≤ 1/5` is a sufficient explicit form of the
card's smallness/branch hypothesis. -/
theorem numeric_product_small {beta x : ℝ} (hbeta : |beta| ≤ 1 / 5)
    (hx : x ∈ productSpectrum 1 (1 / 4 : ℝ)) : |beta * x| ≤ 1 / 2 := by
  simp [productSpectrum] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [abs_mul] at *
  all_goals nlinarith [abs_nonneg beta]

/-- The explicit cubic error bound for the concrete product test. -/
theorem numeric_product_tail_bound (beta : ℝ) (hbeta : |beta| ≤ 1 / 5) :
    |((productSpectrum 1 (1 / 4 : ℝ)).map fun x =>
      logRemainder (beta * x)).sum| ≤ 825 / 16 * |beta| ^ 3 := by
  have h := abs_traceLog_remainder_le (productSpectrum 1 (1 / 4 : ℝ)) beta
    (fun x hx => numeric_product_small hbeta hx)
  rw [numeric_product_cubic_norm_sum] at h
  calc
    |((productSpectrum 1 (1 / 4 : ℝ)).map fun x =>
      logRemainder (beta * x)).sum| ≤ 2 * |beta| ^ 3 * (825 / 32) := h
    _ = 825 / 16 * |beta| ^ 3 := by ring

/-- The Einstein prefactor after substituting `beta = ℓ²/(48π)`.
The last identification with `1/(16πG)` uses the natural-units convention
`G = ℓ²`. -/
theorem einstein_prefactor (ell G : ℝ) (hell : ell ≠ 0)
    (hG : G = ell ^ 2) :
    3 * (ell ^ 2 / (48 * Real.pi)) / ell ^ 4 = 1 / (16 * Real.pi * G) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hG]
  field_simp
  ring

#print axioms productSpectrum_length
#print axioms trace_product
#print axioms trace_sq_product
#print axioms quadratic_is_gauss_bonnet_plus_five_ricci
#print axioms traceLog_expansion
#print axioms abs_logRemainder_le
#print axioms abs_traceLog_remainder_le
#print axioms product_traceLog_expansion
#print axioms numeric_product_first_coefficient
#print axioms numeric_product_second_coefficient
#print axioms numeric_product_cubic_norm_sum
#print axioms numeric_product_small
#print axioms numeric_product_tail_bound
#print axioms einstein_prefactor

end B125
end
