/-
Seventh batch: the remaining theorem-grade cards.

Each contribution is reproduced verbatim except for its import line; all are self-contained
(`import Mathlib`) and keep their own scope delimiters. Nothing in the earlier modules is
modified.
-/
import Mathlib


/-! ## B65 — the resolvent contour integral is the spectral projector

Integrated from `.ultramath/smwvvnwls/m1/B65.lean`.
-/

open Metric
open Complex
open scoped Matrix.Norms.Elementwise

namespace B65

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The resolvent `R(z) = (zI - A)⁻¹` of `A = diag(a,b)`. -/
noncomputable def diagonalResolvent (a b z : ℂ) : Mat2 :=
  (z • (1 : Mat2) - Matrix.diagonal ![a, b])⁻¹

lemma diagonalResolvent_eq (a b z : ℂ) (hz : ∀ i, z - ![a, b] i ≠ 0) :
    diagonalResolvent a b z = Matrix.diagonal (fun i => (z - ![a, b] i)⁻¹) := by
  unfold diagonalResolvent
  have h : z • (1 : Mat2) - Matrix.diagonal ![a, b] =
      Matrix.diagonal (fun i => z - ![a, b] i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [h]
  apply Matrix.inv_eq_right_inv
  calc
    Matrix.diagonal (fun i => z - ![a, b] i) *
        Matrix.diagonal (fun i => (z - ![a, b] i)⁻¹) =
        Matrix.diagonal (fun i => (z - ![a, b] i) * (z - ![a, b] i)⁻¹) :=
      Matrix.diagonal_mul_diagonal _ _
    _ = Matrix.diagonal (fun _ => 1) := by
      congr 1
      funext i
      exact mul_inv_cancel₀ (hz i)
    _ = 1 := Matrix.diagonal_one

/-- Away from both poles, the resolvent is continuous and hence circle integrable. -/
lemma diagonal_partialFraction_circleIntegrable {a b c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ sphere c R) (hb : b ∉ sphere c R) :
    CircleIntegrable
      (fun z => Matrix.diagonal (fun i => (z - ![a, b] i)⁻¹) : ℂ → Mat2) c R := by
  apply ContinuousOn.circleIntegrable hR
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    fin_cases i
    · change z - a ≠ 0
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha)
    · change z - b ≠ 0
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hb)
  · simp [hij]
    exact continuousOn_const

/-- The residue calculation on a positively oriented circle. -/
lemma normalized_circleIntegral_inv_of_mem_ball {a c : ℂ} {R : ℝ}
    (ha : a ∈ ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(c, R), (z - a)⁻¹) = 1 := by
  rw [circleIntegral.integral_sub_inv_of_mem_ball ha, smul_eq_mul]
  apply inv_mul_cancel₀
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- If the pole is outside the closed disk, Cauchy's theorem gives zero. -/
lemma circleIntegral_inv_of_not_mem_closedBall {a c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ closedBall c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty
  · refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    apply sub_ne_zero.mpr
    change z ≠ a
    rintro rfl
    exact ha hz
  · intro z hz
    refine (differentiableAt_id.sub_const a).inv ?_
    apply sub_ne_zero.mpr
    change z ≠ a
    rintro rfl
    exact ha (ball_subset_closedBall hz.1)

lemma normalized_circleIntegral_inv_of_not_mem_closedBall {a c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∉ closedBall c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  rw [circleIntegral_inv_of_not_mem_closedBall hR ha, smul_zero]

/-- Evaluation of a matrix entry commutes with circle integration. -/
lemma circleIntegral_apply {f : ℂ → Mat2} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (i j : Fin 2) :
    (∮ z in C(c, R), f z) i j = ∮ z in C(c, R), f z i j := by
  let Li : Mat2 →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj i
  let Lj : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj j
  let L : Mat2 →L[ℂ] ℂ := Lj.comp Li
  unfold circleIntegral
  change L (∫ θ : ℝ in 0..2 * Real.pi,
      deriv (circleMap c R) θ • f (circleMap c R θ)) =
    ∫ θ : ℝ in 0..2 * Real.pi,
      L (deriv (circleMap c R) θ • f (circleMap c R θ))
  exact (L.intervalIntegral_comp_comm hf.out).symm

/-- **Finite form of B65.** For `A = diag(a,b)`, a positively oriented circle enclosing
`a` and excluding `b` from its closed disk produces the spectral projector onto the `a`-line. -/
theorem diagonal_spectral_projector {a b w : ℂ} {R : ℝ}
    (ha : a ∈ ball w R) (hb : b ∉ closedBall w R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(w, R), diagonalResolvent a b z) =
      Matrix.diagonal ![1, 0] := by
  have hR : 0 ≤ R := (dist_nonneg.trans_lt ha).le
  have haS : a ∉ sphere w R := by
    intro h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball h ha
  have hbS : b ∉ sphere w R := by
    intro h
    exact hb (sphere_subset_closedBall h)
  let D : ℂ → Mat2 := fun z => Matrix.diagonal (fun i => (z - ![a, b] i)⁻¹)
  have hEq : Set.EqOn (diagonalResolvent a b) D (sphere w R) := by
    intro z hz
    dsimp [D]
    apply diagonalResolvent_eq
    intro i
    fin_cases i
    · change z - a ≠ 0
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz haS)
    · change z - b ≠ 0
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hbS)
  have hIntD : CircleIntegrable D w R :=
    diagonal_partialFraction_circleIntegrable hR haS hbS
  rw [circleIntegral.integral_congr hR hEq]
  ext i j
  change (2 * (Real.pi : ℂ) * I)⁻¹ • ((∮ z in C(w, R), D z) i j) =
    Matrix.diagonal ![1, 0] i j
  rw [circleIntegral_apply hIntD i j]
  by_cases hij : i = j
  · subst j
    fin_cases i
    · simpa [D] using
        (normalized_circleIntegral_inv_of_mem_ball (a := a) (c := w) (R := R) ha)
    · simpa [D] using
        (normalized_circleIntegral_inv_of_not_mem_closedBall (a := b) (c := w) (R := R) hR hb)
  · simp [D, hij, circleIntegral]

/-- The contour integral is indeed idempotent. -/
theorem diagonal_spectral_projector_idempotent {a b w : ℂ} {R : ℝ}
    (ha : a ∈ ball w R) (hb : b ∉ closedBall w R) :
    let P : Mat2 :=
      (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(w, R), diagonalResolvent a b z)
    P * P = P := by
  dsimp only
  rw [diagonal_spectral_projector ha hb, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The circle `|z| = 1` separates the eigenvalues `0` and `2`. -/
theorem unit_circle_zero_two :
    (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(0, 1), diagonalResolvent 0 2 z) =
      Matrix.diagonal ![1, 0] := by
  apply diagonal_spectral_projector
  · simp
  · norm_num [Metric.mem_closedBall, dist_zero_right]

#print axioms diagonalResolvent_eq
#print axioms diagonal_partialFraction_circleIntegrable
#print axioms normalized_circleIntegral_inv_of_mem_ball
#print axioms circleIntegral_inv_of_not_mem_closedBall
#print axioms normalized_circleIntegral_inv_of_not_mem_closedBall
#print axioms circleIntegral_apply
#print axioms diagonal_spectral_projector
#print axioms diagonal_spectral_projector_idempotent
#print axioms unit_circle_zero_two

end B65


/-! ## B121 — the Jordan criterion needs A12 != 0 (REFUTATION)

Integrated from `.ultramath/smwvvnwls/m5/B121.lean`.
-/

/-!
# B121: the displayed Jordan criterion is false at the scalar-T point

The card uses `A(H) = T*H + H*T - 2*tr(T*H)*G` on traceless
symmetric matrices.  At the coplanar wall `G = diagonal(w)` with
`w₁+w₂ = 1`, its shape block is upper triangular.  The displayed
condition for a Jordan block is
`t₁+t₂-2*t₃ = (t₁-t₂)*(w₁-w₂)`.

At `T = 1` this condition holds at every wall point, but the transport is
`2*H` on every traceless matrix.  In particular its shape block is `2*I`,
not a nontrivial Jordan block.
-/

namespace B121

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The transport map occurring in cards B36 and B171, from which B121's
shape block is computed. -/
def transport (T G H : Mat 3) : Mat 3 :=
  T * H + H * T - (2 * Matrix.trace (T * H)) • G

/-- On traceless matrices, scalar `T = 1` makes the transport equal to `2`. -/
theorem transport_one_of_trace_zero {G H : Mat 3} (hH : Matrix.trace H = 0) :
    transport 1 G H = (2 : ℝ) • H := by
  simp [transport, hH, two_smul]

/-- The first standard Frobenius-orthonormal diagonal shape direction. -/
noncomputable def E₁ : Mat 3 :=
  (1 / Real.sqrt 2) • Matrix.diagonal ![(1 : ℝ), -1, 0]

/-- The second standard Frobenius-orthonormal diagonal shape direction. -/
noncomputable def E₂ : Mat 3 :=
  (1 / Real.sqrt 6) • Matrix.diagonal ![(1 : ℝ), 1, -2]

/-- The coplanar Gram matrix in the counterexample. -/
noncomputable def G₀ : Mat 3 := Matrix.diagonal ![(1 : ℝ) / 2, 1 / 2, 0]

/-- Frobenius pairing on real matrices. -/
def frob (H K : Mat 3) : ℝ := Matrix.trace (H.transpose * K)

/-- The actual shape block in the Frobenius frame `(E₁,E₂)`, specialized to
our witness `T = 1`, `G = G₀`. -/
noncomputable def shape₀ : Mat 2 :=
  !![frob E₁ (transport 1 G₀ E₁), frob E₁ (transport 1 G₀ E₂);
     frob E₂ (transport 1 G₀ E₁), frob E₂ (transport 1 G₀ E₂)]

/-- Diagonalizability, expressed without any library-specific Jordan notion:
an invertible change of basis makes the matrix diagonal. -/
def Diagonalizable (A : Mat 2) : Prop :=
  ∃ P D : Mat 2, P.det ≠ 0 ∧ D.IsDiag ∧ A * P = P * D

/-- The scalar shape matrix is diagonalizable (indeed already diagonal). -/
theorem diagonalizable_two_one : Diagonalizable ((2 : ℝ) • (1 : Mat 2)) := by
  refine ⟨1, 2 • 1, ?_, ?_, ?_⟩
  · simp
  · exact Matrix.IsDiag.smul 2 (Matrix.isDiag_one)
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply, Matrix.ofNat_apply]

theorem trace_E₁ : Matrix.trace E₁ = 0 := by
  simp [E₁, Matrix.trace, Fin.sum_univ_three]

theorem trace_E₂ : Matrix.trace E₂ = 0 := by
  simp [E₂, Matrix.trace, Fin.sum_univ_three]
  ring

theorem frob_diagonal (u v : Fin 3 → ℝ) :
    frob (Matrix.diagonal u) (Matrix.diagonal v) = ∑ i, u i * v i := by
  simp [frob, Matrix.diagonal_mul_diagonal]

theorem frob_smul (a b : ℝ) (H K : Mat 3) :
    frob (a • H) (b • K) = a * b * frob H K := by
  simp [frob, smul_smul, mul_comm]

theorem frob_E₁_E₁ : frob E₁ E₁ = 1 := by
  rw [E₁, frob_smul, frob_diagonal]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, one_mul, neg_mul,
    mul_neg, mul_zero, add_zero]
  calc
    _ = ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) * 2 := by ring
    _ = 1 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

theorem frob_E₂_E₂ : frob E₂ E₂ = 1 := by
  rw [E₂, frob_smul, frob_diagonal]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, one_mul, neg_mul,
    mul_neg]
  calc
    _ = ((1 / Real.sqrt 6) * (1 / Real.sqrt 6)) * 6 := by ring
    _ = 1 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num

theorem frob_E₁_E₂ : frob E₁ E₂ = 0 := by
  rw [E₁, E₂, frob_smul, frob_diagonal]
  simp [Fin.sum_univ_three]

theorem frob_E₂_E₁ : frob E₂ E₁ = 0 := by
  rw [E₂, E₁, frob_smul, frob_diagonal]
  simp [Fin.sum_univ_three]

theorem frob_two_right (H K : Mat 3) : frob H ((2 : ℝ) • K) = 2 * frob H K := by
  simp [frob]

/-- The actual Frobenius shape block at the witness is `2*I`; its
upper-right entry is zero even though the displayed Jordan equality holds. -/
theorem shape₀_eq_two_one : shape₀ = (2 : ℝ) • (1 : Mat 2) := by
  rw [shape₀, transport_one_of_trace_zero trace_E₁,
    transport_one_of_trace_zero trace_E₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frob_two_right, frob_E₁_E₁, frob_E₂_E₂,
      frob_E₁_E₂, frob_E₂_E₁]

/-- The witness satisfies the exact Jordan equality printed on B121. -/
theorem displayed_condition_at_witness :
    let t₁ : ℝ := 1
    let t₂ : ℝ := 1
    let t₃ : ℝ := 1
    let w₁ : ℝ := 1 / 2
    let w₂ : ℝ := 1 / 2
    t₁ + t₂ - 2 * t₃ = (t₁ - t₂) * (w₁ - w₂) := by
  norm_num

/-- Therefore the printed equality cannot be equivalent to being a
nontrivial Jordan block: its forward implication fails at this witness. -/
theorem displayed_jordan_iff_is_false :
    ¬ (((1 : ℝ) + 1 - 2 * 1 = (1 - 1) * (1 / 2 - 1 / 2)) ↔
      ¬ Diagonalizable shape₀) := by
  intro h
  have hcondition : (1 : ℝ) + 1 - 2 * 1 = (1 - 1) * (1 / 2 - 1 / 2) := by
    norm_num
  have hdiag : Diagonalizable shape₀ := by
    rw [shape₀_eq_two_one]
    exact diagonalizable_two_one
  exact (h.mp hcondition) hdiag

/-- The wall-point hypotheses are genuine: both retained weights are strictly
positive and sum to one, and the dropped weight is zero. -/
theorem witness_is_regular_coplanar_wall :
    (0 : ℝ) < 1 / 2 ∧ (0 : ℝ) < 1 / 2 ∧
      (1 / 2 : ℝ) + 1 / 2 + 0 = 1 := by
  norm_num

/-- The witness Gram matrix has rank exactly two, so this is the regular
rank-two wall rather than the excluded collinear stratum. -/
theorem rank_G₀ : G₀.rank = 2 := by
  classical
  rw [G₀, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![(1 : ℝ) / 2, 1 / 2, 0] : Fin 3 → ℝ) x ≠ 0)).card = 2
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![(1 : ℝ) / 2, 1 / 2, 0] : Fin 3 → ℝ) x ≠ 0)) = {0, 1} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

/-- The perturbation matrix `T = 1` is strictly positive definite, as required
by the card's `T = diag(t) ≻ 0` hypothesis. -/
theorem witness_T_posDef : (1 : Mat 3).PosDef := Matrix.PosDef.one

/-- The witness Gram matrix has trace one. -/
theorem trace_G₀ : Matrix.trace G₀ = 1 := by
  norm_num [G₀, Fin.sum_univ_three]

#print axioms transport_one_of_trace_zero
#print axioms diagonalizable_two_one
#print axioms trace_E₁
#print axioms trace_E₂
#print axioms frob_diagonal
#print axioms frob_smul
#print axioms frob_E₁_E₁
#print axioms frob_E₂_E₂
#print axioms frob_E₁_E₂
#print axioms frob_E₂_E₁
#print axioms frob_two_right
#print axioms shape₀_eq_two_one
#print axioms displayed_condition_at_witness
#print axioms displayed_jordan_iff_is_false
#print axioms witness_is_regular_coplanar_wall
#print axioms rank_G₀
#print axioms witness_T_posDef
#print axioms trace_G₀

end B121


/-! ## B117 — the normalised distance sandwich and both equality cases

Integrated from `.ultramath/smwvvnwls/m7/B117.lean`.
-/

/-!
# B117: the sharp angle sandwich for permutation graph projectors

For principal angles `θ j ∈ [0, π/2]`, B116 gives
`dH = (2 / n) * ∑ j, sin (θ j)^2` and `L² = ∑ j, (θ j)^2`.
This file proves the resulting sharp sandwich and its exact equality cases.
The spectral identification of endpoint angles with a permutation involution is
kept separate from the finite trigonometric theorem.
-/

open scoped BigOperators Real
open Finset

namespace B117

variable {n : ℕ}

/-- The squared intrinsic length, before division by `n`. -/
def lengthSq (θ : Fin n → ℝ) : ℝ := ∑ j, θ j ^ 2

/-- The chordal/Hamming fraction in the normalization of B116. -/
noncomputable def hamming (θ : Fin n → ℝ) : ℝ :=
  (2 / (n : ℝ)) * ∑ j, Real.sin (θ j) ^ 2

/-- Jordan's inequality, squared and in the exact constant used by B117. -/
lemma sq_le_pi_sq_div_four_mul_sin_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi / 2) :
    x ^ 2 ≤ (Real.pi ^ 2 / 4) * Real.sin x ^ 2 := by
  have h := Real.mul_le_sin hx0 hxπ
  have hc : 0 ≤ 2 / Real.pi * x := by positivity
  have hs : 0 ≤ Real.sin x := hc.trans h
  have hsq : (2 / Real.pi * x) ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hc h 2
  have hfactor : 0 ≤ Real.pi ^ 2 / 4 := by positivity
  calc
    x ^ 2 = (Real.pi ^ 2 / 4) * (2 / Real.pi * x) ^ 2 := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ ≤ (Real.pi ^ 2 / 4) * Real.sin x ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hfactor

#print axioms B117.sq_le_pi_sq_div_four_mul_sin_sq

/-- Strict Jordan inequality away from both endpoints. -/
lemma sq_lt_pi_sq_div_four_mul_sin_sq {x : ℝ}
    (hx0 : 0 < x) (hxπ : x < Real.pi / 2) :
    x ^ 2 < (Real.pi ^ 2 / 4) * Real.sin x ^ 2 := by
  have h := Real.mul_lt_sin hx0 hxπ
  have hc : 0 ≤ 2 / Real.pi * x := by positivity
  have hsq : (2 / Real.pi * x) ^ 2 < Real.sin x ^ 2 :=
    pow_lt_pow_left₀ h hc (by norm_num)
  have hfactor : 0 < Real.pi ^ 2 / 4 := by positivity
  calc
    x ^ 2 = (Real.pi ^ 2 / 4) * (2 / Real.pi * x) ^ 2 := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ < (Real.pi ^ 2 / 4) * Real.sin x ^ 2 :=
      mul_lt_mul_of_pos_left hsq hfactor

#print axioms B117.sq_lt_pi_sq_div_four_mul_sin_sq

/-- Equality in Jordan's squared inequality occurs exactly at the endpoints. -/
lemma sq_eq_pi_sq_div_four_mul_sin_sq_iff {x : ℝ}
    (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi / 2) :
    x ^ 2 = (Real.pi ^ 2 / 4) * Real.sin x ^ 2 ↔
      x = 0 ∨ x = Real.pi / 2 := by
  constructor
  · intro heq
    by_cases h0 : x = 0
    · exact Or.inl h0
    right
    by_contra hπ
    have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h0)
    have hxπ' : x < Real.pi / 2 := lt_of_le_of_ne hxπ hπ
    exact (ne_of_lt (sq_lt_pi_sq_div_four_mul_sin_sq hx0' hxπ')) heq
  · rintro (rfl | rfl)
    · simp
    · rw [Real.sin_pi_div_two]
      ring

#print axioms B117.sq_eq_pi_sq_div_four_mul_sin_sq_iff

/-- The unnormalized lower bound. -/
lemma sum_sin_sq_le_lengthSq (θ : Fin n → ℝ) :
    (∑ j, Real.sin (θ j) ^ 2) ≤ lengthSq θ := by
  exact Finset.sum_le_sum fun j _ ↦ Real.sin_sq_le_sq

#print axioms B117.sum_sin_sq_le_lengthSq

/-- The unnormalized sharp upper bound. -/
lemma lengthSq_le_pi_sq_div_four_mul_sum_sin_sq (θ : Fin n → ℝ)
    (hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ Real.pi / 2) :
    lengthSq θ ≤ (Real.pi ^ 2 / 4) * ∑ j, Real.sin (θ j) ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦
    sq_le_pi_sq_div_four_mul_sin_sq (hθ j).1 (hθ j).2

#print axioms B117.lengthSq_le_pi_sq_div_four_mul_sum_sin_sq

/-- Lower equality forces every principal angle to vanish. -/
lemma sum_sin_sq_eq_lengthSq_iff (θ : Fin n → ℝ) :
    (∑ j, Real.sin (θ j) ^ 2) = lengthSq θ ↔ ∀ j, θ j = 0 := by
  rw [lengthSq, Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ Finset.univ) ↦ Real.sin_sq_le_sq)]
  constructor
  · intro h j
    by_contra hj
    exact (ne_of_lt (Real.sin_sq_lt_sq hj)) (h j (Finset.mem_univ j))
  · intro h j _
    rw [h j, Real.sin_zero]

#print axioms B117.sum_sin_sq_eq_lengthSq_iff

/-- Upper equality holds exactly when every angle is `0` or `π/2`. -/
lemma lengthSq_eq_pi_sq_div_four_mul_sum_sin_sq_iff (θ : Fin n → ℝ)
    (hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ Real.pi / 2) :
    lengthSq θ = (Real.pi ^ 2 / 4) * ∑ j, Real.sin (θ j) ^ 2 ↔
      ∀ j, θ j = 0 ∨ θ j = Real.pi / 2 := by
  rw [lengthSq, Finset.mul_sum, Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ Finset.univ) ↦
      sq_le_pi_sq_div_four_mul_sin_sq (hθ j).1 (hθ j).2)]
  constructor
  · intro h j
    exact (sq_eq_pi_sq_div_four_mul_sin_sq_iff (hθ j).1 (hθ j).2).mp
      (h j (Finset.mem_univ j))
  · intro h j _
    exact (sq_eq_pi_sq_div_four_mul_sin_sq_iff (hθ j).1 (hθ j).2).mpr (h j)

#print axioms B117.lengthSq_eq_pi_sq_div_four_mul_sum_sin_sq_iff

lemma hamming_div_two_eq_sum_sin_sq_div (θ : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0) :
    hamming θ / 2 = (∑ j, Real.sin (θ j) ^ 2) / (n : ℝ) := by
  rw [hamming]
  field_simp [hn]
  <;> ring

#print axioms B117.hamming_div_two_eq_sum_sin_sq_div

lemma pi_sq_div_eight_mul_hamming_eq (θ : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0) :
    (Real.pi ^ 2 / 8) * hamming θ =
      ((Real.pi ^ 2 / 4) * ∑ j, Real.sin (θ j) ^ 2) / (n : ℝ) := by
  rw [hamming]
  field_simp [hn]
  <;> ring

#print axioms B117.pi_sq_div_eight_mul_hamming_eq

lemma div_nat_eq_div_nat_iff {a b : ℝ} {n : ℕ} (hn : (n : ℝ) ≠ 0) :
    a / (n : ℝ) = b / (n : ℝ) ↔ a = b := by
  constructor
  · intro h
    apply mul_right_cancel₀ hn
    exact (div_eq_div_iff hn hn).mp h
  · intro h
    rw [h]

#print axioms B117.div_nat_eq_div_nat_iff

/-- The displayed B117 lower bound. -/
theorem b117_lower (θ : Fin n → ℝ) :
    hamming θ / 2 ≤ lengthSq θ / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [hamming, lengthSq]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [hamming_div_two_eq_sum_sin_sq_div θ hn']
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < n)).mpr
    (sum_sin_sq_le_lengthSq θ)

#print axioms B117.b117_lower

/-- The displayed B117 upper bound, with its exact constant `π²/8`. -/
theorem b117_upper (θ : Fin n → ℝ)
    (hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ Real.pi / 2) :
    lengthSq θ / (n : ℝ) ≤ (Real.pi ^ 2 / 8) * hamming θ := by
  by_cases hn : n = 0
  · subst n
    simp [hamming, lengthSq]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [pi_sq_div_eight_mul_hamming_eq θ hn']
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < n)).mpr
    (lengthSq_le_pi_sq_div_four_mul_sum_sin_sq θ hθ)

#print axioms B117.b117_upper

/-- The full displayed two-sided rigidity estimate. -/
theorem b117_angle_sandwich (θ : Fin n → ℝ)
    (hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ Real.pi / 2) :
    hamming θ / 2 ≤ lengthSq θ / (n : ℝ) ∧
      lengthSq θ / (n : ℝ) ≤ (Real.pi ^ 2 / 8) * hamming θ :=
  ⟨b117_lower θ, b117_upper θ hθ⟩

#print axioms B117.b117_angle_sandwich

/-- Lower equality in the displayed normalization is equivalent to zero angles. -/
theorem b117_lower_eq_iff (θ : Fin n → ℝ) :
    hamming θ / 2 = lengthSq θ / (n : ℝ) ↔ ∀ j, θ j = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [hamming, lengthSq]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [hamming_div_two_eq_sum_sin_sq_div θ hn', div_nat_eq_div_nat_iff hn']
  exact sum_sin_sq_eq_lengthSq_iff θ

#print axioms B117.b117_lower_eq_iff

/--
Upper equality in the displayed normalization: every principal angle is zero or
a right angle. This is the angle-list form of the card's involution clause.
-/
theorem b117_upper_eq_iff (θ : Fin n → ℝ)
    (hθ : ∀ j, 0 ≤ θ j ∧ θ j ≤ Real.pi / 2) :
    lengthSq θ / (n : ℝ) = (Real.pi ^ 2 / 8) * hamming θ ↔
      ∀ j, θ j = 0 ∨ θ j = Real.pi / 2 := by
  by_cases hn : n = 0
  · subst n
    simp [hamming, lengthSq]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [pi_sq_div_eight_mul_hamming_eq θ hn', div_nat_eq_div_nat_iff hn']
  exact lengthSq_eq_pi_sq_div_four_mul_sum_sin_sq_iff θ hθ

#print axioms B117.b117_upper_eq_iff

/-- The principal angles of the identity versus a transposition on two points. -/
noncomputable def swapAngles : Fin 2 → ℝ := ![0, Real.pi / 2]

lemma swapAngles_range (j : Fin 2) :
    0 ≤ swapAngles j ∧ swapAngles j ≤ Real.pi / 2 := by
  fin_cases j <;> simp [swapAngles] <;> positivity

#print axioms B117.swapAngles_range

theorem swap_hamming : hamming swapAngles = 1 := by
  norm_num [hamming, swapAngles, Fin.sum_univ_two, Real.sin_pi_div_two]

#print axioms B117.swap_hamming

theorem swap_lengthSq_div :
    lengthSq swapAngles / (2 : ℝ) = Real.pi ^ 2 / 8 := by
  simp [lengthSq, swapAngles, Fin.sum_univ_two]
  ring

#print axioms B117.swap_lengthSq_div

/-- The `n = 2` swap case saturates the upper bound. -/
theorem swap_upper_equality :
    lengthSq swapAngles / (2 : ℝ) =
      (Real.pi ^ 2 / 8) * hamming swapAngles := by
  rw [swap_lengthSq_div, swap_hamming, mul_one]

#print axioms B117.swap_upper_equality

/-- The three angles for one 3-cycle: the two nontrivial phases are conjugate. -/
noncomputable def threeCycleAngles : Fin 3 → ℝ :=
  ![0, Real.pi / 3, Real.pi / 3]

lemma threeCycleAngles_range (j : Fin 3) :
    0 ≤ threeCycleAngles j ∧ threeCycleAngles j ≤ Real.pi / 2 := by
  have h20 : 0 ≤ Real.pi / 2 := by positivity
  have h30 : 0 ≤ Real.pi / 3 := by positivity
  have h32 : Real.pi / 3 ≤ Real.pi / 2 := by gcongr; norm_num
  fin_cases j
  · simpa [threeCycleAngles] using
      (show 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.pi / 2 from ⟨le_rfl, h20⟩)
  · simpa [threeCycleAngles] using
      (show 0 ≤ Real.pi / 3 ∧ Real.pi / 3 ≤ Real.pi / 2 from ⟨h30, h32⟩)
  · simpa [threeCycleAngles] using
      (show 0 ≤ Real.pi / 3 ∧ Real.pi / 3 ≤ Real.pi / 2 from ⟨h30, h32⟩)

#print axioms B117.threeCycleAngles_range

theorem threeCycle_hamming : hamming threeCycleAngles = 1 := by
  unfold hamming
  rw [Fin.sum_univ_three]
  change (2 / (3 : ℝ)) *
    (Real.sin 0 ^ 2 + Real.sin (Real.pi / 3) ^ 2 + Real.sin (Real.pi / 3) ^ 2) = 1
  rw [Real.sin_zero, Real.sq_sin_pi_div_three]
  norm_num

#print axioms B117.threeCycle_hamming

theorem threeCycle_lengthSq_div :
    lengthSq threeCycleAngles / (3 : ℝ) = 2 * Real.pi ^ 2 / 27 := by
  simp [lengthSq, threeCycleAngles, Fin.sum_univ_three]
  ring

#print axioms B117.threeCycle_lengthSq_div

/-- The card's `0.593` entry for a 3-cycle is the exact ratio `16/27`. -/
theorem threeCycle_ratio :
    lengthSq threeCycleAngles / (3 : ℝ) =
      (16 / 27 : ℝ) * ((Real.pi ^ 2 / 8) * hamming threeCycleAngles) := by
  rw [threeCycle_lengthSq_div, threeCycle_hamming, mul_one]
  ring

#print axioms B117.threeCycle_ratio

/-- In particular, a 3-cycle does not attain the upper bound. -/
theorem threeCycle_upper_strict :
    lengthSq threeCycleAngles / (3 : ℝ) <
      (Real.pi ^ 2 / 8) * hamming threeCycleAngles := by
  rw [threeCycle_lengthSq_div, threeCycle_hamming, mul_one]
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  nlinarith

#print axioms B117.threeCycle_upper_strict

/-- A permutation squaring to one consists exactly of fixed points and swaps. -/
theorem perm_sq_eq_one_iff_fixed_or_swap {ι : Type*} (ρ : Equiv.Perm ι) :
    ρ ^ 2 = 1 ↔
      ∀ x, ρ x = x ∨ (ρ x ≠ x ∧ ρ (ρ x) = x) := by
  constructor
  · intro h x
    have hx : ρ (ρ x) = x := by
      have hx' := DFunLike.congr_fun h x
      simpa [pow_two, Equiv.Perm.mul_apply] using hx'
    by_cases hfix : ρ x = x
    · exact Or.inl hfix
    · exact Or.inr ⟨hfix, hx⟩
  · intro h
    ext x
    rcases h x with hfix | hswap
    · simp [pow_two, Equiv.Perm.mul_apply, hfix]
    · simp [pow_two, Equiv.Perm.mul_apply, hswap.2]

#print axioms B117.perm_sq_eq_one_iff_fixed_or_swap

/-- The relative unitary `U†V` for two permutation matrices. -/
noncomputable def relativePermMatrix {n : ℕ}
    (U V : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  (U.permMatrix ℂ).conjTranspose * V.permMatrix ℂ

/-- The relative permutation matrix of identity and the swap squares to `I`. -/
theorem relative_swap_matrix_sq :
    relativePermMatrix (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1) ^ 2 = 1 := by
  simp only [relativePermMatrix, Matrix.permMatrix_one,
    Matrix.conjTranspose_one, one_mul]
  rw [pow_two, ← Matrix.permMatrix_mul]
  have h : Equiv.swap (0 : Fin 2) 1 * Equiv.swap 0 1 = 1 := by decide
  rw [h]
  exact Matrix.permMatrix_one

#print axioms B117.relative_swap_matrix_sq

end B117


/-! ## B79 — the discriminant winds by an integer, and the factor two

Integrated from `.ultramath/smwvvnwls/m8/B79.lean`.
-/

open scoped ComplexConjugate

namespace B79

noncomputable section

/-- A nonzero continuous complex loop has a continuous unwrapped argument whose
endpoint change, divided by `2π`, is an integer. -/
theorem exists_integer_winding (d : ℝ → ℂ) (hd : Continuous d)
    (hd0 : ∀ t, d t ≠ 0) (hloop : d 1 = d 0) :
    ∃ θ : C(ℝ, ℝ), ∃ n : ℤ,
      (∀ t, d t = ‖d t‖ * Complex.exp (θ t * Complex.I)) ∧
      (θ 1 - θ 0) / (2 * Real.pi) = n := by
  let u : ℝ → ℂ := fun t => d t / ‖d t‖
  have hu : Continuous u := by
    exact hd.div (Complex.continuous_ofReal.comp hd.norm)
      (fun t => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hd0 t)))
  let γ : C(ℝ, Circle) :=
    ⟨fun t => ⟨u t, by
      simp [Submonoid.unitSphere, u, norm_ne_zero_iff.mpr (hd0 t)]⟩, by
      apply Continuous.subtype_mk
      exact hu⟩
  obtain ⟨θ, ⟨hθ0, hθ⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts γ 0
      (Complex.arg (γ 0)) (Circle.exp_arg (γ 0))
  have hlift (t : ℝ) : Circle.exp (θ t) = γ t := by
    simpa [Function.comp_apply] using congrFun hθ t
  have hcircle : Circle.exp (θ 1) = Circle.exp (θ 0) := by
    rw [hlift, hlift]
    apply Circle.ext
    change d 1 / (‖d 1‖ : ℂ) = d 0 / (‖d 0‖ : ℂ)
    rw [hloop]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hcircle
  refine ⟨θ, n, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun z : Circle => (z : ℂ)) (hlift t)
    have ht' : Complex.exp (θ t * Complex.I) = d t / ‖d t‖ := by
      change Complex.exp (θ t * Complex.I) = d t / ‖d t‖ at ht
      exact ht
    calc
      d t = (‖d t‖ : ℂ) * (d t / ‖d t‖) := by
        field_simp [norm_ne_zero_iff.mpr (hd0 t)]
      _ = ‖d t‖ * Complex.exp (θ t * Complex.I) := by rw [← ht']
  · rw [hn]
    field_simp [Real.pi_ne_zero]
    ring

/-- The standard two-by-two exceptional-point family. -/
def H (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; z, 0]

/-- The characteristic-polynomial discriminant `(tr A)^2 - 4 det A`. -/
def disc (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := A.trace ^ 2 - 4 * A.det

lemma disc_H (z : ℂ) : disc (H z) = 4 * z := by
  simp [disc, H, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- If `λ² = z`, the two eigenvalues are `λ` and `-λ`; the square of their
continuously tracked difference is the discriminant. -/
lemma difference_sq_eq_disc (z l : ℂ) (hl : l ^ 2 = z) :
    (l - -l) ^ 2 = disc (H z) := by
  rw [disc_H, ← hl]
  ring

/-- One circuit of the exceptional point at `z = 0`, parameterized by turns. -/
def z (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

/-- A continuously tracked eigenvalue branch on that circuit. -/
def lambda (t : ℝ) : ℂ := Complex.exp ((Real.pi * t : ℝ) * Complex.I)

lemma lambda_sq (t : ℝ) : lambda t ^ 2 = z t := by
  rw [lambda, ← Complex.exp_nat_mul, z]
  congr 1
  push_cast
  ring

lemma discriminant_eq_difference_sq (t : ℝ) :
    4 * z t = (2 * lambda t) ^ 2 := by
  rw [mul_pow, lambda_sq]
  norm_num

lemma z_zero : z 0 = 1 := by simp [z]

lemma z_one : z 1 = 1 := by
  simp [z]

lemma z_ne_zero (t : ℝ) : z t ≠ 0 := Complex.exp_ne_zero _

lemma z_continuous : Continuous z := by
  unfold z
  fun_prop

lemma discriminant_loop : (4 : ℂ) * z 1 = 4 * z 0 := by rw [z_zero, z_one]

lemma discriminant_continuous : Continuous (fun t => (4 : ℂ) * z t) :=
  continuous_const.mul z_continuous

lemma discriminant_ne_zero (t : ℝ) : (4 : ℂ) * z t ≠ 0 :=
  mul_ne_zero (by norm_num) (z_ne_zero t)

lemma lambda_one_eq_neg_lambda_zero : lambda 1 = -lambda 0 := by
  simp [lambda, Complex.exp_pi_mul_I]

/-- Without closure, the same calculation for the eigenvalue branch gives `1/2`,
not an integer. -/
lemma eigenvalue_phase_change_one_half :
    (Real.pi * 1 - Real.pi * 0) / (2 * Real.pi) = (1 / 2 : ℝ) := by
  calc
    (Real.pi * 1 - Real.pi * 0) / (2 * Real.pi) = Real.pi / (2 * Real.pi) := by ring
    _ = (1 / 2 : ℝ) := by field_simp [Real.pi_ne_zero]

/-- The literal assertion that there is no algebraic eigenvector at the
collision would be false: the nilpotent matrix `H 0` has `(1, 0)` as one. -/
lemma collision_has_eigenvector :
    Matrix.mulVec (H 0) ![1, 0] = (0 : Fin 2 → ℂ) ∧
      ![1, 0] ≠ (0 : Fin 2 → ℂ) := by
  constructor
  · ext i
    fin_cases i <;> simp [H, Matrix.mulVec]
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

/-- The discriminant's unwrapped phase on the explicit circuit. -/
def theta (t : ℝ) : ℝ := 2 * Real.pi * t

lemma theta_eq_two_eigenvalue_phase (t : ℝ) :
    theta t = 2 * (Real.pi * t) := by
  unfold theta
  ring

lemma example_winding_one :
    (theta 1 - theta 0) / (2 * Real.pi) = ((1 : ℤ) : ℝ) := by
  simp [theta]

lemma discriminant_norm (t : ℝ) : ‖(4 : ℂ) * z t‖ = 4 := by
  simp [z, Complex.norm_exp]

lemma discriminant_unwrapped_arg (t : ℝ) :
    (4 : ℂ) * z t = ‖(4 : ℂ) * z t‖ * Complex.exp (theta t * Complex.I) := by
  rw [discriminant_norm]
  rfl

/-- On the exceptional-point circuit, the displayed discriminant really has
`theta` as an unwrapped argument, and its normalized phase change is `1 : ℤ`. -/
theorem exceptional_point_winding :
    (∀ t, (4 : ℂ) * z t =
      ‖(4 : ℂ) * z t‖ * Complex.exp (theta t * Complex.I)) ∧
    (theta 1 - theta 0) / (2 * Real.pi) = ((1 : ℤ) : ℝ) :=
  ⟨discriminant_unwrapped_arg, example_winding_one⟩

end
end B79

#print axioms B79.exists_integer_winding
#print axioms B79.disc_H
#print axioms B79.difference_sq_eq_disc
#print axioms B79.lambda_sq
#print axioms B79.discriminant_eq_difference_sq
#print axioms B79.z_zero
#print axioms B79.z_one
#print axioms B79.z_ne_zero
#print axioms B79.z_continuous
#print axioms B79.discriminant_loop
#print axioms B79.discriminant_continuous
#print axioms B79.discriminant_ne_zero
#print axioms B79.lambda_one_eq_neg_lambda_zero
#print axioms B79.eigenvalue_phase_change_one_half
#print axioms B79.collision_has_eigenvector
#print axioms B79.theta_eq_two_eigenvalue_phase
#print axioms B79.example_winding_one
#print axioms B79.discriminant_norm
#print axioms B79.discriminant_unwrapped_arg
#print axioms B79.exceptional_point_winding


/-! ## B81 — the curvature sum rule by antisymmetry

Integrated from `.ultramath/smwvvnwls/m6/work/B81.lean`.
-/

namespace B81

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The antisymmetrised off-diagonal summand in B81.  `N b c` represents
`⟨L b|∂ₙT|R c⟩`, and `K b c` represents `⟨L b|∂ₖT|R c⟩`.
The `if` is exactly the exclusion `c ≠ b`; no diagonal term is inserted. -/
def summand (N K : ι → ι → ℂ) (lam : ι → ℂ) (b c : ι) : ℂ := by
  classical
  exact if c = b then 0 else
    (N b c * K c b - K b c * N c b) / (lam b - lam c) ^ 2

/-- The curvature of band `b`, using exactly the card's `c ≠ b` sum. -/
def curvature (N K : ι → ι → ℂ) (lam : ι → ℂ) (b : ι) : ℂ :=
  ∑ c : ι, summand N K lam b c

lemma summand_swap (N K : ι → ι → ℂ) (lam : ι → ℂ) (b c : ι) :
    summand N K lam c b = -summand N K lam b c := by
  classical
  unfold summand
  by_cases h : c = b
  · subst c
    simp
  · have h' : b ≠ c := Ne.symm h
    simp only [h, h', ite_false]
    rw [show lam c - lam b = -(lam b - lam c) by abel, neg_sq]
    ring

/-- **B81 sum rule.**  The finite band curvatures sum to zero.

No simplicity or nondegeneracy hypothesis is needed: when `lam b = lam c`,
both off-diagonal paired terms use division by zero and vanish, while every
other pair cancels under `(b,c) ↦ (c,b)`. -/
theorem curvature_sum_eq_zero (N K : ι → ι → ℂ) (lam : ι → ℂ) :
    (∑ b : ι, curvature N K lam b) = 0 := by
  classical
  have h : (∑ b : ι, curvature N K lam b) =
      -(∑ b : ι, curvature N K lam b) := by
    calc
      (∑ b : ι, curvature N K lam b) =
          ∑ c : ι, ∑ b : ι, summand N K lam b c := by
            unfold curvature
            exact Finset.sum_comm
      _ = ∑ b : ι, ∑ c : ι, -summand N K lam b c := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro c _
            exact summand_swap N K lam b c
      _ = -(∑ b : ι, curvature N K lam b) := by
            unfold curvature
            simp
  exact CharZero.eq_neg_self_iff.mp h

/-- At a collision the corresponding off-diagonal summands are zero in the
literal complex-field transcription (`a / 0 = 0`), so the proof still applies. -/
lemma summand_of_eigenvalue_eq (N K : ι → ι → ℂ) {lam : ι → ℂ}
    {b c : ι} (h : lam b = lam c) : summand N K lam b c = 0 := by
  unfold summand
  by_cases hbc : c = b
  · simp [hbc]
  · simp [hbc, h]

/-- A concrete two-band witness: one curvature is `1`, the other is `-1`.
Thus the sum rule is not being established only for identically zero data. -/
def N2 : Bool → Bool → ℂ
  | false, true => 1
  | _, _ => 0

def K2 : Bool → Bool → ℂ
  | true, false => 1
  | _, _ => 0

def lam2 : Bool → ℂ
  | false => 0
  | true => 1

theorem two_band_curvature_false : curvature N2 K2 lam2 false = 1 := by
  norm_num [curvature, summand, N2, K2, lam2]

theorem two_band_curvature_true : curvature N2 K2 lam2 true = -1 := by
  norm_num [curvature, summand, N2, K2, lam2]

theorem two_band_curvature_ne_zero : curvature N2 K2 lam2 false ≠ 0 := by
  rw [two_band_curvature_false]
  exact one_ne_zero

#print axioms summand_swap
#print axioms curvature_sum_eq_zero
#print axioms summand_of_eigenvalue_eq
#print axioms two_band_curvature_false
#print axioms two_band_curvature_true
#print axioms two_band_curvature_ne_zero

end

end B81


/-! ## B84 — second order in the spectrum, first order in non-normality

Integrated from `.ultramath/smwvvnwls/m4/B84.lean`.
-/

open Matrix

namespace B84

noncomputable section

/-- A real symmetric two-by-two unperturbed operator. -/
def base (a d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, d]

/-- A real skew-symmetric generator. -/
def skew (e : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, e; -e, 0]

/-- The perturbation family in card B84. -/
def HN (a d e ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := base a d + ε • skew e

/-- The exact upper and lower spectral branches of `HN`. -/
def lamPlus (a d e ε : ℝ) : ℝ :=
  (a + d + Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2)) / 2

def lamMinus (a d e ε : ℝ) : ℝ :=
  (a + d - Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2)) / 2

lemma base_transpose (a d : ℝ) : (base a d).transpose = base a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [base]

lemma skew_transpose (e : ℝ) : (skew e).transpose = -skew e := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]

lemma HN_apply (a d e ε : ℝ) :
    HN a d e ε = !![a, ε * e; -(ε * e), d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HN, base, skew]

lemma HN_transpose (a d e ε : ℝ) :
    (HN a d e ε).transpose = !![a, -(ε * e); ε * e, d] := by
  rw [HN_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The two exact branches really are eigenvalues.  Away from the unperturbed
point we give continuous eigenvectors; at that point we use the coordinate axes. -/
lemma lamPlus_eigenvalue (a d e ε : ℝ) (hd : d < a)
    (hdisc : 0 ≤ (a - d)^2 - 4 * ε^2 * e^2) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (HN a d e ε).mulVec v = lamPlus a d e ε • v := by
  by_cases hε : ε * e = 0
  · refine ⟨![1, 0], by simp, ?_⟩
    have hs : Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2) = a - d := by
      have hz : 4 * ε^2 * e^2 = 0 := by
        calc
          4 * ε^2 * e^2 = 4 * (ε * e)^2 := by ring
          _ = 0 := by rw [hε]; norm_num
      rw [hz]
      simp [Real.sqrt_sq (sub_nonneg.mpr hd.le)]
    ext i
    fin_cases i <;>
      simp [HN_apply, lamPlus, hs, hε, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · let r := Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2)
    have hr : r^2 = (a - d)^2 - 4 * ε^2 * e^2 := Real.sq_sqrt hdisc
    refine ⟨![2 * ε * e, r - (a - d)], ?_, ?_⟩
    · intro hv
      have h0 : 2 * ε * e = 0 := by
        simpa only [Matrix.cons_val_zero, Pi.zero_apply] using congrFun hv 0
      exact hε (by nlinarith)
    · ext i
      fin_cases i <;>
        simp [HN_apply, lamPlus, r, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at * <;>
        nlinarith

lemma lamMinus_eigenvalue (a d e ε : ℝ) (hd : d < a)
    (hdisc : 0 ≤ (a - d)^2 - 4 * ε^2 * e^2) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (HN a d e ε).mulVec v = lamMinus a d e ε • v := by
  by_cases hε : ε * e = 0
  · refine ⟨![0, 1], by simp, ?_⟩
    have hs : Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2) = a - d := by
      have hz : 4 * ε^2 * e^2 = 0 := by
        calc
          4 * ε^2 * e^2 = 4 * (ε * e)^2 := by ring
          _ = 0 := by rw [hε]; norm_num
      rw [hz]
      simp [Real.sqrt_sq (sub_nonneg.mpr hd.le)]
    ext i
    fin_cases i <;>
      simp [HN_apply, lamMinus, hs, hε, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · let r := Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2)
    have hr : r^2 = (a - d)^2 - 4 * ε^2 * e^2 := Real.sq_sqrt hdisc
    refine ⟨![2 * ε * e, -(r + (a - d))], ?_, ?_⟩
    · intro hv
      have h0 : 2 * ε * e = 0 := by
        simpa only [Matrix.cons_val_zero, Pi.zero_apply] using congrFun hv 0
      exact hε (by nlinarith)
    · ext i
      fin_cases i <;>
        simp [HN_apply, lamMinus, r, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at * <;>
        nlinarith

/-- These are all the real eigenvalues, not merely two examples. -/
theorem real_eigenvalue_iff (a d e ε μ : ℝ) (hd : d < a)
    (hdisc : 0 ≤ (a - d)^2 - 4 * ε^2 * e^2) :
    (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (HN a d e ε).mulVec v = μ • v) ↔
      μ = lamPlus a d e ε ∨ μ = lamMinus a d e ε := by
  constructor
  · rintro ⟨v, hv, hμ⟩
    have hz : (HN a d e ε - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hμ]
      simp
    have hdet : (HN a d e ε - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hz⟩
    have hpoly : (a - μ) * (d - μ) + ε^2 * e^2 = 0 := by
      rw [HN_apply, Matrix.one_fin_two, Matrix.det_fin_two] at hdet
      simp at hdet
      nlinarith
    have hr : (Real.sqrt ((a - d)^2 - 4 * ε^2 * e^2))^2 =
        (a - d)^2 - 4 * ε^2 * e^2 := Real.sq_sqrt hdisc
    have hfactor : (μ - lamPlus a d e ε) * (μ - lamMinus a d e ε) = 0 := by
      dsimp [lamPlus, lamMinus]
      nlinarith
    rcases mul_eq_zero.mp hfactor with hp | hm
    · exact Or.inl (sub_eq_zero.mp hp)
    · exact Or.inr (sub_eq_zero.mp hm)
  · rintro (rfl | rfl)
    · exact lamPlus_eigenvalue a d e ε hd hdisc
    · exact lamMinus_eigenvalue a d e ε hd hdisc

/-- Both eigenvalue shifts are bounded by a fixed constant times `ε^2`.
Nonnegativity of the discriminant keeps these exact branches real; the strict
inequality, which holds for sufficiently small `ε`, makes them simple. -/
theorem eigenvalue_shift_quadratic (a d e ε : ℝ) (hd : d < a)
    (hdisc : 0 ≤ (a - d)^2 - 4 * ε^2 * e^2) :
    |lamPlus a d e ε - a| ≤ (2 * e^2 / (a - d)) * ε^2 ∧
    |lamMinus a d e ε - d| ≤ (2 * e^2 / (a - d)) * ε^2 := by
  let δ := a - d
  let r := Real.sqrt (δ^2 - 4 * ε^2 * e^2)
  have hδ : 0 < δ := sub_pos.mpr hd
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = δ^2 - 4 * ε^2 * e^2 := Real.sq_sqrt hdisc
  have hrle : r ≤ δ := by
    have h := Real.sqrt_le_sqrt (show δ^2 - 4 * ε^2 * e^2 ≤ δ^2 by
      nlinarith [sq_nonneg (ε * e)])
    rw [Real.sqrt_sq hδ.le] at h
    exact h
  have hprod : (δ - r) * (δ + r) = 4 * ε^2 * e^2 := by nlinarith
  have hfactor : δ * (δ - r) ≤ (δ - r) * (δ + r) := by
    calc
      δ * (δ - r) ≤ (δ + r) * (δ - r) :=
        mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hrle)
      _ = (δ - r) * (δ + r) := by ring
  have hbound : δ - r ≤ (4 * e^2 * ε^2) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith [hprod, hfactor]
  have hplus : |lamPlus a d e ε - a| = (δ - r) / 2 := by
    rw [show lamPlus a d e ε - a = (r - δ) / 2 by simp [lamPlus, δ, r]; ring]
    rw [abs_of_nonpos (by linarith)]
    ring
  have hminus : |lamMinus a d e ε - d| = (δ - r) / 2 := by
    rw [show lamMinus a d e ε - d = (δ - r) / 2 by simp [lamMinus, δ, r]; ring]
    exact abs_of_nonneg (by linarith)
  rw [hplus, hminus]
  constructor
  · calc
      (δ - r) / 2 ≤ ((4 * e^2 * ε^2) / δ) / 2 := by linarith
      _ = (2 * e^2 / δ) * ε^2 := by ring
  · calc
      (δ - r) / 2 ≤ ((4 * e^2 * ε^2) / δ) / 2 := by linarith
      _ = (2 * e^2 / δ) * ε^2 := by ring

/-- The symmetric/skew commutator expansion, valid in every dimension. -/
lemma symmetric_skew_commutator (n : Type*) [Fintype n] [DecidableEq n]
    (D E : Matrix n n ℝ) (ε : ℝ) (hD : D.transpose = D) (hE : E.transpose = -E) :
    (D + ε • E).transpose * (D + ε • E) - (D + ε • E) * (D + ε • E).transpose =
      (2 * ε) • (D * E - E * D) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, hD, hE, smul_neg, ← neg_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  module

lemma base_skew_commutator (a d e : ℝ) :
    base a d * skew e - skew e * base a d =
      !![0, e * (a - d); e * (a - d), 0] := by
  rw [base, skew, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The operator normality defect is exactly first order in `ε`. -/
theorem normality_commutator_linear (a d e ε : ℝ) :
    (HN a d e ε).transpose * HN a d e ε - HN a d e ε * (HN a d e ε).transpose =
      ε • !![0, 2 * e * (a - d); 2 * e * (a - d), 0] := by
  rw [HN, symmetric_skew_commutator (n := Fin 2) (base a d) (skew e) ε (base_transpose a d)
    (skew_transpose e), base_skew_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- In the genuinely nonnormal case, linear growth does not degenerate:
normality holds exactly at the unperturbed point. -/
theorem normal_iff_epsilon_eq_zero (a d e ε : ℝ) (hd : a ≠ d) (he : e ≠ 0) :
    HN a d e ε * (HN a d e ε).transpose = (HN a d e ε).transpose * HN a d e ε ↔ ε = 0 := by
  constructor
  · intro h
    have hc : ε • !![0, 2 * e * (a - d); 2 * e * (a - d), 0] =
        (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
      calc
        _ = (HN a d e ε).transpose * HN a d e ε - HN a d e ε * (HN a d e ε).transpose :=
          (normality_commutator_linear a d e ε).symm
        _ = 0 := sub_eq_zero.mpr h.symm
    have h01 := congrFun (congrFun hc 0) 1
    simp at h01
    rcases h01 with hε | he' | had
    · exact hε
    · exact (he he').elim
    · exact (hd (sub_eq_zero.mp had)).elim
  · rintro rfl
    have h := normality_commutator_linear a d e 0
    simp only [zero_smul, sub_eq_zero] at h
    exact h.symm

#print axioms base_transpose
#print axioms skew_transpose
#print axioms HN_apply
#print axioms HN_transpose
#print axioms lamPlus_eigenvalue
#print axioms lamMinus_eigenvalue
#print axioms real_eigenvalue_iff
#print axioms eigenvalue_shift_quadratic
#print axioms symmetric_skew_commutator
#print axioms base_skew_commutator
#print axioms normality_commutator_linear
#print axioms normal_iff_epsilon_eq_zero

end

end B84


/-! ## B88 — the axis count from the fixed-point equations

Integrated from `.ultramath/smwvvnwls/m9/B88Main.lean`.
-/

open Matrix

namespace B88

/-- A plane rotation, with cosine and sine supplied separately. -/
def rot (C S : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![C, -S; S, C]

/-- The latitude factor in the displayed Gram formula. -/
def lat (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, 0; 0, 1]

/-- The displayed Gram family for a real symmetric Q. -/
def gram (A B D c C S : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  lat c * (rot C S)ᵀ * !![A, B; B, D] * rot C S * lat c

/-- Coincidence of the two eigenvalues of a real two-by-two matrix. -/
def Degenerate (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ μ : ℝ, A = μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Expanded entries of the displayed family. -/
theorem gram_eq (A B D c C S : ℝ) :
    gram A B D c C S =
      !![c ^ 2 * (A * C ^ 2 + 2 * B * C * S + D * S ^ 2),
         c * ((D - A) * C * S + B * (C ^ 2 - S ^ 2));
         c * ((D - A) * C * S + B * (C ^ 2 - S ^ 2)),
         A * S ^ 2 - 2 * B * C * S + D * C ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, lat, rot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct] <;> ring_nf <;> simp

/-- The mass matrix reconstructed from m=(1,2,3), in the (u,v) frame:
Q = (5/8, 1/12; 1/12, 5/9). -/
noncomputable def Q123 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![5 / 8, 1 / 12; 1 / 12, 5 / 9]

/-- Q - I/2 is the rank-one positive form (3,2)(3,2)ᵀ/72. -/
theorem Q123_rank_one :
    Q123 = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (1 / 72 : ℝ) • !![3 * 3, 3 * 2; 2 * 3, 2 * 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q123]

/-- Decomposed entries for Q123, with z₁=3C+2S and z₂=3S-2C. -/
theorem gram123_eq (c C S : ℝ) (htrig : C ^ 2 + S ^ 2 = 1) :
    gram (5 / 8) (1 / 12) (5 / 9) c C S =
      !![c ^ 2 * (1 / 2 + (3 * C + 2 * S) ^ 2 / 72),
         -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72;
         -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72,
         1 / 2 + (3 * S - 2 * C) ^ 2 / 72] := by
  rw [gram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | (field_simp; nlinarith [htrig]) |
      (apply Or.inl; field_simp; nlinarith [htrig])

/-- Exact degeneracy classification for the unequal-mass matrix.  The second
Q-eigendirection is excluded because it would need c²=49/36>1. -/
theorem degenerate123_iff (c C S : ℝ) (htrig : C ^ 2 + S ^ 2 = 1)
    (hc : c ^ 2 ≤ 1) :
    Degenerate (gram (5 / 8) (1 / 12) (5 / 9) c C S) ↔
      2 * C = 3 * S ∧ c ^ 2 = 36 / 49 := by
  have hz : (3 * C + 2 * S) ^ 2 + (3 * S - 2 * C) ^ 2 = 13 := by
    nlinarith
  constructor
  · rintro ⟨μ, hμ⟩
    rw [gram123_eq _ _ _ htrig] at hμ
    have h00raw := congrFun (congrFun hμ 0) 0
    have h01raw := congrFun (congrFun hμ 0) 1
    have h11raw := congrFun (congrFun hμ 1) 1
    have h00 : c ^ 2 * (1 / 2 + (3 * C + 2 * S) ^ 2 / 72) = μ := by
      calc
        _ = (!![c ^ 2 * (1 / 2 + (3 * C + 2 * S) ^ 2 / 72),
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72;
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72,
           1 / 2 + (3 * S - 2 * C) ^ 2 / 72] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := rfl
        _ = (μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 := h00raw
        _ = μ := by simp
    have h01 : -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72 = 0 := by
      calc
        _ = (!![c ^ 2 * (1 / 2 + (3 * C + 2 * S) ^ 2 / 72),
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72;
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72,
           1 / 2 + (3 * S - 2 * C) ^ 2 / 72] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := rfl
        _ = (μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 := h01raw
        _ = 0 := by simp
    have h11 : 1 / 2 + (3 * S - 2 * C) ^ 2 / 72 = μ := by
      calc
        _ = (!![c ^ 2 * (1 / 2 + (3 * C + 2 * S) ^ 2 / 72),
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72;
           -c * (3 * C + 2 * S) * (3 * S - 2 * C) / 72,
           1 / 2 + (3 * S - 2 * C) ^ 2 / 72] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := rfl
        _ = (μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 := h11raw
        _ = μ := by simp
    have hc0 : c ≠ 0 := by
      intro hc0
      subst c
      simp at h00
      rw [← h00] at h11
      nlinarith [sq_nonneg (3 * S - 2 * C)]
    have hzprod : (3 * C + 2 * S) * (3 * S - 2 * C) = 0 := by
      have hmul : c * ((3 * C + 2 * S) * (3 * S - 2 * C)) = 0 := by
        nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left hc0
    rcases mul_eq_zero.mp hzprod with hz1 | hz2
    · have hz2sq : (3 * S - 2 * C) ^ 2 = 13 := by nlinarith
      rw [hz1] at h00
      rw [hz2sq] at h11
      rw [← h11] at h00
      norm_num at h00 h11
      have hbad : c ^ 2 = 49 / 36 := by nlinarith
      rw [hbad] at hc
      norm_num at hc
    · constructor
      · linarith
      · rw [hz2] at h11
        simp at h11
        rw [← h11] at h00
        have hz1sq : (3 * C + 2 * S) ^ 2 = 13 := by nlinarith
        rw [hz1sq] at h00
        norm_num at h00
        nlinarith
  · rintro ⟨hline, hcval⟩
    have hz2 : 3 * S - 2 * C = 0 := by linarith
    have hz1sq : (3 * C + 2 * S) ^ 2 = 13 := by nlinarith
    refine ⟨1 / 2, ?_⟩
    rw [gram123_eq _ _ _ htrig]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz2, hz1sq, hcval] <;> norm_num

/-- Necessary chart form of degeneracy.  Here `(u,v)=r(C,S)` and `r²+c²=1`;
in the Jacobi-Hopf chart, `u=2a²-1`, `v=2ab cos ψ`,
`c=2ab sin ψ`, and `b²=1-a²`. -/
theorem degenerate123_chart (u v c r C S : ℝ)
    (htrig : C ^ 2 + S ^ 2 = 1) (hc : c ^ 2 ≤ 1)
    (hu : r * C = u) (hv : r * S = v) (hr : r ^ 2 + c ^ 2 = 1)
    (hdeg : Degenerate (gram (5 / 8) (1 / 12) (5 / 9) c C S)) :
    ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
      u = 3 * ε / 7 ∧ v = 2 * ε / 7 ∧ c = 6 * δ / 7 := by
  have hclass := (degenerate123_iff c C S htrig hc).mp hdeg
  have hline := hclass.1
  have hcval := hclass.2
  have hr2 : r ^ 2 = 13 / 49 := by nlinarith
  have huvnorm : u ^ 2 + v ^ 2 = r ^ 2 := by
    calc
      u ^ 2 + v ^ 2 = r ^ 2 * (C ^ 2 + S ^ 2) := by rw [← hu, ← hv]; ring
      _ = r ^ 2 := by rw [htrig]; ring
  have hlineuv : 2 * u = 3 * v := by
    have heq : 2 * u - 3 * v = 0 := by
      calc
        2 * u - 3 * v = r * (2 * C - 3 * S) := by rw [← hu, ← hv]; ring
        _ = 0 := by rw [hline]; ring
    linarith
  have hvval : v = 2 * u / 3 := by linarith
  rw [hvval] at huvnorm
  have hu2 : u ^ 2 = 9 / 49 := by nlinarith
  refine ⟨7 * u / 3, 7 * c / 6, ?_, ?_, by ring, ?_, by ring⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Conversely, all four sign choices give a degeneracy, so the necessary
chart conditions are exhaustive and non-vacuous. -/
theorem degenerate123_at_signs (ε δ : ℝ) (hε : ε ^ 2 = 1) (hδ : δ ^ 2 = 1) :
    Degenerate (gram (5 / 8) (1 / 12) (5 / 9) (6 * δ / 7)
      (3 * ε / Real.sqrt 13) (2 * ε / Real.sqrt 13)) := by
  have h13 : (Real.sqrt 13 : ℝ) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have h13pos : (0 : ℝ) < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  have h13ne : Real.sqrt 13 ≠ 0 := ne_of_gt h13pos
  have htrig : (3 * ε / Real.sqrt 13) ^ 2 +
      (2 * ε / Real.sqrt 13) ^ 2 = 1 := by
    calc
      _ = 13 * ε ^ 2 / (Real.sqrt 13) ^ 2 := by ring
      _ = 13 * ε ^ 2 / 13 := by rw [h13]
      _ = 1 := by rw [hε]; norm_num
  have hc : (6 * δ / 7 : ℝ) ^ 2 ≤ 1 := by
    calc
      (6 * δ / 7 : ℝ) ^ 2 = 36 / 49 * δ ^ 2 := by ring
      _ = 36 / 49 := by rw [hδ]; ring
      _ ≤ 1 := by norm_num
  apply (degenerate123_iff _ _ _ htrig hc).mpr
  constructor
  · ring
  · calc
      (6 * δ / 7 : ℝ) ^ 2 = 36 / 49 * δ ^ 2 := by ring
      _ = 36 / 49 := by rw [hδ]; ring

/-- There are exactly two choices for each sign variable, hence exactly four
sign pairs in the chart classification. -/
theorem four_sign_choices (ε δ : ℝ) (hε : ε ^ 2 = 1) (hδ : δ ^ 2 = 1) :
    (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) := by
  have he : (ε - 1) * (ε + 1) = 0 := by nlinarith
  have hd : (δ - 1) * (δ + 1) = 0 := by nlinarith
  constructor
  · rcases mul_eq_zero.mp he with h | h
    · left
      linarith
    · right
      linarith
  · rcases mul_eq_zero.mp hd with h | h
    · left
      linarith
    · right
      linarith

/-- The two signs of the horizontal eigenline are exactly the two displayed
values of a²: u=2a²-1=3/7 gives 5/7, while u=-3/7 gives 2/7. -/
theorem displayed_a_squared (a ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hu : 2 * a ^ 2 - 1 = 3 * ε / 7) : a ^ 2 = 5 / 7 ∨ a ^ 2 = 2 / 7 := by
  rcases hε with rfl | rfl
  · left
    nlinarith
  · right
    nlinarith

/-- The two displayed squared coordinates sum to one. -/
theorem displayed_axis_coordinates_sum_one :
    (5 / 7 : ℝ) + 2 / 7 = 1 := by norm_num

/-- The three side-coefficient vectors for masses (1,2,3), in the (u,v)
frame.  They come from μ₀₁=2/3, μ₂=3/2, α=2/3 and β=1/3. -/
noncomputable def sideCoeff123 : Fin 3 → Fin 2 → ℝ :=
  ![![3 / 4, 0], ![0, 2 / 3], ![-(1 / 4), -(1 / 3)]]

/-- Q is the sum of the three side-coefficient outer products. -/
theorem Q123_from_side_coefficients :
    Q123 = ∑ k, Matrix.of fun i j => sideCoeff123 k i * sideCoeff123 k j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q123, sideCoeff123, Fin.sum_univ_three] <;> norm_num

/-- For equal masses Q is scalar, and the displayed Gram family is
longitude-independent. -/
theorem equal_mass_gram_eq (q c C S : ℝ) (htrig : C ^ 2 + S ^ 2 = 1) :
    gram q 0 q c C S = !![q * c ^ 2, 0; 0, q] := by
  rw [gram_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
    linear_combination c ^ 2 * q * htrig
  · simp
  · simp
  · simp
    linear_combination q * htrig

/-- Equal masses have exactly the two polar degeneracies c=±1. -/
theorem equal_mass_degenerate_iff (q c C S : ℝ) (hq : 0 < q)
    (htrig : C ^ 2 + S ^ 2 = 1) :
    Degenerate (gram q 0 q c C S) ↔ c ^ 2 = 1 := by
  constructor
  · rintro ⟨μ, hμ⟩
    rw [equal_mass_gram_eq _ _ _ _ htrig] at hμ
    have h00 := congrFun (congrFun hμ 0) 0
    have h11 := congrFun (congrFun hμ 1) 1
    simp at h00 h11
    rw [← h11] at h00
    have hp : (c ^ 2 - 1) * q = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hc | hq0
    · linarith
    · exact (ne_of_gt hq hq0).elim
  · intro hc
    refine ⟨q, ?_⟩
    rw [equal_mass_gram_eq _ _ _ _ htrig]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]

#print axioms gram_eq
#print axioms Q123_rank_one
#print axioms gram123_eq
#print axioms degenerate123_iff
#print axioms degenerate123_chart
#print axioms degenerate123_at_signs
#print axioms four_sign_choices
#print axioms displayed_a_squared
#print axioms displayed_axis_coordinates_sum_one
#print axioms Q123_from_side_coefficients
#print axioms equal_mass_gram_eq
#print axioms equal_mass_degenerate_iff

/-- The explicit spectrum of the reconstructed unequal-mass Q. -/
theorem Q123_eigenvectors :
    Q123 *ᵥ ![3, 2] = (49 / 72 : ℝ) • ![3, 2] ∧
      Q123 *ᵥ ![-2, 3] = (1 / 2 : ℝ) • ![-2, 3] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [Q123, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

#print axioms Q123_eigenvectors

end B88


/-! ## B143 — the exact spectra, and the mixed rates are not 1/eps (OVERREACH)

Integrated from `.ultramath/smwvvnwls/m12/B143.lean`.
-/

open Matrix Filter
open scoped Topology

/-! Finite-dimensional checks for card B143.  `S` is G^(-1/2) and
`K` is G^(-1) in the displayed congruence operator. -/
namespace B143

noncomputable section

variable (ε : ℝ)

def G3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - 2 * ε, 0, 0;
     0, ε, 0;
     0, 0, ε]

def S3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(Real.sqrt (1 - 2 * ε))⁻¹, 0, 0;
     0, (Real.sqrt ε)⁻¹, 0;
     0, 0, (Real.sqrt ε)⁻¹]

def K3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 - 2 * ε)⁻¹, 0, 0;
     0, ε⁻¹, 0;
     0, 0, ε⁻¹]

def C0 {n : Type*} [Fintype n] (S K G H : Matrix n n ℝ) : Matrix n n ℝ :=
  S * H * S - (Matrix.trace (K * H)) • G

def Hdiag : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, 1, 0;
     0, 0, -1]

def HdiagLarge : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-2, 0, 0;
     0, 1, 0;
     0, 0, 1]

def Hoff23 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

def Hoff12 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 0]

def Hoff13 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
     0, 0, 0;
     1, 0, 0]

theorem corner_small_diagonal_eigen (hε : 0 < ε) :
    C0 (S3 ε) (K3 ε) (G3 ε) Hdiag = (ε⁻¹) • Hdiag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S3, K3, G3, Hdiag, Matrix.trace,
      Fin.sum_univ_three] <;> field_simp <;> simp [Real.sq_sqrt hε.le]

theorem corner_small_frame_eigen (hε : 0 < ε) :
    C0 (S3 ε) (K3 ε) (G3 ε) Hoff23 = (ε⁻¹) • Hoff23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S3, K3, G3, Hoff23, Matrix.trace,
      Fin.sum_univ_three] <;> field_simp <;> simp [Real.sq_sqrt hε.le]

theorem corner_large_diagonal_eigen (hε : 0 < ε) (hA : 0 < 1 - 2 * ε) :
    C0 (S3 ε) (K3 ε) (G3 ε) HdiagLarge =
      ((6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε))) • HdiagLarge := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S3, K3, G3, HdiagLarge, Matrix.trace,
      Fin.sum_univ_three] <;> field_simp <;>
    simp [Real.sq_sqrt hε.le, Real.sq_sqrt hA.le] <;> ring_nf <;> simp [hε.ne']

theorem corner_mixed12_eigen (hε : 0 < ε) (hA : 0 < 1 - 2 * ε) :
    C0 (S3 ε) (K3 ε) (G3 ε) Hoff12 =
      ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) • Hoff12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S3, K3, G3, Hoff12, Matrix.trace,
      Fin.sum_univ_three] <;> field_simp <;>
    simp [Real.sq_sqrt hε.le, Real.sq_sqrt hA.le]

theorem corner_mixed13_eigen (hε : 0 < ε) (hA : 0 < 1 - 2 * ε) :
    C0 (S3 ε) (K3 ε) (G3 ε) Hoff13 =
      ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) • Hoff13 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S3, K3, G3, Hoff13, Matrix.trace,
      Fin.sum_univ_three] <;> field_simp <;>
    simp [Real.sq_sqrt hε.le, Real.sq_sqrt hA.le]

end


theorem corner_mixed_scaled (ε : ℝ) (hε : 0 < ε) (hA : 0 < 1 - 2 * ε) :
    ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) =
      Real.sqrt ε / Real.sqrt (1 - 2 * ε) := by
  have hsε : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hε)
  have hsA : Real.sqrt (1 - 2 * ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hA)
  field_simp
  rw [Real.sq_sqrt hε.le]

theorem corner_mixed_scaled_tendsto : Tendsto
    (fun ε : ℝ => ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹))
    (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun ε : ℝ => Real.sqrt ε / Real.sqrt (1 - 2 * ε)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have ht : Tendsto (fun ε : ℝ => Real.sqrt ε / Real.sqrt (1 - 2 * ε))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ ht
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 : ℝ) / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hεlt
  have hA : 0 < 1 - 2 * ε := by linarith
  have hsε : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hε)
  have hsA : Real.sqrt (1 - 2 * ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hA)
  field_simp
  rw [Real.sq_sqrt hε.le]



section Smooth

noncomputable def G2 (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - ε, 0;
     0, ε]

noncomputable def S2 (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(Real.sqrt (1 - ε))⁻¹, 0;
     0, (Real.sqrt ε)⁻¹]

noncomputable def K2 (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - ε)⁻¹, 0;
     0, ε⁻¹]

def H2diag : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

def H2frame : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

theorem smooth_diagonal_eigen (ε : ℝ) (hε : 0 < ε) (hB : 0 < 1 - ε) :
    C0 (S2 ε) (K2 ε) (G2 ε) H2diag =
      ((1 - 2 * ε + 2 * ε ^ 2) / (ε * (1 - ε))) • H2diag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S2, K2, G2, H2diag, Matrix.trace,
      Fin.sum_univ_two] <;> field_simp <;>
    simp [Real.sq_sqrt hε.le, Real.sq_sqrt hB.le] <;> ring_nf <;>
    simp [hε.ne']

theorem smooth_frame_eigen (ε : ℝ) (hε : 0 < ε) (hB : 0 < 1 - ε) :
    C0 (S2 ε) (K2 ε) (G2 ε) H2frame =
      ((Real.sqrt (1 - ε) * Real.sqrt ε)⁻¹) • H2frame := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C0, S2, K2, G2, H2frame, Matrix.trace,
      Fin.sum_univ_two] <;> ring

theorem smooth_diagonal_expansion (ε : ℝ) (hε : ε ≠ 0) (hB : 1 - ε ≠ 0) :
    (1 - 2 * ε + 2 * ε ^ 2) / (ε * (1 - ε)) =
      ε⁻¹ - 1 + ε / (1 - ε) := by
  field_simp
  ring

end Smooth

theorem trace_congruence {n : Type*} [Fintype n] (S K H : Matrix n n ℝ)
    (hSS : S * S = K) :
    Matrix.trace (S * H * S) = Matrix.trace (K * H) := by
  calc
    Matrix.trace (S * H * S) = Matrix.trace (S * (S * H)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((S * S) * H) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (K * H) := by rw [hSS]


/-- The corner's third fast eigendirection has inverse-epsilon rate, with
constant `-2` rather than the smooth-wall constant `-1`. -/
theorem corner_large_diagonal_expansion (ε : ℝ) (hε : ε ≠ 0)
    (hA : 1 - 2 * ε ≠ 0) :
    (6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε)) =
      ε⁻¹ - 2 + 2 * ε / (1 - 2 * ε) := by
  field_simp
  ring

/-- `Tr G = 1` for the corner family. -/
theorem corner_gram_trace (ε : ℝ) : Matrix.trace (G3 ε) = 1 := by
  simp [G3, Matrix.trace, Fin.sum_univ_three]
  ring

/-- The five exhibited corner directions are traceless. -/
theorem corner_directions_traceless :
    Matrix.trace Hdiag = 0 ∧ Matrix.trace HdiagLarge = 0 ∧
      Matrix.trace Hoff12 = 0 ∧ Matrix.trace Hoff13 = 0 ∧
      Matrix.trace Hoff23 = 0 := by
  norm_num [Matrix.trace, Fin.sum_univ_three, Hdiag, HdiagLarge,
    Hoff12, Hoff13, Hoff23]

/-- `Tr G = 1` for the smooth-wall model. -/
theorem smooth_gram_trace (ε : ℝ) : Matrix.trace (G2 ε) = 1 := by
  simp [G2, Matrix.trace, Fin.sum_univ_two]

/-- The two exhibited smooth-wall directions are traceless. -/
theorem smooth_directions_traceless :
    Matrix.trace H2diag = 0 ∧ Matrix.trace H2frame = 0 := by
  norm_num [Matrix.trace, Fin.sum_univ_two, H2diag, H2frame]

/-- A rate cannot have an inverse-epsilon lower bound after its scaled
values tend to zero. -/
theorem not_inverse_epsilon_of_scaled_tendsto_zero (r : ℝ → ℝ)
    (h : Tendsto (fun ε => ε * r ε) (𝓝[>] 0) (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ ε * r ε := by
  rintro ⟨c, hc, hbound⟩
  have hupper : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * r ε < c / 2 :=
    h.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < c / 2))
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hupper, hbound] with ε hu hl
    linarith
  exact he.exists.elim (fun _ h => h)

/-- The unqualified full-spectrum corner claim is false: the mixed
frame directions have no positive asymptotic lower bound `c / ε`. -/
theorem corner_mixed_not_inverse_epsilon :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c ≤ ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) :=
  not_inverse_epsilon_of_scaled_tendsto_zero _ corner_mixed_scaled_tendsto

/-- Exact rational witness: no rounded decimal is involved. -/
theorem corner_numeric_witness :
    ((Real.sqrt (1 - 2 * (144 / 5329 : ℝ)) *
      Real.sqrt (144 / 5329 : ℝ))⁻¹) = 5329 / 852 ∧
    (144 / 5329 : ℝ) * ((Real.sqrt (1 - 2 * (144 / 5329 : ℝ)) *
      Real.sqrt (144 / 5329 : ℝ))⁻¹) = 12 / 71 ∧
    (12 / 71 : ℝ) < 1 / 4 := by
  have hε : Real.sqrt (144 / 5329 : ℝ) = 12 / 73 := by
    rw [Real.sqrt_eq_cases] <;> norm_num
  have hA : Real.sqrt (1 - 2 * (144 / 5329 : ℝ)) = 71 / 73 := by
    convert (show Real.sqrt (5041 / 5329 : ℝ) = 71 / 73 by
      rw [Real.sqrt_eq_cases] <;> norm_num) using 1 <;> norm_num
  refine ⟨?_, ?_, by norm_num⟩ <;> rw [hε, hA] <;> norm_num


/-- The five corner eigendirections as a family indexed by `Fin 5`. -/
def cornerDirections : Fin 5 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![HdiagLarge, Hdiag, Hoff12, Hoff13, Hoff23]


theorem corner_directions_linearIndependent :
    LinearIndependent ℝ cornerDirections := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrFun (congrFun hg (0 : Fin 3)) (0 : Fin 3)
  have h01 := congrFun (congrFun hg (0 : Fin 3)) (1 : Fin 3)
  have h02 := congrFun (congrFun hg (0 : Fin 3)) (2 : Fin 3)
  have h12 := congrFun (congrFun hg (1 : Fin 3)) (2 : Fin 3)
  have h11 := congrFun (congrFun hg (1 : Fin 3)) (1 : Fin 3)
  simp [cornerDirections, Fin.sum_univ_five, HdiagLarge, Hdiag,
    Hoff12, Hoff13, Hoff23] at h00 h01 h02 h12 h11
  fin_cases i <;> simp_all



theorem corner_traceless_symmetric_span (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : H.transpose = H) (htrace : Matrix.trace H = 0) :
    H = (-H 0 0 / 2) • HdiagLarge + (H 1 1 + H 0 0 / 2) • Hdiag +
      H 0 1 • Hoff12 + H 0 2 • Hoff13 + H 1 2 • Hoff23 := by
  have h10 : H 1 0 = H 0 1 := by
    have h := congrFun (congrFun hsym (0 : Fin 3)) (1 : Fin 3)
    simpa [Matrix.transpose_apply] using h
  have h20 : H 2 0 = H 0 2 := by
    have h := congrFun (congrFun hsym (0 : Fin 3)) (2 : Fin 3)
    simpa [Matrix.transpose_apply] using h
  have h21 : H 2 1 = H 1 2 := by
    have h := congrFun (congrFun hsym (1 : Fin 3)) (2 : Fin 3)
    simpa [Matrix.transpose_apply] using h
  simp [Matrix.trace, Fin.sum_univ_three] at htrace
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HdiagLarge, Hdiag, Hoff12, Hoff13, Hoff23] <;>
    nlinarith



theorem corner_large_scaled_tendsto : Tendsto
    (fun ε : ℝ => ε * ((6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε))))
    (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt
      (fun ε : ℝ => 1 - 2 * ε + 2 * ε ^ 2 / (1 - 2 * ε)) 0 := by
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have ht : Tendsto (fun ε : ℝ => 1 - 2 * ε + 2 * ε ^ 2 / (1 - 2 * ε))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ ht
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 : ℝ) / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hεlt
  change 0 < ε at hε
  have hA : 1 - 2 * ε ≠ 0 := by linarith
  have hε0 : ε ≠ 0 := ne_of_gt hε
  field_simp [hε0, hA]
  ring


theorem corner_top_three_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    (Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹ < ε⁻¹ ∧
    (Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹ <
      (6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε)) := by
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) < 1 / 2 :=
    corner_mixed_scaled_tendsto.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 / 2 <
      ε * ((6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε))) :=
    corner_large_scaled_tendsto.eventually
      (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  filter_upwards [hm, hL, self_mem_nhdsWithin] with ε hm hL hε
  change 0 < ε at hε
  have hs : ε * ε⁻¹ = 1 := by field_simp
  constructor
  · have h : ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) < ε * ε⁻¹ := by
      rw [hs]
      linarith
    exact lt_of_mul_lt_mul_left h hε.le
  · have h : ε * ((Real.sqrt (1 - 2 * ε) * Real.sqrt ε)⁻¹) <
        ε * ((6 * ε ^ 2 - 4 * ε + 1) / (ε * (1 - 2 * ε))) := by linarith
    exact lt_of_mul_lt_mul_left h hε.le

#print axioms corner_small_diagonal_eigen
#print axioms corner_small_frame_eigen
#print axioms corner_large_diagonal_eigen
#print axioms corner_mixed12_eigen
#print axioms corner_mixed13_eigen
#print axioms corner_mixed_scaled
#print axioms corner_mixed_scaled_tendsto
#print axioms smooth_diagonal_eigen
#print axioms smooth_frame_eigen
#print axioms smooth_diagonal_expansion
#print axioms trace_congruence
#print axioms corner_large_diagonal_expansion
#print axioms corner_gram_trace
#print axioms corner_directions_traceless
#print axioms smooth_gram_trace
#print axioms smooth_directions_traceless
#print axioms not_inverse_epsilon_of_scaled_tendsto_zero
#print axioms corner_mixed_not_inverse_epsilon
#print axioms corner_numeric_witness
#print axioms corner_directions_linearIndependent
#print axioms corner_traceless_symmetric_span
#print axioms corner_large_scaled_tendsto
#print axioms corner_top_three_eventually

end B143


/-! ## B55 — the three wall radii as exact roots

Integrated from `.ultramath/smwvvnwls/m11/B55.lean`.
-/

open Complex

namespace B55

/-- The complex parameter `s` in card B55, specialised to `m = 7/20`, `γ = 1`. -/
noncomputable def s (k : ℝ) : ℂ :=
  (k : ℂ) ^ 2 + ((7 / 20 : ℂ) + Complex.I) ^ 2

/-- The determinant formula displayed in card B55 (up to the harmless explicit
specialisation of `m` and `γ`). -/
noncomputable def detg (k : ℝ) : ℝ :=
  (1 / 16 : ℝ) * (1 / s k).re *
    ((1 / s k).re - k ^ 2 * (1 / (s k) ^ 2).re)

lemma s_re (k : ℝ) : (s k).re = k ^ 2 - 351 / 400 := by
  norm_num [s, pow_two, Complex.mul_re, Complex.mul_im]
  ring

lemma s_im (k : ℝ) : (s k).im = 7 / 10 := by
  norm_num [s, pow_two, Complex.mul_re, Complex.mul_im]

lemma s_ne_zero (k : ℝ) : s k ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  rw [s_im] at hi
  norm_num at hi

lemma inv_s_re (k : ℝ) :
    (1 / s k).re = (k ^ 2 - 351 / 400) /
      ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply, s_re, s_im]
  ring

lemma inv_s_sq_re (k : ℝ) :
    (1 / (s k) ^ 2).re =
      ((k ^ 2 - 351 / 400) ^ 2 - (7 / 10 : ℝ) ^ 2) /
        ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) ^ 2 := by
  have hD : (k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2 ≠ 0 := by
    positivity
  rw [one_div, ← inv_pow, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, s_re, s_im]
  field_simp [hD]

/-- Clear the two complex denominators in the displayed determinant formula. -/
lemma detg_eq (k : ℝ) :
    detg k =
      (k ^ 2 - 351 / 400) *
        ((k ^ 2 - 351 / 400) *
            ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) -
          k ^ 2 * ((k ^ 2 - 351 / 400) ^ 2 - (7 / 10 : ℝ) ^ 2)) /
        (16 * ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) ^ 3) := by
  have hD : (k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2 ≠ 0 := by
    positivity
  rw [detg, inv_s_re, inv_s_sq_re]
  field_simp [hD]

/-- The determinant numerator factors into the three exact wall equations. -/
lemma detg_eq_factored (k : ℝ) :
    detg k =
      (-(k ^ 2 - 351 / 400) * (5200 * k ^ 2 - 12123) *
        (10800 * k ^ 2 - 5837)) /
        (1024000000 * ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) ^ 3) := by
  have hD : (k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2 ≠ 0 := by
    positivity
  rw [detg_eq]
  field_simp [hD]
  ring

/-- Exact zero locus of the displayed B55 determinant for `m = 7/20`, `γ = 1`.
The three printed wall radii are decimal roundings of square roots of these
three rational values of `k²`; they are not themselves exact equalities. -/
theorem detg_eq_zero_iff (k : ℝ) :
    detg k = 0 ↔
      k ^ 2 = 351 / 400 ∨ k ^ 2 = 5837 / 10800 ∨ k ^ 2 = 12123 / 5200 := by
  have hden : 1024000000 *
      ((k ^ 2 - 351 / 400) ^ 2 + (7 / 10 : ℝ) ^ 2) ^ 3 ≠ 0 := by
    positivity
  rw [detg_eq_factored]
  constructor
  · intro h
    have hN := (div_eq_zero_iff.mp h).resolve_right hden
    rcases mul_eq_zero.mp hN with hN | hN
    · rcases mul_eq_zero.mp hN with h | h
      · left
        linarith [neg_eq_zero.mp h]
      · right
        right
        linarith
    · right
      left
      linarith
  · rintro (h | h | h) <;>
      rw [div_eq_zero_iff] <;>
      left <;> rw [h] <;> norm_num

/-- The inner printed radius is the correct nearest rounding to six decimal
places: its exact value lies in `[0.7351615, 0.7351625)`. -/
theorem inner_wall_rounding :
    (7351615 / 10000000 : ℝ) ≤ Real.sqrt (5837 / 10800) ∧
      Real.sqrt (5837 / 10800) < 7351625 / 10000000 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

/-- The middle printed radius is likewise a rounding, not an exact equality. -/
theorem middle_wall_rounding :
    (9367495 / 10000000 : ℝ) ≤ Real.sqrt (351 / 400) ∧
      Real.sqrt (351 / 400) < 9367505 / 10000000 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

/-- The remaining outer decimal `1.526875` is certified as the nearest
six-decimal rounding of the exact outer wall radius. -/
theorem outer_wall_rounding :
    (15268745 / 10000000 : ℝ) ≤ Real.sqrt (12123 / 5200) ∧
      Real.sqrt (12123 / 5200) < 15268755 / 10000000 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

/-- The exact outer radius really is a zero of the displayed determinant. -/
theorem detg_outer_wall : detg (Real.sqrt (12123 / 5200)) = 0 := by
  apply (detg_eq_zero_iff _).2
  right
  right
  exact Real.sq_sqrt (by norm_num)

/-- Under a literal exact reading, the printed decimal is not a wall. This is
not an objection to its intended use as a rounded numerical value. -/
theorem rounded_outer_is_not_exact_wall :
    detg (1526875 / 1000000 : ℝ) ≠ 0 := by
  intro h
  have hz := (detg_eq_zero_iff (1526875 / 1000000 : ℝ)).1 h
  norm_num at hz

end B55

#print axioms B55.s_re
#print axioms B55.s_im
#print axioms B55.s_ne_zero
#print axioms B55.inv_s_re
#print axioms B55.inv_s_sq_re
#print axioms B55.detg_eq
#print axioms B55.detg_eq_factored
#print axioms B55.detg_eq_zero_iff
#print axioms B55.inner_wall_rounding
#print axioms B55.middle_wall_rounding
#print axioms B55.outer_wall_rounding
#print axioms B55.detg_outer_wall
#print axioms B55.rounded_outer_is_not_exact_wall



/-! ## B101 — the sheet formula is the first order of the exact Airy model

Integrated from `.ultramath/smwvvnwls/m13/B101ThinFilm.lean`.
-/

open Asymptotics Filter Topology

noncomputable section

namespace B101ThinFilm

/-- `HasLinear f a b` says that, as the real variable `t` tends to zero,
`f t = a + t*b + O(t^2)`.  The error is complex, so this also covers complex
refractive indices. -/
def HasLinear (f : ℝ → ℂ) (a b : ℂ) : Prop :=
  (fun t => f t - (a + (t : ℂ) * b)) =O[𝓝 0] fun t => (t : ℂ) ^ 2

lemma hasLinear_const (a : ℂ) : HasLinear (fun _ => a) a 0 := by
  unfold HasLinear
  simpa using (isBigO_zero (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0))

lemma hasLinear_id_mul (b : ℂ) : HasLinear (fun t : ℝ => (t : ℂ) * b) 0 b := by
  unfold HasLinear
  simpa using (isBigO_zero (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0))

lemma hasLinear_affine (a b : ℂ) : HasLinear (fun t : ℝ => a + (t : ℂ) * b) a b := by
  unfold HasLinear
  simpa using (isBigO_zero (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0))

lemma HasLinear.add {f g : ℝ → ℂ} {a b c d : ℂ}
    (hf : HasLinear f a b) (hg : HasLinear g c d) :
    HasLinear (fun t => f t + g t) (a + c) (b + d) := by
  unfold HasLinear at hf hg ⊢
  exact (hf.add hg).congr_left (fun t => by ring)

lemma HasLinear.sub {f g : ℝ → ℂ} {a b c d : ℂ}
    (hf : HasLinear f a b) (hg : HasLinear g c d) :
    HasLinear (fun t => f t - g t) (a - c) (b - d) := by
  unfold HasLinear at hf hg ⊢
  exact (hf.sub hg).congr_left (fun t => by ring)

lemma HasLinear.tendsto {f : ℝ → ℂ} {a b : ℂ} (hf : HasLinear f a b) :
    Tendsto f (𝓝 0) (𝓝 a) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).pow 2
  have he : Tendsto (fun t => f t - (a + (t : ℂ) * b)) (𝓝 0) (𝓝 0) :=
    hf.trans_tendsto ht
  have ha : Tendsto (fun t : ℝ => a + (t : ℂ) * b) (𝓝 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).mul_const b)
  have h := he.add ha
  simpa only [sub_add_cancel, zero_add] using h

lemma HasLinear.bounded {f : ℝ → ℂ} {a b : ℂ} (hf : HasLinear f a b) :
    f =O[𝓝 0] (fun _ => (1 : ℂ)) :=
  hf.tendsto.isBigO_one ℂ

lemma HasLinear.mul {f g : ℝ → ℂ} {a b c d : ℂ}
    (hf : HasLinear f a b) (hg : HasLinear g c d) :
    HasLinear (fun t => f t * g t) (a * c) (a * d + b * c) := by
  have hfO : (fun t => f t - (a + (t : ℂ) * b)) =O[𝓝 0] fun t => (t : ℂ) ^ 2 := hf
  have hgO : (fun t => g t - (c + (t : ℂ) * d)) =O[𝓝 0] fun t => (t : ℂ) ^ 2 := hg
  have h1 : (fun t : ℝ => f t * (g t - (c + (t : ℂ) * d))) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
    simpa using hf.bounded.mul hgO
  have h2 : (fun t : ℝ => (f t - (a + (t : ℂ) * b)) * (c + (t : ℂ) * d)) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
    simpa using hfO.mul (hasLinear_affine c d).bounded
  have h3 : (fun t : ℝ => (a + (t : ℂ) * b) * (c + (t : ℂ) * d) -
      (a * c + (t : ℂ) * (a * d + b * c))) =O[𝓝 0] fun t => (t : ℂ) ^ 2 := by
    exact (isBigO_const_mul_self (b * d) (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0)).congr_left
      (fun t => by ring)
  unfold HasLinear
  exact ((h1.add h2).add h3).congr_left (fun (t : ℝ) => by ring)

lemma hasLinear_exp (c : ℂ) :
    HasLinear (fun t : ℝ => Complex.exp (c * (t : ℂ))) 1 c := by
  have ht : Tendsto (fun t : ℝ => c * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).const_mul c
  have h := (Complex.exp_sub_sum_range_isBigO_pow 2).comp_tendsto ht
  have h' : (fun t : ℝ => Complex.exp (c * (t : ℂ)) -
      (1 + c * (t : ℂ))) =O[𝓝 0] fun t => c ^ 2 * (t : ℂ) ^ 2 := by
    simpa [Function.comp_def, Finset.sum_range_succ, mul_pow] using h
  unfold HasLinear
  exact (h'.trans (isBigO_const_mul_self (c ^ 2) (fun t : ℝ => (t : ℂ) ^ 2)
    (𝓝 0))).congr_left (fun t => by ring)

end B101ThinFilm

namespace B101ThinFilm

lemma HasLinear.inv {f : ℝ → ℂ} {a b : ℂ} (hf : HasLinear f a b) (ha : a ≠ 0) :
    HasLinear (fun t => (f t)⁻¹) a⁻¹ (-b / a ^ 2) := by
  have hfO : (fun t => f t - (a + (t : ℂ) * b)) =O[𝓝 0] fun t => (t : ℂ) ^ 2 := hf
  have hN : (fun t : ℝ => (t : ℂ) ^ 2 * b ^ 2 -
      (f t - (a + (t : ℂ) * b)) * (a - (t : ℂ) * b)) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
    have h1 : (fun t : ℝ => (t : ℂ) ^ 2 * b ^ 2) =O[𝓝 0] fun t => (t : ℂ) ^ 2 :=
      (isBigO_const_mul_self (b ^ 2) (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0)).congr_left
        (fun t => by ring)
    have h2 : (fun t : ℝ => (f t - (a + (t : ℂ) * b)) *
        (a - (t : ℂ) * b)) =O[𝓝 0] fun t => (t : ℂ) ^ 2 := by
      simpa only [sub_eq_add_neg, neg_mul, mul_neg, mul_one] using
        hfO.mul (hasLinear_affine a (-b)).bounded
    exact h1.sub h2
  have hden : Tendsto (fun t => f t * a ^ 2) (𝓝 0) (𝓝 (a * a ^ 2)) :=
    hf.tendsto.mul_const _
  have hden0 : a * a ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ha)
  have hR : (fun t : ℝ => ((t : ℂ) ^ 2 * b ^ 2 -
      (f t - (a + (t : ℂ) * b)) * (a - (t : ℂ) * b)) / (f t * a ^ 2)) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
    have h := hN.mul ((hden.inv₀ hden0).isBigO_one ℂ)
    simpa [div_eq_mul_inv] using h
  have hfne : ∀ᶠ t in 𝓝 (0 : ℝ), f t ≠ 0 :=
    hf.tendsto.eventually (eventually_ne_nhds ha)
  unfold HasLinear
  refine hR.congr' ?_ EventuallyEq.rfl
  filter_upwards [hfne] with t ht
  field_simp [ht, ha]
  ring

lemma HasLinear.div {f g : ℝ → ℂ} {a b c d : ℂ}
    (hf : HasLinear f a b) (hg : HasLinear g c d) (hc : c ≠ 0) :
    HasLinear (fun t => f t / g t) (a / c) ((b * c - a * d) / c ^ 2) := by
  have h := hf.mul (hg.inv hc)
  convert h using 1
  · ext t
    exact div_eq_mul_inv _ _
  · ring
  · field_simp [hc]
    ring

end B101ThinFilm

namespace B101ThinFilm

/-- Fresnel amplitude reflection coefficient for incidence from `a` into `b`. -/
def fresnel (a b : ℂ) : ℂ := (a - b) / (a + b)

/-- Exact single-film Airy reflection coefficient, read at the top face.
The exponential uses the `exp (-I*ω*t)` time convention. -/
def airyTop (n₀ N nₛ k : ℂ) (t : ℝ) : ℂ :=
  (fresnel n₀ N + fresnel N nₛ * Complex.exp (2 * Complex.I * k * N * (t : ℂ))) /
    (1 + fresnel n₀ N * fresnel N nₛ *
      Complex.exp (2 * Complex.I * k * N * (t : ℂ)))

/-- The same reflection coefficient referenced to the substrate face.  Moving
the reference plane through the ambient-equivalent distance `t` supplies the
additional inverse round-trip phase. -/
def airySubstrate (n₀ N nₛ k : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-2 * Complex.I * k * n₀ * (t : ℂ)) * airyTop n₀ N nₛ k t

/-- First-order shunt admittance of a film whose index is `N`; `ref` is the
index whose displacement current is subtracted at the declared plane. -/
def shunt (N ref k : ℂ) (t : ℝ) : ℂ :=
  -Complex.I * k * (t : ℂ) * (N ^ 2 - ref ^ 2)

/-- Reflection from the shunt-sheet admittance `Y = nₛ + y`. -/
def sheetReflection (n₀ N nₛ ref k : ℂ) (t : ℝ) : ℂ :=
  let y := shunt N ref k t
  (n₀ - (nₛ + y)) / (n₀ + (nₛ + y))

lemma hasLinear_shunt (N ref k : ℂ) :
    HasLinear (shunt N ref k) 0 (-Complex.I * k * (N ^ 2 - ref ^ 2)) := by
  unfold shunt
  convert hasLinear_id_mul (-Complex.I * k * (N ^ 2 - ref ^ 2)) using 1
  ext t
  ring

lemma fresnel_add {n₀ N nₛ : ℂ} (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0) :
    fresnel n₀ N + fresnel N nₛ =
      2 * N * (n₀ - nₛ) / ((n₀ + N) * (N + nₛ)) := by
  unfold fresnel
  field_simp [h₀N, hNs]
  ring

lemma one_add_fresnel_mul {n₀ N nₛ : ℂ} (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0) :
    1 + fresnel n₀ N * fresnel N nₛ =
      2 * N * (n₀ + nₛ) / ((n₀ + N) * (N + nₛ)) := by
  unfold fresnel
  field_simp [h₀N, hNs]
  ring

lemma one_sub_fresnel_sq {n₀ N : ℂ} (h₀N : n₀ + N ≠ 0) :
    1 - fresnel n₀ N ^ 2 = 4 * n₀ * N / (n₀ + N) ^ 2 := by
  unfold fresnel
  field_simp [h₀N]
  ring

lemma hasLinear_airyTop {n₀ N nₛ k : ℂ}
    (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0)
    (hden : 1 + fresnel n₀ N * fresnel N nₛ ≠ 0) (hsum : n₀ + nₛ ≠ 0) :
    HasLinear (airyTop n₀ N nₛ k) ((n₀ - nₛ) / (n₀ + nₛ))
      (2 * Complex.I * k * n₀ * (N ^ 2 - nₛ ^ 2) / (n₀ + nₛ) ^ 2) := by
  have hN : N ≠ 0 := by
    intro hN
    subst N
    simp only [add_zero, zero_add] at h₀N hNs
    simp [fresnel, h₀N, hNs] at hden
  have hq := hasLinear_exp (2 * Complex.I * k * N)
  have hnum := (hasLinear_const (fresnel n₀ N)).add
    ((hasLinear_const (fresnel N nₛ)).mul hq)
  have hden' := (hasLinear_const 1).add
    (((hasLinear_const (fresnel n₀ N)).mul
      (hasLinear_const (fresnel N nₛ))).mul hq)
  have h := hnum.div hden' (by simpa using hden)
  simp only [mul_one, mul_zero, zero_mul, zero_add, add_zero] at h
  unfold airyTop
  convert h using 1
  · rw [fresnel_add h₀N hNs, one_add_fresnel_mul h₀N hNs]
    field_simp [h₀N, hNs, hN, hsum]
  · rw [show (fresnel N nₛ * (2 * Complex.I * k * N)) *
          (1 + fresnel n₀ N * fresnel N nₛ) -
        (fresnel n₀ N + fresnel N nₛ) *
          (fresnel n₀ N * fresnel N nₛ * (2 * Complex.I * k * N)) =
        (2 * Complex.I * k * N) * fresnel N nₛ * (1 - fresnel n₀ N ^ 2) by ring,
      one_add_fresnel_mul h₀N hNs, one_sub_fresnel_sq h₀N]
    simp only [fresnel]
    field_simp [h₀N, hNs, hN, hsum]
    ring

lemma hasLinear_airySubstrate {n₀ N nₛ k : ℂ}
    (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0)
    (hden : 1 + fresnel n₀ N * fresnel N nₛ ≠ 0) (hsum : n₀ + nₛ ≠ 0) :
    HasLinear (airySubstrate n₀ N nₛ k) ((n₀ - nₛ) / (n₀ + nₛ))
      (2 * Complex.I * k * n₀ * (N ^ 2 - n₀ ^ 2) / (n₀ + nₛ) ^ 2) := by
  have hp := hasLinear_exp (-2 * Complex.I * k * n₀)
  have ht := hasLinear_airyTop (k := k) h₀N hNs hden hsum
  have h := hp.mul ht
  unfold airySubstrate
  convert h using 1
  · ring
  · field_simp [hsum]
    ring

lemma hasLinear_sheetReflection {n₀ N nₛ ref k : ℂ} (hsum : n₀ + nₛ ≠ 0) :
    HasLinear (sheetReflection n₀ N nₛ ref k) ((n₀ - nₛ) / (n₀ + nₛ))
      (2 * Complex.I * k * n₀ * (N ^ 2 - ref ^ 2) / (n₀ + nₛ) ^ 2) := by
  have hy := hasLinear_shunt N ref k
  have hY := (hasLinear_const nₛ).add hy
  have hnum := (hasLinear_const n₀).sub hY
  have hden := (hasLinear_const n₀).add hY
  have h := hnum.div hden (by simpa using hsum)
  unfold sheetReflection
  convert h using 1
  · ring
  · field_simp [hsum]
    ring

end B101ThinFilm

namespace B101ThinFilm

/-- Top-face form of the thin-film expansion.  Here the sheet subtracts the
substrate displacement current, so its shunt contains `N^2 - nₛ^2`. -/
theorem b101_top_face_expansion {n₀ N nₛ k : ℂ}
    (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0)
    (hden : 1 + fresnel n₀ N * fresnel N nₛ ≠ 0) (hsum : n₀ + nₛ ≠ 0) :
    (fun t => airyTop n₀ N nₛ k t - sheetReflection n₀ N nₛ nₛ k t) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
  have h₁ := hasLinear_airyTop (k := k) h₀N hNs hden hsum
  have h₂ := hasLinear_sheetReflection (n₀ := n₀) (N := N) (nₛ := nₛ)
    (ref := nₛ) (k := k) hsum
  have h := h₁.sub h₂
  unfold HasLinear at h
  exact h.congr_left (fun t => by ring)

/-- B101, read at the substrate face: with `y = -I*k*d*(N^2-n₀^2)` and
`Y = nₛ + y`, the exact Airy reflection referenced to that plane agrees with
`(n₀-Y)/(n₀+Y)` up to `O(d^2)`. -/
theorem b101_substrate_face_expansion {n₀ N nₛ k : ℂ}
    (h₀N : n₀ + N ≠ 0) (hNs : N + nₛ ≠ 0)
    (hden : 1 + fresnel n₀ N * fresnel N nₛ ≠ 0) (hsum : n₀ + nₛ ≠ 0) :
    (fun t => airySubstrate n₀ N nₛ k t - sheetReflection n₀ N nₛ n₀ k t) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
  have h₁ := hasLinear_airySubstrate (k := k) h₀N hNs hden hsum
  have h₂ := hasLinear_sheetReflection (n₀ := n₀) (N := N) (nₛ := nₛ)
    (ref := n₀) (k := k) hsum
  have h := h₁.sub h₂
  unfold HasLinear at h
  exact h.congr_left (fun t => by ring)

/-- In the usual physical case of positive real ambient, film and substrate
indices, every denominator hypothesis in `b101_substrate_face_expansion`
follows from positivity. -/
theorem b101_positive_real_indices {n₀ N nₛ k : ℝ}
    (hn₀ : 0 < n₀) (hN : 0 < N) (hnₛ : 0 < nₛ) :
    (fun t => airySubstrate (n₀ : ℂ) (N : ℂ) (nₛ : ℂ) (k : ℂ) t -
      sheetReflection (n₀ : ℂ) (N : ℂ) (nₛ : ℂ) (n₀ : ℂ) (k : ℂ) t) =O[𝓝 0]
      fun t => (t : ℂ) ^ 2 := by
  have hn₀C : (n₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn₀.ne'
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hnₛC : (nₛ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnₛ.ne'
  have h₀N : (n₀ : ℂ) + (N : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (add_pos hn₀ hN).ne'
  have hNs : (N : ℂ) + (nₛ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (add_pos hN hnₛ).ne'
  have hsum : (n₀ : ℂ) + (nₛ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (add_pos hn₀ hnₛ).ne'
  apply b101_substrate_face_expansion h₀N hNs _ hsum
  rw [one_add_fresnel_mul h₀N hNs]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hNC) hsum) (mul_ne_zero h₀N hNs)

end B101ThinFilm

#print axioms B101ThinFilm.hasLinear_const
#print axioms B101ThinFilm.hasLinear_id_mul
#print axioms B101ThinFilm.hasLinear_affine
#print axioms B101ThinFilm.HasLinear.add
#print axioms B101ThinFilm.HasLinear.sub
#print axioms B101ThinFilm.HasLinear.tendsto
#print axioms B101ThinFilm.HasLinear.bounded
#print axioms B101ThinFilm.HasLinear.mul
#print axioms B101ThinFilm.hasLinear_exp
#print axioms B101ThinFilm.HasLinear.inv
#print axioms B101ThinFilm.HasLinear.div
#print axioms B101ThinFilm.hasLinear_shunt
#print axioms B101ThinFilm.fresnel_add
#print axioms B101ThinFilm.one_add_fresnel_mul
#print axioms B101ThinFilm.one_sub_fresnel_sq
#print axioms B101ThinFilm.hasLinear_airyTop
#print axioms B101ThinFilm.hasLinear_airySubstrate
#print axioms B101ThinFilm.hasLinear_sheetReflection
#print axioms B101ThinFilm.b101_top_face_expansion
#print axioms B101ThinFilm.b101_substrate_face_expansion
#print axioms B101ThinFilm.b101_positive_real_indices


/-! ## B182 — the residence time, and the two limits that do not commute

Integrated from `.ultramath/smwvvnwls/m2/B182.lean`.
-/

/-!
# B182: delayed return versus no return
The impulse is represented by the initial data `x 0 = E`, `y 0 = 0`.
-/

open Set MeasureTheory Filter

namespace B182
noncomputable section

/-- `κ + a`, the decay rate of accessible stock when there is no return. -/
def c (κ a : ℝ) : ℝ := κ + a
/-- Discriminant of the characteristic polynomial `X² + (c+b)X + κb`. -/
def discr (κ a b : ℝ) : ℝ := (c κ a + b) ^ 2 - 4 * κ * b
/-- Positive square root of the discriminant. -/
def δ (κ a b : ℝ) : ℝ := Real.sqrt (discr κ a b)
/-- Slow characteristic rate. -/
def r (κ a b : ℝ) : ℝ := (δ κ a b - c κ a - b) / 2
/-- Fast characteristic rate. -/
def s (κ a b : ℝ) : ℝ := -(c κ a + b + δ κ a b) / 2
/-- Coefficient of the slow exponential in the accessible stock. -/
def A (κ a b : ℝ) : ℝ := (δ κ a b + b - c κ a) / (2 * δ κ a b)
/-- Coefficient of the fast exponential in the accessible stock. -/
def B (κ a b : ℝ) : ℝ := (δ κ a b + c κ a - b) / (2 * δ κ a b)
/-- Accessible stock after an impulse of size `E`. -/
def x (E κ a b t : ℝ) : ℝ :=
  E * (A κ a b * Real.exp (r κ a b * t) + B κ a b * Real.exp (s κ a b * t))
/-- Retained stock after an impulse of size `E`. -/
def y (E κ a b t : ℝ) : ℝ :=
  E * (a / δ κ a b) * (Real.exp (r κ a b * t) - Real.exp (s κ a b * t))
/-- The long-time stock: zero with return, and the displayed trapped share without it. -/
def eventualStock (E κ a b : ℝ) : ℝ :=
  if b = 0 then E * a / c κ a else 0

lemma c_pos {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : 0 < c κ a := by
  dsimp [c]
  linarith

lemma discr_pos {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 < discr κ a b := by
  by_cases hb0 : b = 0
  · subst b
    have hc := c_pos hκ ha
    simp [discr, sq_pos_of_pos hc]
  · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hab : 0 < a * b := mul_pos ha hb'
    have hsq : 0 ≤ (c κ a - b) ^ 2 := sq_nonneg _
    dsimp [discr, c] at hsq ⊢
    nlinarith

lemma δ_pos {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 < δ κ a b := Real.sqrt_pos.mpr (discr_pos hκ ha hb)
lemma δ_ne {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    δ κ a b ≠ 0 := (δ_pos hκ ha hb).ne'
lemma δ_sq {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    (δ κ a b) ^ 2 = (c κ a + b) ^ 2 - 4 * κ * b := by
  exact Real.sq_sqrt (discr_pos hκ ha hb).le

lemma δ_lt {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    δ κ a b < c κ a + b := by
  have hδ : 0 ≤ δ κ a b := (δ_pos hκ ha hb.le).le
  have hcb : 0 < c κ a + b := by linarith [c_pos hκ ha]
  have hsq : (δ κ a b) ^ 2 < (c κ a + b) ^ 2 := by
    rw [δ_sq hκ ha hb.le]
    nlinarith [mul_pos hκ hb]
  by_contra h
  have hle : c κ a + b ≤ δ κ a b := le_of_not_gt h
  have hprod : 0 ≤ (δ κ a b - (c κ a + b)) * (δ κ a b + (c κ a + b)) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  nlinarith

lemma r_neg {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    r κ a b < 0 := by
  have h := δ_lt hκ ha hb
  dsimp [r]
  linarith
lemma s_neg {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    s κ a b < 0 := by
  have hδ := δ_pos hκ ha hb
  have hc := c_pos hκ ha
  have hsum : 0 < c κ a + b + δ κ a b := by positivity
  dsimp [s]
  linarith
lemma r_sub_s (κ a b : ℝ) : r κ a b - s κ a b = δ κ a b := by
  dsimp [r, s]
  ring
lemma r_mul_s {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    r κ a b * s κ a b = κ * b := by
  have hδ := δ_sq hκ ha hb
  dsimp [r, s]
  nlinarith
lemma weights_add (κ a b : ℝ) (hδ : δ κ a b ≠ 0) : A κ a b + B κ a b = 1 := by
  unfold A B
  field_simp [hδ]
  ring
lemma r_add_c {κ a b : ℝ} (hδ : δ κ a b ≠ 0) :
    r κ a b + c κ a = δ κ a b * B κ a b := by
  unfold r B
  field_simp [hδ]
  ring
lemma s_add_c {κ a b : ℝ} (hδ : δ κ a b ≠ 0) :
    s κ a b + c κ a = -(δ κ a b * A κ a b) := by
  unfold s A
  field_simp [hδ]
  ring
lemma r_eq {κ a b : ℝ} (hδ : δ κ a b ≠ 0) :
    r κ a b = δ κ a b * A κ a b - b := by
  unfold r A
  field_simp [hδ]
  ring
lemma neg_s_eq {κ a b : ℝ} (hδ : δ κ a b ≠ 0) :
    -s κ a b = δ κ a b * B κ a b + b := by
  unfold s B
  field_simp [hδ]
  ring
lemma δ_sq_mul_weights {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    (δ κ a b) ^ 2 * A κ a b * B κ a b = a * b := by
  have hδ := δ_ne hκ ha hb
  have hδsq := δ_sq hκ ha hb
  unfold A B
  field_simp [hδ]
  dsimp [c] at hδsq ⊢
  nlinarith
lemma weighted_rates {κ a b : ℝ} (hδ : δ κ a b ≠ 0) :
    A κ a b * s κ a b + B κ a b * r κ a b = -b := by
  unfold A B r s
  field_simp [hδ]
  ring

lemma exp_hasDerivAt (u t : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (u * v)) (u * Real.exp (u * t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul u).exp

lemma x_hasDerivAt (E κ a b t : ℝ) :
    HasDerivAt (x E κ a b)
      (E * (A κ a b * (r κ a b * Real.exp (r κ a b * t)) +
        B κ a b * (s κ a b * Real.exp (s κ a b * t)))) t := by
  have hr := (exp_hasDerivAt (r κ a b) t).const_mul (A κ a b)
  have hs := (exp_hasDerivAt (s κ a b) t).const_mul (B κ a b)
  change HasDerivAt (fun v : ℝ =>
    E * (A κ a b * Real.exp (r κ a b * v) + B κ a b * Real.exp (s κ a b * v))) _ t
  exact (hr.add hs).const_mul E
lemma y_hasDerivAt (E κ a b t : ℝ) :
    HasDerivAt (y E κ a b)
      (E * (a / δ κ a b) *
        (r κ a b * Real.exp (r κ a b * t) - s κ a b * Real.exp (s κ a b * t))) t := by
  have hr := exp_hasDerivAt (r κ a b) t
  have hs := exp_hasDerivAt (s κ a b) t
  change HasDerivAt (fun v : ℝ => E * (a / δ κ a b) *
    (Real.exp (r κ a b * v) - Real.exp (s κ a b * v))) _ t
  exact (hr.sub hs).const_mul (E * (a / δ κ a b))
lemma x_initial (E κ a b : ℝ) (hδ : δ κ a b ≠ 0) : x E κ a b 0 = E := by
  calc
    x E κ a b 0 = E * (A κ a b + B κ a b) := by simp [x]
    _ = E := by rw [weights_add _ _ _ hδ, mul_one]
lemma y_initial (E κ a b : ℝ) : y E κ a b 0 = 0 := by
  simp [y]

/-- The first displayed evolution equation, after the impulse. -/
lemma x_evolution {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b)
    (E t : ℝ) :
    HasDerivAt (x E κ a b) (-(c κ a) * x E κ a b t + b * y E κ a b t) t := by
  have hδ := δ_ne hκ ha hb
  have hr := r_add_c (κ := κ) (a := a) (b := b) hδ
  have hs := s_add_c (κ := κ) (a := a) (b := b) hδ
  have hw := δ_sq_mul_weights hκ ha hb
  convert x_hasDerivAt E κ a b t using 1
  dsimp [x, y]
  symm
  have hw' : δ κ a b * A κ a b * B κ a b = a * b / δ κ a b := by
    apply (eq_div_iff hδ).2
    nlinarith
  have hr' : A κ a b * r κ a b = -(c κ a) * A κ a b + a * b / δ κ a b := by
    calc
      A κ a b * r κ a b = A κ a b * (r κ a b + c κ a) - c κ a * A κ a b := by ring
      _ = A κ a b * (δ κ a b * B κ a b) - c κ a * A κ a b := by rw [hr]
      _ = -(c κ a) * A κ a b + a * b / δ κ a b := by
        rw [show A κ a b * (δ κ a b * B κ a b) = δ κ a b * A κ a b * B κ a b by ring, hw']
        ring
  have hs' : B κ a b * s κ a b = -(c κ a) * B κ a b - a * b / δ κ a b := by
    calc
      B κ a b * s κ a b = B κ a b * (s κ a b + c κ a) - c κ a * B κ a b := by ring
      _ = B κ a b * (-(δ κ a b * A κ a b)) - c κ a * B κ a b := by rw [hs]
      _ = -(c κ a) * B κ a b - a * b / δ κ a b := by
        rw [show B κ a b * (-(δ κ a b * A κ a b)) = -(δ κ a b * A κ a b * B κ a b) by ring, hw']
        ring
  calc
    E * (A κ a b * (r κ a b * Real.exp (r κ a b * t)) +
        B κ a b * (s κ a b * Real.exp (s κ a b * t))) =
        E * Real.exp (r κ a b * t) * (A κ a b * r κ a b) +
          E * Real.exp (s κ a b * t) * (B κ a b * s κ a b) := by ring
    _ = E * Real.exp (r κ a b * t) * (-(c κ a) * A κ a b + a * b / δ κ a b) +
          E * Real.exp (s κ a b * t) * (-(c κ a) * B κ a b - a * b / δ κ a b) := by
        rw [hr', hs']
    _ = -(c κ a) * (E * (A κ a b * Real.exp (r κ a b * t) +
          B κ a b * Real.exp (s κ a b * t))) +
        b * (E * (a / δ κ a b) *
          (Real.exp (r κ a b * t) - Real.exp (s κ a b * t))) := by ring

/-- The second displayed evolution equation, with no forcing in the retained stock. -/
lemma y_evolution {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b)
    (E t : ℝ) :
    HasDerivAt (y E κ a b) (a * x E κ a b t - b * y E κ a b t) t := by
  have hδ := δ_ne hκ ha hb
  have hr := r_eq (κ := κ) (a := a) (b := b) hδ
  have hs := neg_s_eq (κ := κ) (a := a) (b := b) hδ
  convert y_hasDerivAt E κ a b t using 1
  dsimp [x, y]
  symm
  have hr' : (a / δ κ a b) * r κ a b = a * A κ a b - b * (a / δ κ a b) := by
    rw [hr]
    field_simp [hδ]
  have hs' : -(a / δ κ a b) * s κ a b = a * B κ a b + b * (a / δ κ a b) := by
    calc
      -(a / δ κ a b) * s κ a b = (a / δ κ a b) * (-s κ a b) := by ring
      _ = (a / δ κ a b) * (δ κ a b * B κ a b + b) := by rw [hs]
      _ = a * B κ a b + b * (a / δ κ a b) := by field_simp [hδ]
  calc
    E * (a / δ κ a b) *
        (r κ a b * Real.exp (r κ a b * t) - s κ a b * Real.exp (s κ a b * t)) =
        E * Real.exp (r κ a b * t) * ((a / δ κ a b) * r κ a b) +
          E * Real.exp (s κ a b * t) * (-(a / δ κ a b) * s κ a b) := by ring
    _ = E * Real.exp (r κ a b * t) * (a * A κ a b - b * (a / δ κ a b)) +
          E * Real.exp (s κ a b * t) * (a * B κ a b + b * (a / δ κ a b)) := by
        rw [hr', hs']
    _ = a * (E * (A κ a b * Real.exp (r κ a b * t) +
          B κ a b * Real.exp (s κ a b * t))) -
        b * (E * (a / δ κ a b) *
          (Real.exp (r κ a b * t) - Real.exp (s κ a b * t))) := by ring

lemma exp_tendsto_zero {u : ℝ} (hu : u < 0) :
    Tendsto (fun t : ℝ => Real.exp (u * t)) atTop (nhds 0) := by
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hu)

lemma x_integrable {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (E : ℝ) :
    IntegrableOn (x E κ a b) (Ioi 0) := by
  have hr := (integrableOn_exp_mul_Ioi (r_neg hκ ha hb) 0).const_mul (A κ a b)
  have hs := (integrableOn_exp_mul_Ioi (s_neg hκ ha hb.le) 0).const_mul (B κ a b)
  change IntegrableOn (fun t : ℝ =>
    E * (A κ a b * Real.exp (r κ a b * t) + B κ a b * Real.exp (s κ a b * t))) (Ioi 0)
  exact (hr.add hs).const_mul E

lemma y_integrable {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (E : ℝ) :
    IntegrableOn (y E κ a b) (Ioi 0) := by
  have hr := integrableOn_exp_mul_Ioi (r_neg hκ ha hb) 0
  have hs := integrableOn_exp_mul_Ioi (s_neg hκ ha hb.le) 0
  change IntegrableOn (fun t : ℝ => E * (a / δ κ a b) *
    (Real.exp (r κ a b * t) - Real.exp (s κ a b * t))) (Ioi 0)
  exact (hr.sub hs).const_mul (E * (a / δ κ a b))

lemma x_integral_raw {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (E : ℝ) :
    (∫ t in Ioi 0, x E κ a b t) =
      E * (A κ a b * (-1 / r κ a b) + B κ a b * (-1 / s κ a b)) := by
  have hr : IntegrableOn (fun t : ℝ => A κ a b * Real.exp (r κ a b * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (r_neg hκ ha hb) 0).const_mul _
  have hs : IntegrableOn (fun t : ℝ => B κ a b * Real.exp (s κ a b * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (s_neg hκ ha hb.le) 0).const_mul _
  unfold x
  rw [integral_const_mul, integral_add hr hs, integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (r_neg hκ ha hb), integral_exp_mul_Ioi (s_neg hκ ha hb.le)]
  norm_num

lemma y_integral_raw {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (E : ℝ) :
    (∫ t in Ioi 0, y E κ a b t) =
      E * (a / δ κ a b) * ((-1 / r κ a b) - (-1 / s κ a b)) := by
  have hr := integrableOn_exp_mul_Ioi (r_neg hκ ha hb) 0
  have hs := integrableOn_exp_mul_Ioi (s_neg hκ ha hb.le) 0
  unfold y
  rw [integral_const_mul, integral_sub hr hs,
    integral_exp_mul_Ioi (r_neg hκ ha hb), integral_exp_mul_Ioi (s_neg hκ ha hb.le)]
  norm_num

/-- The integrated accessible stock is exactly the impulse divided by the release rate. -/
theorem accessible_stock_integral {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (E : ℝ) : (∫ t in Ioi 0, x E κ a b t) = E / κ := by
  rw [x_integral_raw hκ ha hb]
  have hr : r κ a b ≠ 0 := (r_neg hκ ha hb).ne
  have hs : s κ a b ≠ 0 := (s_neg hκ ha hb.le).ne
  have hw := weighted_rates (κ := κ) (a := a) (b := b) (δ_ne hκ ha hb.le)
  have hp := r_mul_s hκ ha hb.le
  have hAlg : A κ a b * (-1 / r κ a b) + B κ a b * (-1 / s κ a b) = 1 / κ := by
    calc
      A κ a b * (-1 / r κ a b) + B κ a b * (-1 / s κ a b) =
          -(A κ a b * s κ a b + B κ a b * r κ a b) / (r κ a b * s κ a b) := by
        field_simp [hr, hs]
        ring
      _ = b / (κ * b) := by rw [hw, hp]; ring
      _ = 1 / κ := by field_simp [hκ.ne', hb.ne']
  rw [hAlg]
  ring

/-- The integrated retained stock accounts for the `a/b` delay factor. -/
theorem retained_stock_integral {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (E : ℝ) : (∫ t in Ioi 0, y E κ a b t) = E * a / (κ * b) := by
  rw [y_integral_raw hκ ha hb]
  have hr : r κ a b ≠ 0 := (r_neg hκ ha hb).ne
  have hs : s κ a b ≠ 0 := (s_neg hκ ha hb.le).ne
  have hAlg : (-1 / r κ a b) - (-1 / s κ a b) = δ κ a b / (κ * b) := by
    calc
      (-1 / r κ a b) - (-1 / s κ a b) =
          (r κ a b - s κ a b) / (r κ a b * s κ a b) := by
        field_simp [hr, hs]
        ring
      _ = δ κ a b / (κ * b) := by rw [r_sub_s, r_mul_s hκ ha hb.le]
  rw [hAlg]
  field_simp [δ_ne hκ ha hb.le, hκ.ne', hb.ne']

/-- Total stock-time, before normalizing by the impulse. -/
theorem total_stock_integral {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (E : ℝ) :
    (∫ t in Ioi 0, (x E κ a b t + y E κ a b t)) = E / κ * (1 + a / b) := by
  rw [integral_add (x_integrable hκ ha hb E) (y_integrable hκ ha hb E),
    accessible_stock_integral hκ ha hb, retained_stock_integral hκ ha hb]
  field_simp [hκ.ne', hb.ne']

/-- The card's mean residence time `(1 + a/b)/κ`, for a nonzero impulse. -/
theorem mean_residence {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) {E : ℝ} (hE : E ≠ 0) :
    (∫ t in Ioi 0, (x E κ a b t + y E κ a b t)) / E = (1 + a / b) / κ := by
  rw [total_stock_integral hκ ha hb]
  field_simp [hE, hκ.ne', hb.ne']

/-- Integrated release is the whole impulse whenever `b > 0`. -/
theorem total_outflow {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (E : ℝ) : (∫ t in Ioi 0, κ * x E κ a b t) = E := by
  rw [integral_const_mul, accessible_stock_integral hκ ha hb]
  field_simp [hκ.ne']

lemma total_stock_tendsto_positive {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (E : ℝ) :
    Tendsto (fun t => x E κ a b t + y E κ a b t) atTop (nhds 0) := by
  have hr := exp_tendsto_zero (r_neg hκ ha hb)
  have hs := exp_tendsto_zero (s_neg hκ ha hb.le)
  have hx0 := ((hr.const_mul (A κ a b)).add (hs.const_mul (B κ a b))).const_mul E
  have hy0 := (hr.sub hs).const_mul (E * (a / δ κ a b))
  have hx : Tendsto (x E κ a b) atTop (nhds 0) := by
    change Tendsto (fun t : ℝ =>
      E * (A κ a b * Real.exp (r κ a b * t) + B κ a b * Real.exp (s κ a b * t)))
      atTop (nhds 0)
    simpa using hx0
  have hy : Tendsto (y E κ a b) atTop (nhds 0) := by
    change Tendsto (fun t : ℝ => E * (a / δ κ a b) *
      (Real.exp (r κ a b * t) - Real.exp (s κ a b * t))) atTop (nhds 0)
    simpa using hy0
  simpa using hx.add hy

lemma δ_at_zero {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : δ κ a 0 = c κ a := by
  simpa [δ, discr] using Real.sqrt_sq (c_pos hκ ha).le

lemma r_at_zero {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : r κ a 0 = 0 := by
  unfold r
  rw [δ_at_zero hκ ha]
  ring
lemma s_at_zero {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : s κ a 0 = -c κ a := by
  unfold s
  rw [δ_at_zero hκ ha]
  ring
lemma A_at_zero {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : A κ a 0 = 0 := by
  unfold A
  rw [δ_at_zero hκ ha]
  field_simp [(c_pos hκ ha).ne']
  ring
lemma B_at_zero {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) : B κ a 0 = 1 := by
  unfold B
  rw [δ_at_zero hκ ha]
  field_simp [(c_pos hκ ha).ne']
  ring

/-- With no return, the limiting stock is exactly `E * a/(κ+a)`. -/
theorem total_stock_tendsto_no_return {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) (E : ℝ) :
    Tendsto (fun t => x E κ a 0 t + y E κ a 0 t) atTop (nhds (E * a / c κ a)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-c κ a * t)) atTop (nhds 0) :=
    exp_tendsto_zero (neg_lt_zero.mpr (c_pos hκ ha))
  have hfun : (fun t => x E κ a 0 t + y E κ a 0 t) =
      (fun t => E * a / c κ a + (E - E * a / c κ a) * Real.exp (-c κ a * t)) := by
    funext t
    simp [x, y, A_at_zero hκ ha, B_at_zero hκ ha, r_at_zero hκ ha,
      s_at_zero hκ ha, δ_at_zero hκ ha]
    ring
  rw [hfun]
  simpa using tendsto_const_nhds.add (he.const_mul (E - E * a / c κ a))

/-- Long-time stock for either regime, including the boundary `b = 0`. -/
theorem total_stock_tendsto {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 ≤ b) (E : ℝ) :
    Tendsto (fun t => x E κ a b t + y E κ a b t) atTop
      (nhds (eventualStock E κ a b)) := by
  by_cases hb0 : b = 0
  · subst b
    simpa [eventualStock] using total_stock_tendsto_no_return hκ ha E
  · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    simpa [eventualStock, hb0] using total_stock_tendsto_positive hκ ha hb' E

/-- The outer limit as the return rate tends to zero from above is zero. -/
theorem eventualStock_tendsto_right (E κ a : ℝ) :
    Tendsto (eventualStock E κ a) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb0 : b ≠ 0 := ne_of_gt (show 0 < b from hb)
  simp [eventualStock, hb0]

/-- The two orders of limits do not agree for a positive impulse and positive capture rate. -/
theorem limits_do_not_commute {κ a E : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hE : 0 < E) :
    Tendsto (eventualStock E κ a) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      eventualStock E κ a 0 = E * a / (κ + a) ∧ eventualStock E κ a 0 ≠ 0 := by
  refine ⟨eventualStock_tendsto_right E κ a, by simp [eventualStock, c], ?_⟩
  rw [show eventualStock E κ a 0 = E * a / c κ a by simp [eventualStock]]
  exact (div_pos (mul_pos hE ha) (c_pos hκ ha)).ne'

lemma abs_c_sub_b_le_δ {κ a b : ℝ} (_hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    |c κ a - b| ≤ δ κ a b := by
  calc
    |c κ a - b| = Real.sqrt ((c κ a - b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (discr κ a b) := Real.sqrt_le_sqrt (by
      dsimp [discr, c]
      nlinarith [mul_nonneg ha.le hb])
    _ = δ κ a b := rfl

lemma A_nonneg {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ A κ a b := by
  have hbds := abs_le.mp (abs_c_sub_b_le_δ hκ ha hb)
  have hδ := (δ_pos hκ ha hb).le
  unfold A
  exact div_nonneg (by linarith [hbds.2]) (by positivity)

lemma B_nonneg {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ B κ a b := by
  have hbds := abs_le.mp (abs_c_sub_b_le_δ hκ ha hb)
  have hδ := (δ_pos hκ ha hb).le
  unfold B
  exact div_nonneg (by linarith [hbds.1]) (by positivity)

/-- The explicit accessible stock is nonnegative for nonnegative time and impulse. -/
theorem accessible_nonneg {κ a b E t : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 ≤ b) (hE : 0 ≤ E) (_ht : 0 ≤ t) : 0 ≤ x E κ a b t := by
  dsimp [x]
  exact mul_nonneg hE (add_nonneg
    (mul_nonneg (A_nonneg hκ ha hb) (Real.exp_pos _).le)
    (mul_nonneg (B_nonneg hκ ha hb) (Real.exp_pos _).le))

/-- The explicit retained stock is nonnegative: the slow exponential dominates the fast one. -/
theorem retained_nonneg {κ a b E t : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 ≤ b) (hE : 0 ≤ E) (ht : 0 ≤ t) : 0 ≤ y E κ a b t := by
  have hrδ : s κ a b ≤ r κ a b := by
    have hdiff := r_sub_s κ a b
    have hδ := δ_pos hκ ha hb
    linarith
  have hst : s κ a b * t ≤ r κ a b * t := mul_le_mul_of_nonneg_right hrδ ht
  have he : Real.exp (s κ a b * t) ≤ Real.exp (r κ a b * t) := Real.exp_le_exp.mpr hst
  dsimp [y]
  exact mul_nonneg (mul_nonneg hE (div_nonneg ha.le (δ_pos hκ ha hb).le)) (sub_nonneg.mpr he)

/-- In the zero-capture boundary case, the elementary solution works even at a repeated root. -/
theorem zero_capture_solution {κ : ℝ} (_hκ : 0 < κ) (E b t : ℝ) :
    HasDerivAt (fun u : ℝ => E * Real.exp (-κ * u))
        (-(κ + 0) * (E * Real.exp (-κ * t)) + b * 0) t ∧
      HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (0 * (E * Real.exp (-κ * t)) - b * 0) t := by
  constructor
  · convert (exp_hasDerivAt (-κ) t).const_mul E using 1
    ring
  · simpa using (hasDerivAt_const t (0 : ℝ))

/-- The mean formula remains valid at zero capture, for every positive return rate. -/
theorem mean_residence_zero_capture {κ b E : ℝ} (hκ : 0 < κ) (_hb : 0 < b)
    (hE : E ≠ 0) :
    (∫ t in Ioi 0, E * Real.exp (-κ * t)) / E = (1 + (0 : ℝ) / b) / κ := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hκ) 0]
  norm_num
  field_simp [hE, hκ.ne']

end
end B182

-- Axiom audit (every declared lemma and theorem above).
#print axioms B182.c_pos
#print axioms B182.discr_pos
#print axioms B182.δ_pos
#print axioms B182.δ_ne
#print axioms B182.δ_sq
#print axioms B182.δ_lt
#print axioms B182.r_neg
#print axioms B182.s_neg
#print axioms B182.r_sub_s
#print axioms B182.r_mul_s
#print axioms B182.weights_add
#print axioms B182.r_add_c
#print axioms B182.s_add_c
#print axioms B182.r_eq
#print axioms B182.neg_s_eq
#print axioms B182.δ_sq_mul_weights
#print axioms B182.weighted_rates
#print axioms B182.exp_hasDerivAt
#print axioms B182.x_hasDerivAt
#print axioms B182.y_hasDerivAt
#print axioms B182.x_initial
#print axioms B182.y_initial
#print axioms B182.x_evolution
#print axioms B182.y_evolution
#print axioms B182.exp_tendsto_zero
#print axioms B182.x_integrable
#print axioms B182.y_integrable
#print axioms B182.x_integral_raw
#print axioms B182.y_integral_raw
#print axioms B182.accessible_stock_integral
#print axioms B182.retained_stock_integral
#print axioms B182.total_stock_integral
#print axioms B182.mean_residence
#print axioms B182.total_outflow
#print axioms B182.total_stock_tendsto_positive
#print axioms B182.δ_at_zero
#print axioms B182.r_at_zero
#print axioms B182.s_at_zero
#print axioms B182.A_at_zero
#print axioms B182.B_at_zero
#print axioms B182.total_stock_tendsto_no_return
#print axioms B182.total_stock_tendsto
#print axioms B182.eventualStock_tendsto_right
#print axioms B182.limits_do_not_commute
#print axioms B182.abs_c_sub_b_le_δ
#print axioms B182.A_nonneg
#print axioms B182.B_nonneg
#print axioms B182.accessible_nonneg
#print axioms B182.retained_nonneg
#print axioms B182.zero_capture_solution
#print axioms B182.mean_residence_zero_capture


/-! ## B126 — the log-det derivative and the selected quadratic form

Integrated from `.ultramath/smwvvnwls/m14/B126.lean`.
-/

/-!
# B126 — finite trace-log response and its positive quadratic form

The full-spectrum theorem is proved for an arbitrary finite real matrix.
For a positive diagonal matrix we also isolate an arbitrary coordinate
cluster, differentiate its log-ledger in diagonal directions, and compute
the complex source form, its sign and its exact kernel.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Matrix Polynomial

namespace RelationalAtlas.B126

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det (1 + t M)`, the normalized determinant curve. -/
def unitDet (M : Matrix n n ℝ) (t : ℝ) : ℝ := (1 + t • M).det

/-- The part of the normalized determinant polynomial of degree at least two. -/
def unitQuadratic (M : Matrix n n ℝ) : Polynomial ℝ :=
  (Matrix.det (1 + (Polynomial.X : ℝ[X]) • M.map Polynomial.C)).divX.divX

lemma unitDet_eq_expansion (M : Matrix n n ℝ) (t : ℝ) :
    unitDet M t = 1 + M.trace * t + (unitQuadratic M).eval t * t ^ 2 := by
  unfold unitDet unitQuadratic
  exact Matrix.det_one_add_smul t M

@[simp] lemma unitDet_zero (M : Matrix n n ℝ) : unitDet M 0 = 1 := by
  simp [unitDet]

/-- The characteristic-polynomial calculation gives the full-spectrum
normalized response, without diagonalizability or Hermitian hypotheses. -/
theorem hasDerivAt_unitDet_zero (M : Matrix n n ℝ) :
    HasDerivAt (unitDet M) M.trace 0 := by
  have hfun : unitDet M = fun t : ℝ =>
      1 + M.trace * t + (unitQuadratic M).eval t * t ^ 2 := by
    funext t
    exact unitDet_eq_expansion M t
  rw [hfun]
  convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul M.trace)).add
    (((unitQuadratic M).hasDerivAt 0).mul ((hasDerivAt_id (0 : ℝ)).pow 2)) using 1 <;>
    (try ext x) <;> simp [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]

lemma mul_unit_normalized (K B : Matrix n n ℝ) (hK : IsUnit K.det) (t : ℝ) :
    K * (1 + t • (K⁻¹ * B)) = K + t • B := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv K hK, Matrix.one_mul]

/-- **Full-spectrum trace-log derivative.**  If `K` is invertible, then
`d/dt log det(K+tB) = Tr(K⁻¹B)` at zero.  This permits real negative
eigenvalues as well: `Real.log` is used in Mathlib's nonzero-even convention,
and only the determinant's nonvanishing is needed. -/
theorem hasDerivAt_logdet_full (K B : Matrix n n ℝ) (hK : K.det ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (K + t • B).det) (K⁻¹ * B).trace 0 := by
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hK
  have hcurve : (fun t : ℝ => Real.log (K + t • B).det) =
      fun t : ℝ => Real.log (K.det * unitDet (K⁻¹ * B) t) := by
    funext t
    rw [← mul_unit_normalized K B hunit t, Matrix.det_mul]
    rfl
  rw [hcurve]
  have hd := (hasDerivAt_unitDet_zero (K⁻¹ * B)).const_mul K.det
  have hlog := hd.log (mul_ne_zero hK (by simp))
  convert hlog using 1 <;> simp [hK]

/-- The displayed derivative, in `deriv` notation. -/
theorem deriv_logdet_full (K B : Matrix n n ℝ) (hK : K.det ≠ 0) :
    deriv (fun t : ℝ => Real.log (K + t • B).det) 0 = (K⁻¹ * B).trace :=
  (hasDerivAt_logdet_full K B hK).deriv

/-- A nonsingular real diagonal matrix has the coordinatewise inverse. -/
lemma inv_diagonal_real (d : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [hd i]
  · simp [h]

/-- Orthogonal projector onto a coordinate spectral cluster. -/
def clusterProjector (J : Finset n) : Matrix n n ℝ :=
  Matrix.diagonal fun i => if i ∈ J then 1 else 0

/-- The selected trace-log `Σ log λ` in a diagonal eigenbasis. -/
def clusterLog (d : n → ℝ) (J : Finset n) : ℝ := ∑ i ∈ J, Real.log (d i)

/-- The response form `Σ λ⁻¹ ‖P_λ b‖²`; here `P_λ` is the orthogonal
coordinate projector, and `Complex.normSq` is the squared complex norm. -/
def sourceForm (d : n → ℝ) (J : Finset n) (b : n → ℂ) : ℝ :=
  ∑ i ∈ J, (d i)⁻¹ * Complex.normSq (b i)

/-- In diagonal perturbation directions, every coordinate cluster has the
announced trace-log derivative.  This version permits equal eigenvalues and
an arbitrary selected subset; it does not assert that an arbitrary
non-diagonal perturbation preserves those coordinates. -/
theorem hasDerivAt_clusterLog (d v : n → ℝ) (J : Finset n)
    (hd : ∀ i ∈ J, d i ≠ 0) :
    HasDerivAt (fun t : ℝ => clusterLog (fun i => d i + t * v i) J)
      (∑ i ∈ J, (d i)⁻¹ * v i) 0 := by
  unfold clusterLog
  apply HasDerivAt.fun_sum
  intro i hi
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (d i)).log
    (by simpa using hd i hi) using 1 <;>
    simp [div_eq_mul_inv, mul_comm]

/-- The sum in the derivative is literally `Tr(P_C K⁻¹ B)` for diagonal
`K = diag d` and `B = diag v`. -/
theorem trace_cluster_diagonal (d v : n → ℝ) (J : Finset n)
    (hd : ∀ i, d i ≠ 0) :
    (clusterProjector J * (Matrix.diagonal d)⁻¹ * Matrix.diagonal v).trace =
      ∑ i ∈ J, (d i)⁻¹ * v i := by
  classical
  rw [inv_diagonal_real d hd]
  simp [clusterProjector, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Finset.sum_ite_mem]

/-- Thus the selected diagonal response has exactly the sign and prefactor
in the card's first display. -/
theorem hasDerivAt_clusterLog_eq_trace (d v : n → ℝ) (J : Finset n)
    (hd : ∀ i, d i ≠ 0) :
    HasDerivAt (fun t : ℝ => clusterLog (fun i => d i + t * v i) J)
      (clusterProjector J * (Matrix.diagonal d)⁻¹ * Matrix.diagonal v).trace 0 := by
  rw [trace_cluster_diagonal d v J hd]
  exact hasDerivAt_clusterLog d v J (fun i _ => hd i)

/-- `P_C K⁻¹`, with a real diagonal `K`, promoted to a complex matrix. -/
def selectedResolvent (d : n → ℝ) (J : Finset n) : Matrix n n ℂ :=
  Matrix.diagonal fun i => if i ∈ J then (((d i)⁻¹ : ℝ) : ℂ) else 0

/-- The complex sesquilinear evaluation `bᴴ Q b` in coordinates. -/
def daggerForm (Q : Matrix n n ℂ) (b : n → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (b i) * (Q *ᵥ b) i

/-- The second equality on the card: the dagger evaluation is exactly the  weighted spectral sum of squared norms. -/
theorem daggerForm_selectedResolvent (d : n → ℝ) (J : Finset n) (b : n → ℂ) :
    daggerForm (selectedResolvent d J) b = (sourceForm d J b : ℂ) := by
  classical
  simp [daggerForm, selectedResolvent, sourceForm, Matrix.mulVec_diagonal,
    Complex.ofReal_sum, Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- For a real source and the full cluster, the trace response to the rank-one
perturbation `bbᵀ` is the real spectral quadratic form. -/
theorem trace_inverse_diagonal_rankOne (d b : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    ((Matrix.diagonal d)⁻¹ * Matrix.vecMulVec b b).trace =
      ∑ i, (d i)⁻¹ * b i ^ 2 := by
  classical
  rw [inv_diagonal_real d hd]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full-cluster response to a rank-one real source, with the derivative
and the displayed source form on the two sides of one equation. -/
theorem deriv_logdet_diagonal_rankOne (d b : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    deriv (fun t : ℝ => Real.log
      (Matrix.diagonal d + t • Matrix.vecMulVec b b).det) 0 =
      sourceForm d Finset.univ (fun i => (b i : ℂ)) := by
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    simp [Matrix.det_diagonal, Finset.prod_ne_zero_iff, hd]
  rw [deriv_logdet_full _ _ hdet, trace_inverse_diagonal_rankOne d b hd]
  simp [sourceForm, Complex.normSq_ofReal, pow_two]

/-- Without positive eigenvalues the quadratic-form inequality can fail,
even though all entries are invertible.  This tests the card's explicit
`K = Kᴴ > 0` positivity hypothesis; it is not a counterexample to it. -/
theorem sourceForm_can_be_negative_without_positivity :
    ∃ (d : Fin 2 → ℝ) (J : Finset (Fin 2)) (b : Fin 2 → ℂ),
      (∀ i, d i ≠ 0) ∧ sourceForm d J b < 0 := by
  refine ⟨fun _ => -1, {0}, fun _ => 1, ?_, ?_⟩
  · norm_num
  · norm_num [sourceForm]

/-- Positivity is a consequence of positive selected eigenvalues. -/
theorem sourceForm_nonneg (d : n → ℝ) (J : Finset n) (b : n → ℂ)
    (hd : ∀ i ∈ J, 0 < d i) : 0 ≤ sourceForm d J b := by
  unfold sourceForm
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (inv_nonneg.mpr (hd i hi).le) (Complex.normSq_nonneg _)

/-- The kernel of the positive response is exactly the complement of the
selected cluster: no selected source component can be silent. -/
theorem sourceForm_eq_zero_iff (d : n → ℝ) (J : Finset n) (b : n → ℂ)
    (hd : ∀ i ∈ J, 0 < d i) :
    sourceForm d J b = 0 ↔ ∀ i ∈ J, b i = 0 := by
  have hnonneg : ∀ i ∈ J, 0 ≤ (d i)⁻¹ * Complex.normSq (b i) := fun i hi =>
    mul_nonneg (inv_nonneg.mpr (hd i hi).le) (Complex.normSq_nonneg _)
  unfold sourceForm
  rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  apply forall₂_congr
  intro i hi
  have hdi : (d i)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (hd i hi))
  simp [hdi]

#print axioms unitDet_eq_expansion
#print axioms unitDet_zero
#print axioms hasDerivAt_unitDet_zero
#print axioms mul_unit_normalized
#print axioms hasDerivAt_logdet_full
#print axioms deriv_logdet_full
#print axioms inv_diagonal_real
#print axioms hasDerivAt_clusterLog
#print axioms trace_cluster_diagonal
#print axioms hasDerivAt_clusterLog_eq_trace
#print axioms daggerForm_selectedResolvent
#print axioms trace_inverse_diagonal_rankOne
#print axioms deriv_logdet_diagonal_rankOne
#print axioms sourceForm_can_be_negative_without_positivity
#print axioms sourceForm_nonneg
#print axioms sourceForm_eq_zero_iff

end RelationalAtlas.B126


/-! ## B151 — the log-odds identity and its endpoints

Integrated from `.ultramath/smwvvnwls/m10/B151.lean`.
-/

open scoped BigOperators

noncomputable section

namespace AtlasB151

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real diagonalizable covariance matrix with its displayed real spectrum. -/
def spectralCovariance (P : Matrix ι ι ℝ) (c : ι → ℝ) : Matrix ι ι ℝ :=
  P * Matrix.diagonal c * P⁻¹

/-- The log-odds eigenvalue of the entanglement Hamiltonian in one mode. -/
def modeEpsilon (c : ℝ) : ℝ := Real.log (1 - c) - Real.log c

/-- The entanglement Hamiltonian obtained by conjugating the diagonal log-odds matrix. -/
def spectralEntanglement (P : Matrix ι ι ℝ) (c : ι → ℝ) : Matrix ι ι ℝ :=
  P * Matrix.diagonal (fun i => modeEpsilon (c i)) * P⁻¹

/-- Probability of the all-empty configuration in the finite independent-mode model. -/
def emptyProbability (C : Matrix ι ι ℝ) : ℝ := (1 - C).det

/-- Probability of the all-full configuration in the finite independent-mode model. -/
def fullProbability (C : Matrix ι ι ℝ) : ℝ := C.det

/-- Product mass of a binary occupation pattern (`true` means occupied). -/
def occupationMass (c : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then c i else 1 - c i

omit [Fintype ι] in
lemma one_sub_diagonal (c : ι → ℝ) :
    (1 : Matrix ι ι ℝ) - Matrix.diagonal c = Matrix.diagonal (fun i => 1 - c i) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

lemma one_sub_spectralCovariance (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    1 - spectralCovariance P c = spectralCovariance P (fun i => 1 - c i) := by
  have hPI : P * P⁻¹ = (1 : Matrix ι ι ℝ) :=
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  calc
    1 - spectralCovariance P c = P * 1 * P⁻¹ - P * Matrix.diagonal c * P⁻¹ := by
      simp [spectralCovariance, hPI]
    _ = P * (1 - Matrix.diagonal c) * P⁻¹ := by noncomm_ring
    _ = spectralCovariance P (fun i => 1 - c i) := by
      rw [one_sub_diagonal]
      rfl

lemma det_spectralCovariance (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    (spectralCovariance P c).det = ∏ i, c i := by
  unfold spectralCovariance
  rw [Matrix.det_conj hP, Matrix.det_diagonal]

lemma trace_spectralEntanglement (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    (spectralEntanglement P c).trace = ∑ i, modeEpsilon (c i) := by
  unfold spectralEntanglement
  rw [Matrix.trace_conj hP, Matrix.trace_diagonal]

lemma emptyProbability_pos (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc : ∀ i, c i < 1) : 0 < emptyProbability (spectralCovariance P c) := by
  unfold emptyProbability
  rw [one_sub_spectralCovariance P c hP, det_spectralCovariance _ _ hP]
  exact Finset.prod_pos fun i _ => sub_pos.mpr (hc i)

lemma fullProbability_pos (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc : ∀ i, 0 < c i) : 0 < fullProbability (spectralCovariance P c) := by
  unfold fullProbability
  rw [det_spectralCovariance _ _ hP]
  exact Finset.prod_pos fun i _ => hc i

lemma log_emptyProbability (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc : ∀ i, c i < 1) :
    Real.log (emptyProbability (spectralCovariance P c)) = ∑ i, Real.log (1 - c i) := by
  unfold emptyProbability
  rw [one_sub_spectralCovariance P c hP, det_spectralCovariance _ _ hP]
  exact Real.log_prod fun i _ => ne_of_gt (sub_pos.mpr (hc i))

lemma log_fullProbability (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc : ∀ i, 0 < c i) :
    Real.log (fullProbability (spectralCovariance P c)) = ∑ i, Real.log (c i) := by
  unfold fullProbability
  rw [det_spectralCovariance _ _ hP]
  exact Real.log_prod fun i _ => ne_of_gt (hc i)

lemma occupationMass_total (c : ι → ℝ) : ∑ x, occupationMass c x = 1 := by
  unfold occupationMass
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b = true then c i else 1 - c i)]
  simp

omit [DecidableEq ι] in
lemma occupationMass_all_empty (c : ι → ℝ) :
    occupationMass c (fun _ => false) = ∏ i, (1 - c i) := by
  simp [occupationMass]

omit [DecidableEq ι] in
lemma occupationMass_all_full (c : ι → ℝ) :
    occupationMass c (fun _ => true) = ∏ i, c i := by
  simp [occupationMass]

lemma emptyProbability_eq_occupationMass (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    emptyProbability (spectralCovariance P c) = occupationMass c (fun _ => false) := by
  rw [occupationMass_all_empty]
  unfold emptyProbability
  rw [one_sub_spectralCovariance P c hP, det_spectralCovariance _ _ hP]

lemma fullProbability_eq_occupationMass (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    fullProbability (spectralCovariance P c) = occupationMass c (fun _ => true) := by
  rw [occupationMass_all_full]
  exact det_spectralCovariance P c hP

/-- The exact finite spectral identity behind B151. -/
theorem b151_tau_eq_sum_epsilon (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P) :
    (spectralEntanglement P c).trace = ∑ i, (Real.log (1 - c i) - Real.log (c i)) := by
  simpa [modeEpsilon] using trace_spectralEntanglement P c hP

/-- B151's trace/log-determinant identity for a diagonalized finite covariance matrix. -/
theorem b151_tau_eq_logdet_sub_logdet (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc0 : ∀ i, 0 < c i) (hc1 : ∀ i, c i < 1) :
    (spectralEntanglement P c).trace =
      Real.log (1 - spectralCovariance P c).det - Real.log (spectralCovariance P c).det := by
  calc
    (spectralEntanglement P c).trace =
        ∑ i, (Real.log (1 - c i) - Real.log (c i)) := b151_tau_eq_sum_epsilon P c hP
    _ = (∑ i, Real.log (1 - c i)) - ∑ i, Real.log (c i) := Finset.sum_sub_distrib _ _
    _ = Real.log (emptyProbability (spectralCovariance P c)) -
        Real.log (fullProbability (spectralCovariance P c)) := by
      rw [log_emptyProbability P c hP hc1, log_fullProbability P c hP hc0]
    _ = Real.log (1 - spectralCovariance P c).det -
        Real.log (spectralCovariance P c).det := rfl

/-- The same offset is the logarithm of empty-over-full, with both probabilities nonzero. -/
theorem b151_tau_eq_log_empty_div_full (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc0 : ∀ i, 0 < c i) (hc1 : ∀ i, c i < 1) :
    (spectralEntanglement P c).trace =
      Real.log (emptyProbability (spectralCovariance P c) /
        fullProbability (spectralCovariance P c)) := by
  rw [Real.log_div (ne_of_gt (emptyProbability_pos P c hP hc1))
    (ne_of_gt (fullProbability_pos P c hP hc0))]
  exact b151_tau_eq_logdet_sub_logdet P c hP hc0 hc1

/-- Empty-over-full expressed directly with the two atomic occupation-pattern masses. -/
theorem b151_tau_eq_log_occupationMass_ratio (P : Matrix ι ι ℝ) (c : ι → ℝ) (hP : IsUnit P)
    (hc0 : ∀ i, 0 < c i) (hc1 : ∀ i, c i < 1) :
    (spectralEntanglement P c).trace =
      Real.log (occupationMass c (fun _ => false) / occupationMass c (fun _ => true)) := by
  rw [← emptyProbability_eq_occupationMass P c hP, ← fullProbability_eq_occupationMass P c hP]
  exact b151_tau_eq_log_empty_div_full P c hP hc0 hc1

/-- An occupation exactly zero kills the full-region probability: the lower endpoint is real. -/
theorem fullProbability_zero_of_mode_eq_zero (P : Matrix ι ι ℝ) (c : ι → ℝ)
    (hP : IsUnit P) (j : ι) (hj : c j = 0) :
    fullProbability (spectralCovariance P c) = 0 := by
  unfold fullProbability
  rw [det_spectralCovariance _ _ hP]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- An occupation exactly one kills the empty-region probability: both strict bounds are needed. -/
theorem emptyProbability_zero_of_mode_eq_one (P : Matrix ι ι ℝ) (c : ι → ℝ)
    (hP : IsUnit P) (j : ι) (hj : c j = 1) :
    emptyProbability (spectralCovariance P c) = 0 := by
  unfold emptyProbability
  rw [one_sub_spectralCovariance P c hP, det_spectralCovariance _ _ hP]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

#print axioms occupationMass_total
#print axioms b151_tau_eq_sum_epsilon
#print axioms b151_tau_eq_logdet_sub_logdet
#print axioms b151_tau_eq_log_empty_div_full
#print axioms b151_tau_eq_log_occupationMass_ratio
#print axioms fullProbability_zero_of_mode_eq_zero
#print axioms emptyProbability_zero_of_mode_eq_one

end AtlasB151


/-! ## B147 — the determinant series and its parity-split limits

Integrated from `.ultramath/smwvvnwls/m3/B147.lean`.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace B147

/-- The real Dirichlet series at an integer exponent, indexed by the
positive natural `n+1`. -/
def zeta (p : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ p

/-- The coefficient occurring in the card's exact lattice sum.  Defining it
also at zero avoids a subtype in later reindexing arguments. -/
def coeff (m : ℕ) : ℝ :=
  if m = 0 then 0 else 1 / ((m : ℝ) * (4 * (m : ℝ) ^ 2 - 1))

lemma summable_inv_nat_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
  Real.summable_one_div_nat_pow.mpr hp

lemma summable_inv_nat_succ_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ p) :=
  (summable_nat_add_iff 1).2 (summable_inv_nat_pow hp)

lemma ofReal_zeta_three : (zeta 3 : ℂ) = riemannZeta 3 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow
    (s := (3 : ℂ)) (by norm_num : (1 : ℝ) < (3 : ℂ).re)]
  unfold zeta
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  norm_num [Complex.cpow_natCast]

/-- `∑_{m≥1,n∣m} coeff m`, with the multiples enumerated by `k+1`. -/
def multipleSum (n : ℕ) : ℝ := ∑' k : ℕ, coeff (n * (k + 1))

/-- The leading inverse-cube sum and the inexpensive inverse-fifth-power
comparison used to bound the error. -/
def scaledInvSum (n p : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / (4 * ((n * (k + 1) : ℕ) : ℝ) ^ p)

lemma coeff_nonneg {m : ℕ} (hm : 0 < m) : 0 ≤ coeff m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hd : (0 : ℝ) < 4 * (m : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg (m : ℝ)]
  rw [coeff, ite_eq_right (Nat.ne_of_gt hm)]
  positivity

lemma coeff_lower {m : ℕ} (hm : 0 < m) :
    1 / (4 * (m : ℝ) ^ 3) ≤ coeff m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hd : (0 : ℝ) < 4 * (m : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg (m : ℝ)]
  rw [coeff, ite_eq_right (Nat.ne_of_gt hm)]
  apply one_div_le_one_div_of_le (mul_pos hmpos hd)
  nlinarith

lemma coeff_upper {m : ℕ} (hm : 0 < m) :
    coeff m ≤ 1 / (4 * (m : ℝ) ^ 3) + 1 / (4 * (m : ℝ) ^ 5) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hd : (0 : ℝ) < 4 * (m : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg (m : ℝ)]
  have hd' : -1 + (m : ℝ) ^ 2 * 4 ≠ 0 := by nlinarith
  have hexact :
      1 / ((m : ℝ) * (4 * (m : ℝ) ^ 2 - 1)) =
        1 / (4 * (m : ℝ) ^ 3) +
          1 / (4 * (m : ℝ) ^ 3 * (4 * (m : ℝ) ^ 2 - 1)) := by
    field_simp [ne_of_gt hmpos, ne_of_gt hd, hd'] <;> ring
    field_simp [hd'] <;> ring
  rw [coeff, ite_eq_right (Nat.ne_of_gt hm), hexact]
  apply add_le_add le_rfl
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * (m : ℝ) ^ 5)
  have hp : 0 ≤ (m : ℝ) ^ 3 * (3 * (m : ℝ) ^ 2 - 1) :=
    mul_nonneg (by positivity) (by nlinarith [sq_nonneg (m : ℝ)])
  nlinarith

lemma scaledInvSum_eq (n p : ℕ) :
    scaledInvSum n p = zeta p / (4 * (n : ℝ) ^ p) := by
  unfold scaledInvSum zeta
  calc
    (∑' k : ℕ, 1 / (4 * ((n * (k + 1) : ℕ) : ℝ) ^ p)) =
        ∑' k : ℕ, (1 / (4 * (n : ℝ) ^ p)) *
          (1 / ((k + 1 : ℕ) : ℝ) ^ p) := by
      apply tsum_congr
      intro k
      simp only [Nat.cast_mul, mul_pow]
      ring
    _ = (1 / (4 * (n : ℝ) ^ p)) *
          ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ p := tsum_mul_left
    _ = _ := by ring

lemma summable_scaledInvSum (n p : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / (4 * ((n * (k + 1) : ℕ) : ℝ) ^ p)) := by
  have h := (summable_inv_nat_succ_pow hp).mul_left (1 / (4 * (n : ℝ) ^ p))
  apply h.congr
  intro k
  simp only [Nat.cast_mul, mul_pow]
  ring

lemma summable_multipleSum (n : ℕ) (hn : 0 < n) :
    Summable (fun k : ℕ => coeff (n * (k + 1))) := by
  apply Summable.of_nonneg_of_le
    (fun k => coeff_nonneg (Nat.mul_pos hn (Nat.succ_pos k)))
    (fun k => coeff_upper (Nat.mul_pos hn (Nat.succ_pos k)))
  exact (summable_scaledInvSum n 3 (by omega)).add
    (summable_scaledInvSum n 5 (by omega))

lemma multipleSum_lower (n : ℕ) (hn : 0 < n) :
    zeta 3 / (4 * (n : ℝ) ^ 3) ≤ multipleSum n := by
  rw [← scaledInvSum_eq n 3]
  exact Summable.tsum_le_tsum
    (fun k => coeff_lower (Nat.mul_pos hn (Nat.succ_pos k)))
    (summable_scaledInvSum n 3 (by omega)) (summable_multipleSum n hn)

lemma multipleSum_upper (n : ℕ) (hn : 0 < n) :
    multipleSum n ≤ zeta 3 / (4 * (n : ℝ) ^ 3) + zeta 5 / (4 * (n : ℝ) ^ 5) := by
  rw [← scaledInvSum_eq n 3, ← scaledInvSum_eq n 5]
  unfold scaledInvSum
  rw [← Summable.tsum_add
    (summable_scaledInvSum n 3 (by omega)) (summable_scaledInvSum n 5 (by omega))]
  exact Summable.tsum_le_tsum
    (fun k => coeff_upper (Nat.mul_pos hn (Nat.succ_pos k)))
    (summable_multipleSum n hn)
    ((summable_scaledInvSum n 3 (by omega)).add
      (summable_scaledInvSum n 5 (by omega)))

lemma tendsto_inv_nat_sq :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  simpa [div_pow] using h

lemma tendsto_scaled_correction :
    Tendsto (fun n : ℕ => zeta 5 / (4 * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have h := tendsto_inv_nat_sq.const_mul (zeta 5 / 4)
  convert h using 1 <;> simp <;> ring

/-- The odd-parity lattice asymptotic, in the equivalent form where the
multiples of `n` are summed.  The extraneous `n=0` value cannot affect the
limit. -/
theorem tendsto_cubed_multipleSum :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * multipleSum n) atTop
      (𝓝 (zeta 3 / 4)) := by
  have hu : Tendsto (fun n : ℕ => zeta 3 / 4 + zeta 5 / (4 * (n : ℝ) ^ 2))
      atTop (𝓝 (zeta 3 / 4)) := by
    simpa using tendsto_const_nhds.add tendsto_scaled_correction
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => zeta 3 / 4) atTop _) hu
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    calc
      zeta 3 / 4 = (n : ℝ) ^ 3 * (zeta 3 / (4 * (n : ℝ) ^ 3)) := by
        field_simp [hnR] <;> ring
      _ ≤ (n : ℝ) ^ 3 * multipleSum n :=
        mul_le_mul_of_nonneg_left (multipleSum_lower n hn) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (n : ℝ) ^ 3 * multipleSum n ≤
          (n : ℝ) ^ 3 * (zeta 3 / (4 * (n : ℝ) ^ 3) +
            zeta 5 / (4 * (n : ℝ) ^ 5)) :=
        mul_le_mul_of_nonneg_left (multipleSum_upper n hn) (by positivity)
      _ = zeta 3 / 4 + zeta 5 / (4 * (n : ℝ) ^ 2) := by
        field_simp [hnR] <;> ring

/-- The card's lattice sum, with its explicit lower limit `m ≥ 1`. -/
def latticeSum (l : ℕ) : ℝ :=
  ∑' m : {m : ℕ // 0 < m ∧ l ∣ 2 * m}, coeff m

/-- Positive multiples of `n`, viewed as the lattice indices selected by an
equivalent divisibility predicate. -/
def multipleEquiv (l n : ℕ) (hn : 0 < n)
    (h : ∀ m : ℕ, l ∣ 2 * m ↔ n ∣ m) :
    ℕ ≃ {m : ℕ // 0 < m ∧ l ∣ 2 * m} := by
  let e : ℕ → {m : ℕ // 0 < m ∧ l ∣ 2 * m} := fun k =>
    ⟨n * (k + 1), Nat.mul_pos hn (Nat.succ_pos k), (h _).2 (dvd_mul_right n (k + 1))⟩
  apply Equiv.ofBijective e
  constructor
  · intro a b hab
    have hmul : n * (a + 1) = n * (b + 1) := congrArg Subtype.val hab
    have hadd := Nat.mul_left_cancel hn hmul
    omega
  · rintro ⟨m, hm, hml⟩
    have hnm : n ∣ m := (h m).1 hml
    rcases hnm with ⟨q, rfl⟩
    have hq : 0 < q := by
      by_contra hq0
      have : q = 0 := by omega
      subst q
      simp at hm
    refine ⟨q - 1, ?_⟩
    apply Subtype.ext
    change n * (q - 1 + 1) = n * q
    congr 1
    omega

lemma latticeSum_eq_multipleSum (l n : ℕ) (hn : 0 < n)
    (h : ∀ m : ℕ, l ∣ 2 * m ↔ n ∣ m) :
    latticeSum l = multipleSum n := by
  let e := multipleEquiv l n hn h
  change (∑' m : {m : ℕ // 0 < m ∧ l ∣ 2 * m}, coeff m) =
    ∑' k : ℕ, coeff (n * (k + 1))
  exact (Equiv.tsum_eq e (fun m => coeff m)).symm

lemma odd_dvd_two_mul {l : ℕ} (hl : Odd l) (m : ℕ) : l ∣ 2 * m ↔ l ∣ m := by
  have hc : l.Coprime 2 := Nat.coprime_two_right.mpr hl
  exact (hc.dvd_mul_left)

lemma two_mul_succ_dvd_two_mul (n m : ℕ) : 2 * (n + 1) ∣ 2 * m ↔ n + 1 ∣ m := by
  exact Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)

lemma riemannZeta_three_re : (riemannZeta 3).re = zeta 3 := by
  have h := congrArg Complex.re ofReal_zeta_three
  simpa using h.symm

/-- The exact doubling identity visible in small odd-cycle calculations. -/
theorem latticeSum_two_mul_of_odd {l : ℕ} (hl : Odd l) (hn : 0 < l) :
    latticeSum (2 * l) = latticeSum l := by
  rw [latticeSum_eq_multipleSum (2 * l) l hn
      (fun m => Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)),
    latticeSum_eq_multipleSum l l hn (odd_dvd_two_mul hl)]

theorem tendsto_cubed_latticeSum_odd :
    Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ 3 * latticeSum (2 * n + 1))
      atTop (𝓝 (zeta 3 / 4)) := by
  have hmap : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := fun n => 2 * n + 1)
      (fun n => by omega) tendsto_id
  apply (tendsto_cubed_multipleSum.comp hmap).congr
  intro n
  simp only [Function.comp_apply]
  rw [latticeSum_eq_multipleSum (2 * n + 1) (2 * n + 1) (by omega)
    (odd_dvd_two_mul ⟨n, by omega⟩)]

theorem tendsto_cubed_latticeSum_even :
    Tendsto (fun n : ℕ => ((2 * (n + 1) : ℕ) : ℝ) ^ 3 * latticeSum (2 * (n + 1)))
      atTop (𝓝 (2 * zeta 3)) := by
  have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 3 * multipleSum (n + 1))
      atTop (𝓝 (zeta 3 / 4)) :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_cubed_multipleSum
  have h8 := hshift.const_mul 8
  convert h8 using 1
  · ext n
    rw [latticeSum_eq_multipleSum (2 * (n + 1)) (n + 1) (by omega)
      (two_mul_succ_dvd_two_mul n)]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · ring

/-- Quantitative finite-length bounds behind the odd limit. -/
lemma cubed_latticeSum_odd_bounds (n : ℕ) :
    zeta 3 / 4 ≤ ((2 * n + 1 : ℕ) : ℝ) ^ 3 * latticeSum (2 * n + 1) ∧
      ((2 * n + 1 : ℕ) : ℝ) ^ 3 * latticeSum (2 * n + 1) ≤
        zeta 3 / 4 + zeta 5 / (4 * ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  have hl : 0 < 2 * n + 1 := by omega
  have hlR : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hl)
  rw [latticeSum_eq_multipleSum (2 * n + 1) (2 * n + 1) hl
    (odd_dvd_two_mul ⟨n, by omega⟩)]
  constructor
  · calc
      zeta 3 / 4 = ((2 * n + 1 : ℕ) : ℝ) ^ 3 *
        (zeta 3 / (4 * ((2 * n + 1 : ℕ) : ℝ) ^ 3)) := by
          field_simp [hlR] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multipleSum_lower _ hl) (by positivity)
  · calc
      ((2 * n + 1 : ℕ) : ℝ) ^ 3 * multipleSum (2 * n + 1) ≤
          ((2 * n + 1 : ℕ) : ℝ) ^ 3 *
            (zeta 3 / (4 * ((2 * n + 1 : ℕ) : ℝ) ^ 3) +
              zeta 5 / (4 * ((2 * n + 1 : ℕ) : ℝ) ^ 5)) :=
        mul_le_mul_of_nonneg_left (multipleSum_upper _ hl) (by positivity)
      _ = _ := by field_simp [hlR] <;> ring

/-- Quantitative finite-length bounds behind the even limit. -/
lemma cubed_latticeSum_even_bounds (n : ℕ) :
    2 * zeta 3 ≤ ((2 * (n + 1) : ℕ) : ℝ) ^ 3 * latticeSum (2 * (n + 1)) ∧
      ((2 * (n + 1) : ℕ) : ℝ) ^ 3 * latticeSum (2 * (n + 1)) ≤
        2 * zeta 3 + 2 * zeta 5 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hn : 0 < n + 1 := by omega
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [latticeSum_eq_multipleSum (2 * (n + 1)) (n + 1) hn
    (two_mul_succ_dvd_two_mul n)]
  constructor
  · calc
      2 * zeta 3 = ((2 * (n + 1) : ℕ) : ℝ) ^ 3 *
        (zeta 3 / (4 * ((n + 1 : ℕ) : ℝ) ^ 3)) := by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          field_simp [hnR] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multipleSum_lower _ hn) (by positivity)
  · calc
      ((2 * (n + 1) : ℕ) : ℝ) ^ 3 * multipleSum (n + 1) ≤
          ((2 * (n + 1) : ℕ) : ℝ) ^ 3 *
            (zeta 3 / (4 * ((n + 1 : ℕ) : ℝ) ^ 3) +
              zeta 5 / (4 * ((n + 1 : ℕ) : ℝ) ^ 5)) :=
        mul_le_mul_of_nonneg_left (multipleSum_upper _ hn) (by positivity)
      _ = _ := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp [hnR] <;> ring

theorem tendsto_cubed_latticeSum_odd_riemann :
    Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ 3 * latticeSum (2 * n + 1))
      atTop (𝓝 ((riemannZeta 3).re / 4)) := by
  rw [riemannZeta_three_re]
  exact tendsto_cubed_latticeSum_odd

theorem tendsto_cubed_latticeSum_even_riemann :
    Tendsto (fun n : ℕ => ((2 * (n + 1) : ℕ) : ℝ) ^ 3 * latticeSum (2 * (n + 1)))
      atTop (𝓝 (2 * (riemannZeta 3).re)) := by
  rw [riemannZeta_three_re]
  exact tendsto_cubed_latticeSum_even

end B147

#print axioms B147.summable_inv_nat_pow
#print axioms B147.summable_inv_nat_succ_pow
#print axioms B147.ofReal_zeta_three
#print axioms B147.coeff_nonneg
#print axioms B147.coeff_lower
#print axioms B147.coeff_upper
#print axioms B147.scaledInvSum_eq
#print axioms B147.summable_scaledInvSum
#print axioms B147.summable_multipleSum
#print axioms B147.multipleSum_lower
#print axioms B147.multipleSum_upper
#print axioms B147.tendsto_inv_nat_sq
#print axioms B147.tendsto_scaled_correction
#print axioms B147.tendsto_cubed_multipleSum
#print axioms B147.multipleEquiv
#print axioms B147.latticeSum_eq_multipleSum
#print axioms B147.odd_dvd_two_mul
#print axioms B147.two_mul_succ_dvd_two_mul
#print axioms B147.riemannZeta_three_re
#print axioms B147.latticeSum_two_mul_of_odd
#print axioms B147.tendsto_cubed_latticeSum_odd
#print axioms B147.tendsto_cubed_latticeSum_even
#print axioms B147.cubed_latticeSum_odd_bounds
#print axioms B147.cubed_latticeSum_even_bounds
#print axioms B147.tendsto_cubed_latticeSum_odd_riemann
#print axioms B147.tendsto_cubed_latticeSum_even_riemann


/-! ## B107 — the Hopf exponent as a homogeneity weight

Integrated from `.ultramath/smwvvnwls/m16/B107.lean`.
-/

/-!
# B107: the finite algebraic part of the rational-map charge formula

The card uses the numerator `N = z^α * w^β`, denominator
`D = z^p + w^q`, and charge `α*q + β*p`.  Under the weighted action
`(z,w) ↦ (u^q*z, u^p*w)`, this file proves the exact homogeneity of `N`
and `D`.  Consequently the denominator zero locus is invariant, and when
`u^(p*q) = 1` the rational function `N/D` has weight exactly `α*q + β*p`.

The identification of this weighted winding/linking count with the Hopf
invariant is topological and is not redefined here.
-/

namespace B107

/-- The numerator in the displayed rational map. -/
def numerator {R : Type*} [CommSemiring R] (z w : R) (α β : ℕ) : R :=
  z ^ α * w ^ β

/-- The denominator in the displayed rational map. -/
def denominator {R : Type*} [CommSemiring R] (z w : R) (p q : ℕ) : R :=
  z ^ p + w ^ q

/-- The four-integer weight appearing in the card. -/
def weight (α β p q : ℕ) : ℕ := α * q + β * p

/-- The displayed rational function, with ordinary field division. -/
def rationalMap {K : Type*} [Field K] (z w : K) (α β p q : ℕ) : K :=
  numerator z w α β / denominator z w p q

/-- The numerator has precisely the weight asserted by B107. -/
theorem numerator_scaled {R : Type*} [CommSemiring R]
    (u z w : R) (α β p q : ℕ) :
    numerator (u ^ q * z) (u ^ p * w) α β =
      u ^ weight α β p q * numerator z w α β := by
  simp only [numerator, weight, mul_pow, ← pow_mul]
  rw [Nat.mul_comm q α, Nat.mul_comm p β, pow_add]
  ring

/-- The denominator is weighted-homogeneous of degree `p*q`. -/
theorem denominator_scaled {R : Type*} [CommSemiring R]
    (u z w : R) (p q : ℕ) :
    denominator (u ^ q * z) (u ^ p * w) p q =
      u ^ (p * q) * denominator z w p q := by
  simp only [denominator, mul_pow, ← pow_mul]
  rw [Nat.mul_comm q p, mul_add]

/-- Weighted scaling preserves the denominator knot as a zero locus. -/
theorem denominator_zero_of_scaled {R : Type*} [CommSemiring R]
    (u z w : R) (p q : ℕ) (h : denominator z w p q = 0) :
    denominator (u ^ q * z) (u ^ p * w) p q = 0 := by
  rw [denominator_scaled, h, mul_zero]

/-- On a denominator-preserving weighted action, the full rational function
has precisely the card's weight.  No nonvanishing hypothesis is needed:
field division by zero is total and the denominator is literally unchanged. -/
theorem rationalMap_scaled_of_denominator_fixed {K : Type*} [Field K]
    (u z w : K) (α β p q : ℕ) (hu : u ^ (p * q) = 1) :
    rationalMap (u ^ q * z) (u ^ p * w) α β p q =
      u ^ weight α β p q * rationalMap z w α β p q := by
  simp only [rationalMap, numerator_scaled, denominator_scaled, hu, one_mul,
    mul_div_assoc]

/-- The no-common-zero check on the punctured complex plane.  The sphere
condition implies `z ≠ 0 ∨ w ≠ 0`; positivity of `p,q` is the torus-knot
hypothesis.  The result includes zero numerator exponents. -/
theorem no_common_zero_on_punctured_plane {K : Type*} [Field K]
    (z w : K) (hzw : z ≠ 0 ∨ w ≠ 0) (α β p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    ¬ (numerator z w α β = 0 ∧ denominator z w p q = 0) := by
  rintro ⟨hn, hd⟩
  have hz : z = 0 ∨ w = 0 := by
    rcases mul_eq_zero.mp hn with h | h
    · exact Or.inl (eq_zero_of_pow_eq_zero h)
    · exact Or.inr (eq_zero_of_pow_eq_zero h)
  rcases hz with rfl | rfl
  · have hw : w ≠ 0 := by simpa using hzw
    have hwq : w ^ q = 0 := by
      simpa [denominator, Nat.ne_of_gt hp] using hd
    exact (pow_ne_zero q hw) hwq
  · have hz : z ≠ 0 := by simpa using hzw
    have hzp : z ^ p = 0 := by
      simpa [denominator, Nat.ne_of_gt hq] using hd
    exact (pow_ne_zero p hz) hzp

/-- With the unit-sphere condition carried explicitly, admissibility follows
for every nonnegative pair of numerator exponents. -/
theorem complex_sphere_admissible (z w : ℂ) (α β p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hs : z ≠ 0 ∨ w ≠ 0) :
    ¬ (z ^ α * w ^ β = 0 ∧ z ^ p + w ^ q = 0) := by
  exact no_common_zero_on_punctured_plane z w hs α β p q hp hq

/-- The usual complex unit `3`-sphere is contained in the punctured plane. -/
theorem complex_unit_sphere_punctured (z w : ℂ)
    (hs : Complex.normSq z + Complex.normSq w = 1) : z ≠ 0 ∨ w ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨rfl, rfl⟩
  norm_num at hs

/-- Admissibility stated with the literal complex unit-sphere equation. -/
theorem complex_unit_sphere_admissible (z w : ℂ) (α β p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hs : Complex.normSq z + Complex.normSq w = 1) :
    ¬ (z ^ α * w ^ β = 0 ∧ z ^ p + w ^ q = 0) := by
  exact no_common_zero_on_punctured_plane z w
    (complex_unit_sphere_punctured z w hs) α β p q hp hq

/-- Degenerate numerator check: a constant numerator has zero weight. -/
theorem constant_numerator_weight (p q : ℕ) : weight 0 0 p q = 0 := by
  simp [weight]

/-- The two linear Hopf-map checks at `p = q = 1`. -/
theorem linear_basepoint_weights :
    weight 1 0 1 1 = 1 ∧ weight 0 1 1 1 = 1 := by
  decide

/-- The five exact `T(3,4)` elimination cases printed on the card. -/
theorem T34_witnesses :
    weight 1 1 3 4 = 7 ∧
    weight 1 2 3 4 = 10 ∧
    weight 2 1 3 4 = 11 ∧
    weight 1 3 3 4 = 13 ∧
    weight 3 1 3 4 = 15 := by
  decide

/-- In particular, fixing this denominator does not fix the charge. -/
theorem T34_charges_pairwise_distinct :
    [weight 1 1 3 4, weight 1 2 3 4, weight 2 1 3 4,
      weight 1 3 3 4, weight 3 1 3 4].Nodup := by
  decide

/-- Arithmetic behind the converse: two distinct coprime denominator exponent
pairs admit numerator loadings with the same weight `7`.  Knot distinctness
itself is the standard torus-knot classification and is not proved here. -/
theorem shared_weight_different_exponent_pairs :
    weight 1 1 3 4 = weight 1 2 2 3 ∧
    Nat.Coprime 3 4 ∧ Nat.Coprime 2 3 ∧ (3, 4) ≠ (2, 3) := by
  decide

#print axioms B107.numerator_scaled
#print axioms B107.denominator_scaled
#print axioms B107.denominator_zero_of_scaled
#print axioms B107.rationalMap_scaled_of_denominator_fixed
#print axioms B107.no_common_zero_on_punctured_plane
#print axioms B107.complex_sphere_admissible
#print axioms B107.complex_unit_sphere_punctured
#print axioms B107.complex_unit_sphere_admissible
#print axioms B107.constant_numerator_weight
#print axioms B107.linear_basepoint_weights
#print axioms B107.T34_witnesses
#print axioms B107.T34_charges_pairwise_distinct
#print axioms B107.shared_weight_different_exponent_pairs

end B107


/-! ## B94 — the padding law, with the knot constant left external

Integrated from `.ultramath/smwvvnwls/m15/B94.lean`.
-/

/-!
# B94: fixed-block padding, normalized Hamming distance, and no wall

The matrices below are the already regularized finite matrices.  Thus the fixed
regulator is not an extra perturbation of the padding.  Nonvanishing determinants
are hypothesized where the logarithm of a product is split.
-/

open Filter Topology

/-- The exact scalar cancellation in the B94 padding family. -/
theorem b94_fixed_block_identity {n h : ℝ} (hn : 0 < n) (hh : 0 < h)
    (base delta : ℝ) :
    |(base + delta) / n - base / n| = (|delta| / h) * (h / n) := by
  have hdiff : (base + delta) / n - base / n = delta / n := by ring
  rw [hdiff, abs_div, abs_of_pos hn]
  field_simp

/-- The response along fixed-block padding is exactly `|δ| / n`, also at `n = 0`
with Lean's convention `x / 0 = 0`. -/
theorem b94_normalized_response (base delta : ℝ) (n : ℕ) :
    |(base + delta) / (n : ℝ) - base / (n : ℝ)| = |delta| / (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
      have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hdiff : (base + delta) / ((n + 1 : ℕ) : ℝ) - base / ((n + 1 : ℕ) : ℝ) =
          delta / ((n + 1 : ℕ) : ℝ) := by ring
      rw [hdiff, abs_div, abs_of_pos hn]

/-- The intensive response tends to zero as trivial padding increases. -/
theorem b94_response_tendsto_zero (base delta : ℝ) :
    Tendsto (fun n : ℕ => |(base + delta) / (n : ℝ) - base / (n : ℝ)|)
      atTop (𝓝 0) := by
  simpa only [b94_normalized_response] using
    (tendsto_const_div_atTop_nhds_zero_nat |delta|)

/-- Consequently no positive constant is a floor throughout the padding family. -/
theorem b94_no_positive_floor (base delta epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, n ≠ 0 ∧ |(base + delta) / (n : ℝ) - base / (n : ℝ)| < epsilon := by
  have ht := b94_response_tendsto_zero base delta
  have hev : ∀ᶠ n : ℕ in atTop,
      |(base + delta) / (n : ℝ) - base / (n : ℝ)| < epsilon :=
    ht.eventually (Iio_mem_nhds hepsilon)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N + 1, Nat.succ_ne_zero N, hN (N + 1) (Nat.le_succ N)⟩

/-- Hamming distance normalized by the number of points. -/
noncomputable def normalizedHamming {ι β : Type*} [Fintype ι] [DecidableEq β]
    (f g : ι → β) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card ι : ℝ)

/-- A nontrivial transposition differs from the identity at exactly two points. -/
theorem hammingDist_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) :
    hammingDist (Equiv.swap a b) (fun x => x) = 2 := by
  classical
  unfold hammingDist
  have hset : Finset.univ.filter (fun x => Equiv.swap a b x ≠ x) = {a, b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hxa : x = a
    · subst x
      simp [Equiv.swap_apply_left, Ne.symm hab]
    by_cases hxb : x = b
    · subst x
      simp [Equiv.swap_apply_right, hab]
    · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb, hxa, hxb]
  rw [hset, Finset.card_pair hab]

/-- In normalized Hamming distance, one transposition costs exactly `2 / n`. -/
theorem normalizedHamming_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) :
    normalizedHamming (Equiv.swap a b) (fun x => x) =
      2 / (Fintype.card ι : ℝ) := by
  rw [normalizedHamming, hammingDist_swap a b hab]
  norm_num

/-- The `Fin n` form of the normalized transposition cost. -/
theorem normalizedHamming_swap_fin {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    normalizedHamming (Equiv.swap a b) (fun x => x) = 2 / (n : ℝ) := by
  simpa using normalizedHamming_swap a b hab


/-- Append a fixed trivial/background block to an already regularized matrix. -/
def fixedBlockPad {r k : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin r ⊕ Fin k) (Fin r ⊕ Fin k) ℝ :=
  Matrix.fromBlocks A 0 0 T

/-- Logarithmic determinants split over the fixed block and its trivial padding. -/
theorem log_det_fixedBlockPad {r k : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) (hA : A.det ≠ 0) (hT : T.det ≠ 0) :
    Real.log (fixedBlockPad A T).det = Real.log A.det + Real.log T.det := by
  unfold fixedBlockPad
  rw [Matrix.det_fromBlocks_zero₂₁, Real.log_mul hA hT]

/-- The common padded background cancels exactly from the difference. -/
theorem log_det_fixedBlockPad_sub {r k : ℕ} (A A' : Matrix (Fin r) (Fin r) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) (hA : A.det ≠ 0) (hA' : A'.det ≠ 0)
    (hT : T.det ≠ 0) :
    Real.log (fixedBlockPad A' T).det - Real.log (fixedBlockPad A T).det =
      Real.log A'.det - Real.log A.det := by
  rw [log_det_fixedBlockPad A' T hA' hT, log_det_fixedBlockPad A T hA hT]
  ring

/-- **B94, finite block-padding form.**  Here `δ = log det A' - log det A` is
fixed with the two defect blocks, `h` is the fixed number of moved points, and
`r + k` is the total number of points after `k` trivial padding rows are added.
Thus the normalized response is `(|δ| / h) * (h / (r+k))`: the slope is exactly
independent of the amount of padding. -/
theorem b94_blockPadding_identity {r k h : ℕ} (hrk : 0 < r + k) (hh : 0 < h)
    (A A' : Matrix (Fin r) (Fin r) ℝ) (T : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.det ≠ 0) (hA' : A'.det ≠ 0) (hT : T.det ≠ 0) :
    |Real.log (fixedBlockPad A' T).det / ((r + k : ℕ) : ℝ) -
        Real.log (fixedBlockPad A T).det / ((r + k : ℕ) : ℝ)| =
      (|Real.log A'.det - Real.log A.det| / (h : ℝ)) *
        ((h : ℝ) / ((r + k : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < ((r + k : ℕ) : ℝ) := by exact_mod_cast hrk
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  rw [log_det_fixedBlockPad A' T hA' hT, log_det_fixedBlockPad A T hA hT]
  have hrewrite : Real.log A'.det + Real.log T.det =
      (Real.log A.det + Real.log T.det) + (Real.log A'.det - Real.log A.det) := by
    ring
  rw [hrewrite]
  exact b94_fixed_block_identity hn hhR _ _

/-- Specialize the transposition calculation to two points: the normalized
Hamming cost is one. -/
theorem normalizedHamming_swap_two (a b : Fin 2) (hab : a ≠ b) :
    normalizedHamming (Equiv.swap a b) (fun x => x) = 1 := by
  rw [normalizedHamming_swap_fin a b hab]
  norm_num


#print axioms b94_fixed_block_identity
#print axioms b94_normalized_response
#print axioms b94_response_tendsto_zero
#print axioms b94_no_positive_floor
#print axioms hammingDist_swap
#print axioms normalizedHamming_swap
#print axioms normalizedHamming_swap_fin
#print axioms log_det_fixedBlockPad
#print axioms log_det_fixedBlockPad_sub
#print axioms b94_blockPadding_identity
#print axioms normalizedHamming_swap_two

