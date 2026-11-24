/-
Fourth batch: finite kernels and refutations for the Operator-First Relational Atlas.

The brief for this batch was the same as the third: read each card's own displayed formula
and try to break it before proving it. A refutation counts as a result. Every section is
wrapped in its own `section ... end` so that a file's `open`s cannot leak into the next one.
Nothing in the earlier modules is modified.
-/
import Mathlib

noncomputable section


/-! ## B179 — the fold normal form, and the point where the chart degenerates

Integrated from `.ultramath/smwu0t12t/m12/B179.lean`.
-/
section


/-!
# B179: the fold normal form

The archived card displays
`ds² = dX²/(4c²X) = dλ²/c²`, with `X = λ²`, and says that
`λ ↦ -λ` is an isometry.  We formalize `ds²` as a symmetric bilinear form on
one-dimensional tangent vectors, and `dX` as the derivative pushforward.
Thus the main theorem is not merely an assertion about two named symbols:
it holds for every pair of tangent vectors.

The singular expression is evaluated in real division, so the coordinate
identity needs `λ ≠ 0`.  This excludes only the point at which the displayed
`1/X` coefficient itself is singular.  The equivalent regular form is defined
at the fold as well.  The hypothesis `c ≠ 0` is the card's non-degenerate
horizon hypothesis (`c = κ ≠ 0`) and makes the denominators nondegenerate.
-/

namespace RelationalAtlas.B179

noncomputable section

/-- The squared (signed) lapse coordinate in the card, `X = λ²`. -/
def lapse (lambda : ℝ) : ℝ := lambda ^ 2

/-- The derivative pushforward of a tangent vector, i.e. the value of `df`. -/
def tangent (f : ℝ → ℝ) (x v : ℝ) : ℝ := deriv f x * v

/-- The singular form `dX²/(4c²X)`, read bilinearly. -/
def singularFoldForm (c X dX₀ dX₁ : ℝ) : ℝ :=
  dX₀ * dX₁ / (4 * c ^ 2 * X)

/-- The regular form `dλ²/c²`, read bilinearly. -/
def regularFoldForm (c dl0 dl1 : ℝ) : ℝ :=
  dl0 * dl1 / c ^ 2

lemma lapse_hasDerivAt (lambda : ℝ) : HasDerivAt lapse (2 * lambda) lambda := by
  change HasDerivAt (fun x : ℝ => x ^ 2) (2 * lambda) lambda
  convert (hasDerivAt_pow 2 lambda) using 1
  norm_num

lemma tangent_lapse (lambda v : ℝ) : tangent lapse lambda v = 2 * lambda * v := by
  unfold tangent
  rw [(lapse_hasDerivAt lambda).deriv]

/-- **B179's displayed coordinate identity.**  The factor `4` is exactly
 cancelled by `(d(λ²))² = 4λ²(dλ)²`. -/
theorem b179_fold_coordinate_change
    (c lambda v₀ v₁ : ℝ) (hc : c ≠ 0) (hlambda : lambda ≠ 0) :
    singularFoldForm c (lapse lambda)
        (tangent lapse lambda v₀) (tangent lapse lambda v₁) =
      regularFoldForm c v₀ v₁ := by
  rw [singularFoldForm, regularFoldForm, tangent_lapse, tangent_lapse, lapse]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hlambda2 : lambda ^ 2 ≠ 0 := pow_ne_zero 2 hlambda
  field_simp
  ring

/-- The quadratic (line-element) specialization of B179, for `dλ = v`. -/
theorem b179_fold_line_element
    (c lambda v : ℝ) (hc : c ≠ 0) (hlambda : lambda ≠ 0) :
    singularFoldForm c (lapse lambda)
        (tangent lapse lambda v) (tangent lapse lambda v) = v ^ 2 / c ^ 2 := by
  rw [b179_fold_coordinate_change c lambda v v hc hlambda]
  simp [regularFoldForm, pow_two]

/-- The squared coordinate is unchanged by reflection. -/
theorem b179_lapse_even (lambda : ℝ) : lapse (-lambda) = lapse lambda := by
  simp [lapse]

/-- The regular form really is non-null, as the card's shape-space remark
requires: a nonzero tangent vector has strictly positive squared length. -/
theorem b179_regularFoldForm_pos
    (c v : ℝ) (hc : c ≠ 0) (hv : v ≠ 0) : 0 < regularFoldForm c v v := by
  unfold regularFoldForm
  exact div_pos (mul_self_pos.mpr hv) (sq_pos_of_ne_zero hc)

/-- The necessary qualification at the fold.  With the raw singular quotient,
the witness `c = 1`, `λ = 0`, `dλ = 1` gives `0`, not `1`.  Thus the displayed
coordinate calculation belongs to either side (`λ ≠ 0`), while the regular
form above supplies the extension across `λ = 0`. -/
theorem b179_raw_formula_fails_at_fold :
    singularFoldForm 1 (lapse 0)
        (tangent lapse 0 1) (tangent lapse 0 1) ≠ (1 : ℝ) ^ 2 / 1 ^ 2 := by
  rw [tangent_lapse]
  norm_num [singularFoldForm, lapse]

/-- In contrast, the regular doubled-side value at that same tangent vector is
exactly the nonzero value `1`, including at the fold. -/
theorem b179_regular_formula_at_fold : regularFoldForm 1 1 1 = (1 : ℝ) := by
  norm_num [regularFoldForm]

lemma reflection_hasDerivAt (lambda : ℝ) :
    HasDerivAt (fun x : ℝ => -x) (-1) lambda := hasDerivAt_neg' lambda

lemma tangent_reflection (lambda v : ℝ) :
    tangent (fun x : ℝ => -x) lambda v = -v := by
  unfold tangent
  rw [(reflection_hasDerivAt lambda).deriv]
  ring

/-- **B179's reflection isometry**, at the level of its regular metric form.
No hypothesis at `λ = 0` is needed: this is the smooth doubled-side form. -/
theorem b179_reflection_isometry (c lambda v₀ v₁ : ℝ) :
    regularFoldForm c
        (tangent (fun x : ℝ => -x) lambda v₀)
        (tangent (fun x : ℝ => -x) lambda v₁) =
      regularFoldForm c v₀ v₁ := by
  simp only [tangent_reflection, regularFoldForm]
  ring

/-- The distance associated to the one-dimensional regular line element,
with its constant positive scale `1 / |c|`. -/
def foldDist (c x y : ℝ) : ℝ := |x - y| / |c|

/-- Reflection is an isometry for the distance integrating the regular form. -/
theorem b179_reflection_isometry_dist (c x y : ℝ) :
    foldDist c (-x) (-y) = foldDist c x y := by
  unfold foldDist
  congr 1
  rw [show -x - -y = -(x - y) by ring, abs_neg]

/-- The card's horizon specialization: `X = N`, `c = κ`. -/
theorem b179_horizon_specialization
    (kappa N sqrtN v : ℝ) (hkappa : kappa ≠ 0) (hsqrtN : sqrtN ≠ 0)
    (hN : N = lapse sqrtN) :
    singularFoldForm kappa N
        (tangent lapse sqrtN v) (tangent lapse sqrtN v) = v ^ 2 / kappa ^ 2 := by
  subst N
  exact b179_fold_line_element kappa sqrtN v hkappa hsqrtN

/-- The card's coplanar-wall specialization (`c = 1`), with no extra scale. -/
theorem b179_shape_wall_specialization
    (w₃ sqrtw₃ v : ℝ) (hsqrtw₃ : sqrtw₃ ≠ 0) (hw₃ : w₃ = lapse sqrtw₃) :
    singularFoldForm 1 w₃
        (tangent lapse sqrtw₃ v) (tangent lapse sqrtw₃ v) = v ^ 2 := by
  subst w₃
  simpa using b179_fold_line_element 1 sqrtw₃ v one_ne_zero hsqrtw₃

#print axioms lapse_hasDerivAt
#print axioms tangent_lapse
#print axioms b179_fold_coordinate_change
#print axioms b179_fold_line_element
#print axioms b179_regularFoldForm_pos
#print axioms b179_raw_formula_fails_at_fold
#print axioms b179_regular_formula_at_fold
#print axioms b179_lapse_even
#print axioms reflection_hasDerivAt
#print axioms tangent_reflection
#print axioms b179_reflection_isometry
#print axioms b179_reflection_isometry_dist
#print axioms b179_horizon_specialization
#print axioms b179_shape_wall_specialization

end

end RelationalAtlas.B179


end

/-! ## B203 — the recombination length and the factor four

Integrated from `.ultramath/smwu0t12t/m3/B203.lean`.
-/
section

/-
B203 — The book ratios fix the route; the signs fix the endpoint.

The archived card has SHA-256
9e5829dfd69864963cfc574410553e6cfcb1922d9504d08b402f155635468dda.
It displays

  Lrec = 2 Σ |rⱼ| = 2 Σ artanh √(E⁻ⱼ/E⁺ⱼ),
  Dend = 2 |Σ rⱼ|,
  Lrec - Dend = 4 min(R₊,R₋),
  rⱼ = (1/2) log(Eⱼ₊₁/Eⱼ),
  equality iff every step has one sign.

We prove all these finite identities.  The equality statement reads "one sign"
as one *weak* sign, so zero steps are allowed: either every rⱼ ≥ 0 or every
rⱼ ≤ 0.  The artanh statement uses the card's own explanatory hypothesis
E⁻ⱼ/E⁺ⱼ = tanh²(rⱼ); no additional sign convention for rⱼ is needed.
-/

noncomputable section

namespace RelationalAtlas.B203

open scoped BigOperators

/-- The total forward increment, called `R₊` on the card. -/
def positiveTotal (n : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, max (r j) 0

/-- The total backward increment, called `R₋` on the card (a nonnegative number). -/
def negativeTotal (n : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, max (-r j) 0

/-- The route length `Lrec` on the card. -/
def routeLength (n : ℕ) (r : ℕ → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range n, |r j|

/-- The endpoint distance `Dend` on the card. -/
def endDistance (n : ℕ) (r : ℕ → ℝ) : ℝ :=
  2 * |∑ j ∈ Finset.range n, r j|

/-- The card's logarithmic increment for positive vertex energies `E`. -/
def chainIncrement (E : ℕ → ℝ) (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (E (j + 1) / E j)

private lemma step_decomposition (x : ℝ) :
    x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with hx | hx
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]

private lemma abs_step_decomposition (x : ℝ) :
    |x| = max x 0 + max (-x) 0 := by
  rcases le_total 0 x with hx | hx
  · simp [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · simp [abs_of_nonpos hx, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]

/-- Splitting a sum into its forward and backward totals gives the signed sum. -/
theorem sum_eq_positive_sub_negative (n : ℕ) (r : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, r j) = positiveTotal n r - negativeTotal n r := by
  unfold positiveTotal negativeTotal
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ step_decomposition (r j)

/-- The same splitting gives the sum of absolute increments. -/
theorem sum_abs_eq_positive_add_negative (n : ℕ) (r : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, |r j|) = positiveTotal n r + negativeTotal n r := by
  unfold positiveTotal negativeTotal
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ abs_step_decomposition (r j)

private lemma two_total_defect (a b : ℝ) :
    2 * (a + b) - 2 * |a - b| = 4 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- **B203's exact defect formula, including the factor four.** -/
theorem route_sub_end_eq_four_min (n : ℕ) (r : ℕ → ℝ) :
    routeLength n r - endDistance n r =
      4 * min (positiveTotal n r) (negativeTotal n r) := by
  unfold routeLength endDistance
  rw [sum_abs_eq_positive_add_negative, sum_eq_positive_sub_negative]
  exact two_total_defect _ _

/-- Route and endpoint agree exactly when the smaller signed total vanishes. -/
theorem route_eq_end_iff_min_eq_zero (n : ℕ) (r : ℕ → ℝ) :
    routeLength n r = endDistance n r ↔
      min (positiveTotal n r) (negativeTotal n r) = 0 := by
  have hdefect := route_sub_end_eq_four_min n r
  constructor
  · intro h
    have hz : routeLength n r - endDistance n r = 0 := sub_eq_zero.mpr h
    rw [hdefect] at hz
    linarith
  · intro h
    rw [h] at hdefect
    simp only [mul_zero, sub_eq_zero] at hdefect
    exact hdefect

private lemma positiveTotal_nonneg (n : ℕ) (r : ℕ → ℝ) :
    0 ≤ positiveTotal n r := by
  exact Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

private lemma negativeTotal_nonneg (n : ℕ) (r : ℕ → ℝ) :
    0 ≤ negativeTotal n r := by
  exact Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

private lemma min_totals_eq_zero_iff (n : ℕ) (r : ℕ → ℝ) :
    min (positiveTotal n r) (negativeTotal n r) = 0 ↔
      positiveTotal n r = 0 ∨ negativeTotal n r = 0 := by
  constructor
  · intro h
    rcases le_total (positiveTotal n r) (negativeTotal n r) with hab | hba
    · exact Or.inl ((min_eq_left hab).symm.trans h)
    · exact Or.inr ((min_eq_right hba).symm.trans h)
  · rintro (h | h)
    · rw [h, min_eq_left (negativeTotal_nonneg n r)]
    · rw [h, min_eq_right (positiveTotal_nonneg n r)]

private lemma positiveTotal_eq_zero_iff (n : ℕ) (r : ℕ → ℝ) :
    positiveTotal n r = 0 ↔ ∀ j ∈ Finset.range n, r j ≤ 0 := by
  constructor
  · intro h j hj
    have hz : max (r j) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ Finset.range n) ↦ le_max_right (r k) 0)).mp h j hj
    calc
      r j ≤ max (r j) 0 := le_max_left _ _
      _ = 0 := hz
  · intro h
    exact Finset.sum_eq_zero fun j hj ↦ max_eq_right (h j hj)

private lemma negativeTotal_eq_zero_iff (n : ℕ) (r : ℕ → ℝ) :
    negativeTotal n r = 0 ↔ ∀ j ∈ Finset.range n, 0 ≤ r j := by
  constructor
  · intro h j hj
    have hz : max (-r j) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ Finset.range n) ↦ le_max_right (-r k) 0)).mp h j hj
    have hneg : -r j ≤ 0 := calc
      -r j ≤ max (-r j) 0 := le_max_left _ _
      _ = 0 := hz
    exact neg_nonpos.mp hneg
  · intro h
    exact Finset.sum_eq_zero fun j hj ↦ max_eq_right (neg_nonpos.mpr (h j hj))

/-- **B203's equality case.**  Equality means that all steps have one weak sign.
Both alternatives hold for the empty chain, and zero steps may occur in either. -/
theorem route_eq_end_iff_one_weak_sign (n : ℕ) (r : ℕ → ℝ) :
    routeLength n r = endDistance n r ↔
      (∀ j ∈ Finset.range n, 0 ≤ r j) ∨
        (∀ j ∈ Finset.range n, r j ≤ 0) := by
  rw [route_eq_end_iff_min_eq_zero, min_totals_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr ((positiveTotal_eq_zero_iff n r).mp h)
    · exact Or.inl ((negativeTotal_eq_zero_iff n r).mp h)
  · rintro (h | h)
    · exact Or.inr ((negativeTotal_eq_zero_iff n r).mpr h)
    · exact Or.inl ((positiveTotal_eq_zero_iff n r).mpr h)

private lemma tanh_abs (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rcases le_total 0 x with hx | hx
  · have ht : 0 ≤ Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
    rw [abs_of_nonneg hx, abs_of_nonneg ht]
  · have hs : Real.sinh x ≤ 0 := by
      have h := Real.sinh_nonneg_iff.mpr (neg_nonneg.mpr hx)
      rw [Real.sinh_neg] at h
      linarith
    have ht : Real.tanh x ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg hs (Real.cosh_pos x).le
    rw [abs_of_nonpos hx, abs_of_nonpos ht, Real.tanh_neg]

/-- Taking `artanh` undoes absolute `tanh`, with the same signless absolute value
that occurs in the card's book ratios. -/
theorem artanh_abs_tanh (x : ℝ) :
    Real.artanh |Real.tanh x| = |x| := by
  rw [← tanh_abs, Real.artanh_tanh]

/-- **The per-edge book-ratio formula.**  This is valid for either sign of `r`. -/
theorem abs_eq_artanh_sqrt_book_ratio {r eminus eplus : ℝ}
    (hratio : eminus / eplus = (Real.tanh r) ^ 2) :
    |r| = Real.artanh (Real.sqrt (eminus / eplus)) := by
  rw [hratio, Real.sqrt_sq_eq_abs, artanh_abs_tanh]

/-- **B203's second expression for route length**, under the book-ratio hypothesis
stated in the card's "Why it holds" paragraph. -/
theorem routeLength_eq_book_sum (n : ℕ) (r eminus eplus : ℕ → ℝ)
    (hbook : ∀ j ∈ Finset.range n,
      eminus j / eplus j = (Real.tanh (r j)) ^ 2) :
    routeLength n r =
      2 * ∑ j ∈ Finset.range n,
        Real.artanh (Real.sqrt (eminus j / eplus j)) := by
  unfold routeLength
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦ abs_eq_artanh_sqrt_book_ratio (hbook j hj)

/-- **The logarithmic increments telescope.**  Positivity is assumed only at the
`n+1` vertices actually visited. -/
theorem sum_chainIncrement {n : ℕ} (E : ℕ → ℝ)
    (hE : ∀ j ≤ n, 0 < E j) :
    (∑ j ∈ Finset.range n, chainIncrement E j) =
      (1 / 2 : ℝ) * (Real.log (E n) - Real.log (E 0)) := by
  calc
    (∑ j ∈ Finset.range n, chainIncrement E j) =
        ∑ j ∈ Finset.range n,
          (1 / 2 : ℝ) * (Real.log (E (j + 1)) - Real.log (E j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hnz : E j ≠ 0 := ne_of_gt (hE j hjn.le)
      have hsnz : E (j + 1) ≠ 0 := ne_of_gt (hE (j + 1) hjn)
      rw [chainIncrement, Real.log_div hsnz hnz]
    _ = (1 / 2 : ℝ) *
        ∑ j ∈ Finset.range n, (Real.log (E (j + 1)) - Real.log (E j)) := by
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * (Real.log (E n) - Real.log (E 0)) :=
      congrArg (fun x : ℝ ↦ (1 / 2 : ℝ) * x)
        (Finset.sum_range_sub (fun j ↦ Real.log (E j)) n)

/-- The out-and-back example in the card, with its decimals read as exact rationals. -/
theorem out_and_back_witness :
    let r : ℕ → ℝ := fun j => if j = 0 then (2 / 5 : ℝ) else -(2 / 5 : ℝ)
    routeLength 2 r = 8 / 5 ∧ endDistance 2 r = 0 := by
  dsimp
  norm_num [routeLength, endDistance, Finset.sum_range_succ]

/-- The first three-step witness in the card: route 2.2, endpoint 1.0, defect 1.2. -/
theorem first_three_step_witness :
    let r : ℕ → ℝ := fun j =>
      if j = 0 then (2 / 5 : ℝ) else if j = 1 then (2 / 5 : ℝ) else -(3 / 10 : ℝ)
    routeLength 3 r = 11 / 5 ∧ endDistance 3 r = 1 ∧
      routeLength 3 r - endDistance 3 r = 6 / 5 := by
  dsimp
  norm_num [routeLength, endDistance, Finset.sum_range_succ]

/-- The second three-step witness: route 2.2, endpoint 0.6, defect 1.6. -/
theorem second_three_step_witness :
    let r : ℕ → ℝ := fun j =>
      if j = 0 then (2 / 5 : ℝ) else if j = 1 then -(2 / 5 : ℝ) else (3 / 10 : ℝ)
    routeLength 3 r = 11 / 5 ∧ endDistance 3 r = 3 / 5 ∧
      routeLength 3 r - endDistance 3 r = 8 / 5 := by
  dsimp
  norm_num [routeLength, endDistance, Finset.sum_range_succ]

#print axioms step_decomposition
#print axioms abs_step_decomposition
#print axioms two_total_defect
#print axioms positiveTotal_nonneg
#print axioms negativeTotal_nonneg
#print axioms min_totals_eq_zero_iff
#print axioms positiveTotal_eq_zero_iff
#print axioms negativeTotal_eq_zero_iff
#print axioms tanh_abs
#print axioms RelationalAtlas.B203.sum_eq_positive_sub_negative
#print axioms RelationalAtlas.B203.sum_abs_eq_positive_add_negative
#print axioms RelationalAtlas.B203.route_sub_end_eq_four_min
#print axioms RelationalAtlas.B203.route_eq_end_iff_min_eq_zero
#print axioms RelationalAtlas.B203.route_eq_end_iff_one_weak_sign
#print axioms RelationalAtlas.B203.artanh_abs_tanh
#print axioms RelationalAtlas.B203.abs_eq_artanh_sqrt_book_ratio
#print axioms RelationalAtlas.B203.routeLength_eq_book_sum
#print axioms RelationalAtlas.B203.sum_chainIncrement
#print axioms RelationalAtlas.B203.out_and_back_witness
#print axioms RelationalAtlas.B203.first_three_step_witness
#print axioms RelationalAtlas.B203.second_three_step_witness

end RelationalAtlas.B203


end

/-! ## B207 — the hyperbolic system, with a > 0 shown to be necessary

Integrated from `.ultramath/smwu0t12t/m9/B207.lean`.
-/
section


/-!
# B207 — the doubled Schwarzschild slice

Source: `atlas/cards/html/B207.html`, SHA-256
`8640b9e576f9d94c8b792cc171b23ff5c97f9716245756772fcbeca35c0cda33`.
The displayed formulas are

* `(1 + λ)ψ/2 = 1`, `(1 − λ)ψ/2 = a/ρ`,
  `λ = tanh (log (ρ/a) / 2)`;
* `ψ = 1 + a/ρ`, `λ = (1 − a/ρ)/(1 + a/ρ)`, and inversion
  `ρ ↦ a²/ρ` sends `λ` to `−λ`;
* Reissner–Nordström: `r₊r₋ = Q²`, `τ₊ = −τ₋`.

The card's "Why it holds" also displays `r = Q exp τ` and
`(r + Q²/r)/2 = Q cosh τ`; those identities are formalised below too.
The physical domain is `0 < a`, `0 < ρ`, and `0 < Q < M`.  The last
section includes the `a = 0` boundary witness showing why the mass
positivity cannot simply be dropped from the tanh and inversion claims.
No geometric or graph-theoretic consequence is asserted.
-/

noncomputable section

namespace RelationalAtlas.B207

open Real

/-- The isotropic Schwarzschild conformal factor in the card. -/
def psi (a ρ : ℝ) : ℝ := 1 + a / ρ

/-- The half-amplitude difference in the card, exactly as displayed. -/
def lambda (a ρ : ℝ) : ℝ := (1 - a / ρ) / (1 + a / ρ)

/-- First conformal-factor identity. -/
theorem factor_plus (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) :
    (1 + lambda a ρ) * psi a ρ / 2 = 1 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hd : 1 + a / ρ ≠ 0 := by positivity
  simp only [lambda, psi]
  field_simp
  ring

/-- Second conformal-factor identity. -/
theorem factor_minus (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) :
    (1 - lambda a ρ) * psi a ρ / 2 = a / ρ := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hd : 1 + a / ρ ≠ 0 := by positivity
  simp only [lambda, psi]
  field_simp
  ring

/-- The alternative displacement-over-sum expression for `lambda`. -/
theorem lambda_eq_displacement (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) :
    lambda a ρ = (ρ - a) / (ρ + a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hd : 1 + a / ρ ≠ 0 := by positivity
  have hsum : ρ + a ≠ 0 := by positivity
  simp only [lambda]
  field_simp

/-- `tanh t = (exp (2t) − 1)/(exp (2t) + 1)`. -/
theorem tanh_exp_ratio (t : ℝ) :
    tanh t = (exp (2 * t) - 1) / (exp (2 * t) + 1) := by
  have h2 : exp (2 * t) = exp t * exp t := by
    rw [← exp_add]
    ring_nf
  have hn : exp (-t) = (exp t)⁻¹ := exp_neg t
  have he : 0 < exp t := exp_pos t
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, h2, hn]
  have h1 : exp t + (exp t)⁻¹ ≠ 0 := by positivity
  have h3 : exp t * exp t + 1 ≠ 0 := by positivity
  field_simp

/-- The scalar log-ratio chart, in the sign convention displayed in B207. -/
theorem displacement_eq_tanh_log (z : ℝ) (hz : 0 < z) :
    (z - 1) / (z + 1) = tanh (log z / 2) := by
  rw [tanh_exp_ratio]
  have h : 2 * (log z / 2) = log z := by ring
  rw [h, exp_log hz]

/-- The card's hyperbolic-tangent formula for `lambda`. -/
theorem lambda_eq_tanh (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) :
    lambda a ρ = tanh (log (ρ / a) / 2) := by
  rw [lambda_eq_displacement a ρ ha hρ,
    ← displacement_eq_tanh_log (ρ / a) (div_pos hρ ha)]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hsum : ρ + a ≠ 0 := by positivity
  field_simp

/-- Inversion about the horizon negates the half-amplitude difference. -/
theorem lambda_inversion (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) :
    lambda a (a ^ 2 / ρ) = -lambda a ρ := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hswap : a / (a ^ 2 / ρ) = ρ / a := by
    field_simp
  have hd : 1 + a / ρ ≠ 0 := by positivity
  have hd' : 1 + ρ / a ≠ 0 := by positivity
  simp only [lambda, hswap]
  field_simp
  ring

/-- At the horizon `ρ = a`, the two half-amplitudes coincide and `lambda = 0`. -/
theorem lambda_at_horizon (a : ℝ) (ha : 0 < a) : lambda a a = 0 := by
  rw [lambda_eq_displacement a a ha ha]
  simp

/-- Standard outer and inner Reissner–Nordström horizon radii. -/
def rPlus (M Q : ℝ) : ℝ := M + sqrt (M ^ 2 - Q ^ 2)

def rMinus (M Q : ℝ) : ℝ := M - sqrt (M ^ 2 - Q ^ 2)

/-- The product identity needs only a real square root, not the logarithms. -/
theorem horizon_product (M Q : ℝ) (h : 0 ≤ M ^ 2 - Q ^ 2) :
    rPlus M Q * rMinus M Q = Q ^ 2 := by
  have hs := Real.sq_sqrt h
  simp only [rPlus, rMinus]
  nlinarith

/-- In the non-extremal charged regime the square root is strictly below `M`. -/
theorem sqrt_lt_mass (M Q : ℝ) (hQ : 0 < Q) (hQM : Q < M) :
    sqrt (M ^ 2 - Q ^ 2) < M := by
  have hM : 0 < M := lt_trans hQ hQM
  rw [Real.sqrt_lt' hM]
  nlinarith [sq_pos_of_pos hQ]

/-- Both horizon radii are positive, so their rapidity logarithms are genuine. -/
theorem rPlus_pos (M Q : ℝ) (hQ : 0 < Q) (hQM : Q < M) : 0 < rPlus M Q := by
  have hM : 0 < M := lt_trans hQ hQM
  have hs : 0 ≤ sqrt (M ^ 2 - Q ^ 2) := Real.sqrt_nonneg _
  simp only [rPlus]
  linarith

theorem rMinus_pos (M Q : ℝ) (hQ : 0 < Q) (hQM : Q < M) : 0 < rMinus M Q := by
  have hs := sqrt_lt_mass M Q hQ hQM
  simp only [rMinus]
  linarith

/-- The rapidity coordinate defined by the displayed relation `r = Q exp τ`. -/
def rapidity (Q r : ℝ) : ℝ := log (r / Q)

/-- Every positive radius is recovered from its rapidity. -/
theorem radius_eq_exp_rapidity (Q r : ℝ) (hQ : 0 < Q) (hr : 0 < r) :
    r = Q * exp (rapidity Q r) := by
  simp only [rapidity]
  rw [exp_log (div_pos hr hQ)]
  field_simp [ne_of_gt hQ]

/-- The displayed cosh form of the Schwarzschild/radius offset identity. -/
theorem radius_cosh_rapidity (Q r : ℝ) (hQ : 0 < Q) (hr : 0 < r) :
    (r + Q ^ 2 / r) / 2 = Q * cosh (rapidity Q r) := by
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hr0 : r ≠ 0 := ne_of_gt hr
  simp only [rapidity, cosh_eq, exp_neg]
  rw [exp_log (div_pos hr hQ)]
  have hi : (r / Q)⁻¹ = Q / r := by
    field_simp
  rw [hi]
  field_simp

/-- The outer and inner rapidities are opposite, as displayed in B207. -/
theorem horizon_rapidities_opposite (M Q : ℝ) (hQ : 0 < Q) (hQM : Q < M) :
    rapidity Q (rPlus M Q) = -rapidity Q (rMinus M Q) := by
  have hd : 0 ≤ M ^ 2 - Q ^ 2 := by nlinarith [sq_nonneg Q]
  have hp : rPlus M Q * rMinus M Q = Q ^ 2 := horizon_product M Q hd
  have hrp : 0 < rPlus M Q := rPlus_pos M Q hQ hQM
  have hrm : 0 < rMinus M Q := rMinus_pos M Q hQ hQM
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hone : (rPlus M Q / Q) * (rMinus M Q / Q) = 1 := by
    field_simp
    nlinarith
  have hl : log (rPlus M Q / Q) + log (rMinus M Q / Q) = 0 := by
    rw [← log_mul (div_ne_zero (ne_of_gt hrp) hQ0)
      (div_ne_zero (ne_of_gt hrm) hQ0), hone, log_one]
  simp only [rapidity]
  linarith

/-- Boundary witness: with zero mass and `ρ = 1`, the literal tanh formula is
false in Lean's totalised real arithmetic.  Thus `0 < a` is a real hypothesis,
not merely convenient notation. -/
theorem tanh_claim_fails_at_zero_mass :
    lambda 0 1 ≠ tanh (log ((1 : ℝ) / 0) / 2) := by
  norm_num [lambda]

/-- The same zero-mass witness also breaks the displayed inversion statement. -/
theorem inversion_claim_fails_at_zero_mass :
    lambda 0 (0 ^ 2 / (1 : ℝ)) ≠ -lambda 0 1 := by
  norm_num [lambda]

#print axioms RelationalAtlas.B207.factor_plus
#print axioms RelationalAtlas.B207.factor_minus
#print axioms RelationalAtlas.B207.lambda_eq_displacement
#print axioms RelationalAtlas.B207.tanh_exp_ratio
#print axioms RelationalAtlas.B207.displacement_eq_tanh_log
#print axioms RelationalAtlas.B207.lambda_eq_tanh
#print axioms RelationalAtlas.B207.lambda_inversion
#print axioms RelationalAtlas.B207.lambda_at_horizon
#print axioms RelationalAtlas.B207.horizon_product
#print axioms RelationalAtlas.B207.sqrt_lt_mass
#print axioms RelationalAtlas.B207.rPlus_pos
#print axioms RelationalAtlas.B207.rMinus_pos
#print axioms RelationalAtlas.B207.radius_eq_exp_rapidity
#print axioms RelationalAtlas.B207.radius_cosh_rapidity
#print axioms RelationalAtlas.B207.horizon_rapidities_opposite
#print axioms RelationalAtlas.B207.tanh_claim_fails_at_zero_mass
#print axioms RelationalAtlas.B207.inversion_claim_fails_at_zero_mass

end RelationalAtlas.B207


end

/-! ## B25 — the susceptibility is real and nonnegative; degeneracy is not

Integrated from `.ultramath/smwu0t12t/m15/B25.lean`.
-/
section


noncomputable section

open scoped Topology

namespace RelationalAtlas.B25

/-- The card's displayed sum.  `A n m` is `⟨n|∂H|m⟩`, and `γ n m` is the
real gap.  Only pairs with `m ≠ n` contribute, exactly as displayed. -/
def gapSusceptibility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) : ℝ :=
  ∑ n : ι, ∑ m : ι,
    if m ≠ n then Complex.normSq (A n m) / (γ n m) ^ 2 else 0

/-- The special case `γ n m = E n - E m` in the target statement. -/
def spectralSusceptibility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (A : ι → ι → ℂ) : ℝ :=
  gapSusceptibility (fun n m => E n - E m) A

/-- Every summand is real and nonnegative.  No Hermiticity hypothesis is
needed for this algebraic realness assertion: a squared modulus is already
real and nonnegative, and the gaps are real. -/
theorem gapSusceptibility_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) :
    0 ≤ gapSusceptibility γ A := by
  unfold gapSusceptibility
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  · exact le_rfl

/-- The same displayed expression written in the complex field really is
invariant under complex conjugation. -/
def complexGapSusceptibility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) : ℂ :=
  ∑ n : ι, ∑ m : ι,
    if m ≠ n then (Complex.normSq (A n m) : ℂ) / (γ n m : ℂ) ^ 2 else 0

theorem complexGapSusceptibility_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) :
    (starRingEnd ℂ) (complexGapSusceptibility γ A) =
      complexGapSusceptibility γ A := by
  simp [complexGapSusceptibility, apply_ite]

theorem complexGapSusceptibility_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) :
    (complexGapSusceptibility γ A).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact complexGapSusceptibility_conj γ A

/-- Strict positivity needs a nonzero numerator *and* a nonzero gap; the
off-diagonal condition `m ≠ n` alone is insufficient. -/
theorem gapSusceptibility_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℂ) {n m : ι}
    (hmn : m ≠ n) (hγ : γ n m ≠ 0) (hA : A n m ≠ 0) :
    0 < gapSusceptibility γ A := by
  have hterm : 0 < Complex.normSq (A n m) / (γ n m) ^ 2 :=
    div_pos (Complex.normSq_pos.mpr hA) (sq_pos_of_ne_zero hγ)
  have hinner : 0 < ∑ k : ι,
      if k ≠ n then Complex.normSq (A n k) / (γ n k) ^ 2 else 0 := by
    apply Finset.sum_pos'
    · intro k hk
      split_ifs
      · exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
      · exact le_rfl
    · exact ⟨m, Finset.mem_univ _, by simpa [hmn] using hterm⟩
  unfold gapSusceptibility
  apply Finset.sum_pos'
  · intro k hk
    apply Finset.sum_nonneg
    intro l hl
    split_ifs
    · exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
    · exact le_rfl
  · exact ⟨n, Finset.mem_univ _, hinner⟩

/-- An explicit degeneracy witness.  The two eigenvalue labels are distinct
and one off-diagonal derivative matrix element is `1`, but both gaps vanish.
With Lean's total convention `x / 0 = 0`, the displayed real-valued sum is
zero, not positive and not an infinite extended-real value. -/
theorem degenerate_gap_witness :
    let E : Fin 2 → ℝ := fun _ => 0
    let A : Fin 2 → Fin 2 → ℂ := fun n m => if n = m then 0 else 1
    (1 : Fin 2) ≠ 0 ∧ A 0 1 ≠ 0 ∧ E 0 = E 1 ∧
      spectralSusceptibility E A = 0 := by
  norm_num [spectralSusceptibility, gapSusceptibility, Fin.sum_univ_two]

/-- Consequently, distinct eigenvalue labels and a nonzero off-diagonal
matrix element do **not** by themselves imply strict positivity.  This is the
literal counterexample; adding `E n ≠ E m` repairs it below. -/
theorem offDiagonal_nonzero_alone_not_positive :
    ¬ (∀ (E : Fin 2 → ℝ) (A : Fin 2 → Fin 2 → ℂ),
      (∃ n m, m ≠ n ∧ A n m ≠ 0) → 0 < spectralSusceptibility E A) := by
  intro h
  let E : Fin 2 → ℝ := fun _ => 0
  let A : Fin 2 → Fin 2 → ℂ := fun n m => if n = m then 0 else 1
  have hpos := h E A ⟨0, 1, by decide, by norm_num [A]⟩
  have hzero : spectralSusceptibility E A = 0 := by
    norm_num [E, A, spectralSusceptibility, gapSusceptibility, Fin.sum_univ_two]
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos)

/-- Nondegeneracy repairs strict positivity for any nonzero off-diagonal
matrix element. -/
theorem spectralSusceptibility_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ℝ) (A : ι → ι → ℂ) {n m : ι}
    (hmn : m ≠ n) (hgap : E n ≠ E m) (hA : A n m ≠ 0) :
    0 < spectralSusceptibility E A := by
  apply gapSusceptibility_pos (fun n m => E n - E m) A hmn
  · exact sub_ne_zero.mpr hgap
  · exact hA

/-- A two-level Hermitian derivative with unit off-diagonal matrix elements. -/
def twoLevelDerivative : Fin 2 → Fin 2 → ℂ :=
  fun n m => if n = m then 0 else 1

/-- Energies `0` and `δ`, so both displayed gaps have magnitude `|δ|`. -/
def twoLevelEnergy (δ : ℝ) : Fin 2 → ℝ := ![0, δ]

/-- The exact inverse-square law in the two-level example, including Lean's
value at the degenerate point `δ = 0`. -/
theorem twoLevel_susceptibility (δ : ℝ) :
    spectralSusceptibility (twoLevelEnergy δ) twoLevelDerivative = 2 / δ ^ 2 := by
  norm_num [spectralSusceptibility, gapSusceptibility, twoLevelDerivative,
    twoLevelEnergy, Fin.sum_univ_two]
  ring

/-- Every prescribed positive gap size gives strict positivity. -/
theorem twoLevel_susceptibility_pos {δ : ℝ} (hδ : δ ≠ 0) :
    0 < spectralSusceptibility (twoLevelEnergy δ) twoLevelDerivative := by
  rw [twoLevel_susceptibility]
  exact div_pos (by norm_num) (sq_pos_of_ne_zero hδ)

/-- The inverse-square susceptibility is arbitrarily large at arbitrarily
small nonzero gaps, which is the finite content of the card's divergence
sentence. -/
theorem exists_arbitrarily_small_large_gap_susceptibility
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      M < spectralSusceptibility (twoLevelEnergy δ) twoLevelDerivative := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max (1 / ε) (|M| + 1))
  let δ : ℝ := 1 / (N + 1 : ℝ)
  have hNpos : 0 < (N : ℝ) := by
    have hmax : 0 ≤ max (1 / ε) (|M| + 1) := by
      apply le_trans (show 0 ≤ |M| + 1 by positivity) (le_max_right _ _)
    exact hmax.trans_lt hN
  have hNε : 1 / ε < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  refine ⟨δ, by positivity, ?_, ?_⟩
  · dsimp [δ]
    have hεN : 1 < ε * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hNε
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  · rw [twoLevel_susceptibility]
    have hMN : |M| + 1 < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    have hM : M < (N : ℝ) := (le_abs_self M).trans_lt (by linarith)
    dsimp [δ]
    rw [show 2 / (1 / ((N : ℝ) + 1)) ^ 2 = 2 * ((N : ℝ) + 1) ^ 2 by
      field_simp]
    nlinarith [sq_nonneg (N : ℝ)]

#print axioms RelationalAtlas.B25.gapSusceptibility_nonneg
#print axioms RelationalAtlas.B25.complexGapSusceptibility_conj
#print axioms RelationalAtlas.B25.twoLevel_susceptibility
#print axioms RelationalAtlas.B25.twoLevel_susceptibility_pos
#print axioms RelationalAtlas.B25.exists_arbitrarily_small_large_gap_susceptibility
#print axioms RelationalAtlas.B25.complexGapSusceptibility_im
#print axioms RelationalAtlas.B25.gapSusceptibility_pos
#print axioms RelationalAtlas.B25.degenerate_gap_witness
#print axioms RelationalAtlas.B25.offDiagonal_nonzero_alone_not_positive
#print axioms RelationalAtlas.B25.spectralSusceptibility_pos

end RelationalAtlas.B25


end

/-! ## B152 — a unitary particle-hole exchange forces a vanishing offset

Integrated from `.ultramath/smwu0t12t/m6/B152.lean`.
-/
section


/-!
# B152 — a particle–hole symmetry pins the offset at zero

The archived card displays

  `U C_A Uᴴ = I − C_A ⇒ τ_A = 0`,

and its Carry section also allows `U C_A Uᴴ = (I − C_A)ᵀ`.  B151, on which
B152 builds, defines `τ_A = log det (I − C_A) − log det C_A` for a finite
Hermitian covariance satisfying the strict condition `0 < C_A < I`.

The argument is direct determinant invariance.  Consequently the algebraic
results below need neither Hermiticity nor strict positive-definiteness; those
hypotheses guarantee that the determinant logarithms in the physical card are
finite real logarithms, but play no role in the cancellation itself.
-/

noncomputable section

open Matrix

namespace RelationalAtlas.B152

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real-valued offset from B151, written for complex covariance matrices.
For a Hermitian covariance with `0 < C < I`, both determinants are positive real
numbers, so this is exactly `log det (I − C) − log det C`. -/
def offset (C : Matrix n n ℂ) : ℝ :=
  Real.log ((1 - C).det.re) - Real.log (C.det.re)

/-- Unitary conjugation preserves the determinant.  Only `U * Uᴴ = 1`, one of
the two unitarity equations, is used in the finite-matrix calculation. -/
theorem det_unitary_conjugation {U C : Matrix n n ℂ}
    (hU : U * Uᴴ = 1) :
    (U * C * Uᴴ).det = C.det := by
  calc
    (U * C * Uᴴ).det = U.det * C.det * Uᴴ.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
    _ = (U * Uᴴ).det * C.det := by
      rw [Matrix.det_mul]
      ring
    _ = C.det := by rw [hU, Matrix.det_one, one_mul]

/-- **B152, complement form.**  The displayed particle–hole relation forces the
empty-region and full-region determinants to agree. -/
theorem det_complement_eq_det {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    (1 - C).det = C.det := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  calc
    (1 - C).det = (U * C * Uᴴ).det := congrArg Matrix.det hPH.symm
    _ = C.det := det_unitary_conjugation hUU

/-- **B152, main display.**  Particle–hole symmetry makes the offset exactly
zero; no extra symmetry-of-spectrum hypothesis is required. -/
theorem offset_eq_zero {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    offset C = 0 := by
  unfold offset
  rw [det_complement_eq_det hU hPH, sub_self]

/-- The alternative relation in the card's Carry section gives the same
 determinants, since transposition preserves determinant. -/
theorem det_complement_eq_det_of_transpose {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    (1 - C).det = C.det := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  calc
    (1 - C).det = ((1 - C)ᵀ).det := (Matrix.det_transpose _).symm
    _ = (U * C * Uᴴ).det := congrArg Matrix.det hPH.symm
    _ = C.det := det_unitary_conjugation hUU

/-- **B152, transpose form of the Carry hypothesis.** -/
theorem offset_eq_zero_of_transpose {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    offset C = 0 := by
  unfold offset
  rw [det_complement_eq_det_of_transpose hU hPH, sub_self]

/-! A concrete two-dimensional check: swap the occupations `1/4` and `3/4`. -/

/-- The real symmetric swap matrix, viewed as a complex unitary. -/
def swap₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- A strict covariance whose two occupations are interchanged by `swap₂`. -/
def covariance₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 4, 0; 0, 3 / 4]

/-- The witness is unitary. -/
theorem swap₂_unitary : swap₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap₂, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The witness satisfies the exact displayed relation `U C Uᴴ = I − C`. -/
theorem swap₂_particleHole : swap₂ * covariance₂ * swap₂ᴴ = 1 - covariance₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap₂, covariance₂, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The common determinant in the two-dimensional check is `3/16`. -/
theorem covariance₂_det_complement : (1 - covariance₂).det = (3 / 16 : ℂ) := by
  norm_num [covariance₂, Matrix.det_fin_two, Matrix.one_apply]

/-- The explicit check has zero offset, as the general theorem predicts. -/
theorem covariance₂_offset_eq_zero : offset covariance₂ = 0 :=
  offset_eq_zero swap₂_unitary swap₂_particleHole

/-! ### The unitarity hypothesis is essential

Dropping unitarity while retaining the displayed conjugacy equation does permit
a nonzero offset, already in one mode.  Thus this is a proof of B152 as written,
not a claim that an arbitrary nonunitary congruence preserves spectrum. -/

/-- The nonunitary scalar matrix `U = [2]`, used only as a boundary check. -/
def nonunitaryU₁ : Matrix (Fin 1) (Fin 1) ℂ := !![2]

/-- The scalar covariance `C = [1/5]`. -/
def nonunitaryC₁ : Matrix (Fin 1) (Fin 1) ℂ := !![1 / 5]

/-- Even this nonunitary witness satisfies `U C Uᴴ = I − C`:
`2 * (1/5) * 2 = 4/5 = 1 - 1/5`. -/
theorem nonunitaryU₁_particleHole :
    nonunitaryU₁ * nonunitaryC₁ * nonunitaryU₁ᴴ = 1 - nonunitaryC₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nonunitaryU₁, nonunitaryC₁, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The scalar factor `2` is not unitary. -/
theorem nonunitaryU₁_not_unitary :
    ¬ nonunitaryU₁ ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  intro h
  have hUU : nonunitaryU₁ * nonunitaryU₁ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp h)
  have hentry := congrFun (congrFun hUU 0) 0
  norm_num [nonunitaryU₁, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] at hentry

/-- The nonzero offset in the nonunitary check is exactly `log 4`. -/
theorem nonunitaryC₁_offset : offset nonunitaryC₁ = Real.log 4 := by
  have hcomp : (1 - nonunitaryC₁).det = (4 / 5 : ℂ) := by
    rw [Matrix.det_fin_one]
    norm_num [nonunitaryC₁, Matrix.one_apply]
  have hdet : nonunitaryC₁.det = (1 / 5 : ℂ) := by
    rw [Matrix.det_fin_one]
    norm_num [nonunitaryC₁]
  unfold offset
  rw [hcomp, hdet]
  norm_num [Complex.div_re, Complex.normSq_apply]
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  norm_num

/-- In particular, the displayed relation alone, without unitarity, cannot
imply zero offset. -/
theorem nonunitary_particleHole_offset_ne_zero : offset nonunitaryC₁ ≠ 0 := by
  rw [nonunitaryC₁_offset]
  exact ne_of_gt (Real.log_pos (by norm_num))

#print axioms det_unitary_conjugation
#print axioms det_complement_eq_det
#print axioms offset_eq_zero
#print axioms det_complement_eq_det_of_transpose
#print axioms offset_eq_zero_of_transpose
#print axioms swap₂_unitary
#print axioms swap₂_particleHole
#print axioms covariance₂_det_complement
#print axioms covariance₂_offset_eq_zero
#print axioms nonunitaryU₁_particleHole
#print axioms nonunitaryU₁_not_unitary
#print axioms nonunitaryC₁_offset
#print axioms nonunitary_particleHole_offset_ne_zero

end RelationalAtlas.B152


end

/-! ## B181 — the factor two, and a decimal that is only a rounding

Integrated from `.ultramath/smwu0t12t/m10/B181.lean`.
-/
section


/-!
# B181: the square's transverse frequency

The card displays `ω = √(2(2√2 − 1)) = 1.912290`.  The last equality is
numeric notation, not an exact rational equality: we prove the sharp
six-decimal interval and hence also refute its literal exact reading.
-/

namespace B181

open Real

/-- The coefficient of `w₃` in the square's potential. -/
noncomputable def squareSlope : ℝ := 2 * sqrt 2 - 1

/-- The exact transverse frequency stated on B181. -/
noncomputable def squareOmega : ℝ := sqrt (2 * squareSlope)

lemma squareSlope_nonneg : 0 ≤ 2 * squareSlope := by
  have h := Real.one_lt_sqrt_two
  unfold squareSlope
  nlinarith

lemma squareOmega_sq : squareOmega ^ 2 = 2 * (2 * sqrt 2 - 1) := by
  rw [squareOmega, sq_sqrt squareSlope_nonneg]
  rfl

/-- Rational bounds on `√2`, more than sufficient to certify the printed
number to six places after the decimal point. -/
lemma sqrt_two_decimal_bounds :
    (14142135623 : ℝ) / 10000000000 < sqrt 2 ∧
      sqrt 2 < (14142135624 : ℝ) / 10000000000 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

/-- The exact value lies strictly between the displayed six-place decimal and
the midpoint to the next one. Thus `1.912290` is its correctly rounded value
to six digits after the decimal point, not merely its truncation. -/
theorem squareOmega_decimal_bounds :
    (1912290 : ℝ) / 1000000 < squareOmega ∧
      squareOmega < (19122905 : ℝ) / 10000000 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_decimal_bounds
  constructor
  · rw [squareOmega, Real.lt_sqrt (by norm_num)]
    unfold squareSlope
    norm_num at *
    nlinarith
  · rw [squareOmega, Real.sqrt_lt squareSlope_nonneg (by norm_num)]
    unfold squareSlope
    norm_num at *
    nlinarith

theorem squareOmega_lt_next_decimal :
    squareOmega < (1912291 : ℝ) / 1000000 :=
  squareOmega_decimal_bounds.2.trans (by norm_num)

/-- The displayed equality is false if `1.912290` is read as an exact real
number. Corrected statement: it is a six-decimal approximation. -/
theorem squareOmega_ne_displayed_exactly :
    squareOmega ≠ (1912290 : ℝ) / 1000000 := by
  exact ne_of_gt squareOmega_decimal_bounds.1


/-! ## The square inverse-distance potential -/

/-- Exact inverse-distance potential for the square witness. With
`a² = 1/4 - h²` and `w = 4h²`, four raised edges have squared length
`1/2 + w/2`, and the two diagonals have squared length `1/4 - w/4`. -/
noncomputable def squarePotential (w : ℝ) : ℝ :=
  -4 / sqrt ((1 : ℝ) / 2 + w / 2) - 1 / sqrt ((1 : ℝ) / 4 - w / 4)

lemma squarePotential_hasDerivAt : HasDerivAt squarePotential (2 * sqrt 2 - 1) 0 := by
  have hlin1 : HasDerivAt (fun w : ℝ => (1 : ℝ) / 2 + w / 2) (1 / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add (1 / 2)
  have hsqrt1 := hlin1.sqrt (by norm_num : (1 : ℝ) / 2 + 0 / 2 ≠ 0)
  have hinv1 : HasDerivAt (fun w : ℝ => -4 / sqrt ((1 : ℝ) / 2 + w / 2))
      (-4 * (-((1 / 2 : ℝ) / (2 * sqrt ((1 : ℝ) / 2 + 0 / 2))) /
        sqrt ((1 : ℝ) / 2 + 0 / 2) ^ 2)) 0 := by
    simpa [div_eq_mul_inv] using (hsqrt1.inv (by positivity)).const_mul (-4)
  have hlin2 : HasDerivAt (fun w : ℝ => (1 : ℝ) / 4 - w / 4) (-1 / 4) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).div_const 4).const_sub (1 / 4) using 1 <;> norm_num
  have hsqrt2 := hlin2.sqrt (by norm_num : (1 : ℝ) / 4 - 0 / 4 ≠ 0)
  have hinv2 : HasDerivAt (fun w : ℝ => 1 / sqrt ((1 : ℝ) / 4 - w / 4))
      ((-(-1 / 4 : ℝ) / (2 * sqrt ((1 : ℝ) / 4 - 0 / 4))) /
        sqrt ((1 : ℝ) / 4 - 0 / 4) ^ 2) 0 := by
    have h := hsqrt2.inv (by positivity)
    convert h using 1
    · ext w
      simp only [Pi.inv_apply, one_div]
    · ring
  have hadd := hinv1.sub hinv2
  convert hadd using 1
  · rfl
  · have hs1 : sqrt ((1 : ℝ) / 2 + 0 / 2) = (sqrt 2)⁻¹ := by
      rw [show (1 : ℝ) / 2 + 0 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]
    have hs2 : sqrt ((1 : ℝ) / 4 - 0 / 4) = (1 : ℝ) / 2 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    rw [hs1, hs2]
    have hsqrt2ne : sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsq : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hs3 : sqrt 2 ^ 3 = 2 * sqrt 2 := by
      calc
        sqrt 2 ^ 3 = sqrt 2 ^ 2 * sqrt 2 := by ring
        _ = 2 * sqrt 2 := by rw [hsq]
    field_simp
    nlinarith

lemma squarePotential_zero : squarePotential 0 = -4 * sqrt 2 - 2 := by
  have hs1 : sqrt ((1 : ℝ) / 2 + 0 / 2) = (sqrt 2)⁻¹ := by
    rw [show (1 : ℝ) / 2 + 0 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]
  have hs2 : sqrt ((1 : ℝ) / 4 - 0 / 4) = (1 : ℝ) / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
  unfold squarePotential
  rw [hs1, hs2]
  have hsqrt2ne : sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp

/-! ## A potential through the orientation fold -/

/-- A distance potential in the fold chart: it depends on orientation only
through `w = σ²`. -/
noncomputable def foldPotential (f : ℝ → ℝ) (σ : ℝ) : ℝ := f (σ ^ 2)

lemma hasDerivAt_sq (x : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

/-- If `D = f'`, then the fold potential has zero transverse velocity at the
wall and its second derivative there is twice the slope in `w`. For this
formulation we assume that `f` and `D` are differentiable everywhere. -/
theorem foldPotential_derivatives (f D E : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (D x) x) (hD : ∀ x, HasDerivAt D (E x) x) :
    HasDerivAt (foldPotential f) 0 0 ∧
      HasDerivAt (deriv (foldPotential f)) (2 * D 0) 0 := by
  have hV (x : ℝ) : HasDerivAt (foldPotential f) (2 * x * D (x ^ 2)) x := by
    have hcomp := (hf (x ^ 2)).comp x (hasDerivAt_sq x)
    unfold foldPotential
    convert hcomp using 1
    · ext s
      rfl
    · ring
  have hDsq : HasDerivAt (fun s : ℝ => D (s ^ 2)) 0 0 := by
    have hcomp := (hD (0 ^ 2)).comp 0 (hasDerivAt_sq 0)
    simpa [Function.comp_def] using hcomp
  have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  have hprod : HasDerivAt (fun s : ℝ => 2 * s * D (s ^ 2)) (2 * D 0) 0 := by
    have h := hlin.mul hDsq
    convert h using 1
    ring
  have hderiv : deriv (foldPotential f) = fun s : ℝ => 2 * s * D (s ^ 2) := by
    funext s
    exact (hV s).deriv
  constructor
  · simpa using hV 0
  · rw [hderiv]
    exact hprod

/-- The second-derivative identity as an equation for `deriv`, matching the
card's `∂²V/∂σ₃²|₀ = 2∂V/∂w₃|₀`. -/
theorem foldPotential_second_deriv (f D E : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (D x) x) (hD : ∀ x, HasDerivAt D (E x) x) :
    deriv (deriv (foldPotential f)) 0 = 2 * D 0 :=
  ((foldPotential_derivatives f D E hf hD).2).deriv


#print axioms squareSlope_nonneg
#print axioms squareOmega_sq
#print axioms sqrt_two_decimal_bounds
#print axioms squareOmega_decimal_bounds
#print axioms squareOmega_lt_next_decimal
#print axioms squareOmega_ne_displayed_exactly
#print axioms squarePotential_hasDerivAt
#print axioms squarePotential_zero
#print axioms hasDerivAt_sq
#print axioms foldPotential_derivatives
#print axioms foldPotential_second_deriv

end B181


end

/-! ## B91 — positivity criterion: true for a > 0, false at g11 = 0 (REFUTATION)

Integrated from `.ultramath/smwu0t12t/m8/B91.lean`.
-/
section

/-
B91 — positivity of the two-parameter quantum geometric tensor.

Source: `atlas_cards_v7_html.zip`, `cards/html/B91.html`, SHA-256
`b06f028984feca2bef00eeeb27ff9d5bd3208f6a76f62b5febbf241cc10c9eb8`.
The card displays
  Q ⪰ 0 ↔ g₁₁ ≥ 0 and 4 det g ≥ |Ω|²,
with Q = g − (i/2)Ω.  Here `w = Ω₀₁`, so |Ω|² is `w²`, the convention
used explicitly in the determinant calculation of B1.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace AtlasB91

/-- The real symmetric part, with `a = g₁₁`, `b = g₁₂`, `d = g₂₂`. -/
def g (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]

/-- The real antisymmetric curvature matrix, with `w = Ω₀₁`. -/
def Omega (w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, w; -w, 0]

/-- The Hermitian complex matrix `g − (i/2)Ω`. -/
def Q (a b d w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, b - ((w / 2 : ℝ) : ℂ) * Complex.I;
      b + ((w / 2 : ℝ) : ℂ) * Complex.I, d]

lemma Q_eq_card (a b d w : ℝ) :
    Q a b d w = (g a b d).map Complex.ofReal -
      (Complex.I / 2) • (Omega w).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, g, Omega, Matrix.map_apply] <;> ring

#print axioms Q_eq_card

lemma det_g (a b d : ℝ) : (g a b d).det = a * d - b ^ 2 := by
  simp [g, Matrix.det_fin_two, pow_two]

#print axioms det_g

lemma det_Q (a b d w : ℝ) :
    (Q a b d w).det = ((a * d - b ^ 2 - w ^ 2 / 4 : ℝ) : ℂ) := by
  simp [Q, Matrix.det_fin_two]
  ring_nf
  simp [Complex.I_sq]
  ring

#print axioms det_Q

lemma four_det_g_sub_curvature_sq_eq_four_det_Q_re (a b d w : ℝ) :
    4 * (g a b d).det - w ^ 2 = 4 * ((Q a b d w).det.re) := by
  rw [det_g, det_Q]
  simp [pow_two, Complex.mul_re]
  ring

#print axioms four_det_g_sub_curvature_sq_eq_four_det_Q_re

lemma Q_isHermitian (a b d w : ℝ) : (Q a b d w).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Q, Matrix.conjTranspose_apply]
  all_goals ring

#print axioms Q_isHermitian

/-- The card's inequalities are necessary for positivity. -/
lemma card_conditions_of_posSemidef {a b d w : ℝ} (hQ : (Q a b d w).PosSemidef) :
    0 ≤ a ∧ w ^ 2 ≤ 4 * (g a b d).det := by
  have haC : (0 : ℂ) ≤ (a : ℂ) := by
    simpa [Q] using hQ.diag_nonneg (i := 0)
  have ha : 0 ≤ a := by exact_mod_cast haC
  have hdetC : (0 : ℂ) ≤ (Q a b d w).det := hQ.det_nonneg
  rw [det_Q] at hdetC
  have hdet : 0 ≤ a * d - b ^ 2 - w ^ 2 / 4 := by exact_mod_cast hdetC
  rw [det_g]
  exact ⟨ha, by nlinarith⟩

#print axioms card_conditions_of_posSemidef

/-- The literal unrestricted converse is false.  At `(a,b,d,w) = (0,0,-1,0)`,
its two inequalities hold, but `Q = diag(0,-1)` is not positive semidefinite. -/
lemma boundary_counterexample :
    let a : ℝ := 0
    let b : ℝ := 0
    let d : ℝ := -1
    let w : ℝ := 0
    (0 ≤ a ∧ w ^ 2 ≤ 4 * (g a b d).det) ∧ ¬ (Q a b d w).PosSemidef := by
  constructor
  · norm_num [g, Matrix.det_fin_two]
  · intro hQ
    have hdC : (0 : ℂ) ≤ ((-1 : ℝ) : ℂ) := by
      simpa [Q] using hQ.diag_nonneg (i := 1)
    have hd : (0 : ℝ) ≤ -1 := by exact_mod_cast hdC
    norm_num at hd

#print axioms boundary_counterexample

/-- Equivalently, the displayed equivalence has a right-to-left counterexample. -/
lemma literal_equivalence_false :
    ¬ ∀ a b d w : ℝ,
      (Q a b d w).PosSemidef ↔ (0 ≤ a ∧ w ^ 2 ≤ 4 * (g a b d).det) := by
  intro h
  have hc := boundary_counterexample
  dsimp at hc
  exact hc.2 ((h 0 0 (-1) 0).2 hc.1)

#print axioms literal_equivalence_false


/-- With a strictly positive first pivot, the card's determinant condition is
also sufficient.  This is the nondegenerate case used by the card's wall. -/
lemma posSemidef_of_card_conditions_of_pos {a b d w : ℝ}
    (ha : 0 < a) (h : w ^ 2 ≤ 4 * (g a b d).det) : (Q a b d w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Q_isHermitian a b d w)
  intro x
  rw [Complex.nonneg_iff]
  rw [det_g] at h
  have hD : 0 ≤ a * d - b ^ 2 - w ^ 2 / 4 := by nlinarith
  constructor
  · simp [Q, dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
    apply nonneg_of_mul_nonneg_right ?_ ha
    nlinarith [sq_nonneg (a * (x 0).re + b * (x 1).re + w / 2 * (x 1).im),
      sq_nonneg (a * (x 0).im + b * (x 1).im - w / 2 * (x 1).re),
      mul_nonneg hD (add_nonneg (sq_nonneg (x 1).re) (sq_nonneg (x 1).im))]
  · simp [Q, dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
    ring

#print axioms posSemidef_of_card_conditions_of_pos


/-- Corrected unrestricted criterion: both diagonal principal minors are needed.
The new condition `0 ≤ d` is exactly what excludes the counterexample above. -/
lemma posSemidef_iff_with_diagonals (a b d w : ℝ) :
    (Q a b d w).PosSemidef ↔
      (0 ≤ a ∧ 0 ≤ d ∧ w ^ 2 ≤ 4 * (g a b d).det) := by
  constructor
  · intro hQ
    have hdC : (0 : ℂ) ≤ (d : ℂ) := by
      simpa [Q] using hQ.diag_nonneg (i := 1)
    have hd : 0 ≤ d := by exact_mod_cast hdC
    have hc := card_conditions_of_posSemidef hQ
    exact ⟨hc.1, hd, hc.2⟩
  · rintro ⟨ha, hd, hwall⟩
    by_cases ha0 : a = 0
    · have hb2 : b ^ 2 = 0 := by
        rw [ha0, det_g] at hwall
        nlinarith [sq_nonneg b, sq_nonneg w]
      have hw2 : w ^ 2 = 0 := by
        rw [ha0, det_g] at hwall
        nlinarith [sq_nonneg b, sq_nonneg w]
      have hb : b = 0 := sq_eq_zero_iff.mp hb2
      have hw : w = 0 := sq_eq_zero_iff.mp hw2
      subst a
      subst b
      subst w
      have hdiag : Q 0 0 d 0 = Matrix.diagonal ![(0 : ℂ), (d : ℂ)] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Q, Matrix.diagonal]
      rw [hdiag, Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i
      · simp
      · have hdC : (0 : ℂ) ≤ (d : ℂ) := by exact_mod_cast hd
        simpa using hdC
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact posSemidef_of_card_conditions_of_pos haPos hwall

#print axioms posSemidef_iff_with_diagonals

/-- Strict-pivot repair of the card's displayed equivalence. -/
lemma posSemidef_iff_card_conditions_of_pos {a b d w : ℝ} (ha : 0 < a) :
    (Q a b d w).PosSemidef ↔ (0 ≤ a ∧ w ^ 2 ≤ 4 * (g a b d).det) := by
  exact ⟨card_conditions_of_posSemidef,
    fun hc => posSemidef_of_card_conditions_of_pos ha hc.2⟩

#print axioms posSemidef_iff_card_conditions_of_pos


/-- An equivalent repair using the trace instead of the second diagonal entry.
Either additional nonnegativity condition excludes `diag(0,-1)`. -/
lemma posSemidef_iff_with_trace (a b d w : ℝ) :
    (Q a b d w).PosSemidef ↔
      (0 ≤ a ∧ 0 ≤ a + d ∧ w ^ 2 ≤ 4 * (g a b d).det) := by
  rw [posSemidef_iff_with_diagonals]
  constructor
  · rintro ⟨ha, hd, hwall⟩
    exact ⟨ha, add_nonneg ha hd, hwall⟩
  · rintro ⟨ha, htr, hwall⟩
    refine ⟨ha, ?_, hwall⟩
    rw [det_g] at hwall
    by_contra hd
    have hdneg : d < 0 := lt_of_not_ge hd
    have hapos : 0 < a := by linarith
    have had : a * d < 0 := mul_neg_of_pos_of_neg hapos hdneg
    nlinarith [sq_nonneg b, sq_nonneg w]

#print axioms posSemidef_iff_with_trace

/-- The strict positive-slack Check in the card forces a strictly positive
first pivot when `g₁₁ ≥ 0`; hence the strict-pivot repair applies there without
adding an independent positivity assumption. -/
lemma pivot_pos_of_strict_slack {a b d w : ℝ}
    (ha : 0 ≤ a) (hslack : w ^ 2 < 4 * (g a b d).det) : 0 < a := by
  rw [det_g] at hslack
  by_contra hna
  have ha0 : a = 0 := le_antisymm (le_of_not_gt hna) ha
  subst a
  nlinarith [sq_nonneg b, sq_nonneg w]

#print axioms pivot_pos_of_strict_slack

/-- At strict positive slack the card's literal inequalities are sufficient,
even though its non-strict equivalence is false at the degenerate boundary. -/
lemma posSemidef_of_strict_slack {a b d w : ℝ}
    (ha : 0 ≤ a) (hslack : w ^ 2 < 4 * (g a b d).det) :
    (Q a b d w).PosSemidef :=
  posSemidef_of_card_conditions_of_pos
    (pivot_pos_of_strict_slack ha hslack) hslack.le

#print axioms posSemidef_of_strict_slack

/-- On the licence wall with nonzero curvature, the metric determinant is
strictly positive: it equals `w² / 4`. -/
lemma det_g_pos_of_wall_of_curvature_ne_zero {a b d w : ℝ}
    (hw : w ≠ 0) (hwall : 4 * (g a b d).det = w ^ 2) : 0 < (g a b d).det := by
  have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero hw
  nlinarith

#print axioms det_g_pos_of_wall_of_curvature_ne_zero

/-- The displayed literal locus statement needs the nonzero-curvature clause:
`(a,b,d,w) = (0,0,0,0)` is on the wall but has `det g = 0`. -/
lemma wall_not_inside_metric_positive_literally :
    let a : ℝ := 0
    let b : ℝ := 0
    let d : ℝ := 0
    let w : ℝ := 0
    4 * (g a b d).det = w ^ 2 ∧ ¬ 0 < (g a b d).det := by
  norm_num [g, Matrix.det_fin_two]

#print axioms wall_not_inside_metric_positive_literally

/-- The inclusion is strict even after restricting to nonzero curvature:
`g = I`, `w = 1` has positive metric determinant but is not on the wall. -/
lemma metric_positive_not_always_on_wall :
    let a : ℝ := 1
    let b : ℝ := 0
    let d : ℝ := 1
    let w : ℝ := 1
    w ≠ 0 ∧ 0 < (g a b d).det ∧ 4 * (g a b d).det ≠ w ^ 2 := by
  norm_num [g, Matrix.det_fin_two]

#print axioms metric_positive_not_always_on_wall

end AtlasB91


end

/-! ## B46 — the idempotency defect, and a provenance mismatch

Integrated from `.ultramath/smwu0t12t/m2/B46.lean`.
-/
section


/-!
# B46: idempotency defect along a Grassmannian tangent

The target line and `atlas/coverage/coverage.json` quote
`(Π + hV)² − (Π + hV) = h²V²` for
`V = ΠV(1 − Π) + (1 − Π)VΠ`.  This file proves that statement literally for
finite square matrices over an arbitrary commutative ring.  The proof first
derives the linearized tangent equation `PV + VP = V`, so the linear term in
the unrestricted expansion vanishes exactly as the card says.  No Hermitian or
orthogonality hypothesis is needed for this algebraic identity.

A separate `P = diag(1,0), V = I, h = 1` witness proves that the identity can
fail when tangency is deleted.

Source discrepancy: at the time of this audit, `atlas/cards/html/B46.html`
instead displayed only `Ẇ = Π_{T Gr}(Ẇ) + δ, δ backreacts`.  Its actual
SHA-256 was `b1e69cb1f0204687dd93e35637b17a195cb3459d82ee99125253bed9f3a41607`,
not the ledger's `3626f1bb6af8b5847a7186f3d4b9b7ce5316a9be6362f080915a25306c574fd2`.
Thus the result below addresses the target/ledger formula; it does not assert
that this formula occurs in the current HTML, and it does not formalize the
HTML's projected-trajectory dynamics or the meaning of "backreacts".
-/

namespace AtlasB46

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The card's off-diagonal tangent condition implies the linearized
idempotency condition `P * V + V * P = V`. -/
theorem tangent_linearized (P V : Matrix n n R) (hP : P * P = P)
    (hV : V = P * V * (1 - P) + (1 - P) * V * P) :
    P * V + V * P = V := by
  have hP_left (X : Matrix n n R) : P * (P * X) = P * X := by
    rw [← mul_assoc, hP]
  have hP_right (X : Matrix n n R) : X * P * P = X * P := by
    rw [mul_assoc, hP]
  have hPcomp : P * (1 - P) = 0 := by simp [mul_sub, hP]
  have hcompP : (1 - P) * P = 0 := by simp [sub_mul, hP]
  have hP_comp_left (X : Matrix n n R) : P * ((1 - P) * X) = 0 := by
    rw [← mul_assoc, hPcomp, zero_mul]
  have hcomp_P_right (X : Matrix n n R) : X * (1 - P) * P = 0 := by
    rw [mul_assoc, hcompP, mul_zero]
  calc
    P * V + V * P =
        P * (P * V * (1 - P) + (1 - P) * V * P) +
          (P * V * (1 - P) + (1 - P) * V * P) * P :=
      congrArg (fun W : Matrix n n R => P * W + W * P) hV
    _ = P * V * (1 - P) + (1 - P) * V * P := by
      simp only [mul_add, add_mul, mul_assoc, hP_left, hP_right, hP_comp_left,
        hcomp_P_right, mul_zero, add_zero, zero_add]
    _ = V := hV.symm

/-- Without using tangency, the exact expansion retains the linear obstruction
`P * V + V * P - V`. -/
theorem b46_defect_expansion (P V : Matrix n n R) (h : R)
    (hP : P * P = P) :
    (P + h • V) ^ 2 - (P + h • V) =
      h • (P * V + V * P - V) + h ^ 2 • V ^ 2 := by
  calc
    (P + h • V) ^ 2 - (P + h • V) =
        (P * P - P) + h • (P * V + V * P - V) + h ^ 2 • (V * V) := by
      simp only [pow_two, add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, smul_add, smul_sub]
      module
    _ = h • (P * V + V * P - V) + h ^ 2 • V ^ 2 := by rw [hP]; simp [pow_two]

/-- B46: for an idempotent `P` and a tangent `V`, the idempotency defect of
`P + h • V` is exactly `h² • V²`; there is no linear term. -/
theorem b46_idempotency_defect (P V : Matrix n n R) (h : R)
    (hP : P * P = P)
    (hV : V = P * V * (1 - P) + (1 - P) * V * P) :
    (P + h • V) ^ 2 - (P + h • V) = h ^ 2 • V ^ 2 := by
  rw [b46_defect_expansion P V h hP, tangent_linearized P V hP hV, sub_self,
    smul_zero, zero_add]

/-- A nontangent witness used to check that the tangent hypothesis is essential. -/
def witnessP : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The identity is not tangent to the rank-one idempotent `witnessP`. -/
def witnessV : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

theorem witnessP_idempotent : witnessP * witnessP = witnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessP, Matrix.mul_apply, Fin.sum_univ_two]

theorem witnessV_not_tangent :
    witnessV ≠ witnessP * witnessV * (1 - witnessP) +
      (1 - witnessP) * witnessV * witnessP := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [witnessP, witnessV, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.one_apply] at h00

/-- With `P = diag(1,0)`, `V = I`, and `h = 1`, the left side is
`diag(2,0)` rather than `V² = I`.  Thus deleting the tangent hypothesis makes
the displayed B46 identity false. -/
theorem witness_card_identity_fails :
    (witnessP + (1 : ℝ) • witnessV) ^ 2 - (witnessP + (1 : ℝ) • witnessV) ≠
      (1 : ℝ) ^ 2 • witnessV ^ 2 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  norm_num [witnessP, witnessV, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h11

#print axioms tangent_linearized
#print axioms b46_defect_expansion
#print axioms b46_idempotency_defect
#print axioms witnessP_idempotent
#print axioms witnessV_not_tangent
#print axioms witness_card_identity_fails

end AtlasB46


end

/-! ## B173 — isotropic stars and the bijective quartic

Integrated from `.ultramath/smwu0t12t/m16/B173.lean`.
-/
section


noncomputable section

/-!
# B173 — the Petrov quartic and its five-dimensional coefficient map

The archived card displays
`ψ_Q(z) = n(z)ᵀ Q n(z)`, with
`n(z) = (1 − z², i(1 + z²), −2z)`, `n·n = 0`, and `Q` complex
symmetric and traceless.  Its Check clause says that `Q ↦ ψ_Q` is invertible
on the five traceless directions, and its Witness gives determinant `3072` in
the ordered basis `(diag(1,-1,0), diag(1,1,-2), S₁₂, S₁₃, S₂₃)`.

This file proves those finite algebraic statements exactly.  The coefficient
convention is ascending powers `z⁰, …, z⁴`.  No statement about the global
Petrov/Jordan classification or about unfolding exponents is needed for these
proofs.
-/

namespace RelationalAtlas.B173

open Matrix

/-- The card's isotropic Majorana vector. -/
def n (z : ℂ) : Fin 3 → ℂ :=
  ![1 - z ^ 2, Complex.I * (1 + z ^ 2), -2 * z]

/-- The bilinear (not Hermitian) quadratic form appearing on the card. -/
def quadratic (Q : Matrix (Fin 3) (Fin 3) ℂ) (z : ℂ) : ℂ :=
  ∑ i, ∑ j, n z i * Q i j * n z j

/-- **B173: isotropy.**  The displayed vector satisfies `n·n = 0` for every
complex `z`, including the two poles-at-infinity representatives `z = ±i`. -/
theorem n_isotropic (z : ℂ) : ∑ i, n z i * n z i = 0 := by
  simp [n, Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]

/-- The trace part drops out: adding any scalar multiple of the identity to
`Q` leaves the quartic unchanged.  No symmetry or trace hypothesis on `Q` is
needed for this identity. -/
theorem quadratic_add_scalar_identity
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (t z : ℂ) :
    quadratic (Q + t • (1 : Matrix (Fin 3) (Fin 3) ℂ)) z = quadratic Q z := by
  simp [quadratic, n, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_three,
    smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- A general complex symmetric traceless matrix in the card's ordered basis.
The off-diagonal basis elements are `eᵢeⱼᵀ + eⱼeᵢᵀ`, without a factor `1/2`. -/
def petrovQ (a b c d e : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![a + b, c, d;
     c, -a + b, e;
     d, e, -2 * b]

theorem petrovQ_symmetric (a b c d e : ℂ) :
    (petrovQ a b c d e)ᵀ = petrovQ a b c d e := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [petrovQ]

theorem petrovQ_trace (a b c d e : ℂ) :
    Matrix.trace (petrovQ a b c d e) = 0 := by
  simp [petrovQ, Matrix.trace_fin_three]
  ring

/-- The card's `ψ_Q`, specialised to the five-dimensional traceless space. -/
def psi (a b c d e : ℂ) (z : ℂ) : ℂ := quadratic (petrovQ a b c d e) z

/-- Exact binary-quartic formula for the card's quadratic form. -/
theorem psi_expansion (a b c d e z : ℂ) :
    psi a b c d e z =
      (2 * a + 2 * Complex.I * c) +
      (-4 * d - 4 * Complex.I * e) * z +
      (-12 * b) * z ^ 2 +
      (4 * d - 4 * Complex.I * e) * z ^ 3 +
      (2 * a - 2 * Complex.I * c) * z ^ 4 := by
  simp [psi, quadratic, petrovQ, n, Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The five scalar coefficients of `psi`, in ascending order `z⁰,…,z⁴`. -/
def petrovCoeff (a b c d e : ℂ) : Fin 5 → ℂ :=
  ![2 * a + 2 * Complex.I * c,
    -4 * d - 4 * Complex.I * e,
    -12 * b,
    4 * d - 4 * Complex.I * e,
    2 * a - 2 * Complex.I * c]

/-- The coefficient matrix in the card's stated basis. -/
def coeffMatrix : Matrix (Fin 5) (Fin 5) ℂ :=
  !![2, 0, 2 * Complex.I, 0, 0;
     0, 0, 0, -4, -4 * Complex.I;
     0, -12, 0, 0, 0;
     0, 0, 0, 4, -4 * Complex.I;
     2, 0, -2 * Complex.I, 0, 0]

theorem petrovCoeff_eq_matrix_mulVec (a b c d e : ℂ) :
    petrovCoeff a b c d e = coeffMatrix.mulVec ![a, b, c, d, e] := by
  funext k
  fin_cases k <;>
    simp [petrovCoeff, coeffMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;>
    ring

/-- **B173's numerical witness, exactly.**  The determinant is `3072`; in
particular it is nonzero, so the five traceless directions are independent. -/
theorem coeffMatrix_det : coeffMatrix.det = 3072 := by
  simp [coeffMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  simp [Complex.I_sq]

/-- Recovery of the first diagonal-basis coefficient from the quartic. -/
def recoverA (v : Fin 5 → ℂ) : ℂ := (v 0 + v 4) / 4

/-- Recovery of the second diagonal-basis coefficient from the quartic. -/
def recoverB (v : Fin 5 → ℂ) : ℂ := -(v 2) / 12

/-- Recovery of the `S₁₂` coefficient from the quartic. -/
def recoverC (v : Fin 5 → ℂ) : ℂ := Complex.I * (v 4 - v 0) / 4

/-- Recovery of the `S₁₃` coefficient from the quartic. -/
def recoverD (v : Fin 5 → ℂ) : ℂ := (v 3 - v 1) / 8

/-- Recovery of the `S₂₃` coefficient from the quartic. -/
def recoverE (v : Fin 5 → ℂ) : ℂ := Complex.I * (v 1 + v 3) / 8

theorem recoverA_petrovCoeff (a b c d e : ℂ) :
    recoverA (petrovCoeff a b c d e) = a := by
  simp [recoverA, petrovCoeff]
  ring

theorem recoverB_petrovCoeff (a b c d e : ℂ) :
    recoverB (petrovCoeff a b c d e) = b := by
  simp [recoverB, petrovCoeff]

theorem recoverC_petrovCoeff (a b c d e : ℂ) :
    recoverC (petrovCoeff a b c d e) = c := by
  simp [recoverC, petrovCoeff]
  ring_nf
  simp [Complex.I_sq]

theorem recoverD_petrovCoeff (a b c d e : ℂ) :
    recoverD (petrovCoeff a b c d e) = d := by
  simp [recoverD, petrovCoeff]
  ring

theorem recoverE_petrovCoeff (a b c d e : ℂ) :
    recoverE (petrovCoeff a b c d e) = e := by
  simp [recoverE, petrovCoeff]
  ring_nf
  simp [Complex.I_sq]

/-- Explicit left inverse, hence `Q ↦ ψ_Q` is injective on all five traceless
directions. -/
theorem petrovCoeff_injective {a b c d e a' b' c' d' e' : ℂ}
    (h : petrovCoeff a b c d e = petrovCoeff a' b' c' d' e') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' := by
  have ha : a = a' := by
    rw [← recoverA_petrovCoeff a b c d e, ← recoverA_petrovCoeff a' b' c' d' e', h]
  have hb : b = b' := by
    rw [← recoverB_petrovCoeff a b c d e, ← recoverB_petrovCoeff a' b' c' d' e', h]
  have hc : c = c' := by
    rw [← recoverC_petrovCoeff a b c d e, ← recoverC_petrovCoeff a' b' c' d' e', h]
  have hd : d = d' := by
    rw [← recoverD_petrovCoeff a b c d e, ← recoverD_petrovCoeff a' b' c' d' e', h]
  have he : e = e' := by
    rw [← recoverE_petrovCoeff a b c d e, ← recoverE_petrovCoeff a' b' c' d' e', h]
  exact ⟨ha, hb, hc, hd, he⟩

/-- Explicit inverse in the other direction: every binary quartic coefficient
vector comes from one (and, by the previous theorem, only one) traceless `Q`. -/
theorem petrovCoeff_recover (v : Fin 5 → ℂ) :
    petrovCoeff (recoverA v) (recoverB v) (recoverC v) (recoverD v) (recoverE v) = v := by
  funext k
  fin_cases k <;>
    simp [petrovCoeff, recoverA, recoverB, recoverC, recoverD, recoverE] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring


/-! ### Canonical star configurations and their matrix Jordan data

For these examples the coefficient vector is read homogeneously.  Thus
`![0,0,c₂,0,0]` is `c₂z²w²`, with two double roots (at `z=0` and at
infinity), and `![0,0,0,c₃,0]` is `c₃z³w`, with a triple root at zero and a
simple root at infinity.  This avoids silently discarding roots at infinity
when regarding the quartic only as a function of `z`.
-/

/-- Type D in the card: a diagonal `(λ,λ,-2λ)` operator. -/
def typeD (μ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := petrovQ 0 μ 0 0 0

/-- The two-double-star coefficient vector `−12μz²w²`. -/
theorem typeD_coeff (μ : ℂ) :
    petrovCoeff 0 μ 0 0 0 = ![0, 0, -12 * μ, 0, 0] := by
  funext k
  fin_cases k <;> simp [petrovCoeff] <;> ring

theorem typeD_psi (μ z : ℂ) : psi 0 μ 0 0 0 z = -12 * μ * z ^ 2 := by
  rw [psi_expansion]
  ring

theorem typeD_matrix (μ : ℂ) :
    typeD μ = !![μ, 0, 0; 0, μ, 0; 0, 0, -2 * μ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [typeD, petrovQ]

/-- Kerr's displayed eigenvalue ratio, exact for the canonical type-D matrix. -/
theorem typeD_eigenvalue_ratio (μ : ℂ) :
    typeD μ 2 2 = -2 * typeD μ 0 0 ∧ typeD μ 1 1 = typeD μ 0 0 := by
  simp [typeD, petrovQ]

/-- Type N: the nonzero square-zero representative associated to `4μz⁴`. -/
def typeN (μ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := petrovQ μ 0 (Complex.I * μ) 0 0

theorem typeN_coeff (μ : ℂ) :
    petrovCoeff μ 0 (Complex.I * μ) 0 0 = ![0, 0, 0, 0, 4 * μ] := by
  funext k
  fin_cases k <;> simp [petrovCoeff] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem typeN_psi (μ z : ℂ) : psi μ 0 (Complex.I * μ) 0 0 z = 4 * μ * z ^ 4 := by
  rw [psi_expansion]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The card's `N with Q² = 0` clause, for every scale `μ`. -/
theorem typeN_sq (μ : ℂ) : typeN μ ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeN, petrovQ, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- At nonzero scale this is genuinely type N, not the zero matrix. -/
theorem typeN_ne_zero {μ : ℂ} (hμ : μ ≠ 0) : typeN μ ≠ 0 := by
  intro h
  apply hμ
  have h00 := congrFun (congrFun h 0) 0
  simpa [typeN, petrovQ] using h00

/-- Type III: `8μz³w`, with a triple finite star and one star at infinity. -/
def typeIII (μ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := petrovQ 0 0 0 μ (Complex.I * μ)

theorem typeIII_coeff (μ : ℂ) :
    petrovCoeff 0 0 0 μ (Complex.I * μ) = ![0, 0, 0, 8 * μ, 0] := by
  funext k
  fin_cases k <;> simp [petrovCoeff] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem typeIII_psi (μ z : ℂ) : psi 0 0 0 μ (Complex.I * μ) z = 8 * μ * z ^ 3 := by
  rw [psi_expansion]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Type III is genuinely three-step nilpotent: `Q³=0` but, at nonzero scale,
`Q²≠0`.  This distinguishes it from the preceding type-N representative. -/
theorem typeIII_cube (μ : ℂ) : typeIII μ ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeIII, petrovQ, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem typeIII_sq_ne_zero {μ : ℂ} (hμ : μ ≠ 0) : typeIII μ ^ 2 ≠ 0 := by
  intro h
  apply hμ
  have h00 := congrFun (congrFun h 0) 0
  have hsq : μ ^ 2 = 0 := by
    simpa [typeIII, petrovQ, pow_two, Matrix.mul_apply, Fin.sum_univ_three] using h00
  exact sq_eq_zero_iff.mp hsq

/-- A type-II representative: its quartic is `μz²(z²−1)`, so zero is a
double star and `±1` are simple stars. -/
def typeII (μ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  petrovQ (μ / 4) (μ / 12) (Complex.I * μ / 4) 0 0

theorem typeII_coeff (μ : ℂ) :
    petrovCoeff (μ / 4) (μ / 12) (Complex.I * μ / 4) 0 0 =
      ![0, 0, -μ, 0, μ] := by
  funext k
  fin_cases k <;> simp [petrovCoeff] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem typeII_psi (μ z : ℂ) :
    psi (μ / 4) (μ / 12) (Complex.I * μ / 4) 0 0 z = μ * z ^ 2 * (z ^ 2 - 1) := by
  rw [psi_expansion]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The type-II matrix satisfies `(Q−μI/12)²(Q+μI/6)=0`.  This is the
annihilating polynomial `(X−μ/12)²(X+μ/6)`, with a repeated eigenvalue and a
single nontrivial Jordan block; the next theorem excludes the square-free
annihilating polynomial at nonzero scale. -/
theorem typeII_minimal_factor (μ : ℂ) :
    (typeII μ - (μ / 12) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2 *
      (typeII μ + (μ / 6) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeII, petrovQ, pow_two, Matrix.mul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem typeII_not_squarefree {μ : ℂ} (hμ : μ ≠ 0) :
    (typeII μ - (μ / 12) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *
      (typeII μ + (μ / 6) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ≠ 0 := by
  intro h
  apply hμ
  have h00 := congrFun (congrFun h 0) 0
  have hsq : μ ^ 2 = 0 := by
    simp [typeII, petrovQ, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul] at h00
    ring_nf at h00
    simp [Complex.I_sq] at h00
    linear_combination 16 * h00
  exact sq_eq_zero_iff.mp hsq

#print axioms RelationalAtlas.B173.typeD_coeff
#print axioms RelationalAtlas.B173.typeD_psi
#print axioms RelationalAtlas.B173.typeD_matrix
#print axioms RelationalAtlas.B173.typeD_eigenvalue_ratio
#print axioms RelationalAtlas.B173.typeN_coeff
#print axioms RelationalAtlas.B173.typeN_psi
#print axioms RelationalAtlas.B173.typeN_sq
#print axioms RelationalAtlas.B173.typeN_ne_zero
#print axioms RelationalAtlas.B173.typeIII_coeff
#print axioms RelationalAtlas.B173.typeIII_psi
#print axioms RelationalAtlas.B173.typeIII_cube
#print axioms RelationalAtlas.B173.typeIII_sq_ne_zero
#print axioms RelationalAtlas.B173.typeII_coeff
#print axioms RelationalAtlas.B173.typeII_psi
#print axioms RelationalAtlas.B173.typeII_minimal_factor
#print axioms RelationalAtlas.B173.typeII_not_squarefree

#print axioms RelationalAtlas.B173.n_isotropic
#print axioms RelationalAtlas.B173.quadratic_add_scalar_identity
#print axioms RelationalAtlas.B173.petrovQ_symmetric
#print axioms RelationalAtlas.B173.petrovQ_trace
#print axioms RelationalAtlas.B173.psi_expansion
#print axioms RelationalAtlas.B173.petrovCoeff_eq_matrix_mulVec
#print axioms RelationalAtlas.B173.coeffMatrix_det
#print axioms RelationalAtlas.B173.recoverA_petrovCoeff
#print axioms RelationalAtlas.B173.recoverB_petrovCoeff
#print axioms RelationalAtlas.B173.recoverC_petrovCoeff
#print axioms RelationalAtlas.B173.recoverD_petrovCoeff
#print axioms RelationalAtlas.B173.recoverE_petrovCoeff
#print axioms RelationalAtlas.B173.petrovCoeff_injective
#print axioms RelationalAtlas.B173.petrovCoeff_recover

end RelationalAtlas.B173


end

/-! ## B20 — uniform precision leaves correlations fixed, non-uniform does not

Integrated from `.ultramath/smwu0t12t/m4/B20.lean`.
-/
section


/-!
# B20 -- uniform precision scales Fisher information, not correlations

The archived card displays `rho(lambda_0, drift) approximately -0.98 under
every precision profile`, with the caption `including a uniform two percent
across the curve`.  Its coverage ledger states the theorem to be proved:
`sigma_i -> s sigma_i` scales Fisher information by `s^(-2)` and leaves every
correlation fixed.  The same ledger explicitly classifies `-0.98` as a measured
value for an unspecified eight-point model, not as the theorem.

For a design `D` and positive measurement standard deviations `sigma`, the
entrywise Fisher matrix below is `sum_k (D_k i * D_k j) / (sigma_k)^2`.
Division by zero has Lean's usual convention; the scaling identity is in fact
valid even at zero `sigma`, provided `s` is nonzero.  Nonsingularity is assumed
only where matrix inverses are interpreted as covariances.
-/

noncomputable section

namespace RelationalAtlas.B20

open scoped BigOperators

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- Entrywise weighted least-squares/Fisher matrix for a design `D`. -/
def fisherMatrix (D : ι → n → ℝ) (σ : ι → ℝ) : Matrix n n ℝ :=
  fun i j => ∑ k, D k i * D k j / (σ k) ^ 2

/-- Correlation obtained from a covariance matrix.  Lean's division-by-zero
convention makes this defined at a zero variance as well; no positivity claim
is silently inserted. -/
def correlationOfCov (C : Matrix n n ℝ) (i j : n) : ℝ :=
  C i j / (Real.sqrt (C i i) * Real.sqrt (C j j))

/-- The parameter correlation carried by a Fisher matrix is the correlation of
its inverse, the fitted-parameter covariance. -/
def fisherCorrelation (F : Matrix n n ℝ) (i j : n) : ℝ :=
  correlationOfCov F⁻¹ i j

/-- **Displayed Fisher scaling law.**  Multiplying every standard deviation by
the same nonzero `s` multiplies the whole Fisher matrix by `s^(-2)`. -/
theorem fisherMatrix_uniform (D : ι → n → ℝ) (σ : ι → ℝ) {s : ℝ}
    (hs : s ≠ 0) :
    fisherMatrix D (fun k => s * σ k) = (s⁻¹ ^ 2) • fisherMatrix D σ := by
  ext i j
  simp only [fisherMatrix, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hσ : σ k = 0
  · simp [hσ, hs]
  · field_simp [hs, hσ]

/-- Scaling a covariance matrix by a positive number fixes every correlation,
including at zero-variance entries (where both sides use division by zero). -/
theorem correlationOfCov_smul (C : Matrix n n ℝ) (i j : n) {c : ℝ}
    (hc : 0 < c) :
    correlationOfCov (c • C) i j = correlationOfCov C i j := by
  simp only [correlationOfCov, Matrix.smul_apply, smul_eq_mul]
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le]
  have hroot : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hden : Real.sqrt c * Real.sqrt (C i i) *
      (Real.sqrt c * Real.sqrt (C j j)) =
      c * (Real.sqrt (C i i) * Real.sqrt (C j j)) := by
    calc
      _ = (Real.sqrt c * Real.sqrt c) *
          (Real.sqrt (C i i) * Real.sqrt (C j j)) := by ring
      _ = _ := by rw [hroot]
  rw [hden]
  exact mul_div_mul_left _ _ (ne_of_gt hc)

/-- The inverse of the uniformly rescaled Fisher matrix is the old inverse
scaled by `s^2`.  This is the precise covariance consequence of the displayed
`s^(-2)` law. -/
theorem fisherMatrix_inv_uniform (D : ι → n → ℝ) (σ : ι → ℝ) {s : ℝ}
    (hs : s ≠ 0) (hF : IsUnit (fisherMatrix D σ).det) :
    (fisherMatrix D (fun k => s * σ k))⁻¹ = s ^ 2 • (fisherMatrix D σ)⁻¹ := by
  rw [fisherMatrix_uniform D σ hs]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_nonsing_inv _ hF]
  have hscale : s⁻¹ ^ 2 * s ^ 2 = 1 := by field_simp [hs]
  rw [hscale, one_smul]

/-- **B20 scale-invariance theorem.**  Uniform counting precision changes the
size of error bars but not any correlation between fitted parameters. -/
theorem fisherCorrelation_uniform (D : ι → n → ℝ) (σ : ι → ℝ) {s : ℝ}
    (hs : s ≠ 0) (hF : IsUnit (fisherMatrix D σ).det) (i j : n) :
    fisherCorrelation (fisherMatrix D (fun k => s * σ k)) i j =
      fisherCorrelation (fisherMatrix D σ) i j := by
  unfold fisherCorrelation
  rw [fisherMatrix_inv_uniform D σ hs hF]
  exact correlationOfCov_smul _ i j (sq_pos_of_ne_zero hs)

/-! ### A concrete check of what is *not* claimed

For the design with rows `(1,1)` and `(1,7)` (an initial level and drift at
positive times `1` and `7`), all correlations can be evaluated as rational
numbers.  Uniform precision gives `-4/5`.  The non-uniform profile `(5,12)`
gives `-319/481`.  Thus changing relative precisions can change correlations;
only a common precision rescaling is covered by the theorem.  This example is
not a replay of the card's unspecified eight-point numerical experiment. -/

/-- Two exponential-curve design rows, at times `1` and `7`. -/
def design17 : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![1, 7]]

/-- Unit standard deviations at both samples. -/
def uniformPrecision : Fin 2 → ℝ := ![1, 1]

/-- A genuinely non-uniform change of standard deviations. -/
def nonuniformPrecision : Fin 2 → ℝ := ![5, 12]

lemma design17_uniform_fisher :
    fisherMatrix design17 uniformPrecision = !![2, 8; 8, 50] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fisherMatrix, design17, uniformPrecision, Fin.sum_univ_two]

lemma design17_nonuniform_fisher :
    fisherMatrix design17 nonuniformPrecision =
      !![169 / 3600, 319 / 3600; 319 / 3600, 1369 / 3600] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fisherMatrix, design17, nonuniformPrecision, Fin.sum_univ_two]

lemma design17_uniform_fisher_inv :
    (fisherMatrix design17 uniformPrecision)⁻¹ =
      !![25 / 18, -2 / 9; -2 / 9, 1 / 18] := by
  rw [design17_uniform_fisher]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

lemma design17_nonuniform_fisher_inv :
    (fisherMatrix design17 nonuniformPrecision)⁻¹ =
      !![1369 / 36, -319 / 36; -319 / 36, 169 / 36] := by
  rw [design17_nonuniform_fisher]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

lemma design17_uniform_isUnit : IsUnit (fisherMatrix design17 uniformPrecision).det := by
  rw [design17_uniform_fisher, isUnit_iff_ne_zero]
  norm_num [Matrix.det_fin_two]

/-- Exact correlation for the concrete model under unit precision. -/
lemma design17_uniform_correlation :
    fisherCorrelation (fisherMatrix design17 uniformPrecision) 0 1 = -4 / 5 := by
  unfold fisherCorrelation correlationOfCov
  rw [design17_uniform_fisher_inv]
  change (-2 / 9 : ℝ) / (Real.sqrt (25 / 18) * Real.sqrt (1 / 18)) = -4 / 5
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25 / 18)]
  rw [show (25 / 18 : ℝ) * (1 / 18) = (5 / 18) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- The same model under its non-uniform precision profile has a different
correlation, with no numerical approximation involved. -/
lemma design17_nonuniform_correlation :
    fisherCorrelation (fisherMatrix design17 nonuniformPrecision) 0 1 =
      -319 / 481 := by
  unfold fisherCorrelation correlationOfCov
  rw [design17_nonuniform_fisher_inv]
  change (-319 / 36 : ℝ) /
    (Real.sqrt (1369 / 36) * Real.sqrt (169 / 36)) = -319 / 481
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1369 / 36)]
  rw [show (1369 / 36 : ℝ) * (169 / 36) = (481 / 36) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Non-uniformity is essential to the counterexample.**  Rescaling only the
relative precision profile is not correlation preserving. -/
theorem nonuniform_precision_changes_correlation :
    fisherCorrelation (fisherMatrix design17 nonuniformPrecision) 0 1 ≠
      fisherCorrelation (fisherMatrix design17 uniformPrecision) 0 1 := by
  rw [design17_nonuniform_correlation, design17_uniform_correlation]
  norm_num

/-- The card's uniform two-percent caption, instantiated on the concrete model:
common precision `1/50` leaves the exact value `-4/5` unchanged. -/
theorem design17_two_percent_correlation :
    fisherCorrelation
      (fisherMatrix design17 (fun k => (1 / 50 : ℝ) * uniformPrecision k)) 0 1 =
        -4 / 5 := by
  rw [fisherCorrelation_uniform design17 uniformPrecision (by norm_num)
    design17_uniform_isUnit]
  exact design17_uniform_correlation

end RelationalAtlas.B20

#print axioms RelationalAtlas.B20.fisherMatrix_uniform
#print axioms RelationalAtlas.B20.correlationOfCov_smul
#print axioms RelationalAtlas.B20.fisherMatrix_inv_uniform
#print axioms RelationalAtlas.B20.fisherCorrelation_uniform
#print axioms RelationalAtlas.B20.design17_uniform_fisher
#print axioms RelationalAtlas.B20.design17_nonuniform_fisher
#print axioms RelationalAtlas.B20.design17_uniform_fisher_inv
#print axioms RelationalAtlas.B20.design17_nonuniform_fisher_inv
#print axioms RelationalAtlas.B20.design17_uniform_isUnit
#print axioms RelationalAtlas.B20.design17_uniform_correlation
#print axioms RelationalAtlas.B20.design17_nonuniform_correlation
#print axioms RelationalAtlas.B20.nonuniform_precision_changes_correlation
#print axioms RelationalAtlas.B20.design17_two_percent_correlation


end

/-! ## B177 — the effective potential, and the order of differentiability

Integrated from `.ultramath/smwu0t12t/m1/B177.lean`.
-/
section


/-!
B177: Schwarzschild circular-orbit potential and the ISCO wobble generator.
Units are G = c = M = 1.  The potential is differentiated with `L` fixed;
only after the second derivative do we impose `L² = r² / (r - 3)`.
This order is exactly the one stated in the card's "Why it holds" section.
-/

namespace B177


noncomputable def effectivePotential (L r : ℝ) : ℝ :=
  (1 - 2 / r) * (1 + L ^ 2 / r ^ 2)

noncomputable def firstFixedL (L r : ℝ) : ℝ :=
  2 / r ^ 2 - 2 * L ^ 2 / r ^ 3 + 6 * L ^ 2 / r ^ 4

noncomputable def secondFixedL (L r : ℝ) : ℝ :=
  -4 / r ^ 3 + 6 * L ^ 2 / r ^ 4 - 24 * L ^ 2 / r ^ 5

lemma hasDerivAt_effectivePotential_fixedL (L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (effectivePotential L) (firstFixedL L r) r := by
  have h₁ : HasDerivAt (fun x : ℝ => 2 / x) (-2 / r ^ 2) r := by
    convert (hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hr using 1
    · ext x
      rfl
    · simp
  have h₂ : HasDerivAt (fun x : ℝ => L ^ 2 / x ^ 2) (-2 * L ^ 2 / r ^ 3) r := by
    convert (hasDerivAt_const r (L ^ 2)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr) using 1
    · dsimp
      field_simp; ring
  have h₃ : HasDerivAt (fun x : ℝ => 2 * L ^ 2 / x ^ 3) (-6 * L ^ 2 / r ^ 4) r := by
    convert (hasDerivAt_const r (2 * L ^ 2)).div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr) using 1
    · dsimp
      field_simp; ring
  have h := (((hasDerivAt_const r (1 : ℝ)).sub h₁).add h₂).sub h₃
  convert h using 1
  · ext x
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [show effectivePotential L x = 1 - 2 / x + L ^ 2 / x ^ 2 - 2 * L ^ 2 / x ^ 3 by
      unfold effectivePotential
      ring]
  · unfold firstFixedL
    ring

lemma hasDerivAt_firstFixedL (L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (firstFixedL L) (secondFixedL L r) r := by
  have h₁ : HasDerivAt (fun x : ℝ => 2 / x ^ 2) (-4 / r ^ 3) r := by
    convert (hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr) using 1
    dsimp
    field_simp; ring
  have h₂ : HasDerivAt (fun x : ℝ => 2 * L ^ 2 / x ^ 3) (-6 * L ^ 2 / r ^ 4) r := by
    convert (hasDerivAt_const r (2 * L ^ 2)).div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr) using 1
    dsimp
    field_simp; ring
  have h₃ : HasDerivAt (fun x : ℝ => 6 * L ^ 2 / x ^ 4) (-24 * L ^ 2 / r ^ 5) r := by
    convert (hasDerivAt_const r (6 * L ^ 2)).div (hasDerivAt_pow 4 r) (pow_ne_zero 4 hr) using 1
    dsimp
    field_simp; ring
  have h := (h₁.sub h₂).add h₃
  convert h using 1
  · ext x
    rfl
  · unfold secondFixedL
    ring

lemma deriv_deriv_effectivePotential (L r : ℝ) (hr : 0 < r) :
    deriv (deriv (effectivePotential L)) r = secondFixedL L r := by
  have heq : deriv (effectivePotential L) =ᶠ[nhds r] firstFixedL L := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hasDerivAt_effectivePotential_fixedL L x (ne_of_gt hx)).deriv
  calc
    deriv (deriv (effectivePotential L)) r = deriv (firstFixedL L) r := heq.deriv_eq
    _ = secondFixedL L r := (hasDerivAt_firstFixedL L r (ne_of_gt hr)).deriv

lemma half_second_at_circular (L r : ℝ) (hr : r ≠ 0) (hr3 : r - 3 ≠ 0)
    (hL : L ^ 2 = r ^ 2 / (r - 3)) :
    secondFixedL L r / 2 = (r - 6) / (r ^ 3 * (r - 3)) := by
  unfold secondFixedL
  rw [hL]
  field_simp
  ring

noncomputable def radialFrequencySq (L r : ℝ) : ℝ := secondFixedL L r / 2
noncomputable def orbitalOmega (L r : ℝ) : ℝ := L / r ^ 2

lemma epicyclic_over_orbital_sq (L r : ℝ) (hr3 : 3 < r)
    (hL : L ^ 2 = r ^ 2 / (r - 3)) :
    radialFrequencySq L r / (orbitalOmega L r) ^ 2 = 1 - 6 / r := by
  have hr : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrm3 : r - 3 ≠ 0 := by linarith
  have hL2pos : 0 < L ^ 2 := by
    rw [hL]
    positivity
  have hL0 : L ≠ 0 := by
    intro h
    rw [h] at hL2pos
    norm_num at hL2pos
  have hrad : radialFrequencySq L r = (r - 6) / (r ^ 3 * (r - 3)) :=
    half_second_at_circular L r hr0 hrm3 hL
  rw [hrad]
  unfold orbitalOmega
  field_simp
  rw [hL]
  field_simp

lemma newtonian_exponent_identity (M r : ℝ) : 1 - 6 * M / r = 3 - (2 + 6 * M / r) := by ring

-- The real 2×2 wobble generator, with q = ½V″.
def wobble (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -q, 0]

lemma wobble_mul_self (q : ℝ) : wobble q * wobble q = -q • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wobble]

lemma isco_half_second (L : ℝ) (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    radialFrequencySq L 6 = 0 := by
  unfold radialFrequencySq
  rw [half_second_at_circular L 6 (by norm_num) (by norm_num) hL]
  norm_num

lemma isco_wobble_sq (L : ℝ) (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    (wobble (radialFrequencySq L 6)) ^ 2 = 0 := by
  rw [isco_half_second L hL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wobble, sq]

lemma isco_wobble_ne_zero (L : ℝ) (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    wobble (radialFrequencySq L 6) ≠ 0 := by
  rw [isco_half_second L hL]
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [wobble] at h01

lemma stable_half_second_pos (L r : ℝ) (hr : 6 < r)
    (hL : L ^ 2 = r ^ 2 / (r - 3)) : 0 < radialFrequencySq L r := by
  have hr3 : 3 < r := by linarith
  have hden : 0 < r ^ 3 * (r - 3) := mul_pos (pow_pos (by linarith) 3) (by linarith)
  unfold radialFrequencySq
  rw [half_second_at_circular L r (by linarith) (by linarith) hL]
  exact div_pos (by linarith) hden

lemma unstable_half_second_neg (L r : ℝ) (hr3 : 3 < r) (hr6 : r < 6)
    (hL : L ^ 2 = r ^ 2 / (r - 3)) : radialFrequencySq L r < 0 := by
  have hden : 0 < r ^ 3 * (r - 3) := mul_pos (pow_pos (by linarith) 3) (by linarith)
  unfold radialFrequencySq
  rw [half_second_at_circular L r (by linarith) (by linarith) hL]
  exact div_neg_of_neg_of_pos (by linarith) hden

open Polynomial in
lemma wobble_charpoly (q : ℝ) :
    (wobble q).charpoly = X ^ 2 + C q := by
  rw [Matrix.charpoly_fin_two]
  simp [wobble, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]

-- Same generator over the complexes; an eigenvalue supplied as a root of λ²+q.
def wobbleC (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -q, 0]

lemma wobbleC_eigen (q z : ℂ) (hz : z ^ 2 = -q) :
    (wobbleC q).mulVec ![1, z] = z • ![1, z] := by
  ext i
  fin_cases i
  · simp [wobbleC, Matrix.mulVec, dotProduct]
  · simp [wobbleC, Matrix.mulVec, dotProduct]
    rw [← hz]
    ring

lemma imaginary_root_sq (q : ℝ) (hq : 0 ≤ q) :
    (((Real.sqrt q : ℝ) : ℂ) * Complex.I) ^ 2 = -(q : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hq]
  ring

lemma real_root_sq (q : ℝ) (hq : q ≤ 0) :
    (Real.sqrt (-q)) ^ 2 = -q := Real.sq_sqrt (neg_nonneg.mpr hq)

lemma witness_radius_seven (L : ℝ) (hL : L ^ 2 = (7 : ℝ) ^ 2 / (7 - 3)) :
    radialFrequencySq L 7 = 1 / 1372 := by
  unfold radialFrequencySq
  rw [half_second_at_circular L 7 (by norm_num) (by norm_num) hL]
  norm_num

lemma witness_radius_five (L : ℝ) (hL : L ^ 2 = (5 : ℝ) ^ 2 / (5 - 3)) :
    radialFrequencySq L 5 = -1 / 250 := by
  unfold radialFrequencySq
  rw [half_second_at_circular L 5 (by norm_num) (by norm_num) hL]
  norm_num

lemma isco_wobble_nonzero_nilpotent (L : ℝ) (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    wobble (radialFrequencySq L 6) ≠ 0 ∧ IsNilpotent (wobble (radialFrequencySq L 6)) := by
  exact ⟨isco_wobble_ne_zero L hL, ⟨2, isco_wobble_sq L hL⟩⟩

lemma halfSecond_circular (L r : ℝ) (hr : 3 < r) (hL : L ^ 2 = r ^ 2 / (r - 3)) :
    deriv (deriv (effectivePotential L)) r / 2 = (r - 6) / (r ^ 3 * (r - 3)) := by
  rw [deriv_deriv_effectivePotential L r (by linarith)]
  exact half_second_at_circular L r (by linarith) (by linarith) hL

lemma oscillation_eigenvalue (q : ℝ) (hq : 0 ≤ q) :
    let z : ℂ := ((Real.sqrt q : ℝ) : ℂ) * Complex.I
    (wobbleC (q : ℂ)).mulVec ![1, z] = z • ![1, z] := by
  dsimp
  exact wobbleC_eigen (q : ℂ) _ (imaginary_root_sq q hq)

lemma growth_eigenvalue (q : ℝ) (hq : q ≤ 0) :
    let z : ℂ := ((Real.sqrt (-q) : ℝ) : ℂ)
    (wobbleC (q : ℂ)).mulVec ![1, z] = z • ![1, z] := by
  dsimp
  apply wobbleC_eigen
  rw [← Complex.ofReal_pow, real_root_sq q hq]
  simp

end B177

#print axioms B177.hasDerivAt_effectivePotential_fixedL
#print axioms B177.hasDerivAt_firstFixedL
#print axioms B177.deriv_deriv_effectivePotential
#print axioms B177.half_second_at_circular
#print axioms B177.halfSecond_circular
#print axioms B177.epicyclic_over_orbital_sq
#print axioms B177.newtonian_exponent_identity
#print axioms B177.wobble_mul_self
#print axioms B177.wobble_charpoly
#print axioms B177.wobbleC_eigen
#print axioms B177.imaginary_root_sq
#print axioms B177.real_root_sq
#print axioms B177.oscillation_eigenvalue
#print axioms B177.growth_eigenvalue
#print axioms B177.isco_half_second
#print axioms B177.isco_wobble_sq
#print axioms B177.isco_wobble_ne_zero
#print axioms B177.isco_wobble_nonzero_nilpotent
#print axioms B177.stable_half_second_pos
#print axioms B177.unstable_half_second_neg
#print axioms B177.witness_radius_seven
#print axioms B177.witness_radius_five


end

/-! ## B109 — the SLD, the factors of two and four, and the Bures speed

Integrated from `.ultramath/smwu0t12t/m14/B109.lean`.
-/
section

/-
B109 — The moving subspace has a Fisher speed.

The archived card displays

  ρ = P/k,  L = 2 Ṗ,  F_Q = 4 g/k,
  g = (1/2) Tr(Ṗ²),  Bures speed² = g/k,

and its proof specifies F_Q = Tr(ρ L²) and the SLD equation
`dotρ = (Lρ + ρL)/2`.  This file proves those finite-dimensional
normalization identities over `ℂ`.  The tangent hypothesis is exactly
`V P + P V = V`, where `V = Ṗ`.

The Bures assertion uses the standard infinitesimal convention
`Bures speed² = F_Q / 4`; this is made explicit in `buresSpeedSq`.
Differentiability itself and the fidelity formula for Bures distance are
not needed for, and are not asserted by, this algebraic normalization check.
-/


noncomputable section

open Matrix

namespace AtlasB109

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The uniform density matrix on the range of a rank-`k` projector. -/
def rho (P : Matrix n n ℂ) (k : ℂ) : Matrix n n ℂ := k⁻¹ • P

/-- The SLD in the card's convention. -/
def sld (V : Matrix n n ℂ) : Matrix n n ℂ := (2 : ℂ) • V

/-- Half the squared Hilbert--Schmidt speed of the moving projector. -/
def grassmannSpeedSq (V : Matrix n n ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (V * V).trace

/-- SLD quantum Fisher information, exactly `Tr(ρ L²)`. -/
def quantumFisher (P V : Matrix n n ℂ) (k : ℂ) : ℂ :=
  (rho P k * sld V * sld V).trace

/-- The infinitesimal Bures convention `ds_B² = (F_Q/4) ds²`. -/
def buresSpeedSq (P V : Matrix n n ℂ) (k : ℂ) : ℂ :=
  quantumFisher P V k / 4

/-- Uniform normalization really gives a trace-one state when `Tr P = k`. -/
theorem trace_rho (P : Matrix n n ℂ) (k : ℂ) (hk : k ≠ 0)
    (hTr : P.trace = k) : (rho P k).trace = 1 := by
  simp [rho, hTr, hk]

#print axioms AtlasB109.trace_rho

/-- The card's `L = 2V` solves its SLD equation for every nonzero rank
normalization.  No commutativity of `P` and `V` is used. -/
theorem sld_two_tangent (P V : Matrix n n ℂ) (k : ℂ) (hk : k ≠ 0)
    (hV : V * P + P * V = V) :
    (2 : ℂ)⁻¹ • (sld V * rho P k + rho P k * sld V) = k⁻¹ • V := by
  calc
    (2 : ℂ)⁻¹ • (sld V * rho P k + rho P k * sld V) =
        k⁻¹ • (V * P + P * V) := by
      simp [sld, rho, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
      congr 1
      ring
    _ = k⁻¹ • V := by rw [hV]

#print axioms AtlasB109.sld_two_tangent

/-- The trace identity in the card: `2 Tr(PV²) = Tr(V²)`.
It follows from tangency and cyclicity of trace; self-adjointness is not
needed for this algebraic step. -/
theorem two_trace_PVV (P V : Matrix n n ℂ)
    (hV : V * P + P * V = V) :
    (2 : ℂ) * (P * V * V).trace = (V * V).trace := by
  symm
  calc
    (V * V).trace = ((V * P + P * V) * V).trace := by rw [hV]
    _ = (V * P * V).trace + (P * V * V).trace := by
      rw [add_mul, Matrix.trace_add]
    _ = (P * V * V).trace + (P * V * V).trace := by
      rw [← Matrix.trace_mul_cycle P V V]
    _ = 2 * (P * V * V).trace := by ring

#print axioms AtlasB109.two_trace_PVV

/-- Before using tangency, the Fisher trace is `(4/k) Tr(PV²)`. -/
theorem quantumFisher_eq_trace (P V : Matrix n n ℂ) (k : ℂ) (hk : k ≠ 0) :
    quantumFisher P V k = (4 / k) * (P * V * V).trace := by
  simp only [quantumFisher, rho, sld, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_smul, smul_eq_mul, div_eq_mul_inv]
  ring

#print axioms AtlasB109.quantumFisher_eq_trace

/-- **B109, Fisher normalization.**  The SLD Fisher information is exactly
`4g/k`, with `g = Tr(V²)/2`. -/
theorem quantumFisher_eq_four_speed_div (P V : Matrix n n ℂ) (k : ℂ)
    (hk : k ≠ 0) (hV : V * P + P * V = V) :
    quantumFisher P V k = 4 * grassmannSpeedSq V / k := by
  rw [quantumFisher_eq_trace P V k hk]
  have htrace := two_trace_PVV P V hV
  calc
    (4 / k) * (P * V * V).trace = (2 / k) * (2 * (P * V * V).trace) := by ring
    _ = (2 / k) * (V * V).trace := by rw [htrace]
    _ = 4 * grassmannSpeedSq V / k := by
      simp only [grassmannSpeedSq]
      ring

#print axioms AtlasB109.quantumFisher_eq_four_speed_div

/-- **B109, Bures normalization.**  With `ds_B² = F_Q ds²/4`, the squared
Bures speed is precisely `g/k`. -/
theorem buresSpeedSq_eq (P V : Matrix n n ℂ) (k : ℂ)
    (hk : k ≠ 0) (hV : V * P + P * V = V) :
    buresSpeedSq P V k = grassmannSpeedSq V / k := by
  rw [buresSpeedSq, quantumFisher_eq_four_speed_div P V k hk hV]
  ring

#print axioms AtlasB109.buresSpeedSq_eq

/-- All displayed identities, the trace-one normalization, and the SLD
 equation in one statement. -/
theorem b109_identities (P V : Matrix n n ℂ) (k : ℂ)
    (hk : k ≠ 0) (hTr : P.trace = k) (hV : V * P + P * V = V) :
    (rho P k).trace = 1 ∧
      (2 : ℂ)⁻¹ • (sld V * rho P k + rho P k * sld V) = k⁻¹ • V ∧
      quantumFisher P V k = 4 * grassmannSpeedSq V / k ∧
      buresSpeedSq P V k = grassmannSpeedSq V / k := by
  exact ⟨trace_rho P k hk hTr, sld_two_tangent P V k hk hV,
    quantumFisher_eq_four_speed_div P V k hk hV,
    buresSpeedSq_eq P V k hk hV⟩

#print axioms AtlasB109.b109_identities

/-- A concrete rank-one tangency witness on a two-dimensional space. -/
def exampleP : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- A Hermitian off-diagonal tangent of the rank-one projector. -/
def exampleV (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, a; star a, 0]

/-- The explicit projector is idempotent. -/
theorem exampleP_idempotent : exampleP * exampleP = exampleP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exampleP, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms AtlasB109.exampleP_idempotent

/-- The explicit projector is Hermitian and has trace one. -/
theorem exampleP_hermitian_and_trace : examplePᴴ = exampleP ∧ exampleP.trace = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [exampleP]
  · simp [exampleP, Matrix.trace, Fin.sum_univ_two]

#print axioms AtlasB109.exampleP_hermitian_and_trace

/-- The explicit tangent is Hermitian for every complex amplitude. -/
theorem exampleV_hermitian (a : ℂ) : (exampleV a)ᴴ = exampleV a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exampleV]

#print axioms AtlasB109.exampleV_hermitian

/-- The explicit pair satisfies the exact tangent equation. -/
theorem example_tangent (a : ℂ) :
    exampleV a * exampleP + exampleP * exampleV a = exampleV a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exampleP, exampleV, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms AtlasB109.example_tangent

/-- Non-vacuous numerical check: the squared speed is `a * star a = |a|²`. -/
theorem example_speed (a : ℂ) : grassmannSpeedSq (exampleV a) = a * star a := by
  simp [grassmannSpeedSq, exampleV, Matrix.trace, Fin.sum_univ_two]
  ring

#print axioms AtlasB109.example_speed

/-- For the explicit moving rank-one subspace, `F_Q = 4 |a|²`. -/
theorem example_fisher (a : ℂ) :
    quantumFisher exampleP (exampleV a) 1 = 4 * a * star a := by
  rw [quantumFisher_eq_four_speed_div exampleP (exampleV a) 1 (by norm_num)
    (example_tangent a), example_speed]
  ring

#print axioms AtlasB109.example_fisher

/-- The Bures counterpart of the same concrete rank-one computation. -/
theorem example_bures (a : ℂ) :
    buresSpeedSq exampleP (exampleV a) 1 = a * star a := by
  rw [buresSpeedSq_eq exampleP (exampleV a) 1 (by norm_num) (example_tangent a),
    example_speed]
  ring

#print axioms AtlasB109.example_bures

/-- At unit subspace speed this is exactly the card's rank-one row:
`g = 1`, `F_Q = 4`, and `Bures speed² = 1`. -/
theorem example_unit_speed :
    grassmannSpeedSq (exampleV 1) = 1 ∧
      quantumFisher exampleP (exampleV 1) 1 = 4 ∧
      buresSpeedSq exampleP (exampleV 1) 1 = 1 := by
  norm_num [example_speed, example_fisher, example_bures]

#print axioms AtlasB109.example_unit_speed

end AtlasB109


end

/-! ## B24 — the second-order ledger, and the Hermiticity the equality needs

Integrated from `.ultramath/smwu0t12t/m5/B24.lean`.
-/
section


/-!
# B24 — the second-order log-determinant ledger

The archived card displays
`c₂ = -1/2 Tr(RERE) = -1/2 Σ |E_nm|² / ((λ_n + η)(λ_m + η))`,
together with the expansion of `log det(H + η + εE)` whose linear term is
`ε Tr(RE)` and whose quadratic term is `ε² c₂`, where `R = (H + η)⁻¹`.
Its Carry/Check fields assume Hermitian `H`, a shift making `H + η` positive,
and invertibility of `H + η`; they only say "a perturbation E".

This file gives the requested explicit two-dimensional computation.  The
shifted eigenvalues are `A = λ₁ + η` and `B = λ₂ + η`.  With Hermitian
`E = [[a,b],[b*,d]]`, both forms of `c₂` agree and are half the second
derivative.  The literal two-form equality fails without Hermitian `E`.
The zero-eigenvalue boundary has no finite expansion, so the positive-shift
hypothesis is essential.  The arbitrary-dimension analytic series is not
formalised here.
-/
noncomputable section

open scoped ComplexConjugate Topology
open Filter Matrix

namespace RelationalAtlas.B24

/-- The determinant of `(diag(A,B) + ε E)` when `E = [[a,b],[conj b,d]]`. -/
def detCurve (A B a d q : ℝ) (ε : ℝ) : ℝ :=
  (A + ε * a) * (B + ε * d) - ε ^ 2 * q

/-- The numerator in the logarithmic derivative of `detCurve`. -/
def derivNumerator (A B a d q : ℝ) (ε : ℝ) : ℝ :=
  a * (B + ε * d) + (A + ε * a) * d - 2 * ε * q

lemma hasDerivAt_detCurve (A B a d q : ℝ) (ε : ℝ) :
    HasDerivAt (detCurve A B a d q) (derivNumerator A B a d q ε) ε := by
  unfold detCurve derivNumerator
  convert
    (((hasDerivAt_id ε).mul_const a).const_add A |>.mul
      (((hasDerivAt_id ε).mul_const d).const_add B)).sub
      (((hasDerivAt_id ε).pow 2).mul_const q) using 1 <;>
    (try ext x) <;> simp [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]

lemma hasDerivAt_logDetCurve (A B a d q : ℝ) (ε : ℝ)
    (h : detCurve A B a d q ε ≠ 0) :
    HasDerivAt (fun x => Real.log (detCurve A B a d q x))
      (derivNumerator A B a d q ε / detCurve A B a d q ε) ε :=
  (hasDerivAt_detCurve A B a d q ε).log h

lemma hasDerivAt_derivNumerator (A B a d q : ℝ) (ε : ℝ) :
    HasDerivAt (derivNumerator A B a d q) (2 * a * d - 2 * q) ε := by
  unfold derivNumerator
  convert
    (((hasDerivAt_id ε).mul_const d).const_add B).const_mul a |>.add
      ((((hasDerivAt_id ε).mul_const a).const_add A).mul_const d) |>.sub
      (((hasDerivAt_id ε).mul_const q).const_mul 2) using 1 <;>
    (try ext x) <;> simp [id_eq, Pi.sub_apply] <;> ring

lemma eventually_deriv_logDetCurve (A B a d q : ℝ)
    (h : detCurve A B a d q 0 ≠ 0) :
    (fun ε => deriv (fun x => Real.log (detCurve A B a d q x)) ε) =ᶠ[𝓝 0]
      (fun ε => derivNumerator A B a d q ε / detCurve A B a d q ε) := by
  filter_upwards [(hasDerivAt_detCurve A B a d q 0).continuousAt.eventually_ne h]
    with ε hε
  exact (hasDerivAt_logDetCurve A B a d q ε hε).deriv

/-- A general complex `2 × 2` perturbation, kept separate from the Hermitian
special case so that the missing hypothesis can be tested. -/
def perturbation2 (a b c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; c, d]

/-- The resolvent of `diag(A,B)`, with `A = λ₁ + η` and `B = λ₂ + η`. -/
def resolvent2 (A B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(A : ℂ)⁻¹, 0; 0, (B : ℂ)⁻¹]

lemma trace_RERE_two (A B : ℝ) (a b c d : ℂ) :
    trace (resolvent2 A B * perturbation2 a b c d *
      resolvent2 A B * perturbation2 a b c d) =
      a ^ 2 * (A : ℂ)⁻¹ ^ 2 + d ^ 2 * (B : ℂ)⁻¹ ^ 2 +
        2 * b * c * (A : ℂ)⁻¹ * (B : ℂ)⁻¹ := by
  simp [resolvent2, perturbation2, Matrix.trace, Fin.sum_univ_two]
  ring

lemma trace_RE_two (A B : ℝ) (a b c d : ℂ) :
    trace (resolvent2 A B * perturbation2 a b c d) =
      a * (A : ℂ)⁻¹ + d * (B : ℂ)⁻¹ := by
  simp [resolvent2, perturbation2, Matrix.trace, Fin.sum_univ_two]
  ring

/-- The modulus-squared sum on the right-hand side of the card, before
assuming any relation between the two off-diagonal entries. -/
def spectralSum2 (A B : ℝ) (a b c d : ℂ) : ℝ :=
  Complex.normSq a / A ^ 2 + Complex.normSq d / B ^ 2 +
    (Complex.normSq b + Complex.normSq c) / (A * B)

/-- `H + η + εE` in the eigenbasis of a two-dimensional Hermitian `H`,
with `E = [[a,b],[b*,d]]`. -/
def shiftedHermitian2 (A B a d : ℝ) (b : ℂ) (ε : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(A : ℂ) + (ε : ℂ) * (a : ℂ), (ε : ℂ) * b;
     (ε : ℂ) * star b, (B : ℂ) + (ε : ℂ) * (d : ℂ)]

lemma det_shiftedHermitian2 (A B a d : ℝ) (b : ℂ) (ε : ℝ) :
    (shiftedHermitian2 A B a d b ε).det =
      (detCurve A B a d (Complex.normSq b) ε : ℂ) := by
  rw [shiftedHermitian2, Matrix.det_fin_two_of]
  have hb : b * (starRingEnd ℂ) b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  simp only [RCLike.star_def]
  simp [detCurve]
  rw [← hb]
  ring

/-- **B24, repaired spectral identity.**  With a Hermitian perturbation, the
trace form and the modulus-squared eigenbasis form are identical. -/
theorem two_c2_forms_hermitian (A B : ℝ) (a d : ℝ) (b : ℂ) :
    -(1 / 2 : ℂ) * trace (resolvent2 A B *
      perturbation2 (a : ℂ) b (star b) (d : ℂ) * resolvent2 A B *
        perturbation2 (a : ℂ) b (star b) (d : ℂ)) =
      ((-(1 / 2 : ℝ) * spectralSum2 A B (a : ℂ) b (star b) (d : ℂ) : ℝ) : ℂ) := by
  rw [trace_RERE_two]
  have hb : b * (starRingEnd ℂ) b = (Complex.normSq b : ℂ) := Complex.mul_conj b
  simp only [RCLike.star_def]
  simp [spectralSum2, Complex.normSq_conj, Complex.normSq_ofReal]
  rw [← hb]
  ring

/-- **Refutation of the literal two-form equality without Hermitian `E`.**
Take `A = B = 1` and `E = [[0,1],[0,0]]`.  The trace is zero, whereas the
modulus-squared sum is one, so the two displayed values of `c₂` differ. -/
theorem nonHermitian_perturbation_breaks_two_forms :
    -(1 / 2 : ℂ) * trace (resolvent2 1 1 *
      perturbation2 0 1 0 0 * resolvent2 1 1 * perturbation2 0 1 0 0) ≠
      ((-(1 / 2 : ℝ) * spectralSum2 1 1 0 1 0 0 : ℝ) : ℂ) := by
  rw [trace_RERE_two]
  norm_num [spectralSum2]

/-- For the same counterexample the matrix is `[[1,ε],[0,1]]`, so the actual
log-determinant is identically zero and its true `c₂` is zero. -/
theorem nonHermitian_witness_actual_c2 :
    (1 / 2 : ℝ) * iteratedDeriv 2 (fun ε : ℝ => Real.log
      ((!![1, (ε : ℂ); 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det.re)) 0 = 0 := by
  have hfun : (fun ε : ℝ => Real.log
      ((!![1, (ε : ℂ); 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det.re)) =
      (fun _ => 0) := by
    funext ε
    rw [Matrix.det_fin_two_of]
    norm_num
  rw [hfun]
  simp

/-- For a positive two-dimensional `H + η`, the displayed `c₂` is exactly
half the second derivative of `log det(H + η + εE)` at zero. -/
theorem iteratedDeriv_two_logDetCurve (A B a d q : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    iteratedDeriv 2 (fun ε => Real.log (detCurve A B a d q ε)) 0 =
      -(a ^ 2 / A ^ 2 + d ^ 2 / B ^ 2 + 2 * q / (A * B)) := by
  have hD0 : detCurve A B a d q 0 ≠ 0 := by
    simp [detCurve, hA, hB]
  have hQ := (hasDerivAt_derivNumerator A B a d q 0).div
    (hasDerivAt_detCurve A B a d q 0) hD0
  have hQ' := hQ.congr_of_eventuallyEq (eventually_deriv_logDetCurve A B a d q hD0)
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ]
  simp only [iteratedDeriv_one]
  rw [hQ'.deriv]
  simp only [detCurve, derivNumerator, zero_mul, add_zero, mul_zero, sub_zero]
  field_simp [hA, hB]
  ring

lemma log_det_shiftedHermitian2 (A B a d : ℝ) (b : ℂ) :
    (fun ε => Real.log ((shiftedHermitian2 A B a d b ε).det.re)) =
      (fun ε => Real.log (detCurve A B a d (Complex.normSq b) ε)) := by
  funext ε
  rw [det_shiftedHermitian2]
  exact congrArg Real.log (Complex.ofReal_re _)

/-- The constant and linear terms in the card's expansion, together with the
second-order coefficient.  Positivity of `H + η` is used through its consequences
`A ≠ 0` and `B ≠ 0`. -/
theorem logdet_expansion_coefficients (A B a d : ℝ) (b : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    Real.log ((shiftedHermitian2 A B a d b 0).det.re) = Real.log (A * B) ∧
    deriv (fun ε => Real.log ((shiftedHermitian2 A B a d b ε).det.re)) 0 =
      a / A + d / B ∧
    (1 / 2 : ℝ) * iteratedDeriv 2
        (fun ε => Real.log ((shiftedHermitian2 A B a d b ε).det.re)) 0 =
      -(1 / 2 : ℝ) * spectralSum2 A B (a : ℂ) b (star b) (d : ℂ) := by
  have hD0 : detCurve A B a d (Complex.normSq b) 0 ≠ 0 := by
    simp [detCurve, hA, hB]
  refine ⟨?_, ?_, ?_⟩
  · rw [det_shiftedHermitian2]
    simp [detCurve]
  · rw [log_det_shiftedHermitian2]
    rw [(hasDerivAt_logDetCurve A B a d (Complex.normSq b) 0 hD0).deriv]
    simp only [detCurve, derivNumerator, zero_mul, add_zero, mul_zero, sub_zero]
    field_simp [hA, hB]
    ring
  · rw [log_det_shiftedHermitian2, iteratedDeriv_two_logDetCurve A B a d
      (Complex.normSq b) hA hB]
    simp [spectralSum2, RCLike.star_def, Complex.normSq_conj,
      Complex.normSq_ofReal]
    ring

/-- The same second coefficient, written literally as `-1/2 Tr(RERE)`. -/
theorem logdet_c2_eq_trace_RERE (A B a d : ℝ) (b : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (((1 / 2 : ℝ) * iteratedDeriv 2
        (fun ε => Real.log ((shiftedHermitian2 A B a d b ε).det.re)) 0 : ℝ) : ℂ) =
      -(1 / 2 : ℂ) * trace (resolvent2 A B *
        perturbation2 (a : ℂ) b (star b) (d : ℂ) * resolvent2 A B *
          perturbation2 (a : ℂ) b (star b) (d : ℂ)) := by
  rw [(logdet_expansion_coefficients A B a d b hA hB).2.2]
  exact (two_c2_forms_hermitian A B a d b).symm

/-- The linear coefficient is likewise literally `Tr(RE)`. -/
theorem logdet_c1_eq_trace_RE (A B a d : ℝ) (b : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ((deriv (fun ε => Real.log ((shiftedHermitian2 A B a d b ε).det.re)) 0 : ℝ) : ℂ) =
      trace (resolvent2 A B * perturbation2 (a : ℂ) b (star b) (d : ℂ)) := by
  rw [(logdet_expansion_coefficients A B a d b hA hB).2.1, trace_RE_two]
  push_cast
  rfl

/-- At the excluded boundary `λ₁ = η = 0`, take `λ₂ = 1` and `E = I`.
Then `det(H + εE) = ε(1 + ε)`, whose logarithm diverges to `-∞` as
`ε → 0⁺`.  Thus no finite Taylor expansion at `ε = 0` extends across this
zero eigenvalue. -/
theorem singular_logdet_diverges :
    Tendsto (fun ε : ℝ => Real.log
      ((shiftedHermitian2 0 1 1 1 0 ε).det.re)) (𝓝[>] 0) atBot := by
  have hlog : Tendsto (fun ε : ℝ => Real.log (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun ε : ℝ => Real.log (1 + ε)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  rw [log_det_shiftedHermitian2]
  apply (Real.tendsto_log_nhdsGT_zero.atBot_add hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  have he : ε ≠ 0 := ne_of_gt hε
  have h1e : 1 + ε ≠ 0 := by linarith
  simp only [detCurve, Complex.normSq_zero]
  change Real.log ε + Real.log (1 + ε) =
    Real.log ((0 + ε * 1) * (1 + ε * 1) - ε ^ 2 * 0)
  rw [show (0 + ε * 1) * (1 + ε * 1) - ε ^ 2 * 0 = ε * (1 + ε) by ring,
    Real.log_mul he h1e]

/-- Consequently the singular witness cannot converge to any finite base
value, let alone possess the displayed finite linear/quadratic expansion. -/
theorem singular_logdet_has_no_finite_limit (L : ℝ) :
    ¬ Tendsto (fun ε : ℝ => Real.log
      ((shiftedHermitian2 0 1 1 1 0 ε).det.re)) (𝓝[>] 0) (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atBot singular_logdet_diverges L

/- Axiom audit: every proved declaration in this section. -/
#print axioms RelationalAtlas.B24.hasDerivAt_detCurve
#print axioms RelationalAtlas.B24.hasDerivAt_logDetCurve
#print axioms RelationalAtlas.B24.hasDerivAt_derivNumerator
#print axioms RelationalAtlas.B24.eventually_deriv_logDetCurve
#print axioms RelationalAtlas.B24.trace_RERE_two
#print axioms RelationalAtlas.B24.trace_RE_two
#print axioms RelationalAtlas.B24.det_shiftedHermitian2
#print axioms RelationalAtlas.B24.two_c2_forms_hermitian
#print axioms RelationalAtlas.B24.nonHermitian_perturbation_breaks_two_forms
#print axioms RelationalAtlas.B24.nonHermitian_witness_actual_c2
#print axioms RelationalAtlas.B24.iteratedDeriv_two_logDetCurve
#print axioms RelationalAtlas.B24.log_det_shiftedHermitian2
#print axioms RelationalAtlas.B24.logdet_expansion_coefficients
#print axioms RelationalAtlas.B24.logdet_c2_eq_trace_RERE
#print axioms RelationalAtlas.B24.logdet_c1_eq_trace_RE
#print axioms RelationalAtlas.B24.singular_logdet_diverges
#print axioms RelationalAtlas.B24.singular_logdet_has_no_finite_limit

end RelationalAtlas.B24


end

/-! ## B195 — the Bass determinant identity and its exponent

Integrated from `.ultramath/smwu0t12t/m13/B195.lean`.
-/
section


/-!
# B195 — Bass pencil, its two endpoints, and sign-flipped zeta

Source: `atlas/cards/html/B195.html` in the ledger's Zenodo archive.  The
retrieved file has SHA-256
`5778da2b1f2ea471518243835e2af5275a20e99d79bfadd7b754ff5de7c632bd`,
matching `atlas/coverage/coverage.json`.

The main theorem is a finite-matrix Bass/Sylvester calculation.  No unitarity
(or positivity, graph simplicity, or connectedness) is assumed.  The field is
arbitrary, so real and complex transports are both included.  For a negative
exponent the determinant identity is an identity of rational functions; we
accordingly assume `1-u^2 ≠ 0` where a zpow occurs.
-/
open Matrix
variable {𝕜 : Type*} [Field 𝕜]

namespace AtlasB195
variable {v a : Type*} [Fintype v] [DecidableEq v] [Fintype a] [DecidableEq a]

lemma left_normal (q : 𝕜) (hq : q ≠ 0) (X : Matrix a v 𝕜) (Y : Matrix v a 𝕜) :
    q • (1 : Matrix a a 𝕜) - X * Y = q • (1 - (q⁻¹ • X) * Y) := by
  rw [smul_sub, Matrix.smul_mul, smul_smul]
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [hqq]
  module

lemma right_normal (q : 𝕜) (hq : q ≠ 0) (X : Matrix a v 𝕜) (Y : Matrix v a 𝕜) :
    q • (1 : Matrix v v 𝕜) - Y * X = q • (1 - Y * (q⁻¹ • X)) := by
  rw [smul_sub, Matrix.mul_smul, smul_smul]
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [hqq]
  module

lemma scaled_sylvester (q : 𝕜) (hq : q ≠ 0) (X : Matrix a v 𝕜) (Y : Matrix v a 𝕜) :
    q ^ Fintype.card v * (q • (1 : Matrix a a 𝕜) - X * Y).det =
      q ^ Fintype.card a * (q • (1 : Matrix v v 𝕜) - Y * X).det := by
  rw [left_normal q hq X Y, right_normal q hq X Y, Matrix.det_smul, Matrix.det_smul,
    Matrix.det_one_sub_mul_comm]
  ring
end AtlasB195

namespace AtlasB195
variable {v a : Type*} [Fintype v] [DecidableEq v] [Fintype a] [DecidableEq a]

/-- `pencil u A Deg` is exactly `I-uA+u²(Deg-I)` from B195. -/
def pencil (u : 𝕜) (A Deg : Matrix v v 𝕜) : Matrix v v 𝕜 :=
  1 - u • A + u^2 • (Deg - 1)

lemma vertex_factor (u : 𝕜) (S T : Matrix v a 𝕜) :
    (pencil u (S * Tᵀ) (S * Sᵀ))ᵀ =
      (1-u^2) • (1 : Matrix v v 𝕜) - (T-u • S) * (u • Sᵀ) := by
  simp only [pencil, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
  module

/-- The arc-space factorisation underlying Bass's determinant formula. -/
lemma bass_factor_named (u : 𝕜) (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜)
    (hJ : J*J=1) (hTJ : T*J=S) :
    (1-u • (Sᵀ*T-J)) * (1-u • J) =
      (1-u^2) • (1 : Matrix a a 𝕜) - (u • Sᵀ)*(T-u • S) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc, hTJ, hJ]
  module

/-- Cross-multiplied form, useful because `m-card v` may be negative. -/
lemma bass_determinant_cross (u q : 𝕜) (hq : q = 1-u^2) (hq0 : q ≠ 0)
    (m : ℕ) (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜)
    (hJ : J*J=1) (hTJ : T*J=S) (hca : Fintype.card a = 2*m)
    (hJdet : (1-u • J).det = q^m) :
    (1-u • (Sᵀ*T-J)).det * q^(Fintype.card v) =
      q^m * (pencil u (S*Tᵀ) (S*Sᵀ)).det := by
  subst q
  have hfac := congrArg Matrix.det (bass_factor_named u S T J hJ hTJ)
  rw [Matrix.det_mul, hJdet] at hfac
  have hsyl := scaled_sylvester (1-u^2) hq0 (u • Sᵀ) (T-u • S)
  rw [← vertex_factor u S T, Matrix.det_transpose, hca] at hsyl
  rw [← hfac] at hsyl
  have htwo : (2*m) = m+m := by omega
  rw [htwo, pow_add] at hsyl
  have hpm : (1-u^2)^m ≠ 0 := pow_ne_zero m hq0
  apply mul_left_cancel₀ hpm
  -- put the common arc-pair factor on the left
  calc
    (1-u^2)^m * ((1-u • (Sᵀ*T-J)).det * (1-u^2)^Fintype.card v) =
        (1-u^2)^Fintype.card v *
          ((1-u • (Sᵀ*T-J)).det * (1-u^2)^m) := by ring
    _ = (1-u^2)^m * ((1-u^2)^m *
          (pencil u (S*Tᵀ) (S*Sᵀ)).det) := by simpa [mul_assoc] using hsyl

/-- B195's determinant formula, with `m` equal to half the arc basis size. -/
lemma bass_determinant (u q : 𝕜) (hq : q = 1-u^2) (hq0 : q ≠ 0)
    (m : ℕ) (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜)
    (hJ : J*J=1) (hTJ : T*J=S) (hca : Fintype.card a = 2*m)
    (hJdet : (1-u • J).det = q^m) :
    (1-u • (Sᵀ*T-J)).det =
      q^((m : ℤ) - (Fintype.card v : ℤ)) * (pencil u (S*Tᵀ) (S*Sᵀ)).det := by
  have hcross := bass_determinant_cross u q hq hq0 m S T J hJ hTJ hca hJdet
  rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast, div_mul_eq_mul_div,
    eq_div_iff (pow_ne_zero (Fintype.card v) hq0)]
  exact hcross

/-- The exponent in the card's literal `(m-n)d` form.  Basis dimensions
already include the fibre dimension; inverse reversal supplies the displayed
arc determinant. -/
lemma bass_determinant_fiber_exponent (u q : 𝕜) (hq : q = 1-u^2) (hq0 : q ≠ 0)
    (m n d : ℕ) (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜)
    (hJ : J*J=1) (hTJ : T*J=S) (hca : Fintype.card a = 2*(m*d))
    (hcv : Fintype.card v = n*d) (hJdet : (1-u • J).det = q^(m*d)) :
    (1-u • (Sᵀ*T-J)).det =
      q^(((m : ℤ)-(n : ℤ))*(d : ℤ)) * (pencil u (S*Tᵀ) (S*Sᵀ)).det := by
  have h := bass_determinant u q hq hq0 (m*d) S T J hJ hTJ hca hJdet
  simpa only [hcv, Nat.cast_mul, sub_mul] using h

end AtlasB195
namespace AtlasB195

/-- Inverse-reversal transport on the two orientations of one scalar edge. -/
def reversalBlock (x y : 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜 := !![0,y;x,0]

/-- Block-diagonal inverse-reversal transport on all scalar edges. -/
def arcReversal {m : ℕ} (x y : Fin m → 𝕜) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) 𝕜 :=
  blockDiagonal fun k => reversalBlock (x k) (y k)

lemma reversalBlock_sq {x y : 𝕜} (hxy : x*y=1) :
    reversalBlock x y * reversalBlock x y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reversalBlock, Matrix.mul_apply, Fin.sum_univ_two, hxy, mul_comm]

lemma arcReversal_sq {m : ℕ} (x y : Fin m → 𝕜) (hxy : ∀k, x k*y k=1) :
    arcReversal x y * arcReversal x y = 1 := by
  unfold arcReversal
  rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_mul]
  congr 1
  funext k
  exact reversalBlock_sq (hxy k)


lemma det_one_sub_reversalBlock (u x y : 𝕜) (hxy : x*y=1) :
    (1-u • reversalBlock x y).det = 1-u^2 := by
  rw [Matrix.det_fin_two]
  have hyx : y*x=1 := by rw [mul_comm]; exact hxy
  norm_num [reversalBlock]
  calc
    _ = u^2 * (y*x) := by ring
    _ = u^2 := by rw [hyx, mul_one]

lemma det_one_sub_arcReversal {m : ℕ} (u : 𝕜) (x y : Fin m → 𝕜)
    (hxy : ∀k, x k*y k=1) :
    (1-u • arcReversal x y).det = (1-u^2)^m := by
  have hmatrix : (1 : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) 𝕜) - u • arcReversal x y =
      blockDiagonal (fun k => 1-u • reversalBlock (x k) (y k)) := by
    unfold arcReversal
    rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_sub]
    rfl
  rw [hmatrix, Matrix.det_blockDiagonal]
  have hblock (k : Fin m) : (1-u • reversalBlock (x k) (y k)).det = 1-u^2 :=
    det_one_sub_reversalBlock u (x k) (y k) (hxy k)
  simp_rw [hblock]
  simp

/-- The determinant convention for zeta used in the card's first display. -/
noncomputable def iharaZeta {a : Type*} [Fintype a] [DecidableEq a] (u : 𝕜) (B : Matrix a a 𝕜) : 𝕜 :=
  (1-u • B).det⁻¹

/-- Replacing `(u,B)` by `(-u,B)` is the same as replacing `B` by `-B`. -/
lemma zeta_sign_flip {a : Type*} [Fintype a] [DecidableEq a]
    (u : 𝕜) (B : Matrix a a 𝕜) :
    iharaZeta (-u) B = iharaZeta u (-B) := by
  unfold iharaZeta
  congr 2
  module
end AtlasB195

namespace AtlasB195
variable {v : Type*} [Fintype v] [DecidableEq v]

/-- The Bass formula for `m` explicitly paired scalar transport edges. -/
lemma bass_determinant_paired {m : ℕ} (u q : 𝕜) (hq : q = 1-u^2) (hq0 : q ≠ 0)
    (S T : Matrix v (Fin 2 × Fin m) 𝕜) (x y : Fin m → 𝕜)
    (hxy : ∀k, x k*y k=1) (hTJ : T*arcReversal x y=S) :
    (1-u • (Sᵀ*T-arcReversal x y)).det =
      q^((m : ℤ) - (Fintype.card v : ℤ)) * (pencil u (S*Tᵀ) (S*Sᵀ)).det := by
  apply bass_determinant u q hq hq0 m S T (arcReversal x y)
  · exact arcReversal_sq x y hxy
  · exact hTJ
  · simp [Fintype.card_prod, two_mul]
  · rw [hq]
    exact det_one_sub_arcReversal u x y hxy

/-- At `u=1`, the pencil is `Deg-A` (the card's `L⁻`). -/
lemma pencil_at_one (A Deg : Matrix v v 𝕜) : pencil 1 A Deg = Deg-A := by
  unfold pencil
  norm_num

/-- At `u=-1`, the pencil is `Deg+A` (the card's `L⁺`). -/
lemma pencil_at_neg_one (A Deg : Matrix v v 𝕜) : pencil (-1) A Deg = Deg+A := by
  unfold pencil
  norm_num
  module

lemma negative_transport_matrix {a : Type*} [DecidableEq a] [Fintype a]
    (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜) :
    Sᵀ*(-T)-(-J) = -(Sᵀ*T-J) := by
  simp only [Matrix.mul_neg, Matrix.transpose_neg, neg_neg]
  abel

/-- Negating transports negates both `T` and `J`, hence proves `ζρ(-u)=ζ₋ρ(u)`. -/
lemma zeta_negative_transport {a : Type*} [DecidableEq a] [Fintype a]
    (u : 𝕜) (S T : Matrix v a 𝕜) (J : Matrix a a 𝕜) :
    iharaZeta (-u) (Sᵀ*T-J) = iharaZeta u (Sᵀ*(-T)-(-J)) := by
  rw [negative_transport_matrix, ← zeta_sign_flip]

lemma arcReversal_neg {m : ℕ} (x y : Fin m → 𝕜) :
    arcReversal (-x) (-y) = -arcReversal x y := by
  unfold arcReversal reversalBlock
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hkl : k=l
  · subst l
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.blockDiagonal_apply_ne _ _ _ hkl]

/-- The two-vertex, one-edge instance (`n=2`, `m=1`) of the general formula. -/
lemma singleEdge_bass_abstract (u q : 𝕜) (hq : q=1-u^2) (hq0 : q≠0)
    (x y : 𝕜) (hxy : x*y=1) :
    (1-u • ((1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ*reversalBlock x y-reversalBlock x y)).det =
      q^((1 : ℤ)-(2 : ℤ)) *
        (pencil u ((1 : Matrix (Fin 2) (Fin 2) 𝕜)*(reversalBlock x y)ᵀ)
          ((1 : Matrix (Fin 2) (Fin 2) 𝕜)*(1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ)).det := by
  apply bass_determinant u q hq hq0 1 (1 : Matrix (Fin 2) (Fin 2) 𝕜)
    (reversalBlock x y) (reversalBlock x y)
  · exact reversalBlock_sq hxy
  · exact reversalBlock_sq hxy
  · norm_num
  · rw [hq]
    simpa only [pow_one] using det_one_sub_reversalBlock u x y hxy

lemma singleEdge_arc_det (u x y : 𝕜) :
    (1-u • ((1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ*reversalBlock x y-reversalBlock x y)).det = 1 := by
  simp

lemma singleEdge_pencil_det (u x y : 𝕜) (hxy : x*y=1) :
    (pencil u ((1 : Matrix (Fin 2) (Fin 2) 𝕜)*(reversalBlock x y)ᵀ)
      ((1 : Matrix (Fin 2) (Fin 2) 𝕜)*(1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ)).det = 1-u^2 := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) 𝕜)*(reversalBlock x y)ᵀ =
      !![0,x;y,0] by ext i j; fin_cases i <;> fin_cases j <;> simp [reversalBlock]]
  rw [show (1 : Matrix (Fin 2) (Fin 2) 𝕜)*(1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ = 1 by simp]
  rw [show pencil u (!![0,x;y,0] : Matrix (Fin 2) (Fin 2) 𝕜) 1 =
      !![1,-u*x;-u*y,1] by
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [pencil]]
  rw [Matrix.det_fin_two_of]
  have hyx : y*x=1 := by rw [mul_comm]; exact hxy
  calc
    1*1 - (-u*x)*(-u*y) = 1-u^2*(x*y) := by ring
    _ = 1-u^2 := by rw [hxy, mul_one]

lemma singleEdge_bass_value (u : 𝕜) (hq0 : 1-u^2≠0) (x y : 𝕜) (hxy : x*y=1) :
    (1-u • ((1 : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ*reversalBlock x y-reversalBlock x y)).det = 1 := by
  have h := singleEdge_bass_abstract u (1-u^2) rfl hq0 x y hxy
  rw [singleEdge_pencil_det u x y hxy] at h
  have hpow : (1-u^2)^((1 : ℤ)-(2 : ℤ)) * (1-u^2) = 1 := by
    rw [show (1 : ℤ)-(2 : ℤ)=(-1 : ℤ) by norm_num, _root_.zpow_neg_one]
    field_simp
  rw [hpow] at h
  exact h

/-- Reversing the exponent fails: at `u=1/2` it would give `9/16`, not `1`. -/
lemma singleEdge_wrong_exponent_refuted :
    ¬ ((1-(1/2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ*reversalBlock 2 (1/2)-
        reversalBlock 2 (1/2))).det =
      (1-(1/2 : ℝ)^2)^((2 : ℤ)-(1 : ℤ)) *
        (pencil (1/2) ((1 : Matrix (Fin 2) (Fin 2) ℝ)*(reversalBlock 2 (1/2))ᵀ)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ)*(1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)).det) := by
  rw [singleEdge_arc_det, singleEdge_pencil_det] <;> norm_num
end AtlasB195

/- Axiom audit for every proved declaration. -/
#print axioms AtlasB195.left_normal
#print axioms AtlasB195.right_normal
#print axioms AtlasB195.scaled_sylvester
#print axioms AtlasB195.vertex_factor
#print axioms AtlasB195.bass_factor_named
#print axioms AtlasB195.bass_determinant_cross
#print axioms AtlasB195.bass_determinant
#print axioms AtlasB195.bass_determinant_fiber_exponent
#print axioms AtlasB195.reversalBlock_sq
#print axioms AtlasB195.arcReversal_sq
#print axioms AtlasB195.det_one_sub_reversalBlock
#print axioms AtlasB195.det_one_sub_arcReversal
#print axioms AtlasB195.zeta_sign_flip
#print axioms AtlasB195.bass_determinant_paired
#print axioms AtlasB195.pencil_at_one
#print axioms AtlasB195.pencil_at_neg_one
#print axioms AtlasB195.negative_transport_matrix
#print axioms AtlasB195.zeta_negative_transport
#print axioms AtlasB195.arcReversal_neg
#print axioms AtlasB195.singleEdge_bass_abstract
#print axioms AtlasB195.singleEdge_arc_det
#print axioms AtlasB195.singleEdge_pencil_det
#print axioms AtlasB195.singleEdge_bass_value
#print axioms AtlasB195.singleEdge_wrong_exponent_refuted


end

/-! ## B198 — the book energies, and a sign in the auxiliary display

Integrated from `.ultramath/smwu0t12t/m11/B198.lean`.
-/
section


open scoped BigOperators Matrix

namespace AtlasB198

/-- The two scalar energy books displayed by B198. -/
def oppositeEnergy (p a : ℝ) : ℝ := 4 * p - a ^ 2

def sameEnergy (_p a : ℝ) : ℝ := a ^ 2

/-- The signed twist count and its complementary count. -/
def twistPlus (p a : ℝ) : ℝ := p + 1 + a

def twistMinus (p a : ℝ) : ℝ := p + 1 - a

/-- B198's rapidity, with the exact ratio displayed on the card. -/
noncomputable def rapidity (p a : ℝ) : ℝ := Real.log (twistPlus p a / twistMinus p a)

lemma twistPlus_add_twistMinus (p a : ℝ) :
    twistPlus p a + twistMinus p a = 2 * (p + 1) := by
  simp only [twistPlus, twistMinus]
  ring

lemma twistPlus_sub_twistMinus (p a : ℝ) :
    twistPlus p a - twistMinus p a = 2 * a := by
  simp only [twistPlus, twistMinus]
  ring

lemma oppositeEnergy_add_sameEnergy (p a : ℝ) :
    oppositeEnergy p a + sameEnergy p a = 4 * p := by
  simp only [oppositeEnergy, sameEnergy]
  ring

lemma oppositeEnergy_eq_sameEnergy_iff (p a : ℝ) :
    oppositeEnergy p a = sameEnergy p a ↔ a ^ 2 = 2 * p := by
  simp only [oppositeEnergy, sameEnergy]
  constructor <;> intro h <;> nlinarith

/-- AM-GM in the square-root form needed to apply Hasse's inequality. -/
lemma two_sqrt_le_add_one {p : ℝ} (hp : 0 ≤ p) :
    2 * Real.sqrt p ≤ p + 1 := by
  have hs : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp
  nlinarith [sq_nonneg (Real.sqrt p - 1)]

/-- Hasse's strict inequality puts the normalized coefficient in `(-1,1)`. -/
lemma gamma_mem_Ioo_of_hasse {p a : ℝ} (hp : 0 < p)
    (ha : |a| < 2 * Real.sqrt p) : a / (p + 1) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h : |a| < p + 1 := lt_of_lt_of_le ha (two_sqrt_le_add_one hp.le)
  have hp1 : 0 < p + 1 := by linarith
  have h' : |a / (p + 1)| < 1 := by
    rw [abs_div, abs_of_pos hp1]
    exact (div_lt_one hp1).2 h
  exact abs_lt.mp h'

/-- The exact logarithmic relation behind the `tanh` display. -/
lemma rapidity_eq_two_artanh {p a : ℝ} (hp : 0 < p)
    (ha : a / (p + 1) ∈ Set.Ioo (-1 : ℝ) 1) :
    rapidity p a = 2 * Real.artanh (a / (p + 1)) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  have hm : twistMinus p a ≠ 0 := by
    have hlt := ha.2
    have hpos : 0 < p + 1 := by linarith
    have : a < p + 1 := (div_lt_one hpos).mp (lt_of_lt_of_le hlt (by simp))
    simp only [twistMinus]
    linarith
  have hratio : (1 + a / (p + 1)) / (1 - a / (p + 1)) =
      twistPlus p a / twistMinus p a := by
    simp only [twistPlus, twistMinus]
    field_simp
  rw [Real.artanh_eq_half_log (Set.mem_Icc.mpr ⟨ha.1.le, ha.2.le⟩), hratio]
  simp only [rapidity]
  ring

/-- B198's signed coefficient is exactly `tanh (τ/2)`. -/
theorem gamma_eq_tanh_half_rapidity {p a : ℝ} (hp : 0 < p)
    (ha : a / (p + 1) ∈ Set.Ioo (-1 : ℝ) 1) :
    a / (p + 1) = Real.tanh (rapidity p a / 2) := by
  rw [rapidity_eq_two_artanh hp ha]
  convert (Real.tanh_artanh ha).symm using 1
  ring

/-- The same identity directly under the card's strict Hasse bound. -/
theorem gamma_eq_tanh_half_rapidity_of_hasse {p a : ℝ} (hp : 0 < p)
    (ha : |a| < 2 * Real.sqrt p) :
    a / (p + 1) = Real.tanh (rapidity p a / 2) :=
  gamma_eq_tanh_half_rapidity hp (gamma_mem_Ioo_of_hasse hp ha)

/-- The Frobenius parametrization gives the first energy book. -/
lemma oppositeEnergy_eq_angle {p a θ : ℝ} (hp : 0 ≤ p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) :
    oppositeEnergy p a = 2 * p * (1 - Real.cos (2 * θ)) := by
  rw [oppositeEnergy, ha, Real.cos_two_mul, mul_pow, mul_pow, Real.sq_sqrt hp]
  ring

/-- The Frobenius parametrization gives the second energy book. -/
lemma sameEnergy_eq_angle {p a θ : ℝ} (hp : 0 ≤ p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) :
    sameEnergy p a = 2 * p * (1 + Real.cos (2 * θ)) := by
  rw [sameEnergy, ha, Real.cos_two_mul, mul_pow, mul_pow, Real.sq_sqrt hp]
  ring

lemma sameEnergy_le_budget {p a : ℝ} (hp : 0 ≤ p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) : sameEnergy p a ≤ 4 * p := by
  rw [sameEnergy, ha, mul_pow, mul_pow, Real.sq_sqrt hp]
  nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ), sq_nonneg p]

/-- Strict Hasse comes from excluding the endpoints of the angular interval. -/
lemma sameEnergy_lt_budget_of_angle {p a θ : ℝ} (hp : 0 < p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    sameEnergy p a < 4 * p := by
  rw [sameEnergy, ha, mul_pow, mul_pow, Real.sq_sqrt hp.le]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hs]

/-- Directly from Hasse: the squared record cannot reach, let alone exceed, `4p`. -/
theorem sameEnergy_lt_budget_of_hasse {p a : ℝ} (hp : 0 < p)
    (ha : |a| < 2 * Real.sqrt p) : sameEnergy p a < 4 * p := by
  have hs : |a| ^ 2 < (2 * Real.sqrt p) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg a) (by positivity)).2 ha
  rw [sq_abs, mul_pow, Real.sq_sqrt hp.le] at hs
  norm_num at hs
  exact hs

/-- Consequently the opposite book is strictly positive under strict Hasse. -/
theorem oppositeEnergy_pos_of_hasse {p a : ℝ} (hp : 0 < p)
    (ha : |a| < 2 * Real.sqrt p) : 0 < oppositeEnergy p a := by
  have h := sameEnergy_lt_budget_of_hasse hp ha
  simp only [sameEnergy] at h
  simp only [oppositeEnergy]
  linarith

/-- At an odd prime the two integral energy books cannot balance. -/
theorem no_integral_balance_of_odd {p : ℕ} {a : ℤ} (hp : Odd p) :
    a ^ 2 ≠ 2 * (p : ℤ) := by
  intro h
  have hpz : Odd (p : ℤ) := (Int.odd_coe_nat p).2 hp
  rcases Int.even_or_odd a with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    have hp_even : Even (p : ℤ) := by
      refine ⟨k ^ 2, ?_⟩
      rw [hk] at h
      nlinarith
    exact (Int.not_even_iff_odd.2 hpz) hp_even
  · have hsq_odd : Odd (a ^ 2) := (Int.odd_pow' (by norm_num : (2 : ℕ) ≠ 0)).2 hodd
    have hsq_even : Even (a ^ 2) := by
      rw [h]
      exact even_two_mul _
    exact (Int.not_even_iff_odd.2 hsq_odd) hsq_even

/-- In particular, B198's non-balancing assertion holds at every odd prime. -/
theorem no_integral_balance_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) : a ^ 2 ≠ 2 * (p : ℤ) :=
  no_integral_balance_of_odd (hp.odd_of_ne_two hp2)

/-- Oddness is necessary: the exceptional prime `p=2` balances with `a=±2`. -/
theorem prime_two_integral_balance :
    (2 : ℤ) ^ 2 = 2 * ((2 : ℕ) : ℤ) ∧
    (-2 : ℤ) ^ 2 = 2 * ((2 : ℕ) : ℤ) := by norm_num


abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ

def sigmaX : C2 := !![0, 1; 1, 0]
def sigmaY : C2 := !![0, -Complex.I; Complex.I, 0]

noncomputable def frobeniusU (θ : ℝ) : C2 :=
  !![Complex.exp ((θ : ℂ) * Complex.I), 0;
    0, Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)]

noncomputable def edgeD (p : ℝ) : C2 := (Real.sqrt (p / 2) : ℂ) • sigmaX

noncomputable def transport (p θ : ℝ) : C2 :=
  frobeniusU θ * edgeD p * (frobeniusU θ)ᴴ

lemma transport_eq_standard_pauli (p θ : ℝ) : transport p θ =
    (Real.sqrt (p / 2) : ℂ) •
      ((Real.cos (2 * θ) : ℂ) • sigmaX - (Real.sin (2 * θ) : ℂ) • sigmaY) := by
  have hexp_neg (x : ℝ) : Complex.exp (-((x : ℂ) * Complex.I)) =
      (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
    convert Complex.exp_ofReal_mul_I (-x) using 1 <;> simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, frobeniusU, edgeD, sigmaX, sigmaY, Matrix.mul_apply,
      Fin.sum_univ_two, hexp_neg, Complex.exp_ofReal_mul_I, Complex.ext_iff,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Real.cos_two_mul, Real.sin_two_mul, pow_two, Complex.mul_re, Complex.mul_im]
  all_goals constructor
  · linear_combination -(Real.sqrt p / Real.sqrt 2) * Real.sin_sq_add_cos_sq θ
  · ring
  · linear_combination -(Real.sqrt p / Real.sqrt 2) * Real.sin_sq_add_cos_sq θ
  · ring

lemma complex_cos_two_re (θ : ℝ) :
    (Complex.cos (2 * (θ : ℂ))).re = Real.cos (2 * θ) := by
  rw [show 2 * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) by norm_num]
  exact Complex.cos_ofReal_re _

lemma complex_cos_two_im (θ : ℝ) :
    (Complex.cos (2 * (θ : ℂ))).im = 0 := by
  rw [show 2 * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) by norm_num]
  exact Complex.cos_ofReal_im _

lemma complex_sin_two_re (θ : ℝ) :
    (Complex.sin (2 * (θ : ℂ))).re = Real.sin (2 * θ) := by
  rw [show 2 * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) by norm_num]
  exact Complex.sin_ofReal_re _

lemma complex_sin_two_im (θ : ℝ) :
    (Complex.sin (2 * (θ : ℂ))).im = 0 := by
  rw [show 2 * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) by norm_num]
  exact Complex.sin_ofReal_im _

def frobSq (M : C2) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

lemma frobSq_minus (p θ : ℝ) (hp : 0 ≤ p) :
    frobSq (edgeD p - transport p θ) = 2 * p * (1 - Real.cos (2 * θ)) := by
  rw [transport_eq_standard_pauli]
  have hs : (Real.sqrt p / Real.sqrt 2) ^ 2 = p / 2 := by
    rw [← Real.sqrt_div hp]
    exact Real.sq_sqrt (div_nonneg hp (by norm_num))
  simp [frobSq, Fin.sum_univ_two, edgeD, sigmaX, sigmaY, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, complex_cos_two_re, complex_cos_two_im,
    complex_sin_two_re, complex_sin_two_im]
  linear_combination 4 * (1 - Real.cos (2 * θ)) * hs +
    2 * (Real.sqrt p / Real.sqrt 2) ^ 2 * Real.sin_sq_add_cos_sq (2 * θ)

lemma frobSq_plus (p θ : ℝ) (hp : 0 ≤ p) :
    frobSq (edgeD p + transport p θ) = 2 * p * (1 + Real.cos (2 * θ)) := by
  rw [transport_eq_standard_pauli]
  have hs : (Real.sqrt p / Real.sqrt 2) ^ 2 = p / 2 := by
    rw [← Real.sqrt_div hp]
    exact Real.sq_sqrt (div_nonneg hp (by norm_num))
  simp [frobSq, Fin.sum_univ_two, edgeD, sigmaX, sigmaY, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, complex_cos_two_re, complex_cos_two_im,
    complex_sin_two_re, complex_sin_two_im]
  linear_combination 4 * (1 + Real.cos (2 * θ)) * hs +
    2 * (Real.sqrt p / Real.sqrt 2) ^ 2 * Real.sin_sq_add_cos_sq (2 * θ)

/-- The displayed auxiliary conjugation has the wrong sign for standard `σ_y`. -/
theorem printed_auxiliary_conjugation_false :
    transport 2 (Real.pi / 4) ≠
      (Real.sqrt (2 / 2) : ℂ) •
        ((Real.cos (2 * (Real.pi / 4)) : ℂ) • sigmaX +
          (Real.sin (2 * (Real.pi / 4)) : ℂ) • sigmaY) := by
  intro h
  have h01 := congrArg (fun M : C2 => M 0 1) h
  rw [transport_eq_standard_pauli] at h01
  have hpi : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  norm_num [hpi, sigmaX, sigmaY, Complex.ext_iff] at h01

/-- Negating a conjugating matrix has no effect, with no unitarity hypothesis. -/
theorem ad_neg_eq_ad (U X : C2) : (-U) * X * (-U)ᴴ = U * X * Uᴴ := by
  simp

/-- The energy books depend on `a_p²`, hence erase the sign exactly. -/
theorem energies_neg (p a : ℝ) :
    oppositeEnergy p (-a) = oppositeEnergy p a ∧
      sameEnergy p (-a) = sameEnergy p a := by
  simp [oppositeEnergy, sameEnergy]

/-- The signed twist counts and coefficient retain the sign. -/
theorem twist_neg_swap (p a : ℝ) :
    twistPlus p (-a) = twistMinus p a ∧ twistMinus p (-a) = twistPlus p a := by
  simp [twistPlus, twistMinus, sub_eq_add_neg]

theorem gamma_neg (p a : ℝ) : (-a) / (p + 1) = -(a / (p + 1)) := by
  ring

/-- Reversing the signed count also reverses the rapidity. -/
theorem rapidity_neg (p a : ℝ) : rapidity p (-a) = -rapidity p a := by
  simp [rapidity, twistPlus, twistMinus, ← Real.log_inv, sub_eq_add_neg]

/-- `frobSq` is literally the entrywise sum of squared complex norms. -/
lemma frobSq_eq_norm_sum (M : C2) :
    frobSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp [frobSq, Complex.normSq_eq_norm_sq]


/-- B198's first displayed energy is the actual Frobenius distance of the edge. -/
theorem oppositeEnergy_eq_frobSq {p a θ : ℝ} (hp : 0 ≤ p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) :
    oppositeEnergy p a = frobSq (edgeD p - transport p θ) :=
  (oppositeEnergy_eq_angle hp ha).trans (frobSq_minus p θ hp).symm

/-- B198's second displayed energy is the actual Frobenius distance of the edge. -/
theorem sameEnergy_eq_frobSq {p a θ : ℝ} (hp : 0 ≤ p)
    (ha : a = 2 * Real.sqrt p * Real.cos θ) :
    sameEnergy p a = frobSq (edgeD p + transport p θ) :=
  (sameEnergy_eq_angle hp ha).trans (frobSq_plus p θ hp).symm

/-- The literal energy books cannot balance at an odd prime with integral `a_p`. -/
theorem no_energy_balance_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) : oppositeEnergy (p : ℝ) (a : ℝ) ≠ sameEnergy (p : ℝ) (a : ℝ) := by
  intro h
  have hsq : (a : ℝ) ^ 2 = 2 * (p : ℝ) :=
    (oppositeEnergy_eq_sameEnergy_iff (p : ℝ) (a : ℝ)).mp h
  apply no_integral_balance_of_odd_prime hp hp2 a
  exact_mod_cast hsq

/-- The excluded prime really does provide an energy-balance witness. -/
theorem prime_two_energy_balance (a : ℤ) (ha : a = 2 ∨ a = -2) :
    oppositeEnergy (2 : ℝ) (a : ℝ) = sameEnergy (2 : ℝ) (a : ℝ) := by
  rcases ha with rfl | rfl <;> norm_num [oppositeEnergy, sameEnergy]


end AtlasB198

#print axioms AtlasB198.twistPlus_add_twistMinus
#print axioms AtlasB198.twistPlus_sub_twistMinus
#print axioms AtlasB198.oppositeEnergy_add_sameEnergy
#print axioms AtlasB198.oppositeEnergy_eq_sameEnergy_iff
#print axioms AtlasB198.two_sqrt_le_add_one
#print axioms AtlasB198.gamma_mem_Ioo_of_hasse
#print axioms AtlasB198.rapidity_eq_two_artanh
#print axioms AtlasB198.gamma_eq_tanh_half_rapidity
#print axioms AtlasB198.gamma_eq_tanh_half_rapidity_of_hasse
#print axioms AtlasB198.oppositeEnergy_eq_angle
#print axioms AtlasB198.sameEnergy_eq_angle
#print axioms AtlasB198.sameEnergy_le_budget
#print axioms AtlasB198.sameEnergy_lt_budget_of_angle
#print axioms AtlasB198.sameEnergy_lt_budget_of_hasse
#print axioms AtlasB198.oppositeEnergy_pos_of_hasse
#print axioms AtlasB198.no_integral_balance_of_odd
#print axioms AtlasB198.no_integral_balance_of_odd_prime
#print axioms AtlasB198.prime_two_integral_balance
#print axioms AtlasB198.transport_eq_standard_pauli
#print axioms AtlasB198.complex_cos_two_re
#print axioms AtlasB198.complex_cos_two_im
#print axioms AtlasB198.complex_sin_two_re
#print axioms AtlasB198.complex_sin_two_im
#print axioms AtlasB198.frobSq_minus
#print axioms AtlasB198.frobSq_plus
#print axioms AtlasB198.printed_auxiliary_conjugation_false
#print axioms AtlasB198.ad_neg_eq_ad
#print axioms AtlasB198.energies_neg
#print axioms AtlasB198.twist_neg_swap
#print axioms AtlasB198.gamma_neg
#print axioms AtlasB198.rapidity_neg
#print axioms AtlasB198.frobSq_eq_norm_sum
#print axioms AtlasB198.oppositeEnergy_eq_frobSq
#print axioms AtlasB198.sameEnergy_eq_frobSq
#print axioms AtlasB198.no_energy_balance_of_odd_prime
#print axioms AtlasB198.prime_two_energy_balance


end

/-! ## B194 — the commutator sum and the two bow-tie minima

Integrated from `.ultramath/smwu0t12t/m7/work/B194.lean`.
-/
section

/- B194: exact Pauli commutator identity and the two bow-tie minima.
This file is standalone; it imports only Mathlib. -/


open scoped ComplexConjugate

namespace B194

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Squared Frobenius norm, without taking a square root. -/
def frobeniusSq (M : Mat) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

def commutator (M N : Mat) : Mat := M * N - N * M

def sigmaX : Mat := !![0, 1; 1, 0]
def sigmaZ : Mat := !![1, 0; 0, -1]

/-- The qubit projector with real Bloch vector (nx, ny, nz). -/
noncomputable def blochProjector (nx ny nz : ℝ) : Mat :=
  (2 : ℂ)⁻¹ • !![1 + (nz : ℂ), (nx : ℂ) - Complex.I * ny;
    (nx : ℂ) + Complex.I * ny, 1 - (nz : ℂ)]

theorem frobeniusSq_nonneg (M : Mat) : 0 ≤ frobeniusSq M := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem commutator_sigmaX_frobeniusSq (nx ny nz : ℝ) :
    frobeniusSq (commutator (blochProjector nx ny nz) sigmaX) =
      2 * (ny ^ 2 + nz ^ 2) := by
  simp [frobeniusSq, commutator, blochProjector, sigmaX,
    Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem commutator_sigmaZ_frobeniusSq (nx ny nz : ℝ) :
    frobeniusSq (commutator (blochProjector nx ny nz) sigmaZ) =
      2 * (nx ^ 2 + ny ^ 2) := by
  simp [frobeniusSq, commutator, blochProjector, sigmaZ,
    Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem blochProjector_mul_self (nx ny nz : ℝ)
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    blochProjector nx ny nz * blochProjector nx ny nz = blochProjector nx ny nz := by
  have hc : (nx : ℂ) ^ 2 + (ny : ℂ) ^ 2 + (nz : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochProjector, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals linear_combination hc / 4

theorem commutator_sum_frobeniusSq (nx ny nz : ℝ)
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    frobeniusSq (commutator (blochProjector nx ny nz) sigmaX) +
      frobeniusSq (commutator (blochProjector nx ny nz) sigmaZ) =
        2 * (1 + ny ^ 2) := by
  rw [commutator_sigmaX_frobeniusSq, commutator_sigmaZ_frobeniusSq]
  nlinarith

theorem commutator_sum_lower (nx ny nz : ℝ)
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    2 ≤ frobeniusSq (commutator (blochProjector nx ny nz) sigmaX) +
      frobeniusSq (commutator (blochProjector nx ny nz) sigmaZ) := by
  rw [commutator_sum_frobeniusSq nx ny nz h]
  nlinarith [sq_nonneg ny]

theorem commutator_sum_eq_two_iff (nx ny nz : ℝ)
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    frobeniusSq (commutator (blochProjector nx ny nz) sigmaX) +
      frobeniusSq (commutator (blochProjector nx ny nz) sigmaZ) = 2 ↔ ny = 0 := by
  rw [commutator_sum_frobeniusSq nx ny nz h]
  constructor <;> intro hy
  · nlinarith [sq_nonneg ny]
  · rw [hy]
    ring

theorem commutator_sum_attained :
    frobeniusSq (commutator (blochProjector 0 0 1) sigmaX) +
      frobeniusSq (commutator (blochProjector 0 0 1) sigmaZ) = 2 := by
  apply (commutator_sum_eq_two_iff 0 0 1 (by norm_num)).2
  rfl

end B194

noncomputable section

namespace B194.RealGeometry

@[ext]
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace V3

def dot (u v : V3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def normSq (u : V3) : ℝ := u.x ^ 2 + u.y ^ 2 + u.z ^ 2
def Unit (u : V3) : Prop := normSq u = 1

def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def mid (u v : V3) : V3 := ⟨(u.x + v.x) / 2, (u.y + v.y) / 2, (u.z + v.z) / 2⟩
def halfDiff (u v : V3) : V3 := ⟨(u.x - v.x) / 2, (u.y - v.y) / 2, (u.z - v.z) / 2⟩

/-- Reflection across the x-axis: conjugation by sigma_x on Bloch vectors. -/
def reflectX (u : V3) : V3 := ⟨u.x, -u.y, -u.z⟩
/-- Reflection across the z-axis: conjugation by sigma_z on Bloch vectors. -/
def reflectZ (u : V3) : V3 := ⟨-u.x, -u.y, u.z⟩

lemma normSq_nonneg (u : V3) : 0 ≤ normSq u := by
  unfold normSq
  positivity

lemma dot_le_sqrt_normSq {a : V3} (ha : Unit a) (u : V3) :
    dot a u ≤ Real.sqrt (normSq u) := by
  have hsquare : dot a u ^ 2 ≤ normSq u := by
    change normSq a = 1 at ha
    calc
      dot a u ^ 2 ≤ normSq a * normSq u := by
        unfold dot normSq
        nlinarith [sq_nonneg (a.x * u.y - a.y * u.x),
          sq_nonneg (a.x * u.z - a.z * u.x),
          sq_nonneg (a.y * u.z - a.z * u.y)]
      _ = normSq u := by rw [ha]; ring
  calc
    dot a u ≤ |dot a u| := le_abs_self _
    _ = Real.sqrt (dot a u ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (normSq u) := Real.sqrt_le_sqrt hsquare

lemma dot_mid_halfDiff (v w : V3) :
    dot v w = normSq (mid v w) - normSq (halfDiff v w) := by
  simp [dot, normSq, mid, halfDiff]
  ring

lemma normSq_mid_add_halfDiff (v w : V3) :
    normSq (mid v w) + normSq (halfDiff v w) = (normSq v + normSq w) / 2 := by
  simp [normSq, mid, halfDiff]
  ring

lemma dot_eq_one_sub_two_halfDiff {v w : V3} (hv : Unit v) (hw : Unit w) :
    dot v w = 1 - 2 * normSq (halfDiff v w) := by
  have h := normSq_mid_add_halfDiff v w
  unfold Unit at hv hw
  rw [hv, hw] at h
  nlinarith [dot_mid_halfDiff v w]

lemma normSq_add_reflectX (v w : V3) :
    normSq (add w (reflectX v)) =
      4 * (normSq (halfDiff v w) + (mid v w).x ^ 2 - (halfDiff v w).x ^ 2) := by
  simp [normSq, add, reflectX, mid, halfDiff]
  ring

lemma normSq_add_reflectZ (v w : V3) :
    normSq (add w (reflectZ v)) =
      4 * (normSq (halfDiff v w) + (mid v w).z ^ 2 - (halfDiff v w).z ^ 2) := by
  simp [normSq, add, reflectZ, mid, halfDiff]
  ring

/-- Elementary square-root estimate used in the shared-edge minimum. -/
lemma sqrt_pair_le (t p q : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1 - t) :
    Real.sqrt (t + p) + Real.sqrt (t + q) ≤ t + Real.sqrt 2 := by
  have htp : 0 ≤ t + p := by positivity
  have htq : 0 ≤ t + q := by positivity
  have ha : 0 ≤ Real.sqrt (t + p) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt (t + q) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (t + p) ^ 2 = t + p := Real.sq_sqrt htp
  have hb2 : Real.sqrt (t + q) ^ 2 = t + q := Real.sq_sqrt htq
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hsq : (Real.sqrt (t + p) + Real.sqrt (t + q)) ^ 2 ≤ 2 * (1 + t) := by
    nlinarith [sq_nonneg (Real.sqrt (t + p) - Real.sqrt (t + q))]
  have htarget : 2 * (1 + t) ≤ (t + Real.sqrt 2) ^ 2 := by
    nlinarith [mul_nonneg ht (sub_nonneg.2 hr1), sq_nonneg t]
  exact (sq_le_sq₀ (by positivity) (by positivity)).1 (hsq.trans htarget)

/-- Five undirected edge contributions, each equal to ||P - U Q U*||_F^2. -/
def sharedEdgeEnergy (v w a b : V3) : ℝ :=
  (1 - dot v w) + (1 - dot w a) + (1 - dot a (reflectX v)) +
    (1 - dot w b) + (1 - dot b (reflectZ v))

/-- The exact domain of unit-Bloch-vector fields on the four vertices. -/
def sharedEdgeEnergies : Set ℝ := {e | ∃ v w a b : V3,
  Unit v ∧ Unit w ∧ Unit a ∧ Unit b ∧ e = sharedEdgeEnergy v w a b}

lemma sharedEdgeEnergy_lower (v w a b : V3)
    (hv : Unit v) (hw : Unit w) (ha : Unit a) (hb : Unit b) :
    4 - 2 * Real.sqrt 2 ≤ sharedEdgeEnergy v w a b := by
  let u := mid v w
  let d := halfDiff v w
  let t := normSq d
  let sx := add w (reflectX v)
  let sz := add w (reflectZ v)
  have ht : 0 ≤ t := normSq_nonneg d
  have hu : normSq u + t = 1 := by
    dsimp [u, t, d]
    rw [normSq_mid_add_halfDiff, hv, hw]
    norm_num
  have ht1 : t ≤ 1 := by nlinarith [normSq_nonneg u]
  have hpx : 0 ≤ u.x ^ 2 := sq_nonneg _
  have hpz : 0 ≤ u.z ^ 2 := sq_nonneg _
  have hpxz : u.x ^ 2 + u.z ^ 2 ≤ 1 - t := by
    unfold normSq at hu
    nlinarith [sq_nonneg u.y]
  have hpair : Real.sqrt (t + u.x ^ 2) + Real.sqrt (t + u.z ^ 2) ≤ t + Real.sqrt 2 :=
    sqrt_pair_le t (u.x ^ 2) (u.z ^ 2) ht ht1 hpx hpz hpxz
  have hx0 : 0 ≤ t + u.x ^ 2 - d.x ^ 2 := by
    have hnorm := normSq_nonneg sx
    rw [show normSq sx = 4 * (t + u.x ^ 2 - d.x ^ 2) by
      simpa [sx, t, u, d] using normSq_add_reflectX v w] at hnorm
    nlinarith
  have hz0 : 0 ≤ t + u.z ^ 2 - d.z ^ 2 := by
    have hnorm := normSq_nonneg sz
    rw [show normSq sz = 4 * (t + u.z ^ 2 - d.z ^ 2) by
      simpa [sz, t, u, d] using normSq_add_reflectZ v w] at hnorm
    nlinarith
  have hxnorm : Real.sqrt (normSq sx) =
      2 * Real.sqrt (t + u.x ^ 2 - d.x ^ 2) := by
    have hn := Real.sqrt_nonneg (normSq sx)
    have hs := Real.sq_sqrt hx0
    have hforward : normSq sx = 4 * (t + u.x ^ 2 - d.x ^ 2) := by
      simpa [sx, t, u, d] using normSq_add_reflectX v w
    apply (Real.sqrt_eq_iff_mul_self_eq (normSq_nonneg _) (by positivity)).2
    nlinarith
  have hznorm : Real.sqrt (normSq sz) =
      2 * Real.sqrt (t + u.z ^ 2 - d.z ^ 2) := by
    have hn := Real.sqrt_nonneg (normSq sz)
    have hs := Real.sq_sqrt hz0
    have hforward : normSq sz = 4 * (t + u.z ^ 2 - d.z ^ 2) := by
      simpa [sz, t, u, d] using normSq_add_reflectZ v w
    apply (Real.sqrt_eq_iff_mul_self_eq (normSq_nonneg _) (by positivity)).2
    nlinarith
  have hxdrop : Real.sqrt (t + u.x ^ 2 - d.x ^ 2) ≤ Real.sqrt (t + u.x ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg d.x]
  have hzdrop : Real.sqrt (t + u.z ^ 2 - d.z ^ 2) ≤ Real.sqrt (t + u.z ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg d.z]
  have hca := dot_le_sqrt_normSq ha sx
  have hcb := dot_le_sqrt_normSq hb sz
  rw [hxnorm] at hca
  rw [hznorm] at hcb
  have hvw := dot_eq_one_sub_two_halfDiff hv hw
  change dot v w = 1 - 2 * t at hvw
  have henergy : sharedEdgeEnergy v w a b =
      5 - dot v w - dot a sx - dot b sz := by
    simp [sharedEdgeEnergy, sx, sz, dot, add, reflectX, reflectZ]
    ring
  rw [henergy, hvw]
  nlinarith

/-- An explicit field attaining the shared-edge floor. -/
def edgeV : V3 := ⟨-Real.sqrt 2 / 2, 0, -Real.sqrt 2 / 2⟩
def edgeA : V3 := ⟨-1, 0, 0⟩
def edgeB : V3 := ⟨0, 0, -1⟩

lemma edgeV_unit : Unit edgeV := by
  have h := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  simp [Unit, normSq, edgeV]
  nlinarith

lemma edgeA_unit : Unit edgeA := by simp [Unit, normSq, edgeA]
lemma edgeB_unit : Unit edgeB := by simp [Unit, normSq, edgeB]

lemma sharedEdgeEnergy_witness :
    sharedEdgeEnergy edgeV edgeV edgeA edgeB = 4 - 2 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  simp [sharedEdgeEnergy, dot, reflectX, reflectZ, edgeV, edgeA, edgeB]
  nlinarith

lemma isLeast_sharedEdgeEnergies : IsLeast sharedEdgeEnergies (4 - 2 * Real.sqrt 2) := by
  constructor
  · exact ⟨edgeV, edgeV, edgeA, edgeB, edgeV_unit, edgeV_unit,
      edgeA_unit, edgeB_unit, sharedEdgeEnergy_witness.symm⟩
  · rintro e ⟨v, w, a, b, hv, hw, ha, hb, rfl⟩
    exact sharedEdgeEnergy_lower v w a b hv hw ha hb

end V3
end B194.RealGeometry

noncomputable section

namespace B194.RealGeometry.V3

open Real

/-- The cosine of one third of the arccosine, in [1/2,1]. -/
def triCos (c : ℝ) : ℝ := Real.cos (Real.arccos c / 3)
def triSin (c : ℝ) : ℝ := Real.sin (Real.arccos c / 3)

lemma triCos_relation {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    4 * triCos c ^ 3 - 3 * triCos c = c := by
  calc
    4 * triCos c ^ 3 - 3 * triCos c = Real.cos (3 * (Real.arccos c / 3)) := by
      rw [Real.cos_three_mul]
      rfl
    _ = c := by convert Real.cos_arccos hc0 hc1 <;> ring

lemma tri_angle_bounds (c : ℝ) :
    0 ≤ Real.arccos c / 3 ∧ Real.arccos c / 3 ≤ Real.pi / 3 := by
  constructor
  · exact div_nonneg (Real.arccos_nonneg c) (by norm_num)
  · have h := Real.arccos_le_pi c
    have hp := Real.pi_pos
    nlinarith

lemma triCos_bounds (c : ℝ) : 1 / 2 ≤ triCos c ∧ triCos c ≤ 1 := by
  obtain ⟨hp0, hp3⟩ := tri_angle_bounds c
  constructor
  · rw [show (1 / 2 : ℝ) = Real.cos (Real.pi / 3) by rw [Real.cos_pi_div_three]]
    apply Real.cos_le_cos_of_nonneg_of_le_pi hp0
    · nlinarith [Real.pi_pos]
    · exact hp3
  · exact Real.cos_le_one _

lemma triSin_nonneg (c : ℝ) : 0 ≤ triSin c := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi (tri_angle_bounds c).1
  nlinarith [(tri_angle_bounds c).2, Real.pi_pos]

lemma tri_sin_cos_sq (c : ℝ) : triSin c ^ 2 + triCos c ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

lemma triSin_relation {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    Real.sqrt (1 - c ^ 2) = triSin c * (4 * triCos c ^ 2 - 1) := by
  have hc : c = Real.cos (3 * (Real.arccos c / 3)) := by
    rw [show 3 * (Real.arccos c / 3) = Real.arccos c by ring]
    exact (Real.cos_arccos hc0 hc1).symm
  calc
    Real.sqrt (1 - c ^ 2) = Real.sin (Real.arccos c) := (Real.sin_arccos c).symm
    _ = Real.sin (3 * (Real.arccos c / 3)) := by congr 1; ring
    _ = 3 * triSin c - 4 * triSin c ^ 3 := Real.sin_three_mul _
    _ = triSin c * (4 * triCos c ^ 2 - 1) := by
      have h : triSin c ^ 2 = 1 - triCos c ^ 2 := by
        nlinarith [tri_sin_cos_sq c]
      calc
        3 * triSin c - 4 * triSin c ^ 3 = triSin c * (3 - 4 * triSin c ^ 2) := by ring
        _ = triSin c * (4 * triCos c ^ 2 - 1) := by rw [h]; ring

lemma dot_sq_le (a u : V3) : dot a u ^ 2 ≤ normSq a * normSq u := by
  unfold dot normSq
  nlinarith [sq_nonneg (a.x * u.y - a.y * u.x),
    sq_nonneg (a.x * u.z - a.z * u.x),
    sq_nonneg (a.y * u.z - a.z * u.y)]

lemma dot_bounds {a u : V3} (ha : Unit a) (hu : Unit u) :
    -1 ≤ dot a u ∧ dot a u ≤ 1 := by
  have h := dot_sq_le a u
  unfold Unit at ha hu
  rw [ha, hu] at h
  norm_num at h
  exact abs_le.1 h

/-- The two-dimensional residual Cauchy estimate for three unit vectors. -/
lemma residual_dot_le {u b w : V3} (hu : Unit u) (hb : Unit b) (hw : Unit w) :
    dot b w ≤ dot u w * dot u b +
      Real.sqrt (1 - dot u w ^ 2) * Real.sqrt (1 - dot u b ^ 2) := by
  let c := dot u w
  let t := dot u b
  let r : V3 := ⟨b.x - t * u.x, b.y - t * u.y, b.z - t * u.z⟩
  let s : V3 := ⟨w.x - c * u.x, w.y - c * u.y, w.z - c * u.z⟩
  have hu1 : normSq u = 1 := hu
  have hb1 : normSq b = 1 := hb
  have hw1 : normSq w = 1 := hw
  have hbu : dot b u = t := by
    simp [t, dot]
    ring
  have huw : dot u w = c := rfl
  have hrs : dot r s = dot b w - c * t := by
    calc
      dot r s = dot b w - c * dot b u - t * dot u w + c * t * normSq u := by
        simp [r, s, dot, normSq]
        ring
      _ = dot b w - c * t := by rw [hu1, hbu, huw]; ring
  have hr : normSq r = 1 - t ^ 2 := by
    calc
      normSq r = normSq b - 2 * t * dot b u + t ^ 2 * normSq u := by
        simp [r, normSq, dot]
        ring
      _ = 1 - t ^ 2 := by rw [hb1, hbu, hu1]; ring
  have hs : normSq s = 1 - c ^ 2 := by
    calc
      normSq s = normSq w - 2 * c * dot w u + c ^ 2 * normSq u := by
        simp [s, normSq, dot]
        ring
      _ = 1 - c ^ 2 := by
        rw [hw1, hu1]
        dsimp [c]
        simp [dot]
        ring
  have hcauchy := dot_sq_le r s
  rw [hrs, hr, hs] at hcauchy
  have hbounds := dot_bounds hu hb
  have hcbounds := dot_bounds hu hw
  change -1 ≤ t ∧ t ≤ 1 at hbounds
  change -1 ≤ c ∧ c ≤ 1 at hcbounds
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  have hsqrt : |dot b w - c * t| ≤ Real.sqrt ((1 - t ^ 2) * (1 - c ^ 2)) := by
    calc
      |dot b w - c * t| = Real.sqrt ((dot b w - c * t) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((1 - t ^ 2) * (1 - c ^ 2)) := Real.sqrt_le_sqrt hcauchy
  rw [Real.sqrt_mul ht2] at hsqrt
  have hres : dot b w - c * t ≤ Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - c ^ 2) :=
    (le_abs_self _).trans hsqrt
  change dot b w ≤ c * t + Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - t ^ 2)
  nlinarith

/-- Algebraic tangent-line form of the three-edge spherical-chain estimate. -/
lemma chain_scalar {x y t A B : ℝ}
    (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y)
    (hxy : x ^ 2 + y ^ 2 = 1) (ht0 : -1 ≤ t) (ht1 : t ≤ 1)
    (hA0 : 0 ≤ A) (hA : A ^ 2 = 2 + 2 * t)
    (hB0 : 0 ≤ B) (hB : B ^ 2 = 1 - t ^ 2) :
    A + (4 * x ^ 3 - 3 * x) * t + y * (4 * x ^ 2 - 1) * B ≤ 3 * x := by
  let t0 := 2 * x ^ 2 - 1
  let s0 := 2 * x * y
  have hxpos : 0 < x := by nlinarith
  have ht00 : -1 ≤ t0 := by dsimp [t0]; nlinarith [sq_nonneg x]
  have ht01 : t0 ≤ 1 := by dsimp [t0]; nlinarith [sq_nonneg x]
  have hs00 : 0 < s0 := by dsimp [s0]; positivity
  have hs0 : s0 ^ 2 = 1 - t0 ^ 2 := by
    dsimp [s0, t0]
    nlinarith
  have hAtangent : A ≤ 2 * x + (t - t0) / (2 * x) := by
    let R := 2 * x + (t - t0) / (2 * x)
    have hRid : R = (2 * x ^ 2 + 1 + t) / (2 * x) := by
      dsimp [R, t0]
      field_simp [ne_of_gt hxpos]
      ring
    have hnum : 0 ≤ 2 * x ^ 2 + 1 + t := by nlinarith
    have hR : 0 ≤ R := by rw [hRid]; exact div_nonneg hnum (by positivity)
    apply (sq_le_sq₀ hA0 hR).1
    have hid : R ^ 2 - A ^ 2 = (t - t0) ^ 2 / (4 * x ^ 2) := by
      dsimp [R, t0]
      field_simp
      nlinarith
    have hnonneg : 0 ≤ (t - t0) ^ 2 / (4 * x ^ 2) :=
      div_nonneg (sq_nonneg _) (by positivity)
    nlinarith
  have hBtangent : B ≤ s0 - t0 / s0 * (t - t0) := by
    let R := s0 - t0 / s0 * (t - t0)
    have hRid : R = (1 - t0 * t) / s0 := by
      dsimp [R]
      field_simp
      nlinarith
    have hnum : 0 ≤ 1 - t0 * t := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht01) (by nlinarith : 0 ≤ 1 + t),
        mul_nonneg (by nlinarith : 0 ≤ 1 + t0) (sub_nonneg.2 ht1)]
    have hR : 0 ≤ R := by rw [hRid]; positivity
    apply (sq_le_sq₀ hB0 hR).1
    have hid : R ^ 2 - B ^ 2 = (t - t0) ^ 2 / s0 ^ 2 := by
      rw [hRid]
      field_simp
      nlinarith
    have hnonneg : 0 ≤ (t - t0) ^ 2 / s0 ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hk : 0 ≤ y * (4 * x ^ 2 - 1) := mul_nonneg (le_of_lt hy) (by nlinarith)
  have hsum := add_le_add hAtangent (mul_le_mul_of_nonneg_left hBtangent hk)
  dsimp [t0, s0] at hsum
  have hid : 2 * x + (t - (2 * x ^ 2 - 1)) / (2 * x) +
      y * (4 * x ^ 2 - 1) * (2 * x * y - (2 * x ^ 2 - 1) / (2 * x * y) *
        (t - (2 * x ^ 2 - 1))) = 3 * x - (4 * x ^ 3 - 3 * x) * t := by
    field_simp [ne_of_gt hxpos, ne_of_gt hy]
    linear_combination (4 * x ^ 2 * (4 * x ^ 2 - 1)) * hxy
  nlinarith

/-- Maximum of the three adjacent inner products in one holonomy loop. -/
lemma loop_score_le (u a b w : V3)
    (hu : Unit u) (ha : Unit a) (hb : Unit b) (hw : Unit w) :
    dot u a + dot a b + dot b w ≤ 3 * triCos (dot u w) := by
  let c := dot u w
  let t := dot u b
  let x := triCos c
  let y := triSin c
  have hcbounds : -1 ≤ c ∧ c ≤ 1 := dot_bounds hu hw
  have htbounds : -1 ≤ t ∧ t ≤ 1 := dot_bounds hu hb
  have hxbounds := triCos_bounds c
  have hy0 := triSin_nonneg c
  have hxy := tri_sin_cos_sq c
  have hxy' : x ^ 2 + y ^ 2 = 1 := by
    dsimp [x, y]
    nlinarith [hxy]
  have hc := triCos_relation hcbounds.1 hcbounds.2
  have hsqrtc := triSin_relation hcbounds.1 hcbounds.2
  have hfirst : dot u a + dot a b ≤ Real.sqrt (2 + 2 * t) := by
    have hca := dot_le_sqrt_normSq ha (add u b)
    have hcomm : dot u a + dot a b = dot a (add u b) := by
      simp [dot, add]
      ring
    have hnorm : normSq (add u b) = 2 + 2 * t := by
      calc
        normSq (add u b) = normSq u + 2 * dot u b + normSq b := by
          simp [normSq, add, dot]
          ring
        _ = 2 + 2 * t := by rw [hu, hb]; dsimp [t]; ring
    rw [← hcomm, hnorm] at hca
    exact hca
  have hsecond := residual_dot_le hu hb hw
  change dot b w ≤ c * t + Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - t ^ 2) at hsecond
  rw [hsqrtc] at hsecond
  by_cases hy : y = 0
  · have hx : x = 1 := by
      have hxx := hxbounds.2
      have hx0 := hxbounds.1
      rw [hy] at hxy'
      norm_num at hxy'
      nlinarith
    have hcc : c = 1 := by
      change 4 * x ^ 3 - 3 * x = c at hc
      rw [hx] at hc
      norm_num at hc
      exact hc.symm
    have hzero : triCos c = 1 := by
      change x = 1 at hx
      exact hx
    rw [hzero]
    have hua := (dot_bounds hu ha).2
    have hab := (dot_bounds ha hb).2
    have hbw := (dot_bounds hb hw).2
    nlinarith
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have hscalar : Real.sqrt (2 + 2 * t) + (4 * x ^ 3 - 3 * x) * t +
        y * (4 * x ^ 2 - 1) * Real.sqrt (1 - t ^ 2) ≤ 3 * x :=
      chain_scalar hxbounds.1 hxbounds.2 hypos hxy' htbounds.1 htbounds.2
        (Real.sqrt_nonneg _) (Real.sq_sqrt (by nlinarith))
        (Real.sqrt_nonneg _) (Real.sq_sqrt (by nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]))
    change 4 * x ^ 3 - 3 * x = c at hc
    change dot u a + dot a b + dot b w ≤ 3 * x
    nlinarith

lemma triCos_pair_le {cx cz : ℝ}
    (hcx0 : -1 ≤ cx) (hcx1 : cx ≤ 1) (hcz0 : -1 ≤ cz) (hcz1 : cz ≤ 1)
    (hcs : cx + cz ≤ 0) : triCos cx + triCos cz ≤ Real.sqrt 3 := by
  let x := triCos cx
  let z := triCos cz
  have hx := triCos_bounds cx
  have hz := triCos_bounds cz
  have hrX := triCos_relation hcx0 hcx1
  have hrZ := triCos_relation hcz0 hcz1
  change 4 * x ^ 3 - 3 * x = cx at hrX
  change 4 * z ^ 3 - 3 * z = cz at hrZ
  have hx0 : 1 / 2 ≤ x := by dsimp [x]; exact (triCos_bounds cx).1
  have hz0 : 1 / 2 ≤ z := by dsimp [z]; exact (triCos_bounds cz).1
  have hs : 0 ≤ x + z := by nlinarith
  have hspos : 0 < x + z := by nlinarith

  have hcond : (x + z) * (4 * (x + z) ^ 2 - 12 * x * z - 3) ≤ 0 := by
    calc
      (x + z) * (4 * (x + z) ^ 2 - 12 * x * z - 3) =
          (4 * x ^ 3 - 3 * x) + (4 * z ^ 3 - 3 * z) := by ring
      _ = cx + cz := by rw [hrX, hrZ]
      _ ≤ 0 := hcs
  have hfactor : 4 * (x + z) ^ 2 - 12 * x * z - 3 ≤ 0 := by
    by_contra h
    have hp : 0 < 4 * (x + z) ^ 2 - 12 * x * z - 3 := lt_of_not_ge h
    nlinarith [mul_pos hspos hp]
  have hd : triCos cx + triCos cz = x + z := rfl
  rw [hd]
  apply (sq_le_sq₀ hs (Real.sqrt_nonneg _)).1
  have hs3 : (x + z) ^ 2 ≤ 3 := by nlinarith [sq_nonneg (x - z)]
  have hr3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma unit_reflectX {v : V3} (hv : Unit v) : Unit (reflectX v) := by
  simpa [Unit, normSq, reflectX] using hv

lemma unit_reflectZ {v : V3} (hv : Unit v) : Unit (reflectZ v) := by
  simpa [Unit, normSq, reflectZ] using hv

/-- Six undirected edge contributions on two triangles sharing only their base vertex. -/
def sharedVertexEnergy (v a b c d : V3) : ℝ :=
  (1 - dot v a) + (1 - dot a b) + (1 - dot b (reflectX v)) +
    (1 - dot v c) + (1 - dot c d) + (1 - dot d (reflectZ v))

def sharedVertexEnergies : Set ℝ := {e | ∃ v a b c d : V3,
  Unit v ∧ Unit a ∧ Unit b ∧ Unit c ∧ Unit d ∧ e = sharedVertexEnergy v a b c d}

lemma sharedVertexEnergy_lower (v a b c d : V3)
    (hv : Unit v) (ha : Unit a) (hb : Unit b) (hc : Unit c) (hd : Unit d) :
    6 - 3 * Real.sqrt 3 ≤ sharedVertexEnergy v a b c d := by
  let cx := dot v (reflectX v)
  let cz := dot v (reflectZ v)
  have hx := loop_score_le v a b (reflectX v) hv ha hb (unit_reflectX hv)
  have hz := loop_score_le v c d (reflectZ v) hv hc hd (unit_reflectZ hv)
  change dot v a + dot a b + dot b (reflectX v) ≤ 3 * triCos cx at hx
  change dot v c + dot c d + dot d (reflectZ v) ≤ 3 * triCos cz at hz
  have hcx := dot_bounds hv (unit_reflectX hv)
  have hcz := dot_bounds hv (unit_reflectZ hv)
  change -1 ≤ cx ∧ cx ≤ 1 at hcx
  change -1 ≤ cz ∧ cz ≤ 1 at hcz
  have hcs : cx + cz ≤ 0 := by
    dsimp [cx, cz]
    unfold Unit at hv
    unfold normSq at hv
    simp [dot, reflectX, reflectZ]
    nlinarith [sq_nonneg v.y]
  have hpair := triCos_pair_le hcx.1 hcx.2 hcz.1 hcz.2 hcs
  unfold sharedVertexEnergy
  nlinarith

/-- Vector on the unit circle in the x-z Bloch plane. -/
def planar (theta : ℝ) : V3 := ⟨Real.cos theta, 0, Real.sin theta⟩

lemma planar_unit (theta : ℝ) : Unit (planar theta) := by
  simp [Unit, normSq, planar]

lemma dot_planar (theta phi : ℝ) :
    dot (planar theta) (planar phi) = Real.cos (theta - phi) := by
  simp [dot, planar, Real.cos_sub]

lemma dot_planar_reflectX (theta phi : ℝ) :
    dot (planar theta) (reflectX (planar phi)) = Real.cos (theta + phi) := by
  simp [dot, planar, reflectX, Real.cos_add]
  ring

lemma dot_planar_reflectZ (theta phi : ℝ) :
    dot (planar theta) (reflectZ (planar phi)) = -Real.cos (theta + phi) := by
  simp [dot, planar, reflectZ, Real.cos_add]
  ring

def vertexV := planar (-Real.pi / 4)
def vertexA := planar (-Real.pi / 12)
def vertexB := planar (Real.pi / 12)
def vertexC := planar (-5 * Real.pi / 12)
def vertexD := planar (-7 * Real.pi / 12)

lemma cos_neg_pi_six : Real.cos (-Real.pi / 6) = Real.sqrt 3 / 2 := by
  rw [show -Real.pi / 6 = -(Real.pi / 6) by ring, Real.cos_neg, Real.cos_pi_div_six]

lemma cos_neg_five_pi_six : Real.cos (-5 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
  rw [show -5 * Real.pi / 6 = -(Real.pi - Real.pi / 6) by ring,
    Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_six]
  ring

lemma sharedVertexEnergy_witness :
    sharedVertexEnergy vertexV vertexA vertexB vertexC vertexD =
      6 - 3 * Real.sqrt 3 := by
  have h1 : dot vertexV vertexA = Real.sqrt 3 / 2 := by
    rw [vertexV, vertexA, dot_planar]
    convert cos_neg_pi_six using 1 <;> ring
  have h2 : dot vertexA vertexB = Real.sqrt 3 / 2 := by
    rw [vertexA, vertexB, dot_planar]
    convert cos_neg_pi_six using 1 <;> ring
  have h3 : dot vertexB (reflectX vertexV) = Real.sqrt 3 / 2 := by
    rw [vertexB, vertexV, dot_planar_reflectX]
    convert cos_neg_pi_six using 1 <;> ring
  have h4 : dot vertexV vertexC = Real.sqrt 3 / 2 := by
    rw [vertexV, vertexC, dot_planar]
    convert Real.cos_pi_div_six using 1 <;> ring
  have h5 : dot vertexC vertexD = Real.sqrt 3 / 2 := by
    rw [vertexC, vertexD, dot_planar]
    convert Real.cos_pi_div_six using 1 <;> ring
  have h6 : dot vertexD (reflectZ vertexV) = Real.sqrt 3 / 2 := by
    rw [vertexD, vertexV, dot_planar_reflectZ]
    convert congrArg Neg.neg cos_neg_five_pi_six using 1 <;> ring
  unfold sharedVertexEnergy
  rw [h1, h2, h3, h4, h5, h6]
  ring

lemma isLeast_sharedVertexEnergies : IsLeast sharedVertexEnergies (6 - 3 * Real.sqrt 3) := by
  constructor
  · exact ⟨vertexV, vertexA, vertexB, vertexC, vertexD, planar_unit _, planar_unit _,
      planar_unit _, planar_unit _, planar_unit _, sharedVertexEnergy_witness.symm⟩
  · rintro e ⟨v, a, b, c, d, hv, ha, hb, hc, hd, rfl⟩
    exact sharedVertexEnergy_lower v a b c d hv ha hb hc hd

end B194.RealGeometry.V3

noncomputable section

namespace B194.RealGeometry.V3

open B194

/-- The two-by-two density matrix attached to a real Bloch vector. -/
def toBloch (v : V3) : Mat := blochProjector v.x v.y v.z

lemma frobeniusSq_toBloch_sub (v w : V3) :
    frobeniusSq (toBloch v - toBloch w) =
      ((v.x - w.x) ^ 2 + (v.y - w.y) ^ 2 + (v.z - w.z) ^ 2) / 2 := by
  simp [frobeniusSq, toBloch, blochProjector, Fin.sum_univ_two,
    Complex.normSq_apply]
  ring

lemma frobeniusSq_toBloch_sub_of_unit {v w : V3} (hv : Unit v) (hw : Unit w) :
    frobeniusSq (toBloch v - toBloch w) = 1 - dot v w := by
  rw [frobeniusSq_toBloch_sub]
  unfold Unit at hv hw
  unfold normSq at hv hw
  simp [dot]
  nlinarith

lemma sigmaX_toBloch (v : V3) :
    sigmaX * toBloch v * sigmaX = toBloch (reflectX v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBloch, blochProjector, sigmaX, reflectX, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

lemma sigmaZ_toBloch (v : V3) :
    sigmaZ * toBloch v * sigmaZ = toBloch (reflectZ v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBloch, blochProjector, sigmaZ, reflectZ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

lemma frobeniusSq_toBloch_sub_sigmaX {a v : V3} (ha : Unit a) (hv : Unit v) :
    frobeniusSq (toBloch a - sigmaX * toBloch v * sigmaX) =
      1 - dot a (reflectX v) := by
  rw [sigmaX_toBloch, frobeniusSq_toBloch_sub_of_unit ha (unit_reflectX hv)]

lemma frobeniusSq_toBloch_sub_sigmaZ {d v : V3} (hd : Unit d) (hv : Unit v) :
    frobeniusSq (toBloch d - sigmaZ * toBloch v * sigmaZ) =
      1 - dot d (reflectZ v) := by
  rw [sigmaZ_toBloch, frobeniusSq_toBloch_sub_of_unit hd (unit_reflectZ hv)]

/-- The shared-edge real energy is literally the sum of the five Frobenius
edge books used by the card. -/
lemma sharedEdgeEnergy_eq_frobenius (v w a b : V3)
    (hv : Unit v) (hw : Unit w) (ha : Unit a) (hb : Unit b) :
    sharedEdgeEnergy v w a b =
      frobeniusSq (toBloch v - toBloch w) +
      frobeniusSq (toBloch w - toBloch a) +
      frobeniusSq (toBloch a - sigmaX * toBloch v * sigmaX) +
      frobeniusSq (toBloch w - toBloch b) +
      frobeniusSq (toBloch b - sigmaZ * toBloch v * sigmaZ) := by
  rw [frobeniusSq_toBloch_sub_of_unit hv hw,
    frobeniusSq_toBloch_sub_of_unit hw ha,
    frobeniusSq_toBloch_sub_sigmaX ha hv,
    frobeniusSq_toBloch_sub_of_unit hw hb,
    frobeniusSq_toBloch_sub_sigmaZ hb hv]
  rfl

/-- The shared-vertex real energy is literally the sum of the six Frobenius
edge books used by the card. -/
lemma sharedVertexEnergy_eq_frobenius (v a b c d : V3)
    (hv : Unit v) (ha : Unit a) (hb : Unit b) (hc : Unit c) (hd : Unit d) :
    sharedVertexEnergy v a b c d =
      frobeniusSq (toBloch v - toBloch a) +
      frobeniusSq (toBloch a - toBloch b) +
      frobeniusSq (toBloch b - sigmaX * toBloch v * sigmaX) +
      frobeniusSq (toBloch v - toBloch c) +
      frobeniusSq (toBloch c - toBloch d) +
      frobeniusSq (toBloch d - sigmaZ * toBloch v * sigmaZ) := by
  rw [frobeniusSq_toBloch_sub_of_unit hv ha,
    frobeniusSq_toBloch_sub_of_unit ha hb,
    frobeniusSq_toBloch_sub_sigmaX hb hv,
    frobeniusSq_toBloch_sub_of_unit hv hc,
    frobeniusSq_toBloch_sub_of_unit hc hd,
    frobeniusSq_toBloch_sub_sigmaZ hd hv]
  rfl

/-- One sigma_x loop is frustration-free: the x-axis Bloch vector is fixed. -/
def singleLoopXEnergy (v a b : V3) : ℝ :=
  (1 - dot v a) + (1 - dot a b) + (1 - dot b (reflectX v))

def singleLoopXEnergies : Set ℝ := {e | ∃ v a b : V3,
  Unit v ∧ Unit a ∧ Unit b ∧ e = singleLoopXEnergy v a b}

lemma isLeast_singleLoopXEnergies : IsLeast singleLoopXEnergies 0 := by
  let x : V3 := ⟨1, 0, 0⟩
  have hx : Unit x := by simp [x, Unit, normSq]
  constructor
  · refine ⟨x, x, x, hx, hx, hx, ?_⟩
    simp [singleLoopXEnergy, x, dot, reflectX]
  · rintro e ⟨v, a, b, hv, ha, hb, rfl⟩
    have hva := (dot_bounds hv ha).2
    have hab := (dot_bounds ha hb).2
    have hbv := (dot_bounds hb (unit_reflectX hv)).2
    unfold singleLoopXEnergy
    nlinarith

end B194.RealGeometry.V3


end

/-! ## B25, the card's per-level quantity (added at integration)

The B25 section above sums over the level index `n` as well as the partner `m`;
the card's `chi = sum_{m != n} ...` fixes `n` (its Carry field says "a
nondegenerate level n"), so at two levels the summed version is exactly twice
the card's number. This addition states the per-level quantity and its value.
-/
section



/-!
An addition made at integration, not by the author of the B25 section: the card's
`χ = Σ_{m≠n} |⟨n|∂H|m⟩|²/γ_nm²` carries a **free level n** — its Carry field says
"a nondegenerate level n" — so `χ` is a per-level quantity.  The accepted file sums over
`n` as well, which is the total over all levels; at two levels that is exactly twice the
card's number.  This file states the card's own quantity and its two-level value.
-/
noncomputable section

namespace AtlasB25Level

open Matrix

/-- The card's displayed sum with the level `n` held fixed. -/
def levelChi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℝ) (n : ι) : ℝ :=
  ∑ m : ι, if m ≠ n then A n m ^ 2 / γ n m ^ 2 else 0

/-- Every per-level summand is nonnegative, so the level susceptibility of the card is. -/
theorem levelChi_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ι → ℝ) (A : ι → ι → ℝ) (n : ι) : 0 ≤ levelChi γ A n := by
  unfold levelChi
  refine Finset.sum_nonneg fun m _ => ?_
  split_ifs
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact le_rfl

/-- Two levels at energies `0` and `δ` with unit coupling. -/
def twoE (δ : ℝ) : Fin 2 → ℝ := ![0, δ]

/-- Two levels at energies `0` and `δ`, coupling one: the card's per-level susceptibility
of the lower level is `1/δ²`, not the `2/δ²` the double-summed quantity gives. -/
theorem twoLevel_levelChi (δ : ℝ) :
    levelChi (fun n m => twoE δ n - twoE δ m) (fun _ _ => 1) 0 = 1 / δ ^ 2 := by
  simp only [levelChi, twoE]
  rw [Fin.sum_univ_two]
  simp

/-- Consequently the file's double-summed value and the card's per-level value differ by
exactly the factor two at two levels: this is the correction this addition records. -/
theorem double_summed_is_twice_the_level (δ : ℝ) :
    2 * levelChi (fun n m => twoE δ n - twoE δ m) (fun _ _ => 1) 0 = 2 / δ ^ 2 := by
  rw [twoLevel_levelChi]
  ring

end AtlasB25Level

#print axioms AtlasB25Level.levelChi_nonneg
#print axioms AtlasB25Level.twoLevel_levelChi
#print axioms AtlasB25Level.double_summed_is_twice_the_level


end
