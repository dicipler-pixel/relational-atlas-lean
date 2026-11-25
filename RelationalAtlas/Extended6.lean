import RelationalAtlas.Extended3
import RelationalAtlas.Extended4

/-!
Sixth module: the two gap closures that build on the accepted modules rather than starting
from Mathlib alone. Kept apart because they import, so they cannot be appended to
`Extended5`. The B145 section comes first because it is the one whose names resolve
through `RelationalAtlas.B145`.
-/

/-! ## B145 — the boundary of the pseudospectral disk

Integrated from `.ultramath/smwu90bch/m12/B145Boundary.lean`.
-/

/-!
# B145: the exact pseudospectral boundary

The v7 card's displayed set is the *strict* disk and its "Why it holds"
paragraph says that the smallest singular value is `ε` on the circle and `< ε`
inside it. Thus the sharp resolvent statement on that circle is equality with
`ε⁻¹`, not the strict inequality defining pseudospectrum membership.

This file uses the resolvent and norm formula already certified in
`RelationalAtlas.B145`; it adds the equality case and the squared-boundary
statement in the exact form `|w|² = ε |μ| + ε²` used by the gap.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexConjugate BigOperators Topology

namespace RelationalAtlas.B145.BoundaryGap

/-- Equality version of `RelationalAtlas.B145.resolvent_threshold`.
No small-parameter or nonvanishing-coupling hypothesis is needed. -/
lemma resolvent_threshold_eq {ε q a : ℝ} (hε : 0 < ε) (hq : 0 < q) (ha : 0 ≤ a) :
    ε⁻¹ = (a + Real.sqrt (a ^ 2 + 4 * q)) / (2 * q) ↔
      q = ε * a + ε ^ 2 := by
  let s := Real.sqrt (a ^ 2 + 4 * q)
  have hs : s ^ 2 = a ^ 2 + 4 * q := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hsa : 0 < s + a := by positivity
  change ε⁻¹ = (a + s) / (2 * q) ↔ q = ε * a + ε ^ 2
  have hleft : ε⁻¹ = (a + s) / (2 * q) ↔ 2 * q = ε * (a + s) := by
    constructor
    · intro h
      have h' := (eq_div_iff (by positivity : 2 * q ≠ 0)).mp h
      have heq : ε * (ε⁻¹ * (2 * q)) = 2 * q := by
        field_simp [ne_of_gt hε]
      calc
        2 * q = ε * (ε⁻¹ * (2 * q)) := heq.symm
        _ = ε * (a + s) := by rw [h']
    · intro h
      apply (eq_div_iff (by positivity : 2 * q ≠ 0)).mpr
      have heq : ε⁻¹ * (ε * (a + s)) = a + s := by
        field_simp [ne_of_gt hε]
      calc
        ε⁻¹ * (2 * q) = ε⁻¹ * (ε * (a + s)) := by rw [h]
        _ = a + s := heq
  rw [hleft]
  constructor
  · intro h
    have hprod : (s - a) * (s + a) = (2 * ε) * (s + a) := by
      nlinarith [hs]
    have hcancel : s - a = 2 * ε := by
      exact mul_right_cancel₀ (ne_of_gt hsa) hprod
    nlinarith [hs]
  · intro h
    have hsquare : s ^ 2 = (a + 2 * ε) ^ 2 := by
      nlinarith [hs]
    have hslt : s = a + 2 * ε :=
      (sq_eq_sq₀ hs0 (by positivity)).mp hsquare
    nlinarith

/-- At nonzero `w`, the resolvent norm is exactly the pseudospectral threshold
precisely on the displayed squared circle. -/
theorem resolvent_norm_eq_inv_iff {w : ℂ} (hw : w ≠ 0) (μ : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖resolvent w μ‖ = ε⁻¹ ↔ ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2 := by
  rw [resolvent_norm hw μ]
  exact eq_comm.trans
    (resolvent_threshold_eq hε (by positivity) (norm_nonneg μ))

/-- The squared circle has positive radius, so its points are away from the
resolvent's pole. -/
lemma ne_zero_of_sq_boundary {w μ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2) : w ≠ 0 := by
  have hq : 0 < ‖w‖ ^ 2 := by
    rw [h]
    positivity
  intro hw
  subst w
  simp at hq

/-- **B145 boundary, sharp form.** The squared boundary is exactly the locus
where `w ≠ 0` and the resolvent norm equals `ε⁻¹`. -/
theorem sq_boundary_iff_resolvent_norm_eq_inv {w μ : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2 ↔
      (w ≠ 0 ∧ ‖resolvent w μ‖ = ε⁻¹) := by
  constructor
  · intro h
    have hw := ne_zero_of_sq_boundary hε h
    exact ⟨hw, (resolvent_norm_eq_inv_iff hw μ hε).mpr h⟩
  · rintro ⟨hw, hnorm⟩
    exact (resolvent_norm_eq_inv_iff hw μ hε).mp hnorm

lemma norm_eq_radius_of_sq_boundary {w μ : ℂ} {ε : ℝ}
    (h : ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2) :
    ‖w‖ = Real.sqrt (ε * ‖μ‖ + ε ^ 2) := by
  rw [← h, Real.sqrt_sq (norm_nonneg w)]

lemma sq_boundary_iff_norm_eq_radius {w μ : ℂ} {ε : ℝ} (hε : 0 < ε) :
    ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2 ↔
      ‖w‖ = Real.sqrt (ε * ‖μ‖ + ε ^ 2) := by
  constructor
  · exact norm_eq_radius_of_sq_boundary
  · intro h
    calc
      ‖w‖ ^ 2 = (Real.sqrt (ε * ‖μ‖ + ε ^ 2)) ^ 2 := by rw [h]
      _ = ε * ‖μ‖ + ε ^ 2 := Real.sq_sqrt (by positivity)

/-- **The boundary is excluded.** This is the card's own squared boundary
condition, rather than an adjacent radius hypothesis. -/
theorem not_mem_pseudoSpectrum_sq_boundary {ε : ℝ} (hε : 0 < ε)
    (b μ z : ℂ) (hz : ‖z - b‖ ^ 2 = ε * ‖μ‖ + ε ^ 2) :
    z ∉ pseudoSpectrum ε b μ := by
  apply not_mem_pseudoSpectrum_boundary hε b μ z
  exact norm_eq_radius_of_sq_boundary hz

/-- Sharp strict/equality data at and inside the circle. -/
theorem resolvent_threshold_strict_and_eq {w μ : ℂ} (hw : w ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    (ε⁻¹ < ‖resolvent w μ‖ ↔ ‖w‖ ^ 2 < ε * ‖μ‖ + ε ^ 2) ∧
    (‖resolvent w μ‖ = ε⁻¹ ↔ ‖w‖ ^ 2 = ε * ‖μ‖ + ε ^ 2) := by
  constructor
  · rw [resolvent_norm_gt_inv_iff hw μ hε]
    exact Real.lt_sqrt (norm_nonneg w)
  · exact resolvent_norm_eq_inv_iff hw μ hε

#print axioms resolvent_threshold_eq
#print axioms resolvent_norm_eq_inv_iff
#print axioms ne_zero_of_sq_boundary
#print axioms sq_boundary_iff_resolvent_norm_eq_inv
#print axioms norm_eq_radius_of_sq_boundary
#print axioms sq_boundary_iff_norm_eq_radius
#print axioms not_mem_pseudoSpectrum_sq_boundary
#print axioms resolvent_threshold_strict_and_eq

end RelationalAtlas.B145.BoundaryGap


/-! ## B181 — the missing join, and the ISCO attribution refuted

Integrated from `.ultramath/smwu90bch/m2/B181Gap.lean`.
-/

/-!
# B181: the decimal belongs to the square, and the stiffness join

The pinned v7 B181 card (`0c43a577c4490b256d163f57e641bfb2e990a3ee6e935d2bd179e4f208bfeccb`)
contains no ISCO assertion.  Its displayed decimal is the transverse frequency of the
symmetric square.  This file adds the declaration missing from the fourth batch:
the exact square frequency is the second derivative of the actual square potential in
the fold coordinate.  It also treats the height coordinate `h`, where `w₃ = 4h²`,
so that the card's coefficient `8√2 - 4` is checked with the correct factor.

For contrast, the B177 radial frequency at the ISCO is zero; it cannot be B181's
positive displayed frequency.  The decimal bounds themselves are not reproved: we use
`B181.squareOmega_decimal_bounds` and the other fourth-batch declarations.
-/

noncomputable section

namespace B181

open Real Filter
open scoped Topology

/-- The potential obtained by substituting `w = c*x²`.  For `c = 1` this is
`foldPotential U`; for the square's height coordinate, `c = 4`. -/
def scaledFoldPotential (U : ℝ → ℝ) (c x : ℝ) : ℝ := U (c * x ^ 2)

/-- A local version of the second-derivative chain rule through `w = c*x²`.
Only a neighbourhood of the wall is used; unlike fourth-batch
`foldPotential_second_deriv`, this does not impose global differentiability on
an expression whose inverse square roots are singular away from the wall. -/
theorem deriv_deriv_scaledFoldPotential_of_local
    (U D : ℝ → ℝ) (c : ℝ)
    (hU : ∀ᶠ w in 𝓝 0, HasDerivAt U (D w) w)
    (hD : DifferentiableAt ℝ D 0) :
    deriv (deriv (scaledFoldPotential U c)) 0 = 2 * c * D 0 := by
  have hinner (x : ℝ) : HasDerivAt (fun y : ℝ => c * y ^ 2) (c * (2 * x)) x := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact hp.const_mul c
  have hinner_zero : HasDerivAt (fun y : ℝ => c * y ^ 2) 0 0 := by
    convert hinner 0 using 1 <;> norm_num
  have htend : Filter.Tendsto (fun x : ℝ => c * x ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => c * x ^ 2) (0 : ℝ) := by fun_prop
    simpa using hc.tendsto
  have hV : ∀ᶠ x in 𝓝 0,
      HasDerivAt (scaledFoldPotential U c)
        (2 * c * x * D (c * x ^ 2)) x := by
    filter_upwards [htend.eventually hU] with x hx
    have hc := hx.comp x (hinner x)
    change HasDerivAt (fun y : ℝ => U (c * y ^ 2))
      (D (c * x ^ 2) * (c * (2 * x))) x at hc
    change HasDerivAt (fun y : ℝ => U (c * y ^ 2))
      (2 * c * x * D (c * x ^ 2)) x
    convert hc using 1 <;> ring
  have hDcomp : HasDerivAt (fun x : ℝ => D (c * x ^ 2)) 0 0 := by
    have hD0 : HasDerivAt D (deriv D 0) (c * (0 : ℝ) ^ 2) := by
      simpa using hD.hasDerivAt
    have hc := hD0.comp 0 hinner_zero
    simpa [Function.comp_def] using hc
  have hlin : HasDerivAt (fun x : ℝ => 2 * c * x) (2 * c) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).const_mul (2 * c) using 1
    · ext x
      rfl
    · ring
  have hDscaled : HasDerivAt (fun x : ℝ => 2 * c * x * D (c * x ^ 2))
      (2 * c * D 0) 0 := by
    convert hlin.mul hDcomp using 1 <;> norm_num
  have heq : deriv (scaledFoldPotential U c) =ᶠ[𝓝 0]
      (fun x : ℝ => 2 * c * x * D (c * x ^ 2)) := by
    filter_upwards [hV] with x hx
    exact hx.deriv
  exact (hDscaled.congr_of_eventuallyEq heq).deriv

/-- The raw first derivative of the fourth-batch square potential.  Keeping the
unsimplified expression makes the general derivative proof purely algebraic;
its value at zero is identified by uniqueness with the already proved slope. -/
noncomputable def squarePotentialSlope (w : ℝ) : ℝ :=
  -4 * (-((1 / 2 : ℝ) / (2 * sqrt ((1 : ℝ) / 2 + w / 2))) /
      sqrt ((1 : ℝ) / 2 + w / 2) ^ 2) -
    ((-(-1 / 4 : ℝ) / (2 * sqrt ((1 : ℝ) / 4 - w / 4))) /
      sqrt ((1 : ℝ) / 4 - w / 4) ^ 2)

lemma squarePotential_hasDerivAt_of_pos {w : ℝ}
    (ha : 0 < (1 : ℝ) / 2 + w / 2) (hb : 0 < (1 : ℝ) / 4 - w / 4) :
    HasDerivAt squarePotential (squarePotentialSlope w) w := by
  have hlin1 : HasDerivAt (fun w : ℝ => (1 : ℝ) / 2 + w / 2) (1 / 2) w := by
    simpa using ((hasDerivAt_id w).div_const 2).const_add (1 / 2)
  have hsqrt1 := hlin1.sqrt ha.ne'
  have hinv1 : HasDerivAt (fun w : ℝ => -4 / sqrt ((1 : ℝ) / 2 + w / 2))
      (-4 * (-((1 / 2 : ℝ) / (2 * sqrt ((1 : ℝ) / 2 + w / 2))) /
        sqrt ((1 : ℝ) / 2 + w / 2) ^ 2)) w := by
    simpa [div_eq_mul_inv] using (hsqrt1.inv (by positivity)).const_mul (-4)
  have hlin2 : HasDerivAt (fun w : ℝ => (1 : ℝ) / 4 - w / 4) (-1 / 4) w := by
    convert ((hasDerivAt_id w).div_const 4).const_sub (1 / 4) using 1
    · ext x
      rfl
    · ring
  have hsqrt2 := hlin2.sqrt hb.ne'
  have hinv2 : HasDerivAt (fun w : ℝ => 1 / sqrt ((1 : ℝ) / 4 - w / 4))
      ((-(-1 / 4 : ℝ) / (2 * sqrt ((1 : ℝ) / 4 - w / 4))) /
        sqrt ((1 : ℝ) / 4 - w / 4) ^ 2) w := by
    have h := hsqrt2.inv (by positivity)
    convert h using 1
    · ext w
      simp only [Pi.inv_apply, one_div]
    · ring
  exact hinv1.sub hinv2

lemma squarePotential_hasDerivAt_near :
    ∀ᶠ w in 𝓝 0, HasDerivAt squarePotential (squarePotentialSlope w) w := by
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)] with w hw
  apply squarePotential_hasDerivAt_of_pos <;>
    simp only [Set.mem_Ioo] at hw <;> nlinarith [hw.1, hw.2]

lemma differentiableAt_squarePotentialSlope :
    DifferentiableAt ℝ squarePotentialSlope 0 := by
  unfold squarePotentialSlope
  fun_prop (disch := positivity)

/-- The raw slope is the already established square slope at the wall. -/
lemma squarePotentialSlope_zero : squarePotentialSlope 0 = 2 * sqrt 2 - 1 := by
  exact (squarePotential_hasDerivAt_of_pos (w := 0) (by norm_num)
    (by norm_num)).unique squarePotential_hasDerivAt

/-- **The missing stiffness/frequency join.**  For the actual square potential
in the card's fold coordinate `w₃ = σ₃²`, its second derivative at the planar
wall is exactly `squareOmega² = 2(2√2-1)`. -/
theorem squareFold_second_deriv_eq_squareOmega_sq :
    deriv (deriv (foldPotential squarePotential)) 0 = squareOmega ^ 2 := by
  have h := deriv_deriv_scaledFoldPotential_of_local
    squarePotential squarePotentialSlope 1
    squarePotential_hasDerivAt_near differentiableAt_squarePotentialSlope
  rw [squarePotentialSlope_zero] at h
  have hfun : scaledFoldPotential squarePotential 1 = foldPotential squarePotential := by
    funext x
    simp [scaledFoldPotential, foldPotential]
  rw [hfun] at h
  rw [squareOmega_sq]
  convert h using 1 <;> ring

/-- The square potential in the card's alternate-height coordinate: the planar
square has `a² = 1/4-h²`, and the card stipulates `w₃ = 4h²`. -/
noncomputable def squareHeightPotential (h : ℝ) : ℝ := squarePotential (4 * h ^ 2)

/-- In the height coordinate the second derivative is `4ω²`.  Equivalently,
the coefficient of `h²` in the card's display is `2ω² = 8√2-4`; this theorem
fixes the normalization rather than silently identifying `h` with `σ₃`. -/
theorem squareHeight_second_deriv :
    deriv (deriv squareHeightPotential) 0 = 4 * squareOmega ^ 2 := by
  have h := deriv_deriv_scaledFoldPotential_of_local
    squarePotential squarePotentialSlope 4
    squarePotential_hasDerivAt_near differentiableAt_squarePotentialSlope
  rw [squarePotentialSlope_zero] at h
  have hfun : scaledFoldPotential squarePotential 4 = squareHeightPotential := rfl
  rw [hfun] at h
  rw [squareOmega_sq]
  convert h using 1 <;> ring

/-- The precise quadratic coefficient in the height expansion printed on the
card: half of the second derivative is `8√2-4`. -/
theorem squareHeight_quadratic_coefficient :
    deriv (deriv squareHeightPotential) 0 / 2 = 8 * sqrt 2 - 4 := by
  rw [squareHeight_second_deriv, squareOmega_sq]
  ring

/-- B177's radial/epicyclic frequency at the ISCO, using its own normalization
`G = c = M = 1`, `r = 6`, and `L² = 6²/(6-3) = 12`. -/
noncomputable def iscoRadialFrequency (L : ℝ) : ℝ :=
  sqrt (B177.radialFrequencySq L 6)

lemma iscoRadialFrequency_eq_zero (L : ℝ)
    (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) : iscoRadialFrequency L = 0 := by
  rw [iscoRadialFrequency, B177.isco_half_second L hL, Real.sqrt_zero]

/-- Hence B181's positive `1.912290...` cannot be B177's radial frequency at
the ISCO.  This is a refutation of that attribution, not a new physical claim. -/
theorem squareOmega_ne_iscoRadialFrequency (L : ℝ)
    (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    squareOmega ≠ iscoRadialFrequency L := by
  rw [iscoRadialFrequency_eq_zero L hL]
  have hpos : 0 < squareOmega :=
    (show (0 : ℝ) < (1912290 : ℝ) / 1000000 by norm_num).trans
      squareOmega_decimal_bounds.1
  exact ne_of_gt hpos

/-- The complete finite decimal resolution: exact square stiffness, exact
radical value, correct six-place rounding (and not literal equality), and zero
ISCO radial frequency under B177's ISCO angular-momentum hypothesis. -/
theorem b181_decimal_resolution (L : ℝ)
    (hL : L ^ 2 = (6 : ℝ) ^ 2 / (6 - 3)) :
    deriv (deriv (foldPotential squarePotential)) 0 = squareOmega ^ 2 ∧
    squareOmega ^ 2 = 2 * (2 * sqrt 2 - 1) ∧
    (1912290 : ℝ) / 1000000 < squareOmega ∧
    squareOmega < (19122905 : ℝ) / 10000000 ∧
    squareOmega ≠ (1912290 : ℝ) / 1000000 ∧
    iscoRadialFrequency L = 0 ∧
    squareOmega ≠ iscoRadialFrequency L := by
  exact ⟨squareFold_second_deriv_eq_squareOmega_sq, squareOmega_sq,
    squareOmega_decimal_bounds.1, squareOmega_decimal_bounds.2,
    squareOmega_ne_displayed_exactly, iscoRadialFrequency_eq_zero L hL,
    squareOmega_ne_iscoRadialFrequency L hL⟩

#print axioms deriv_deriv_scaledFoldPotential_of_local
#print axioms squarePotential_hasDerivAt_of_pos
#print axioms squarePotential_hasDerivAt_near
#print axioms differentiableAt_squarePotentialSlope
#print axioms squarePotentialSlope_zero
#print axioms squareFold_second_deriv_eq_squareOmega_sq
#print axioms squareHeight_second_deriv
#print axioms squareHeight_quadratic_coefficient
#print axioms iscoRadialFrequency_eq_zero
#print axioms squareOmega_ne_iscoRadialFrequency
#print axioms b181_decimal_resolution

end B181

end

