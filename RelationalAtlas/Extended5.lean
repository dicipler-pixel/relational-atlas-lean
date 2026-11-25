/-
Fifth batch: closing the gaps that blocked whole-card certification.

Each section below closes a gap recorded in the ledger's `corrections` list, or shows that
the gap is real and the honest scope is narrower than the ledger said. Each contribution is
reproduced verbatim except for its import line; each keeps its own scope delimiters, so the
concatenation is balanced. Nothing in the earlier modules is modified.
-/
import Mathlib


/-! ## B112 — the one-zero case, and the free kernel block

Integrated from `.ultramath/smwu90bch/m6/B112Converse.lean`.
-/

/-!
# B112: uniqueness off the kernel--kernel block

For a diagonal density matrix with real eigenvalues `p`, the SLD equation is

  `((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j`.

The main theorems below compare two *arbitrary* solutions `L` and `M`.  If
exactly one of `p i`, `p j` vanishes, they prove `L i j = M i j`; no
positivity, finiteness, Hermiticity, or compatibility assumption is needed.
For nonnegative `p`, the same conclusion holds whenever `(i,j)` is not a
kernel--kernel pair.  Finally, every two solutions differ by precisely an
arbitrary matrix supported on kernel--kernel pairs.

Source checked: Zenodo record 23590925, `atlas_cards_v7_html.zip`, member
`cards/html/B112.html`, SHA-256
`3f0064a5801386d55481395db5b3c374b2b5702f7f23b2bdc5dbc269d8f487b3`.
-/

noncomputable section

namespace AtlasB112Gap

open Matrix

variable {n : Type*}

/-- Two solutions agree on a support--kernel entry with the left weight zero.
The nonzero right weight can be cancelled directly. -/
theorem entrywise_unique_of_left_zero {p : n → ℝ} {V L M : Matrix n n ℂ}
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    (hM : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * M i j = 2 * V i j)
    {i j : n} (hi : p i = 0) (hj : p j ≠ 0) :
    L i j = M i j := by
  have hjc : (p j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hj
  apply mul_left_cancel₀ hjc
  simpa [hi] using (hL i j).trans (hM i j).symm

#print axioms entrywise_unique_of_left_zero

/-- Two solutions agree on a kernel--support entry with the right weight zero.
The nonzero left weight can be cancelled directly. -/
theorem entrywise_unique_of_right_zero {p : n → ℝ} {V L M : Matrix n n ℂ}
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    (hM : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * M i j = 2 * V i j)
    {i j : n} (hi : p i ≠ 0) (hj : p j = 0) :
    L i j = M i j := by
  have hic : (p i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
  apply mul_left_cancel₀ hic
  simpa [hj] using (hL i j).trans (hM i j).symm

#print axioms entrywise_unique_of_right_zero

/-- The card's support--kernel motion is therefore uniquely represented in
*every* solution whenever exactly one of the two weights vanishes. -/
theorem entrywise_unique_of_exactly_one_zero {p : n → ℝ} {V L M : Matrix n n ℂ}
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    (hM : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * M i j = 2 * V i j)
    {i j : n}
    (hij : (p i = 0 ∧ p j ≠ 0) ∨ (p i ≠ 0 ∧ p j = 0)) :
    L i j = M i j := by
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact entrywise_unique_of_left_zero hL hM hi hj
  · exact entrywise_unique_of_right_zero hL hM hi hj

#print axioms entrywise_unique_of_exactly_one_zero

/-- For density eigenvalues (`0 ≤ p`), any two solutions agree off the
kernel--kernel block.  This is the full off-diagonal uniqueness statement;
nonnegativity is what rules out cancellation between two nonzero weights. -/
theorem entrywise_unique_of_not_both_zero {p : n → ℝ} {V L M : Matrix n n ℂ}
    (hp : ∀ i, 0 ≤ p i)
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    (hM : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * M i j = 2 * V i j)
    {i j : n} (hij : ¬ (p i = 0 ∧ p j = 0)) :
    L i j = M i j := by
  have hsum : p i + p j ≠ 0 := by
    intro h
    apply hij
    constructor <;> linarith [hp i, hp j]
  have hc : ((p i : ℂ) + (p j : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr hsum
  apply mul_left_cancel₀ hc
  exact (hL i j).trans (hM i j).symm

#print axioms entrywise_unique_of_not_both_zero

/-- A matrix supported on the kernel--kernel pairs of `p`. -/
def kernelBlock (p : n → ℝ) (K : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => if p i = 0 ∧ p j = 0 then K i j else 0

/-- Adding an arbitrary kernel--kernel block leaves every SLD equation
unchanged.  In particular the kernel--kernel block is genuinely free, not
merely undetected by the off-kernel uniqueness theorem. -/
theorem entrywise_add_kernelBlock {p : n → ℝ} {V L K : Matrix n n ℂ}
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j) (i j : n) :
    ((p i : ℂ) + (p j : ℂ)) * (L + kernelBlock p K) i j = 2 * V i j := by
  by_cases hij : p i = 0 ∧ p j = 0
  · rcases hij with ⟨hi, hj⟩
    have hV := hL i j
    simp [hi, hj] at hV
    simp [kernelBlock, hi, hj, hV]
  · simp [kernelBlock, hij, hL]

#print axioms entrywise_add_kernelBlock

/-- Exact parametrization of solution freedom: two solutions differ by the
kernel--kernel projection of their difference, and nowhere else. -/
theorem eq_add_kernelBlock_of_entrywise {p : n → ℝ} {V L M : Matrix n n ℂ}
    (hp : ∀ i, 0 ≤ p i)
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    (hM : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * M i j = 2 * V i j) :
    M = L + kernelBlock p (M - L) := by
  ext i j
  by_cases hij : p i = 0 ∧ p j = 0
  · simp [kernelBlock, hij]
  · have h := entrywise_unique_of_not_both_zero hp hL hM hij
    simp [kernelBlock, hij, h]

#print axioms eq_add_kernelBlock_of_entrywise

end AtlasB112Gap


/-! ## B119 — every index case of the card symbol, and the half-derivative conversion

Integrated from `.ultramath/smwu90bch/m15/B119General.lean`.
-/

/-!
# B119: the complete two-dimensional first-kind Christoffel formula

The pinned v7 card displays
`Γ_ij,k = ½(G_ik,j + G_jk,i − G_ij,k)` and `G_ij,k = ∂_k g_ij`.
Here `G` is the array of first derivatives at one point of the parameter chart.
No nondegeneracy is needed for these algebraic identities.

The index order in `cardChristoffel` below is exactly the card's.  In
particular, `G i j k` is the `k`-derivative of `g i j`, not the
`i`-derivative of `g j k`.
-/

namespace AtlasB119Gap

/-- The two coordinates in the card's witness are called `x` and `y`. -/
inductive Coord where
  | x
  | y
  deriving DecidableEq, Repr

open Coord

/-- The card's first-kind Christoffel symbol, in its own `G`-indexing. -/
noncomputable def cardChristoffel (G : Coord → Coord → Coord → ℝ)
    (i j k : Coord) : ℝ :=
  (1 / 2 : ℝ) * (G i k j + G j k i - G i j k)

/-- Conversion from the card's `G_ij,k = ∂_k g_ij` convention to an array
`D k i j = ∂_k g_ij`.  This makes the card's formula agree with the usual
`½(∂_j g_ik + ∂_i g_jk − ∂_k g_ij)` half-derivative expression. -/
theorem cardChristoffel_eq_halfDerivative
    (G D : Coord → Coord → Coord → ℝ)
    (hGD : ∀ i j k, G i j k = D k i j) (i j k : Coord) :
    cardChristoffel G i j k =
      (1 / 2 : ℝ) * (D j i k + D i j k - D k i j) := by
  simp only [cardChristoffel, hGD]

/-- All eight index combinations in two dimensions, expanded without using
symmetry of the metric.  Thus this is the full displayed formula, not only
its `(xx,y)` specialization. -/
theorem cardChristoffel_all_eight (G : Coord → Coord → Coord → ℝ) :
    cardChristoffel G x x x = (1 / 2 : ℝ) * G x x x ∧
    cardChristoffel G x x y = G x y x - (1 / 2 : ℝ) * G x x y ∧
    cardChristoffel G x y x =
      (1 / 2 : ℝ) * (G x x y + G y x x - G x y x) ∧
    cardChristoffel G x y y = (1 / 2 : ℝ) * G y y x ∧
    cardChristoffel G y x x = (1 / 2 : ℝ) * G x x y ∧
    cardChristoffel G y x y =
      (1 / 2 : ℝ) * (G y y x + G x y y - G y x y) ∧
    cardChristoffel G y y x = G y x y - (1 / 2 : ℝ) * G y y x ∧
    cardChristoffel G y y y = (1 / 2 : ℝ) * G y y y := by
  simp only [cardChristoffel]
  apply And.intro
  · ring
  apply And.intro
  · ring
  apply And.intro
  · trivial
  apply And.intro
  · ring
  apply And.intro
  · ring
  apply And.intro
  · trivial
  apply And.intro
  · ring
  ring

/-- The metric-symmetry hypothesis on derivative data, coordinate by
coordinate. -/
def MetricSymmetric (G : Coord → Coord → Coord → ℝ) : Prop :=
  ∀ i j k, G i j k = G j i k

/-- The usual simplification of the two mixed symbols uses symmetry of the
metric.  The eight-case theorem above deliberately does not assume it. -/
theorem cardChristoffel_xy_x_of_metricSymmetric
    (G : Coord → Coord → Coord → ℝ) (hG : MetricSymmetric G) :
    cardChristoffel G x y x = (1 / 2 : ℝ) * G x x y := by
  have h := hG x y x
  simp only [cardChristoffel]
  rw [h]
  ring

/-- Likewise `Γ_yx,y` reduces to one half of the `x`-derivative of `g_yy`. -/
theorem cardChristoffel_yx_y_of_metricSymmetric
    (G : Coord → Coord → Coord → ℝ) (hG : MetricSymmetric G) :
    cardChristoffel G y x y = (1 / 2 : ℝ) * G y y x := by
  have h := hG x y y
  simp only [cardChristoffel]
  rw [h]
  ring

/-- Symmetry of the two indices before the comma, for every index
combination, again requires precisely metric symmetry in the derivative
slot being used. -/
theorem cardChristoffel_swap_of_metricSymmetric
    (G : Coord → Coord → Coord → ℝ) (hG : MetricSymmetric G)
    (i j k : Coord) :
    cardChristoffel G i j k = cardChristoffel G j i k := by
  have h₁ := hG i k j
  have h₂ := hG j k i
  simp only [cardChristoffel]
  rw [h₁, h₂, hG i j k]
  ring

/-- The exact bridge from the three-index display to the coefficient of the
geodesic equation: `G_xy,x = ∂_x g_xy` and `G_xx,y = ∂_y g_xx`. -/
theorem card_three_index_display (G : Coord → Coord → Coord → ℝ) :
    cardChristoffel G x x y = G x y x - (1 / 2 : ℝ) * G x x y := by
  simp only [cardChristoffel]
  ring

/-- In the card's `G` notation, `x` is a Killing direction exactly when all
`x`-derivatives of metric entries vanish. -/
def KillingX (G : Coord → Coord → Coord → ℝ) : Prop :=
  ∀ i j, G i j x = 0

/-- The card's transverse coefficient follows from the Killing derivative
condition.  Pointwise `g_xy = 0` is not used, and no inverse metric is
needed because this is a first-kind symbol. -/
theorem card_transverse_coefficient_of_killingX
    (G : Coord → Coord → Coord → ℝ) (hx : KillingX G) :
    cardChristoffel G x x y = -(1 / 2 : ℝ) * G x x y := by
  rw [card_three_index_display, hx x y]
  ring

/-- Only the one actually occurring Killing component is needed for the
card's coefficient. -/
theorem card_transverse_coefficient
    (G : Coord → Coord → Coord → ℝ) (hx : G x y x = 0) :
    cardChristoffel G x x y = -(1 / 2 : ℝ) * G x x y := by
  rw [card_three_index_display, hx]
  ring

/-- The `(xx,y)` equation extracted from the all-eight expansion. -/
theorem cardChristoffel_all_eight_xx_y
    (G : Coord → Coord → Coord → ℝ) :
    cardChristoffel G x x y = G x y x - (1 / 2 : ℝ) * G x x y :=
  (cardChristoffel_all_eight G).2.1

#print axioms cardChristoffel_eq_halfDerivative
#print axioms cardChristoffel_all_eight
#print axioms cardChristoffel_xy_x_of_metricSymmetric
#print axioms cardChristoffel_yx_y_of_metricSymmetric
#print axioms cardChristoffel_swap_of_metricSymmetric
#print axioms card_three_index_display
#print axioms card_transverse_coefficient_of_killingX
#print axioms card_transverse_coefficient
#print axioms cardChristoffel_all_eight_xx_y

end AtlasB119Gap


/-! ## B207 — the extremal hole: the horizons merge and the rapidities vanish

Integrated from `.ultramath/smwu90bch/m9/B207Extremal.lean`.
-/
/-
B207: the extremal Reissner--Nordström endpoint.

The accepted development defines
  rPlus M Q  = M + sqrt (M^2 - Q^2),
  rMinus M Q = M - sqrt (M^2 - Q^2),
  rapidity Q r = log (r / Q),
and proves the displayed identities for 0 < Q < M.  This file keeps those
same definitions and treats Q = M.  No graph or Penrose-inequality assertion
is made.
-/

noncomputable section

namespace RelationalAtlas.B207Extremal

open Real Filter Topology

/-- The outer horizon, with the same formula as the accepted B207 section. -/
def rPlus (M Q : ℝ) : ℝ := M + sqrt (M ^ 2 - Q ^ 2)

/-- The inner horizon, with the same formula as the accepted B207 section. -/
def rMinus (M Q : ℝ) : ℝ := M - sqrt (M ^ 2 - Q ^ 2)

/-- The rapidity in the card's relation `r = Q exp τ`. -/
def rapidity (Q r : ℝ) : ℝ := log (r / Q)

/-- At the extremal endpoint the two horizon radii are both `M`. -/
theorem extremal_horizons_merge (M : ℝ) :
    rPlus M M = M ∧ rMinus M M = M ∧ rPlus M M = rMinus M M := by
  simp [rPlus, rMinus]

/-- The card's product formula degenerates to `r₊r₋ = M² = Q²`. -/
theorem extremal_horizon_product (M : ℝ) :
    rPlus M M * rMinus M M = M ^ 2 := by
  simp [rPlus, rMinus, sq]

/-- Both horizon rapidities exist and vanish at extremality. -/
theorem extremal_horizon_rapidities (M : ℝ) (hM : 0 < M) :
    rapidity M (rPlus M M) = 0 ∧ rapidity M (rMinus M M) = 0 := by
  simp [rapidity, rPlus, rMinus, ne_of_gt hM]

/-- In particular `τ₊ = -τ₋` remains true at the extremal endpoint. -/
theorem extremal_horizon_rapidities_opposite (M : ℝ) (hM : 0 < M) :
    rapidity M (rPlus M M) = -rapidity M (rMinus M M) := by
  rw [(extremal_horizon_rapidities M hM).1,
    (extremal_horizon_rapidities M hM).2, neg_zero]

/-- Both extremal horizons satisfy the displayed relation `r = Q exp τ`
with `Q = M` and `τ = 0`. -/
theorem extremal_radius_eq_exp_rapidity (M : ℝ) (hM : 0 < M) :
    rPlus M M = M * exp (rapidity M (rPlus M M)) ∧
      rMinus M M = M * exp (rapidity M (rMinus M M)) := by
  rw [(extremal_horizon_rapidities M hM).1,
    (extremal_horizon_rapidities M hM).2,
    (extremal_horizons_merge M).1, (extremal_horizons_merge M).2.1]
  norm_num

/-- The displayed cosh formula also remains valid at extremality, where it
becomes `(M + M²/M)/2 = M cosh 0 = M` at either horizon. -/
theorem extremal_radius_cosh_rapidity (M : ℝ) (hM : 0 < M) :
    (rPlus M M + M ^ 2 / rPlus M M) / 2 =
        M * cosh (rapidity M (rPlus M M)) ∧
      (rMinus M M + M ^ 2 / rMinus M M) / 2 =
        M * cosh (rapidity M (rMinus M M)) := by
  rw [(extremal_horizon_rapidities M hM).1,
    (extremal_horizon_rapidities M hM).2,
    (extremal_horizons_merge M).1, (extremal_horizons_merge M).2.1, cosh_zero]
  field_simp [ne_of_gt hM]
  norm_num

/-- The outer horizon is continuous through the nonextremal endpoint. -/
theorem tendsto_rPlus_extremal_left (M : ℝ) :
    Tendsto (fun Q : ℝ => rPlus M Q) (𝓝[<] M) (𝓝 M) := by
  have h : Continuous (fun Q : ℝ => rPlus M Q) := by
    unfold rPlus
    fun_prop
  simpa [rPlus] using (h.tendsto M).mono_left nhdsWithin_le_nhds

/-- The inner horizon has the same continuous extremal limit. -/
theorem tendsto_rMinus_extremal_left (M : ℝ) :
    Tendsto (fun Q : ℝ => rMinus M Q) (𝓝[<] M) (𝓝 M) := by
  have h : Continuous (fun Q : ℝ => rMinus M Q) := by
    unfold rMinus
    fun_prop
  simpa [rMinus] using (h.tendsto M).mono_left nhdsWithin_le_nhds

/-- The outer rapidity tends to zero as `Q ↑ M`; in particular the strict
nonextremal hypothesis is not needed for the limiting value. -/
theorem tendsto_outer_rapidity_extremal_left (M : ℝ) (hM : 0 < M) :
    Tendsto (fun Q : ℝ => rapidity Q (rPlus M Q)) (𝓝[<] M) (𝓝 0) := by
  have hr : Tendsto (fun Q : ℝ => rPlus M Q) (𝓝[<] M) (𝓝 M) :=
    tendsto_rPlus_extremal_left M
  have hQ : Tendsto (fun Q : ℝ => Q) (𝓝[<] M) (𝓝 M) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun Q : ℝ => rPlus M Q / Q) (𝓝[<] M) (𝓝 (M / M)) :=
    hr.div hQ (ne_of_gt hM)
  have hlog := hdiv.log (div_ne_zero (ne_of_gt hM) (ne_of_gt hM))
  simpa [rapidity, ne_of_gt hM] using hlog

/-- The inner rapidity also tends continuously to zero as `Q ↑ M`. -/
theorem tendsto_inner_rapidity_extremal_left (M : ℝ) (hM : 0 < M) :
    Tendsto (fun Q : ℝ => rapidity Q (rMinus M Q)) (𝓝[<] M) (𝓝 0) := by
  have hr : Tendsto (fun Q : ℝ => rMinus M Q) (𝓝[<] M) (𝓝 M) :=
    tendsto_rMinus_extremal_left M
  have hQ : Tendsto (fun Q : ℝ => Q) (𝓝[<] M) (𝓝 M) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun Q : ℝ => rMinus M Q / Q) (𝓝[<] M) (𝓝 (M / M)) :=
    hr.div hQ (ne_of_gt hM)
  have hlog := hdiv.log (div_ne_zero (ne_of_gt hM) (ne_of_gt hM))
  simpa [rapidity, ne_of_gt hM] using hlog

#print axioms RelationalAtlas.B207Extremal.extremal_horizons_merge
#print axioms RelationalAtlas.B207Extremal.extremal_horizon_product
#print axioms RelationalAtlas.B207Extremal.extremal_horizon_rapidities
#print axioms RelationalAtlas.B207Extremal.extremal_horizon_rapidities_opposite
#print axioms RelationalAtlas.B207Extremal.extremal_radius_eq_exp_rapidity
#print axioms RelationalAtlas.B207Extremal.extremal_radius_cosh_rapidity
#print axioms RelationalAtlas.B207Extremal.tendsto_rPlus_extremal_left
#print axioms RelationalAtlas.B207Extremal.tendsto_rMinus_extremal_left
#print axioms RelationalAtlas.B207Extremal.tendsto_outer_rapidity_extremal_left
#print axioms RelationalAtlas.B207Extremal.tendsto_inner_rapidity_extremal_left

end RelationalAtlas.B207Extremal


/-! ## B156 — the pole indices as an exact winding, and their sum

Integrated from `.ultramath/smwu90bch/m7/B156.lean`.
-/

/-!
# B156 — winding of the two meridian-pole models

The pinned v7 card (SHA256
`f39939fb79559a8f61e8e7809912a59895e181a25571e2619248910229a5e6bc`)
gives the local model `(cos φ, sin φ)` and says that it winds once around each
pole.  We model that direction as a point of `Circle`.  Its winding is computed
by Mathlib's fundamental-group winding number after transport by the standard
homeomorphism `AddCircle (2 * π) ≃ₜ Circle`.

Both poles use the same displayed local model, in an oriented chart at the
pole.  No global extension or Poincare--Hopf theorem is assumed or proved.
-/

open unitInterval
open scoped Real

namespace AtlasB156

local instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The winding number of a loop in the complex unit circle, transported to
`AddCircle (2 * π)` by the inverse of the standard exponential homeomorphism. -/
noncomputable def circlePathWinding {x : Circle} (γ : Path x x) : ℤ :=
  AddCircle.windingNumber
    (.of (.mk (γ.map AddCircle.homeomorphCircle'.symm.continuous)))

/-- The card's local meridian model around one pole, parametrized on the unit
interval by `φ = 2πt`. -/
noncomputable def meridianPoleLoop : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * π))
  source' := by simp
  target' := by simp
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)

/-- At parameter `t`, the displayed local direction really is
`(cos(2πt), sin(2πt))`, written as a complex number. -/
theorem meridianPoleLoop_model (t : unitInterval) :
    ((meridianPoleLoop t : Circle) : ℂ) =
      (Real.cos ((t : ℝ) * (2 * π)) : ℂ) +
        (Real.sin ((t : ℝ) * (2 * π)) : ℂ) * Complex.I := by
  simp [meridianPoleLoop, Circle.coe_exp, Complex.exp_mul_I]

/-- The index of either pole's displayed local meridian model is `+1`. -/
theorem meridianPoleLoop_winding : circlePathWinding meridianPoleLoop = 1 := by
  unfold circlePathWinding
  apply Int.cast_injective (α := ℝ)
  rw [AddCircle.windingNumber_eq_div
    (γ := meridianPoleLoop.map AddCircle.homeomorphCircle'.symm.continuous)
    (f := ⟨fun t : unitInterval => (t : ℝ) * (2 * π), by fun_prop⟩)]
  · simp [show (2 : ℝ) * π ≠ 0 by positivity]
  · ext t
    change (↑((t : ℝ) * (2 * π)) : AddCircle (2 * π)) =
      AddCircle.homeomorphCircle'.symm (Circle.exp ((t : ℝ) * (2 * π)))
    rw [← AddCircle.homeomorphCircle'_apply_mk]
    simp

/-- The two pole labels in the card. -/
inductive Pole where
  | north
  | south
  deriving DecidableEq

/-- The local index attached to a pole.  The card supplies the same displayed
model in an oriented punctured chart about each pole. -/
noncomputable def poleIndex : Pole → ℤ
  | .north => circlePathWinding meridianPoleLoop
  | .south => circlePathWinding meridianPoleLoop

theorem north_index : poleIndex .north = 1 := meridianPoleLoop_winding

theorem south_index : poleIndex .south = 1 := meridianPoleLoop_winding

/-- **B156 finite pole count.** The two displayed pole windings add to `2`,
the Euler characteristic of `S²`. -/
theorem pole_sum_eq_euler_characteristic :
    poleIndex .north + poleIndex .south = 2 := by
  rw [north_index, south_index]
  norm_num

/-- The displayed direction returns with sign `+1`, not merely with the same
unoriented line. -/
theorem meridianPoleLoop_sign_return :
    Circle.exp (2 * π) = Circle.exp 0 := by simp

#print axioms AtlasB156.meridianPoleLoop_model
#print axioms AtlasB156.meridianPoleLoop_winding
#print axioms AtlasB156.north_index
#print axioms AtlasB156.south_index
#print axioms AtlasB156.pole_sum_eq_euler_characteristic
#print axioms AtlasB156.meridianPoleLoop_sign_return

end AtlasB156


/-! ## B158 — equality exactly at complex parallelism

Integrated from `.ultramath/smwu90bch/m14/B158Equality.lean`.
-/

/-!
# B158: the weak-value bound and its exact equality case

The card states `p₀ |A_w|² ≤ ⟨i|A²|i⟩` and adds that equality holds when
`|f⟩ ∥ A|i⟩`.  The theorem below proves the stronger biconditional: under the
card's hypotheses, equality holds **exactly** when `A i` is a complex scalar
multiple of `f`.  The scalar is allowed to be zero, which is necessary for the
degenerate case `A i = 0`.

The proof is the equality case of Cauchy--Schwarz for the vectors `f` and
`A i`.  No statement about postselection dynamics is made.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas
namespace B158

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **B158, exact equality case.**  Under the card's normalization,
Hermiticity, and nonzero-overlap hypotheses, the probability-weighted weak
value saturates its second-moment bound if and only if `A i` and `f` lie on
one complex line.  The initial-state normalization is retained from the card,
although this equality characterization does not use it. -/
theorem weak_value_bound_eq_iff_complex_parallel
    (f i : E) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (_hi : ‖i‖ = 1) (hf : ‖f‖ = 1) (hfi : ⟪f, i⟫_ℂ ≠ 0) :
    ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 =
        (⟪i, A (A i)⟫_ℂ).re ↔
      ∃ c : ℂ, A i = c • f := by
  have hfi_norm : ‖⟪f, i⟫_ℂ‖ ≠ 0 := norm_ne_zero_iff.mpr hfi
  have hweighted :
      ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 =
        ‖⟪f, A i⟫_ℂ‖ ^ 2 := by
    rw [norm_div]
    field_simp
  have hmoment : (⟪i, A (A i)⟫_ℂ).re = ‖A i‖ ^ 2 := by
    rw [← hA i (A i)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (A i)
  rw [hweighted, hmoment, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hf0 : f ≠ 0 := by
    intro h
    subst f
    simp at hf
  constructor
  · intro heq
    have hcs : ‖⟪f, A i⟫_ℂ‖ = ‖f‖ * ‖A i‖ := by
      simpa [hf] using heq
    have hparallel : f = 0 ∨ ∃ c : ℂ, A i = c • f :=
      ((norm_inner_eq_norm_tfae ℂ f (A i)).out 1 3).mp hcs
    exact hparallel.resolve_left hf0
  · rintro ⟨c, hc⟩
    have hparallel : f = 0 ∨ ∃ c : ℂ, A i = c • f := Or.inr ⟨c, hc⟩
    have hcs : ‖⟪f, A i⟫_ℂ‖ = ‖f‖ * ‖A i‖ :=
      ((norm_inner_eq_norm_tfae ℂ f (A i)).out 1 3).mpr hparallel
    simpa [hf] using hcs

end B158
end RelationalAtlas

#print axioms RelationalAtlas.B158.weak_value_bound_eq_iff_complex_parallel


/-! ## B77 — the two threshold conditions are different objects

Integrated from `.ultramath/smwu90bch/m16/B77Kissing.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace B77

open scoped RealInnerProductSpace
open InnerProductGeometry

/-- The rank-one linear map `v ↦ ⟪u,v⟫ u`.  For a unit `u` this is the
orthogonal projector onto the real line spanned by `u`. -/
def lineProjector {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) : V →ₗ[ℝ] V where
  toFun v := ⟪u, v⟫ • u
  map_add' v w := by simp [inner_add_right, add_smul]
  map_smul' c v := by
    change (⟪u, c • v⟫ : ℝ) • u = c • (⟪u, v⟫ • u)
    rw [real_inner_smul_right, mul_smul]

/-- Sixty degrees is `π / 3`; its squared sine is exactly three quarters. -/
theorem sin_sq_sixty_degrees : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 :=
  Real.sq_sin_pi_div_three

/-- The threshold inequality at sixty degrees, stated without the card's
extremal-threshold shorthand. -/
theorem sin_sq_sixty_degrees_ge_iff (epsilon : ℝ) :
    Real.sin (Real.pi / 3) ^ 2 ≥ epsilon ↔ epsilon ≤ 3 / 4 := by
  rw [sin_sq_sixty_degrees]

/-- For unit vectors, the cosine of their unoriented angle is their dot product. -/
theorem sin_angle_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.sin (angle u v) ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
  have hcos : Real.cos (angle u v) = ⟪u, v⟫ := by
    symm
    exact inner_eq_cos_angle_of_norm_eq_one hu hv
  have h := Real.sin_sq_add_cos_sq (angle u v)
  rw [hcos] at h
  nlinarith

/-- The oriented kissing-code condition: unit directions are at least sixty
degrees apart exactly when their dot product is at most one half. -/
theorem sixty_degree_separation_iff_dot_le_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.pi / 3 ≤ angle u v ↔ ⟪u, v⟫ ≤ 1 / 2 := by
  have hcos : Real.cos (angle u v) = ⟪u, v⟫ := by
    symm
    exact inner_eq_cos_angle_of_norm_eq_one hu hv
  constructor
  · intro h
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity) (angle_le_pi u v) h
    rw [Real.cos_pi_div_three, hcos] at hc
    exact hc
  · intro h
    by_contra hn
    have hlt : angle u v < Real.pi / 3 := lt_of_not_ge hn
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
      (angle_nonneg u v) (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hlt
    rw [Real.cos_pi_div_three, hcos] at hc
    linarith

/-- The projector/line condition: `sin²θ ≥ 3/4` is exactly `|dot| ≤ 1/2`. -/
theorem sin_sq_threshold_iff_abs_dot_le_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    3 / 4 ≤ Real.sin (angle u v) ^ 2 ↔ |⟪u, v⟫| ≤ 1 / 2 := by
  rw [sin_angle_sq u v hu hv]
  constructor
  · intro h
    apply abs_le_of_sq_le_sq _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  · intro h
    have hs : ⟪u, v⟫ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [sq_le_sq]
      simpa using h
    nlinarith

/-- Antipodal unit vectors pass the one-sided kissing-code test. -/
theorem antipodal_dot_le_half {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (u : V) (hu : ‖u‖ = 1) :
    ⟪u, -u⟫ ≤ 1 / 2 := by
  rw [inner_neg_right, inner_self_eq_one_of_norm_eq_one hu]
  norm_num

/-- Antipodal unit vectors fail the two-sided projector/line test. -/
theorem antipodal_not_abs_dot_le_half {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (u : V) (hu : ‖u‖ = 1) :
    ¬ |⟪u, -u⟫| ≤ 1 / 2 := by
  rw [inner_neg_right, inner_self_eq_one_of_norm_eq_one hu]
  norm_num

/-- Antipodes have the same rank-one line projector. -/
theorem lineProjector_neg {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (u : V) :
    lineProjector (-u) = lineProjector u := by
  ext v
  simp [lineProjector]

/-- The sharp packaged counterexample: the one-sided condition does not ensure
that the associated projectors differ, and the absolute-value condition is the
one that rejects antipodes. -/
theorem antipodal_counterexample {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (u : V) (hu : ‖u‖ = 1) :
    ⟪u, -u⟫ ≤ 1 / 2 ∧ ¬ |⟪u, -u⟫| ≤ 1 / 2 ∧
      lineProjector (-u) = lineProjector u :=
  ⟨antipodal_dot_le_half u hu, antipodal_not_abs_dot_le_half u hu,
    lineProjector_neg u⟩

/-- A concrete non-vacuous instance: the distinct vectors `1` and `-1`
pass and fail the respective tests, yet define exactly the same projector. -/
theorem real_antipodal_counterexample :
    (1 : ℝ) ≠ -1 ∧
    ⟪(1 : ℝ), -1⟫ ≤ 1 / 2 ∧ ¬ |⟪(1 : ℝ), -1⟫| ≤ 1 / 2 ∧
      lineProjector (-1 : ℝ) = lineProjector 1 := by
  exact ⟨by norm_num, antipodal_counterexample 1 (by norm_num)⟩

#print axioms sin_sq_sixty_degrees
#print axioms sin_sq_sixty_degrees_ge_iff
#print axioms sin_angle_sq
#print axioms sixty_degree_separation_iff_dot_le_half
#print axioms sin_sq_threshold_iff_abs_dot_le_half
#print axioms antipodal_dot_le_half
#print axioms antipodal_not_abs_dot_le_half
#print axioms lineProjector_neg
#print axioms antipodal_counterexample
#print axioms real_antipodal_counterexample

end B77


/-! ## B93 — the count is a sign sum, and invariance needs the full line

Integrated from `.ultramath/smwu90bch/m11/B93.lean`.
-/

/-!
# B93: finite signed spectral count across a directed cut

The plane is `ℝ × ℝ`.  For a cut direction `u`, `side u z` is positive
exactly on the right of the directed line through `u`; for example, with
`u = (0,1)` (the upward imaginary axis), `(1,0)` has positive side.  Thus
`eta` below is literally the sum of the card's `+1`/`-1` contributions.
-/

namespace AtlasB93

noncomputable section

open scoped BigOperators
open Set

abbrev Plane := ℝ × ℝ

/-- Positive on the right of the directed line spanned by `u`. -/
def side (u z : Plane) : ℝ := u.2 * z.1 - u.1 * z.2

/-- The contribution of an eigenvalue: right `+1`, left `-1`, on the line `0`. -/
def contribution (x : ℝ) : ℤ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/-- The finite signed count over eigenvalues, repeated according to multiplicity. -/
def eta {n : ℕ} (z : Fin n → Plane) (u : Plane) : ℤ :=
  ∑ i, contribution (side u (z i))

/-- Number of eigenvalues strictly to the right of the directed cut. -/
def rightCount {n : ℕ} (z : Fin n → Plane) (u : Plane) : ℕ :=
  (Finset.univ.filter fun i => 0 < side u (z i)).card

/-- Number of eigenvalues strictly to the left of the directed cut. -/
def leftCount {n : ℕ} (z : Fin n → Plane) (u : Plane) : ℕ :=
  (Finset.univ.filter fun i => side u (z i) < 0).card

/-- The signed sum is exactly the card's right-minus-left display. -/
theorem eta_eq_right_sub_left {n : ℕ} (z : Fin n → Plane) (u : Plane) :
    eta z u = (rightCount z u : ℤ) - (leftCount z u : ℤ) := by
  classical
  let r : Fin n → ℤ := fun i => if 0 < side u (z i) then 1 else 0
  let l : Fin n → ℤ := fun i => if side u (z i) < 0 then 1 else 0
  have hpoint : ∀ i, contribution (side u (z i)) = r i - l i := by
    intro i
    by_cases hr : 0 < side u (z i)
    · have hnl : ¬ side u (z i) < 0 := by linarith
      simp [r, l, contribution, hr, hnl]
    · by_cases hl : side u (z i) < 0
      · simp [r, l, contribution, hr, hl]
      · simp [r, l, contribution, hr, hl]
  calc
    eta z u = ∑ i, (r i - l i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = (∑ i, r i) - ∑ i, l i := by
      exact Finset.sum_sub_distrib r l
    _ = (rightCount z u : ℤ) - (leftCount z u : ℤ) := by
      simp [r, l, rightCount, leftCount]
#print axioms AtlasB93.eta_eq_right_sub_left

/-- A straight motion of the (not necessarily normalized) cut direction. -/
def segment (u v : Plane) (t : ℝ) : Plane :=
  ((1 - t) * u.1 + t * v.1, (1 - t) * u.2 + t * v.2)

@[simp] theorem segment_zero (u v : Plane) : segment u v 0 = u := by
  simp [segment]
#print axioms AtlasB93.segment_zero

@[simp] theorem segment_one (u v : Plane) : segment u v 1 = v := by
  simp [segment]
#print axioms AtlasB93.segment_one

/-- Side is affine during the straight motion. -/
theorem side_segment (u v z : Plane) (t : ℝ) :
    side (segment u v t) z = (1 - t) * side u z + t * side v z := by
  simp only [side, segment]
  ring
#print axioms AtlasB93.side_segment

/-- If an affine side function has no zero on `[0,1]`, its endpoint signs agree. -/
theorem sideSign_eq_of_segment_nonzero {a b : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) * a + t * b ≠ 0) :
    contribution a = contribution b := by
  have ha : a ≠ 0 := by
    intro ha
    exact h 0 (by norm_num) (by simp [ha])
  have hb : b ≠ 0 := by
    intro hb
    exact h 1 (by norm_num) (by simp [hb])
  have hab : 0 < a * b := by
    by_contra hn
    have habneg : a * b < 0 := lt_of_le_of_ne (le_of_not_gt hn) (mul_ne_zero ha hb)
    let d : ℝ := |a| + |b|
    let t : ℝ := |a| / d
    have had : 0 < |a| := abs_pos.mpr ha
    have hbd : 0 < |b| := abs_pos.mpr hb
    have hd : 0 < d := add_pos had hbd
    have ht0 : 0 ≤ t := div_nonneg (abs_nonneg a) (le_of_lt hd)
    have ht1 : t ≤ 1 := by
      apply (div_le_one hd).mpr
      exact le_add_of_nonneg_right (abs_nonneg b)
    apply h t ⟨ht0, ht1⟩
    dsimp [t]
    field_simp [ne_of_gt hd]
    dsimp [d]
    rcases (mul_neg_iff).mp habneg with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [abs_of_pos ha', abs_of_neg hb']
      ring
    · rw [abs_of_neg ha', abs_of_pos hb']
      ring
  rcases (mul_pos_iff).mp hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  · simp [contribution, ha', hb']
  · simp [contribution, ha', hb', not_lt_of_ge (le_of_lt ha'),
      not_lt_of_ge (le_of_lt hb')]
#print axioms AtlasB93.sideSign_eq_of_segment_nonzero

/-- **Finite B93 invariance theorem with the sharp line-gap hypothesis.**

During the straight motion from `u` to `v`, no eigenvalue may lie on the full
line of any moving cut.  Under this hypothesis every contribution is fixed,
hence the right-minus-left count is fixed.  Repeated indices are permitted and
therefore record algebraic multiplicity. -/
theorem eta_eq_of_line_gap {n : ℕ} (z : Fin n → Plane) (u v : Plane)
    (hgap : ∀ i t, t ∈ Icc (0 : ℝ) 1 → side (segment u v t) (z i) ≠ 0) :
    eta z u = eta z v := by
  unfold eta
  apply Finset.sum_congr rfl
  intro i hi
  apply sideSign_eq_of_segment_nonzero
  intro t ht
  rw [← side_segment]
  exact hgap i t ht
#print axioms AtlasB93.eta_eq_of_line_gap

/-- Membership in the forward ray, `_ = c • u` with `c > 0`. -/
def onRay (u z : Plane) : Prop := ∃ c : ℝ, 0 < c ∧ z = c • u

/-- One eigenvalue `1` in the complex plane. -/
def singleSpectrum : Fin 1 → Plane := fun _ => (1, 0)

/-- The two cuts point into the left half-plane, just above and below `-1`. -/
def upperAntipodalCut : Plane := (-1, 1)
def lowerAntipodalCut : Plane := (-1, -1)

/-- Orientation check: the upward imaginary cut counts `1` as right, as in B93. -/
theorem upward_cut_single_eta : eta singleSpectrum (0, 1) = 1 := by
  norm_num [eta, contribution, side, singleSpectrum]
#print axioms AtlasB93.upward_cut_single_eta

/-- The moving forward ray never sweeps the eigenvalue `1`: its first coordinate
is always `-1`, whereas that eigenvalue has first coordinate `1`. -/
theorem antipodal_forward_ray_never_sweeps_eigenvalue :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ¬ onRay (segment upperAntipodalCut lowerAntipodalCut t) (singleSpectrum 0) := by
  intro t ht hmem
  rcases hmem with ⟨c, hc, heq⟩
  have hre : (segment upperAntipodalCut lowerAntipodalCut t).1 = -1 := by
    simp [segment, upperAntipodalCut, lowerAntipodalCut]
    ring
  have hfirst := congrArg Prod.fst heq
  change (1 : ℝ) = c * (segment upperAntipodalCut lowerAntipodalCut t).1 at hfirst
  rw [hre] at hfirst
  nlinarith
#print axioms AtlasB93.antipodal_forward_ray_never_sweeps_eigenvalue

/-- Nevertheless, at the middle of the motion the *full* directed line contains
that eigenvalue, so the sharper line-gap hypothesis is exactly what fails. -/
theorem antipodal_middle_on_cut_line :
    side (segment upperAntipodalCut lowerAntipodalCut (1 / 2 : ℝ))
      (singleSpectrum 0) = 0 := by
  norm_num [side, segment, upperAntipodalCut, lowerAntipodalCut, singleSpectrum]
#print axioms AtlasB93.antipodal_middle_on_cut_line

/-- The one-sided ray-gap reading does not imply invariance: the contribution
changes from right to left and `eta` jumps by `2`, with no forward-ray sweep. -/
theorem antipodal_eta_jumps_without_forward_ray_sweep :
    eta singleSpectrum upperAntipodalCut = 1 ∧
    eta singleSpectrum lowerAntipodalCut = -1 ∧
    eta singleSpectrum upperAntipodalCut - eta singleSpectrum lowerAntipodalCut = 2 := by
  norm_num [eta, contribution, side, singleSpectrum,
    upperAntipodalCut, lowerAntipodalCut]
#print axioms AtlasB93.antipodal_eta_jumps_without_forward_ray_sweep

end
end AtlasB93


/-! ## B60 — saturation and complex parallelism in every dimension

Integrated from `.ultramath/smwu90bch/m13/B60General.lean`.
-/

/-!
# B60: the general-dimensional equality criterion

The two vectors below are the already projected tangent vectors.  The final
corollaries also spell out the projector model `u = (1 - P)x`, `v = (1 - P)y`.
The normalization is the one in the card: `g` is the real Gram matrix and
`Ω = 2 Im ⟪u,v⟫`.  No restriction on the rank of `P` is needed.

The unrestricted equality criterion is symmetric complex collinearity:
`u = 0` or `v = c • u`.  If the asymmetric phrase "`u` and `v` are
complex-parallel" means only the second alternative, its converse requires
`u ≠ 0`; the final theorem gives the degenerate counterexample.
-/

noncomputable section

open Matrix

namespace B60General

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hermitian overlap, conjugate-linear in its first argument. -/
def overlap (u v : E) : ℂ := inner ℂ u v

/-- The real two-direction quantum-metric Gram matrix. -/
def gram (u v : E) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![‖u‖ ^ 2, (overlap u v).re;
     (overlap u v).re, ‖v‖ ^ 2]

/-- Curvature in the normalization for which saturation is `|Ω|² = 4 det g`. -/
def omega (u v : E) : ℝ := 2 * (overlap u v).im

/-- `v` lies on the complex line spanned by `u`. -/
def ComplexParallel (u v : E) : Prop := ∃ c : ℂ, v = c • u

/-- Symmetric complex collinearity, including every zero-vector case. -/
def ComplexCollinear (u v : E) : Prop := u = 0 ∨ ComplexParallel u v

/-- The exact defect is four times the Cauchy--Schwarz defect. -/
theorem saturation_defect (u v : E) :
    4 * (gram u v).det - |omega u v| ^ 2 =
      4 * ((‖u‖ * ‖v‖) ^ 2 - ‖overlap u v‖ ^ 2) := by
  rw [sq_abs]
  simp [gram, omega, overlap, Matrix.det_fin_two, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- Saturation is exactly equality in complex Cauchy--Schwarz. -/
theorem saturation_iff_norm_inner (u v : E) :
    |omega u v| ^ 2 = 4 * (gram u v).det ↔
      ‖overlap u v‖ = ‖u‖ * ‖v‖ := by
  constructor
  · intro h
    have hs : (‖u‖ * ‖v‖) ^ 2 = ‖overlap u v‖ ^ 2 := by
      nlinarith [saturation_defect u v]
    exact ((sq_eq_sq₀ (mul_nonneg (norm_nonneg u) (norm_nonneg v))
      (norm_nonneg (overlap u v))).mp hs).symm
  · intro h
    have hs : (‖u‖ * ‖v‖) ^ 2 = ‖overlap u v‖ ^ 2 := by rw [h]
    nlinarith [saturation_defect u v]

/-- **General equality criterion, zero cases included.** -/
theorem saturation_iff_complexCollinear (u v : E) :
    |omega u v| ^ 2 = 4 * (gram u v).det ↔ ComplexCollinear u v := by
  rw [saturation_iff_norm_inner]
  exact (norm_inner_eq_norm_tfae ℂ u v).out 1 3

/-- **General converse.** Complex parallelism forces saturation in every
complex inner-product space, without any nonzero or rank hypothesis. -/
theorem saturation_of_complexParallel {u v : E} (h : ComplexParallel u v) :
    |omega u v| ^ 2 = 4 * (gram u v).det :=
  (saturation_iff_complexCollinear u v).mpr (Or.inr h)

/-- **General-dimensional sharp converse.** When the first projected tangent
is nonzero, saturation is equivalent to `v = c • u` for some complex scalar. -/
theorem saturation_iff_complexParallel {u v : E} (hu : u ≠ 0) :
    |omega u v| ^ 2 = 4 * (gram u v).det ↔ ComplexParallel u v := by
  rw [saturation_iff_complexCollinear]
  exact or_iff_right hu

/-- Turn an unprojected tangent coordinate vector into a tangent of the
complement of `P`. -/
def projected {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 ((1 - P).mulVec x)

/-- **B60 general converse for projected tangents of an arbitrary-rank band.**
The Hermitian and idempotence hypotheses are the card's band hypotheses;
`P.rank = k` records the rank explicitly.  The proof needs none of the three
because the algebraic identity holds for the two output vectors as given. -/
theorem projected_saturation_of_complexParallel {n k : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hPherm : Pᴴ = P) (hPid : P * P = P)
    (hrank : P.rank = k) (x y : Fin n → ℂ)
    (hparallel : ComplexParallel (projected P x) (projected P y)) :
    |omega (projected P x) (projected P y)| ^ 2 =
      4 * (gram (projected P x) (projected P y)).det :=
  saturation_of_complexParallel hparallel

/-- The full general-`n`, arbitrary-`k` equality criterion for projected
vectors.  The sole added hypothesis is nonvanishing of the first output. -/
theorem projected_saturation_iff_complexParallel {n k : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hPherm : Pᴴ = P) (hPid : P * P = P)
    (hrank : P.rank = k) (x y : Fin n → ℂ)
    (hx : projected P x ≠ 0) :
    |omega (projected P x) (projected P y)| ^ 2 =
        4 * (gram (projected P x) (projected P y)).det ↔
      ComplexParallel (projected P x) (projected P y) :=
  saturation_iff_complexParallel hx

/-- The nonzero hypothesis in the asymmetric converse cannot be deleted:
`u = 0`, `v ≠ 0` saturates but is not of the form `v = c • u`. -/
theorem zero_first_tangent_counterexample :
    ∃ u v : EuclideanSpace ℂ (Fin 1),
      |omega u v| ^ 2 = 4 * (gram u v).det ∧ ¬ ComplexParallel u v := by
  let u : EuclideanSpace ℂ (Fin 1) := 0
  let v : EuclideanSpace ℂ (Fin 1) := !₂[(1 : ℂ)]
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrArg (fun w : EuclideanSpace ℂ (Fin 1) => w 0) h
    norm_num [v] at h0
  have hsat : |omega u v| ^ 2 = 4 * (gram u v).det :=
    (saturation_iff_complexCollinear u v).mpr (Or.inl rfl)
  refine ⟨u, v, hsat, ?_⟩
  rintro ⟨c, hc⟩
  apply hv
  rw [hc]
  simp [u]

end B60General

#print axioms B60General.saturation_defect
#print axioms B60General.saturation_iff_norm_inner
#print axioms B60General.saturation_iff_complexCollinear
#print axioms B60General.saturation_of_complexParallel
#print axioms B60General.saturation_iff_complexParallel
#print axioms B60General.projected_saturation_of_complexParallel
#print axioms B60General.projected_saturation_iff_complexParallel
#print axioms B60General.zero_first_tangent_counterexample


/-! ## B15 — the 1/(2√2) constant belongs to the square root, not to S

Integrated from `.ultramath/smwu90bch/m4/B15Metric.lean`.
-/

/-!
# B15: the local constant belongs to `√S`, not to the raw comparator

The pinned v7 card says `√S → d_R/(2√2)` and its explanation says
`S ≈ d_R²/8`.  This file proves the corresponding finite-spectrum statement.
It also evaluates the literal raw-comparator reading of the older local HTML.
-/

open Filter Set
open scoped Topology BigOperators

namespace B15Metric
noncomputable section

/-- The scalar log-determinant comparator on positive real numbers. -/
noncomputable def scalarS (a b : ℝ) : ℝ :=
  Real.log ((a + b) / 2) - Real.log a / 2 - Real.log b / 2

/-- The exact scalar comparator along `1 ↦ exp (2x)`. -/
noncomputable def logCosh (x : ℝ) : ℝ := Real.log (Real.cosh x)

/-- Exact evaluation of the raw comparator along the scalar affine geodesic. -/
lemma scalarS_one_exp_two (x : ℝ) : scalarS 1 (Real.exp (2 * x)) = logCosh x := by
  have htwo : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  have hinv : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have hfactor : (1 + Real.exp (2 * x)) / 2 = Real.cosh x * Real.exp x := by
    rw [htwo]
    calc
      (1 + Real.exp x * Real.exp x) / 2 =
          (Real.exp (-x) * Real.exp x + Real.exp x * Real.exp x) / 2 := by rw [hinv]
      _ = ((Real.exp x + Real.exp (-x)) / 2) * Real.exp x := by ring
      _ = Real.cosh x * Real.exp x := by rw [Real.cosh_eq]
  simp only [scalarS, Real.log_one, zero_div, sub_zero, Real.log_exp]
  rw [hfactor, Real.log_mul (Real.cosh_pos x).ne' (Real.exp_pos x).ne', Real.log_exp]
  simp only [logCosh]
  ring

lemma hasDerivAt_logCosh (x : ℝ) :
    HasDerivAt logCosh (Real.tanh x) x := by
  change HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

lemma deriv_logCosh : deriv logCosh = Real.tanh := by
  funext x
  exact (hasDerivAt_logCosh x).deriv

lemma hasDerivAt_tanh_zero : HasDerivAt Real.tanh 1 0 := by
  have h := (Real.hasDerivAt_sinh 0).div (Real.hasDerivAt_cosh 0) (Real.cosh_pos 0).ne'
  convert h using 1
  · funext x
    exact Real.tanh_eq_sinh_div_cosh x
  · norm_num

lemma hasDerivAt_deriv_logCosh_zero : HasDerivAt (deriv logCosh) 1 0 := by
  rw [deriv_logCosh]
  exact hasDerivAt_tanh_zero

lemma iteratedDeriv_two_logCosh : iteratedDeriv 2 logCosh 0 = 1 := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    hasDerivAt_deriv_logCosh_zero.deriv]

lemma contDiff_logCosh : ContDiff ℝ 2 logCosh := by
  exact Real.contDiff_cosh.log (fun x => (Real.cosh_pos x).ne')

lemma taylor_logCosh (x : ℝ) :
    taylorWithinEval logCosh 2 Set.univ 0 x = x ^ 2 / 2 := by
  simp [taylorWithinEval_succ, logCosh, iteratedDerivWithin_univ,
    iteratedDeriv_one, deriv_logCosh, iteratedDeriv_two_logCosh]
  ring

/-- The second-order normalization of the scalar comparator. -/
lemma tendsto_logCosh_div_sq :
    Tendsto (fun x => logCosh x / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
  have h₀ := Real.taylor_tendsto (f := logCosh) (n := 2) (s := Set.univ)
    (x₀ := 0) convex_univ (mem_univ 0) contDiff_logCosh.contDiffOn
  simp only [nhdsWithin_univ, sub_zero, taylor_logCosh] at h₀
  have h := h₀.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hh : Tendsto (fun x => (logCosh x - x ^ 2 / 2) / x ^ 2 + 1 / 2)
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by simpa using h.add_const (1 / 2 : ℝ)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change x ≠ 0 at hx
  field_simp [hx]
  ring



lemma tendsto_logCosh_scaled_div_sq (a : ℝ) :
    Tendsto (fun t => logCosh (a * t / 2) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (a ^ 2 / 8)) := by
  by_cases ha : a = 0
  · subst a
    simp [logCosh]
  · have hf : HasDerivAt (fun t : ℝ => a * t / 2) (a / 2) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).const_mul a).div_const 2 using 1
      · funext t
        rfl
      · ring
    have hmap : Tendsto (fun t : ℝ => a * t / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
      simpa using hf.tendsto_nhdsNE (by exact div_ne_zero ha (by norm_num))
    have hc := tendsto_logCosh_div_sq.comp hmap
    have hh := hc.const_mul (a ^ 2 / 4)
    have hconst : (a ^ 2 / 4) * (1 / 2 : ℝ) = a ^ 2 / 8 := by ring
    rw [hconst] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t ≠ 0 at ht
    have hat : a * t / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha ht) (by norm_num)
    change (a ^ 2 / 4) * (logCosh (a * t / 2) / (a * t / 2) ^ 2) =
      logCosh (a * t / 2) / t ^ 2
    field_simp [ht, hat]
    ring

variable {ι : Type*} [Fintype ι]

/-- Finite-spectrum form of the comparator along the affine geodesic
`I ↦ diag (exp (t * h i))`.  The parameter `h` is the initial logarithmic
direction. -/
noncomputable def spectralS (h : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, logCosh (h i * t / 2)

/-- Squared affine-invariant speed in the Frobenius normalization. -/
noncomputable def speedSq (h : ι → ℝ) : ℝ := ∑ i, (h i) ^ 2

/-- Affine-invariant distance along that geodesic, from the identity at time
zero to time `t`. -/
noncomputable def affineDistance (h : ι → ℝ) (t : ℝ) : ℝ :=
  |t| * Real.sqrt (speedSq h)

lemma spectralS_zero (h : ι → ℝ) : spectralS h 0 = 0 := by
  simp [spectralS, logCosh]


/-- The diagonal log-determinant ledger, written as the sum of its scalar
spectral terms. -/
noncomputable def diagonalLedger (h : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, scalarS 1 (Real.exp (h i * t))

/-- No approximation is involved in the passage from B15's raw formula to the
sum of hyperbolic-log terms. -/
lemma diagonalLedger_eq_spectralS (h : ι → ℝ) (t : ℝ) :
    diagonalLedger h t = spectralS h t := by
  unfold diagonalLedger spectralS
  apply Finset.sum_congr rfl
  intro i _
  have he : 2 * (h i * t / 2) = h i * t := by ring
  simpa only [he] using scalarS_one_exp_two (h i * t / 2)

/-- The finite-dimensional version of `S = d_R²/8 + o(d_R²)`. -/
lemma tendsto_spectralS_div_sq (h : ι → ℝ) :
    Tendsto (fun t => spectralS h t / t ^ 2) (𝓝[≠] 0)
      (𝓝 (speedSq h / 8)) := by
  simpa [spectralS, speedSq, Finset.sum_div] using
    (tendsto_finsetSum Finset.univ
      (fun i _ => tendsto_logCosh_scaled_div_sq (h i)))


lemma logCosh_nonneg (x : ℝ) : 0 ≤ logCosh x := by
  exact Real.log_nonneg (Real.one_le_cosh x)

lemma spectralS_nonneg (h : ι → ℝ) (t : ℝ) : 0 ≤ spectralS h t := by
  exact Finset.sum_nonneg (fun i _ => logCosh_nonneg (h i * t / 2))

lemma sqrt_eight : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]

/-- **B15 local metric identity.**  For an arbitrary nonconstant finite-spectrum
affine geodesic, `√S / d_R` tends to exactly `1/(2√2)`. -/
lemma sqrt_spectralS_div_affineDistance_tendsto (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    Tendsto (fun t => Real.sqrt (spectralS h t) / affineDistance h t)
      (𝓝[≠] 0) (𝓝 (1 / (2 * Real.sqrt 2))) := by
  have hq : 0 < Real.sqrt (speedSq h) := Real.sqrt_pos.2 hh
  have hval : Real.sqrt (speedSq h / 8) / Real.sqrt (speedSq h) =
      1 / (2 * Real.sqrt 2) := by
    rw [Real.sqrt_div hh.le 8, sqrt_eight]
    field_simp [ne_of_gt hq, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  have hs := (tendsto_spectralS_div_sq h).sqrt.div_const (Real.sqrt (speedSq h))
  rw [hval] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t _
  change Real.sqrt (spectralS h t / t ^ 2) / Real.sqrt (speedSq h) =
    Real.sqrt (spectralS h t) / (|t| * Real.sqrt (speedSq h))
  rw [Real.sqrt_div (spectralS_nonneg h t), Real.sqrt_sq_eq_abs, div_div]

/-- With the same distance parameter, the *raw* comparator quotient tends to
zero, not to the card's constant. -/
lemma spectralS_div_affineDistance_tendsto_zero (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    Tendsto (fun t => spectralS h t / affineDistance h t) (𝓝[≠] 0) (𝓝 0) := by
  have hq : Real.sqrt (speedSq h) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have ht : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hp := (ht.div_const (Real.sqrt (speedSq h))).mul (tendsto_spectralS_div_sq h)
  simp only [zero_div, zero_mul] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht'
  change t ≠ 0 at ht'
  change (|t| / Real.sqrt (speedSq h)) * (spectralS h t / t ^ 2) =
    spectralS h t / (|t| * Real.sqrt (speedSq h))
  field_simp [ht', hq]
  rw [sq_abs]
  ring

/-- Hence the literal raw-`S` display in the older local HTML cannot have the
v7 limit.  The v7 source's `√S` is essential. -/
lemma not_spectralS_div_affineDistance_tendsto_card_constant (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    ¬ Tendsto (fun t => spectralS h t / affineDistance h t) (𝓝[≠] 0)
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  intro hc
  have heq := tendsto_nhds_unique (spectralS_div_affineDistance_tendsto_zero h hh) hc
  have hn : (1 / (2 * Real.sqrt 2) : ℝ) ≠ 0 := by positivity
  exact hn heq.symm


lemma hasDerivAt_logCosh_scaled (a t : ℝ) :
    HasDerivAt (fun s => logCosh (a * s / 2))
      (Real.tanh (a * t / 2) * (a / 2)) t := by
  convert (hasDerivAt_logCosh (a * t / 2)).comp t
    (((hasDerivAt_id t).const_mul a).div_const 2) using 1
  · funext s
    rfl
  · ring

/-- The raw comparator has zero first derivative at coincidence. -/
lemma hasDerivAt_spectralS_zero (h : ι → ℝ) : HasDerivAt (spectralS h) 0 0 := by
  have hs : HasDerivAt (spectralS h)
      (∑ i, Real.tanh (h i * 0 / 2) * (h i / 2)) 0 := by
    unfold spectralS
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_logCosh_scaled (h i) 0
  simpa using hs

lemma deriv_spectralS_zero (h : ι → ℝ) : deriv (spectralS h) 0 = 0 :=
  (hasDerivAt_spectralS_zero h).deriv


/-- The v7 local statement, expressed directly with B15's raw diagonal
log-determinant ledger. -/
lemma sqrt_diagonalLedger_div_affineDistance_tendsto (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    Tendsto (fun t => Real.sqrt (diagonalLedger h t) / affineDistance h t)
      (𝓝[≠] 0) (𝓝 (1 / (2 * Real.sqrt 2))) := by
  simpa only [diagonalLedger_eq_spectralS] using
    sqrt_spectralS_div_affineDistance_tendsto h hh

/-- Direct raw-comparator version of the local raw quotient: its limit is zero. -/
lemma diagonalLedger_div_affineDistance_tendsto_zero (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    Tendsto (fun t => diagonalLedger h t / affineDistance h t) (𝓝[≠] 0) (𝓝 0) := by
  simpa only [diagonalLedger_eq_spectralS] using
    spectralS_div_affineDistance_tendsto_zero h hh

/-- The raw display in the older local HTML is therefore false as a limit to
`1/(2√2)`; replacing `S` by `√S` gives the true preceding theorem. -/
lemma not_diagonalLedger_div_affineDistance_tendsto_card_constant (h : ι → ℝ)
    (hh : 0 < speedSq h) :
    ¬ Tendsto (fun t => diagonalLedger h t / affineDistance h t) (𝓝[≠] 0)
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  simpa only [diagonalLedger_eq_spectralS] using
    not_spectralS_div_affineDistance_tendsto_card_constant h hh

/-- The raw ledger's tangent derivative at coincidence is zero. -/
lemma hasDerivAt_diagonalLedger_zero (h : ι → ℝ) :
    HasDerivAt (diagonalLedger h) 0 0 := by
  have heq : diagonalLedger h = spectralS h := by
    funext t
    exact diagonalLedger_eq_spectralS h t
  rw [heq]
  exact hasDerivAt_spectralS_zero h

/-- In particular, the literal raw derivative in the 93-card HTML is not the
v7 constant. -/
lemma not_hasDerivAt_diagonalLedger_card_constant (h : ι → ℝ) :
    ¬ HasDerivAt (diagonalLedger h) (1 / (2 * Real.sqrt 2)) 0 := by
  intro hc
  have heq := (hasDerivAt_diagonalLedger_zero h).unique hc
  have hn : (1 / (2 * Real.sqrt 2) : ℝ) ≠ 0 := by positivity
  exact hn heq.symm

#print axioms B15Metric.hasDerivAt_diagonalLedger_zero
#print axioms B15Metric.not_hasDerivAt_diagonalLedger_card_constant
#print axioms B15Metric.scalarS_one_exp_two
#print axioms B15Metric.hasDerivAt_logCosh
#print axioms B15Metric.deriv_logCosh
#print axioms B15Metric.hasDerivAt_tanh_zero
#print axioms B15Metric.hasDerivAt_deriv_logCosh_zero
#print axioms B15Metric.iteratedDeriv_two_logCosh
#print axioms B15Metric.contDiff_logCosh
#print axioms B15Metric.taylor_logCosh
#print axioms B15Metric.tendsto_logCosh_div_sq
#print axioms B15Metric.tendsto_logCosh_scaled_div_sq
#print axioms B15Metric.spectralS_zero
#print axioms B15Metric.diagonalLedger_eq_spectralS
#print axioms B15Metric.tendsto_spectralS_div_sq
#print axioms B15Metric.logCosh_nonneg
#print axioms B15Metric.spectralS_nonneg
#print axioms B15Metric.sqrt_eight
#print axioms B15Metric.sqrt_spectralS_div_affineDistance_tendsto
#print axioms B15Metric.spectralS_div_affineDistance_tendsto_zero
#print axioms B15Metric.not_spectralS_div_affineDistance_tendsto_card_constant
#print axioms B15Metric.hasDerivAt_logCosh_scaled
#print axioms B15Metric.hasDerivAt_spectralS_zero
#print axioms B15Metric.deriv_spectralS_zero
#print axioms B15Metric.sqrt_diagonalLedger_div_affineDistance_tendsto
#print axioms B15Metric.diagonalLedger_div_affineDistance_tendsto_zero
#print axioms B15Metric.not_diagonalLedger_div_affineDistance_tendsto_card_constant

end
end B15Metric


/-! ## B152 — the spectral and energy clauses under the particle-hole exchange

Integrated from `.ultramath/smwu90bch/m8/B152.lean`.
-/

/-!
# B152: the omitted particle--hole spectral clauses

The previous B152 development proved only `offset C = 0`.  This file proves the
other two clauses on the pinned v7 card (SHA-256
`85a5a8e669fbb8138ce15402d4b8f97253d9370cb4c6f809a20e83b0a32a3b7e`):
the occupation spectrum is invariant, with multiplicity, under `ν ↦ 1 - ν`,
and the entanglement-energy spectrum is invariant under `ε ↦ -ε`.
-/

open scoped Matrix
open Matrix Polynomial

namespace RelationalAtlas.B152Gap

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real occupation spectrum, with algebraic multiplicity. -/
def occupationSpectrum (ν : n → ℝ) : Multiset ℝ := Finset.univ.val.map ν

/-- B151's one-mode entanglement energy.  On `0 < ν < 1` this is
`log ((1 - ν) / ν)`, but this subtraction form needs no totalised division. -/
def modeEnergy (ν : ℝ) : ℝ := Real.log (1 - ν) - Real.log ν

/-- The entanglement-energy spectrum, with the occupation multiplicities. -/
def energySpectrum (ν : n → ℝ) : Multiset ℝ :=
  (occupationSpectrum ν).map modeEnergy

@[simp] theorem modeEnergy_complement (ν : ℝ) :
    modeEnergy (1 - ν) = -modeEnergy ν := by
  simp only [modeEnergy, sub_sub_cancel]
  ring

/-- The subtraction form is the card's log-odds away from the two endpoint
occupations. -/
theorem modeEnergy_eq_log_div {ν : ℝ} (h0 : ν ≠ 0) (h1 : 1 - ν ≠ 0) :
    modeEnergy ν = Real.log ((1 - ν) / ν) := by
  rw [modeEnergy, Real.log_div h1 h0]

/-- Unitary conjugation preserves the characteristic polynomial. -/
theorem charpoly_particleHole {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    (1 - C).charpoly = C.charpoly := by
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self (⟨U, hU⟩ : Matrix.unitaryGroup n ℂ))
  calc
    (1 - C).charpoly = (U * C * Uᴴ).charpoly := congrArg Matrix.charpoly hPH.symm
    _ = (Uᴴ * (U * C)).charpoly := Matrix.charpoly_mul_comm (U * C) Uᴴ
    _ = C.charpoly := by rw [← mul_assoc, hUhU, one_mul]

/-- The transpose alternative in the card's Carry field has the same
characteristic-polynomial consequence. -/
theorem charpoly_particleHole_of_transpose {U C : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    (1 - C).charpoly = C.charpoly := by
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self (⟨U, hU⟩ : Matrix.unitaryGroup n ℂ))
  have hu : (U * C * Uᴴ).charpoly = C.charpoly := by
    calc
      (U * C * Uᴴ).charpoly = (Uᴴ * (U * C)).charpoly :=
        Matrix.charpoly_mul_comm (U * C) Uᴴ
      _ = C.charpoly := by rw [← mul_assoc, hUhU, one_mul]
  rw [← hu, hPH, Matrix.charpoly_transpose]

/-- Characteristic polynomial of `I - C` in the eigenbasis of Hermitian `C`. -/
theorem charpoly_complement {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    (1 - C).charpoly =
      ∏ i, (X - Polynomial.C (RCLike.ofReal (1 - hC.eigenvalues i) : ℂ)) := by
  have hcfc : cfc (fun x : ℝ => 1 - x) C = (1 : Matrix n n ℂ) - C := by
    calc
      cfc (fun x : ℝ => 1 - x) C =
          cfc (fun _ : ℝ => (1 : ℝ)) C - cfc (fun x : ℝ => x) C :=
        cfc_sub _ _ C continuousOn_const continuousOn_id
      _ = (1 : Matrix n n ℂ) - C :=
        congrArg₂ (fun A B : Matrix n n ℂ => A - B)
          (cfc_const_one ℝ C hC) (cfc_id' ℝ C hC)
  rw [← hcfc, hC.charpoly_cfc_eq]

/-- Roots of the complement's characteristic polynomial, including
multiplicities. -/
theorem roots_complement {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    (1 - C).charpoly.roots =
      Multiset.map (fun i => (RCLike.ofReal (1 - hC.eigenvalues i) : ℂ)) Finset.univ.val := by
  rw [charpoly_complement hC, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

/-- **B152's occupation-spectrum clause.**  If the complement and `C` have the
same characteristic polynomial, then `ν ↦ 1 - ν` is a permutation of the
occupation spectrum (here stated as equality of multisets, which also preserves
all degeneracies). -/
theorem occupationSpectrum_invariant_of_charpoly {C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hchar : (1 - C).charpoly = C.charpoly) :
    (occupationSpectrum hC.eigenvalues).map (fun ν => 1 - ν) =
      occupationSpectrum hC.eigenvalues := by
  have hroots := congrArg Polynomial.roots hchar
  rw [roots_complement hC, hC.roots_charpoly_eq_eigenvalues] at hroots
  have hreal := congrArg (Multiset.map (RCLike.re (K := ℂ))) hroots
  simpa only [occupationSpectrum, Multiset.map_map, Function.comp_apply,
    RCLike.ofReal_re] using hreal

/-- **B152, complement Carry form:** unitary particle--hole conjugacy makes the
occupation spectrum invariant under `ν ↦ 1 - ν`, with multiplicity. -/
theorem occupationSpectrum_invariant {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    (occupationSpectrum hC.eigenvalues).map (fun ν => 1 - ν) =
      occupationSpectrum hC.eigenvalues :=
  occupationSpectrum_invariant_of_charpoly hC (charpoly_particleHole hU hPH)

/-- **B152, transpose Carry form:** the alternative displayed transpose
conjugacy gives exactly the same occupation-spectrum invariance. -/
theorem occupationSpectrum_invariant_of_transpose {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    (occupationSpectrum hC.eigenvalues).map (fun ν => 1 - ν) =
      occupationSpectrum hC.eigenvalues :=
  occupationSpectrum_invariant_of_charpoly hC
    (charpoly_particleHole_of_transpose hU hPH)

/-- Energy-pairing form of an occupation-pairing identity. -/
theorem energySpectrum_invariant_of_occupationSpectrum_invariant
    {ν : n → ℝ}
    (hν : (occupationSpectrum ν).map (fun x => 1 - x) = occupationSpectrum ν) :
    (energySpectrum ν).map (fun ε => -ε) = energySpectrum ν := by
  unfold energySpectrum
  calc
    ((occupationSpectrum ν).map modeEnergy).map (fun ε => -ε) =
        ((occupationSpectrum ν).map (fun x => 1 - x)).map modeEnergy := by
      simp only [Multiset.map_map, Function.comp_apply, modeEnergy_complement]
    _ = (occupationSpectrum ν).map modeEnergy := congrArg (Multiset.map modeEnergy) hν

/-- **B152's entanglement-energy clause.**  The energies pair as `ε` and `-ε`,
again with multiplicity. -/
theorem energySpectrum_invariant {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    (energySpectrum hC.eigenvalues).map (fun ε => -ε) =
      energySpectrum hC.eigenvalues :=
  energySpectrum_invariant_of_occupationSpectrum_invariant
    (occupationSpectrum_invariant hC hU hPH)

/-- Transpose form of the energy pairing. -/
theorem energySpectrum_invariant_of_transpose {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    (energySpectrum hC.eigenvalues).map (fun ε => -ε) =
      energySpectrum hC.eigenvalues :=
  energySpectrum_invariant_of_occupationSpectrum_invariant
    (occupationSpectrum_invariant_of_transpose hC hU hPH)

/-- A real multiset invariant under negation has sum zero. -/
theorem sum_eq_zero_of_map_neg_eq {s : Multiset ℝ}
    (hs : s.map (fun x => -x) = s) : s.sum = 0 := by
  have h := congrArg Multiset.sum hs
  have hneg : (s.map (fun x : ℝ => -x)).sum = -s.sum := by
    simpa only [Multiset.map_id'] using
      (Multiset.sum_map_neg (m := s) (f := fun x : ℝ => x))
  rw [hneg] at h
  linarith

/-- In particular `Σ εᵢ = 0`; unlike the older determinant argument, this is
proved directly from the individual energy pairing. -/
theorem sum_energySpectrum_eq_zero {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = 1 - C) :
    (energySpectrum hC.eigenvalues).sum = 0 :=
  sum_eq_zero_of_map_neg_eq (energySpectrum_invariant hC hU hPH)

/-- The transpose version also forces `Σ εᵢ = 0`. -/
theorem sum_energySpectrum_eq_zero_of_transpose {U C : Matrix n n ℂ}
    (hC : C.IsHermitian) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hPH : U * C * Uᴴ = (1 - C)ᵀ) :
    (energySpectrum hC.eigenvalues).sum = 0 :=
  sum_eq_zero_of_map_neg_eq (energySpectrum_invariant_of_transpose hC hU hPH)

#print axioms modeEnergy_complement
#print axioms modeEnergy_eq_log_div
#print axioms charpoly_particleHole
#print axioms charpoly_particleHole_of_transpose
#print axioms charpoly_complement
#print axioms roots_complement
#print axioms occupationSpectrum_invariant_of_charpoly
#print axioms occupationSpectrum_invariant
#print axioms occupationSpectrum_invariant_of_transpose
#print axioms energySpectrum_invariant_of_occupationSpectrum_invariant
#print axioms energySpectrum_invariant
#print axioms energySpectrum_invariant_of_transpose
#print axioms sum_eq_zero_of_map_neg_eq
#print axioms sum_energySpectrum_eq_zero
#print axioms sum_energySpectrum_eq_zero_of_transpose

end
end RelationalAtlas.B152Gap


/-! ## B67 — the isotropy threshold, and a counterexample to the lift claim

Integrated from `.ultramath/smwu90bch/m1/B67Lift.lean`.
-/

/-!
# B67: finite algebra of the mechanical lift

The card's display says that a closed shape loop has an *open* horizontal
lift.  That universal wording is false.  The exact finite statement behind
its isotropy threshold is nevertheless true, and is proved below for an
arbitrary finite-dimensional real inner-product space.
-/

open scoped Matrix
open scoped Matrix.Norms.Frobenius
open Module

namespace B67

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A reflection in the hyperplane orthogonal to `v`, together with its
determinant when `v ≠ 0`. -/
noncomputable def hyperplaneReflection [FiniteDimensional ℝ E] (v : E) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ v)ᗮ.reflection

lemma doubleOrthogonal_span_singleton [FiniteDimensional ℝ E] (v : E) :
    (ℝ ∙ v)ᗮᗮ = ℝ ∙ v := by
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.topologicalClosure_eq_self _

lemma det_hyperplaneReflection [FiniteDimensional ℝ E] {v : E} (hv : v ≠ 0) :
    LinearMap.det (hyperplaneReflection v).toLinearMap = -1 := by
  rw [hyperplaneReflection, Submodule.det_reflection, doubleOrthogonal_span_singleton,
    finrank_span_singleton hv]
  norm_num

/-- Determinant one excludes a nontrivial isotropy element when the fixed
subspace has codimension at most one. -/
theorem specialOrthogonal_eq_one_of_fixed_codim_le_one [FiniteDimensional ℝ E]
    (Q : E ≃ₗᵢ[ℝ] E) (K : Submodule ℝ E)
    (hfix : ∀ x ∈ K, Q x = x)
    (hdim : finrank ℝ E ≤ finrank ℝ K + 1)
    (hdet : LinearMap.det Q.toLinearMap = 1) :
    Q = 1 := by
  let W := (ContinuousLinearMap.id ℝ E - Q).ker
  have hKW : K ≤ W := by
    intro x hx
    change x - Q x = 0
    rw [hfix x hx, sub_self]
  have hKdim : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E :=
    K.finrank_add_finrank_orthogonal
  have hKcomp : finrank ℝ Kᗮ ≤ 1 := by omega
  have hWcomp : finrank ℝ Wᗮ ≤ 1 := by
    have hle : Wᗮ ≤ Kᗮ := Submodule.orthogonal_le hKW
    exact (Submodule.finrank_mono hle).trans hKcomp
  obtain ⟨l, hl, hQl⟩ := Q.reflections_generate_dim_aux hWcomp
  cases l with
  | nil => simpa using hQl
  | cons v l =>
      cases l with
      | cons w l => simp at hl
      | nil =>
          by_cases hv : v = 0
          · subst v
            have hQtop : Q = (⊤ : Submodule ℝ E).reflection := by
              simpa using hQl
            rw [hQtop]
            ext x
            exact Submodule.reflection_mem_subspace_eq_self (by simp)
          · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
              mul_one] at hQl
            have hbad : LinearMap.det (hyperplaneReflection v).toLinearMap = 1 := by
              rw [hyperplaneReflection, ← hQl]
              exact hdet
            rw [det_hyperplaneReflection hv] at hbad
            norm_num at hbad

/-- Two nonzero orthogonal normal vectors give a determinant-one isometry
fixing `K`: compose the reflections in their two normal hyperplanes. -/
theorem exists_nontrivial_specialOrthogonal_stabilizer_of_normal_pair
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) {u v : E}
    (huK : u ∈ Kᗮ) (hvK : v ∈ Kᗮ) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℝ u v = 0) :
    ∃ Q : E ≃ₗᵢ[ℝ] E,
      LinearMap.det Q.toLinearMap = 1 ∧ (∀ x ∈ K, Q x = x) ∧ Q ≠ 1 := by
  let ρu := hyperplaneReflection u
  let ρv := hyperplaneReflection v
  let Q := ρu.trans ρv
  have hu_mem : u ∈ (ℝ ∙ v)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact huv
  have hQu : Q u = -u := by
    change ρv (ρu u) = -u
    have hfirst : ρu u = -u := by
      exact Submodule.reflection_orthogonalComplement_singleton_eq_neg u
    rw [hfirst]
    have hsecond : ρv u = u := by
      exact Submodule.reflection_mem_subspace_eq_self hu_mem
    rw [map_neg, hsecond]
  have hQdet : LinearMap.det Q.toLinearMap = 1 := by
    change LinearMap.det (ρv.toLinearMap.comp ρu.toLinearMap) = 1
    rw [LinearMap.det_comp]
    have hdu : LinearMap.det ρu.toLinearMap = -1 := det_hyperplaneReflection hu
    have hdv : LinearMap.det ρv.toLinearMap = -1 := det_hyperplaneReflection hv
    rw [hdu, hdv]
    norm_num
  have hQfix : ∀ x ∈ K, Q x = x := by
    intro x hx
    have hxu : x ∈ (ℝ ∙ u)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact Submodule.inner_left_of_mem_orthogonal hx huK
    have hxv : x ∈ (ℝ ∙ v)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact Submodule.inner_left_of_mem_orthogonal hx hvK
    have hρu : ρu x = x := by
      exact Submodule.reflection_mem_subspace_eq_self hxu
    have hρv : ρv x = x := by
      exact Submodule.reflection_mem_subspace_eq_self hxv
    change ρv (ρu x) = x
    rw [hρu, hρv]
  have hQne : Q ≠ 1 := by
    intro h
    have heq := hQu
    rw [h] at heq
    change u = -u at heq
    apply hu
    have htwo : (2 : ℝ) • u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [heq]
      exact neg_add_cancel u
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨Q, hQdet, hQfix, hQne⟩

/-- Nontrivial isotropy occurs exactly when the configuration span has
codimension at least two.  This is the finite content of
`r ≤ d - 2` for the special orthogonal action. -/
theorem nontrivial_specialOrthogonal_stabilizer_iff
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    (∃ Q : E ≃ₗᵢ[ℝ] E,
      LinearMap.det Q.toLinearMap = 1 ∧ (∀ x ∈ K, Q x = x) ∧ Q ≠ 1) ↔
      finrank ℝ K + 2 ≤ finrank ℝ E := by
  constructor
  · rintro ⟨Q, hdet, hfix, hne⟩
    by_contra h
    have hdim : finrank ℝ E ≤ finrank ℝ K + 1 := by omega
    exact hne (specialOrthogonal_eq_one_of_fixed_codim_le_one Q K hfix hdim hdet)
  · intro hrank
    have hdim : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E :=
      K.finrank_add_finrank_orthogonal
    have hnormal : 2 ≤ finrank ℝ Kᗮ := by omega
    let b := stdOrthonormalBasis ℝ Kᗮ
    let i₀ : Fin (finrank ℝ Kᗮ) := ⟨0, by omega⟩
    let i₁ : Fin (finrank ℝ Kᗮ) := ⟨1, by omega⟩
    let u : E := b i₀
    let v : E := b i₁
    have hi : i₀ ≠ i₁ := by
      intro h
      have := congrArg Fin.val h
      simp [i₀, i₁] at this
    have huv : inner ℝ u v = 0 := by
      exact b.orthonormal.inner_eq_zero hi
    have hu : u ≠ 0 := by
      intro h
      have hn := b.orthonormal.norm_eq_one i₀
      change ‖u‖ = 1 at hn
      rw [h, norm_zero] at hn
      norm_num at hn
    have hv : v ≠ 0 := by
      intro h
      have hn := b.orthonormal.norm_eq_one i₁
      change ‖v‖ = 1 at hn
      rw [h, norm_zero] at hn
      norm_num at hn
    exact exists_nontrivial_specialOrthogonal_stabilizer_of_normal_pair K
      (b i₀).property (b i₁).property hu hv huv


/-! ## The literal loop statement, and the three-body model

A configuration stores the particles as columns.  `sameShape` is equality
modulo left multiplication by a special orthogonal matrix.  The displayed
skew matrix is the spatial angular-momentum matrix for unit masses.
-/

abbrev Configuration (d k : ℕ) := Matrix (Fin d) (Fin k) ℝ

def angularMomentum {d k : ℕ} (X V : Configuration d k) : Matrix (Fin d) (Fin d) ℝ :=
  X * Vᵀ - V * Xᵀ

def SameShape {d k : ℕ} (X Y : Configuration d k) : Prop :=
  ∃ R : Matrix (Fin d) (Fin d) ℝ,
    R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ ∧ Y = R * X

/-- A path equipped with its derivative and the mechanical horizontal
condition.  No unexplained differentiability assumption is hidden. -/
structure HorizontalLift (d k : ℕ) where
  path : ℝ → Configuration d k
  velocity : ℝ → Configuration d k
  path_deriv : ∀ t, HasDerivAt path (velocity t) t
  horizontal : ∀ t, angularMomentum (path t) (velocity t) = 0

def ShapeLoop {d k : ℕ} (γ : HorizontalLift d k) : Prop :=
  SameShape (γ.path 0) (γ.path 1)

def OpenLift {d k : ℕ} (γ : HorizontalLift d k) : Prop :=
  γ.path 1 ≠ γ.path 0

/-- The literal displayed B67 implication for a fixed dimension and number
of particles. -/
def EveryClosedShapeLoopOpens (d k : ℕ) : Prop :=
  ∀ γ : HorizontalLift d k, ShapeLoop γ → OpenLift γ

/-- A gap records how the terminal lift differs from its initial point. -/
def HasGap {d k : ℕ} (γ : HorizontalLift d k) (R : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ ∧ γ.path 1 = R * γ.path 0

noncomputable def constantLift {d k : ℕ} (X : Configuration d k) : HorizontalLift d k where
  path := fun _ => X
  velocity := fun _ => 0
  path_deriv := by
    intro t
    exact hasDerivAt_const t X
  horizontal := by
    intro t
    simp [angularMomentum]

lemma sameShape_refl {d k : ℕ} (X : Configuration d k) : SameShape X X := by
  refine ⟨1, one_mem _, ?_⟩
  simp

lemma constantLift_shapeLoop {d k : ℕ} (X : Configuration d k) :
    ShapeLoop (constantLift X) := by
  exact sameShape_refl X

/-- Pairwise distinct particle positions. -/
def CollisionFree {d k : ℕ} (X : Configuration d k) : Prop :=
  Function.Injective (fun j i => X i j)

/-- Trivial special-orthogonal stabilizer: the point is off the isotropy
strata. -/
def Regular {d k : ℕ} (X : Configuration d k) : Prop :=
  ∀ R : Matrix (Fin d) (Fin d) ℝ,
    R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ → R * X = X → R = 1

/-- The stronger reading including the card's collision and connection
hypotheses, rather than refuting only a degenerate special case. -/
def EveryAdmissibleShapeLoopOpens (d k : ℕ) : Prop :=
  ∀ γ : HorizontalLift d k, ShapeLoop γ →
    (∀ t, CollisionFree (γ.path t)) → (∀ t, Regular (γ.path t)) → OpenLift γ

/-- Three distinct, noncollinear particles: `0`, `e₀`, and `e₁`. -/
def planarThreeBody : Configuration 3 3 :=
  !![0, 1, 0;
     0, 0, 1;
     0, 0, 0]

/-- The counterexample is collision-free, so the card's collision avoidance
hypothesis does not rescue the forced-open wording. -/
theorem planarThreeBody_collisionFree : CollisionFree planarThreeBody := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  fin_cases a <;> fin_cases b <;> simp_all [planarThreeBody]

/-- Any `SO(3)` matrix fixing the planar configuration is the identity.
The determinant-one condition is essential: fixing a hyperplane would
otherwise allow its orientation-reversing reflection. -/
theorem planarThreeBody_stabilizer_eq_one {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix : R * planarThreeBody = planarThreeBody) : R = 1 := by
  have h00 := congrArg (fun M : Configuration 3 3 => M 0 1) hfix
  have h10 := congrArg (fun M : Configuration 3 3 => M 1 1) hfix
  have h20 := congrArg (fun M : Configuration 3 3 => M 2 1) hfix
  have h01 := congrArg (fun M : Configuration 3 3 => M 0 2) hfix
  have h11 := congrArg (fun M : Configuration 3 3 => M 1 2) hfix
  have h21 := congrArg (fun M : Configuration 3 3 => M 2 2) hfix
  norm_num [planarThreeBody, Matrix.mul_apply, Fin.sum_univ_three] at h00 h10 h20 h01 h11 h21
  have hor := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR.1
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) hor
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hor
  norm_num [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, h01, h11, h21,
    Matrix.one_apply] at h02 h12
  have hd := hR.2
  norm_num [Matrix.det_fin_three, h00, h01, h02, h10, h11, h12, h20, h21] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, h00, h01, h02, h10, h11, h12, h20, h21, hd]


lemma planarThreeBody_regular : Regular planarThreeBody := by
  intro R hR hfix
  exact planarThreeBody_stabilizer_eq_one hR hfix

theorem collisionFree_smul {d k : ℕ} {a : ℝ} (ha : a ≠ 0)
    {X : Configuration d k} (hX : CollisionFree X) : CollisionFree (a • X) := by
  intro i j hij
  apply hX
  funext k
  have hk := congrFun hij k
  change a * X k i = a * X k j at hk
  exact mul_left_cancel₀ ha hk

theorem regular_smul {d k : ℕ} {a : ℝ} (ha : a ≠ 0)
    {X : Configuration d k} (hX : Regular X) : Regular (a • X) := by
  intro R hR hfix
  apply hX R hR
  have hs := congrArg (fun M : Configuration d k => a⁻¹ • M) hfix
  simpa [Matrix.mul_smul, smul_smul, ha] using hs

/-- A positive scale going out and back, with nonzero intermediate value.
Squaring the excursion makes positivity automatic on all of `ℝ`. -/
def radialScale (t : ℝ) : ℝ := 1 + (t * (1 - t)) ^ 2

lemma radialScale_ne_zero (t : ℝ) : radialScale t ≠ 0 := by
  have h : 0 ≤ (t * (1 - t)) ^ 2 := sq_nonneg _
  unfold radialScale
  linarith

lemma radialScale_hasDerivAt (t : ℝ) :
    HasDerivAt radialScale ((2 * (t * (1 - t))) * (1 - 2 * t)) t := by
  have ht : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    convert hone.sub ht using 1; ring
  have hu : HasDerivAt (fun s : ℝ => s * (1 - s)) (1 - 2 * t) t := by
    convert ht.mul hsub using 1; ring
  change HasDerivAt (fun s : ℝ => 1 + (s * (1 - s)) ^ 2)
    ((2 * (t * (1 - t))) * (1 - 2 * t)) t
  convert hone.add (hu.pow 2) using 1; ring

/-- A nonconstant, retraced, radial loop.  The velocity is always a scalar
multiple of the instantaneous configuration, hence the angular-momentum
matrix vanishes identically. -/
noncomputable def radialLoop {d k : ℕ} (X : Configuration d k) : HorizontalLift d k where
  path := fun t => radialScale t • X
  velocity := fun t => ((2 * (t * (1 - t))) * (1 - 2 * t)) • X
  path_deriv := by
    intro t
    exact (radialScale_hasDerivAt t).smul_const X
  horizontal := by
    intro t
    simp only [angularMomentum, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    module

lemma radialLoop_shapeLoop {d k : ℕ} (X : Configuration d k) :
    ShapeLoop (radialLoop X) := by
  change SameShape (radialScale 0 • X) (radialScale 1 • X)
  norm_num [radialScale]
  exact sameShape_refl X

lemma radialLoop_not_open {d k : ℕ} (X : Configuration d k) :
    ¬ OpenLift (radialLoop X) := by
  intro h
  apply h
  change radialScale 1 • X = radialScale 0 • X
  norm_num [radialScale]

lemma radialLoop_collisionFree {d k : ℕ} {X : Configuration d k}
    (hX : CollisionFree X) (t : ℝ) : CollisionFree ((radialLoop X).path t) := by
  exact collisionFree_smul (radialScale_ne_zero t) hX

lemma radialLoop_regular {d k : ℕ} {X : Configuration d k}
    (hX : Regular X) (t : ℝ) : Regular ((radialLoop X).path t) := by
  exact regular_smul (radialScale_ne_zero t) hX

lemma radialLoop_planar_nonconstant :
    ∃ t, (radialLoop planarThreeBody).path t ≠ (radialLoop planarThreeBody).path 0 := by
  refine ⟨1 / 2, ?_⟩
  intro h
  have he := congrArg (fun M : Configuration 3 3 => M 0 1) h
  norm_num [radialLoop, radialScale, planarThreeBody] at he

lemma radialLoop_planar_gap_eq_one (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hgap : HasGap (radialLoop planarThreeBody) R) : R = 1 := by
  apply planarThreeBody_stabilizer_eq_one hgap.1
  have h := hgap.2
  norm_num [radialLoop, radialScale] at h
  exact h.symm

/-- Sharp counterexample to the literal open-lift sentence even after
constant loops are excluded.  Every clause that the card explicitly asks
for is present: the base loop is closed, angular momentum is zero, there
are no collisions, every configuration is regular, the gap is in `SO(3)`,
and nevertheless the lift closes with gap one. -/
theorem nonconstant_regular_collisionFree_closed_horizontal_lift :
    ∃ γ : HorizontalLift 3 3,
      ShapeLoop γ ∧ ¬ OpenLift γ ∧
      (∀ t, CollisionFree (γ.path t)) ∧ (∀ t, Regular (γ.path t)) ∧
      (∀ R, HasGap γ R → R = 1) ∧
      (∃ t, γ.path t ≠ γ.path 0) := by
  refine ⟨radialLoop planarThreeBody, radialLoop_shapeLoop _, radialLoop_not_open _,
    radialLoop_collisionFree planarThreeBody_collisionFree,
    radialLoop_regular planarThreeBody_regular, radialLoop_planar_gap_eq_one,
    radialLoop_planar_nonconstant⟩

/-- Even with collision-freeness and trivial isotropy imposed throughout,
closed shape loops need not have open horizontal lifts. -/
theorem admissible_B67_open_lift_claim_is_false :
    ¬ EveryAdmissibleShapeLoopOpens 3 3 := by
  intro h
  have hopen := h (radialLoop planarThreeBody) (radialLoop_shapeLoop _)
    (radialLoop_collisionFree planarThreeBody_collisionFree)
    (radialLoop_regular planarThreeBody_regular)
  exact radialLoop_not_open planarThreeBody hopen

/-- The exact endpoint statement suggested by a closed shape loop: the gap
is some special-orthogonal matrix, with no assertion that it is nontrivial. -/
theorem shapeLoop_iff_exists_gap {d k : ℕ} (γ : HorizontalLift d k) :
    ShapeLoop γ ↔ ∃ R, HasGap γ R := by
  rfl

/-- The regular constant loop refutes the literal universal implication.
It is horizontal, its projection to shape space is closed, and its lift is
closed rather than open. -/
theorem literal_B67_open_lift_claim_is_false : ¬ EveryClosedShapeLoopOpens 3 3 := by
  intro h
  let γ := constantLift planarThreeBody
  have hclosed : ShapeLoop γ := constantLift_shapeLoop planarThreeBody
  have hopen : OpenLift γ := h γ hclosed
  exact hopen rfl

/-- Every special-orthogonal gap of this regular constant loop is trivial. -/
theorem constant_planar_gap_eq_one (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hgap : HasGap (constantLift planarThreeBody) R) : R = 1 := by
  apply planarThreeBody_stabilizer_eq_one hgap.1
  simpa [constantLift] using hgap.2.symm

/-- Three distinct collinear particles: `0`, `e₀`, and `2e₀`. -/
def collinearThreeBody : Configuration 3 3 :=
  !![0, 1, 2;
     0, 0, 0;
     0, 0, 0]

/-- Rotation by π about the collinearity axis. -/
def axialRotation : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0,  0;
     0, -1, 0;
     0, 0, -1]

theorem axialRotation_mem_specialOrthogonal :
    axialRotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hor : axialRotation * axialRotationᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axialRotation, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  exact ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr hor,
    by norm_num [axialRotation, Matrix.det_fin_three]⟩

theorem axialRotation_stabilizes_collinear :
    axialRotation * collinearThreeBody = collinearThreeBody := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axialRotation, collinearThreeBody, Matrix.mul_apply, Fin.sum_univ_three]

theorem axialRotation_ne_one : axialRotation ≠ 1 := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  norm_num [axialRotation, Matrix.one_apply] at h11

/-- The collinear stratum has the nontrivial isotropy that the regular
planar example lacks. -/
theorem collinear_nontrivial_stabilizer :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ,
      R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
      R * collinearThreeBody = collinearThreeBody ∧ R ≠ 1 := by
  exact ⟨axialRotation, axialRotation_mem_specialOrthogonal,
    axialRotation_stabilizes_collinear, axialRotation_ne_one⟩

end B67

/- Kernel audit: every theorem and lemma in this file uses only the
permitted logical axioms. -/
#print axioms B67.doubleOrthogonal_span_singleton
#print axioms B67.det_hyperplaneReflection
#print axioms B67.specialOrthogonal_eq_one_of_fixed_codim_le_one
#print axioms B67.exists_nontrivial_specialOrthogonal_stabilizer_of_normal_pair
#print axioms B67.nontrivial_specialOrthogonal_stabilizer_iff
#print axioms B67.sameShape_refl
#print axioms B67.constantLift_shapeLoop
#print axioms B67.planarThreeBody_collisionFree
#print axioms B67.planarThreeBody_stabilizer_eq_one
#print axioms B67.planarThreeBody_regular
#print axioms B67.collisionFree_smul
#print axioms B67.regular_smul
#print axioms B67.radialScale_ne_zero
#print axioms B67.radialScale_hasDerivAt
#print axioms B67.radialLoop_shapeLoop
#print axioms B67.radialLoop_not_open
#print axioms B67.radialLoop_collisionFree
#print axioms B67.radialLoop_regular
#print axioms B67.radialLoop_planar_nonconstant
#print axioms B67.radialLoop_planar_gap_eq_one
#print axioms B67.nonconstant_regular_collisionFree_closed_horizontal_lift
#print axioms B67.admissible_B67_open_lift_claim_is_false
#print axioms B67.shapeLoop_iff_exists_gap
#print axioms B67.literal_B67_open_lift_claim_is_false
#print axioms B67.constant_planar_gap_eq_one
#print axioms B67.axialRotation_mem_specialOrthogonal
#print axioms B67.axialRotation_stabilizes_collinear
#print axioms B67.axialRotation_ne_one
#print axioms B67.collinear_nontrivial_stabilizer


/-! ## B169 — the correlation moves with the precision, so there is no floor

Integrated from `.ultramath/smwu90bch/m3/B169.lean`.
-/

/-!
# B169 — there is no universal Fisher-correlation floor

For `Ue(phi) = U0 + DeltaU*phi`, the two Jacobian columns are `1` and `phi`.
With inverse-variance weights `w_i = sigma_i^(-2)`, put
`S_j = sum_i w_i*phi_i^j`.  Then `F = [[S0,S1],[S1,S2]]` and the inverse-Fisher
correlation is exactly `-S1/(sqrt S0*sqrt S2)`, while weighted Cauchy--Schwarz
gives `S1^2 <= S0*S2`.

The pinned official v7 B169 HTML has SHA-256
`406a38c26358470862a4d29d49c6d91143755f31acf43192c40b36b074d6985a`.
It reports `-0.999475` for a particular nonlinear eight-point numerical model,
not a general inequality.  On its acquisition grid `phi_i=i/7`, uniform weights
in the two-parameter linear model give `-sqrt(7/10)`.  The positive weights
`(133,1,1,1,1,1,1,1)` give `-1/5`.  Hence the displayed universal `-0.99` floor
is false as finite linear Fisher algebra: relative precisions move correlation.

A separate three-column example `(1,q_i,q_i*phi_i)` leaves normalization free.
It gives a fully marginal correlation `-4/sqrt 17`, also above `-0.99`.  Neither
example claims to replay the nonlinear sensitivity data of the card's measured
witness; the distinction is deliberate.  Uniform rescaling invariance is the
separate, already accepted B20 result and is not reproved here.
-/

noncomputable section
namespace RelationalAtlas.B169
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Weighted moments of a one-dimensional design. -/
def moment (w phi : ι → ℝ) (j : ℕ) : ℝ := ∑ i, w i * phi i ^ j

/-- Fisher information for the two Jacobian columns `(1,phi_i)`. -/
def linearFisher (w phi : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![moment w phi 0, moment w phi 1;
     moment w phi 1, moment w phi 2]

def correlationOfCov (C : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  C 0 1 / (Real.sqrt (C 0 0) * Real.sqrt (C 1 1))

def linearCorrelation (w phi : ι → ℝ) : ℝ :=
  correlationOfCov (linearFisher w phi)⁻¹

/-- Two-by-two adjugate formula, kept scalar so later simplification cannot
unfold the finite sums. -/
theorem fisher_two_inv (a b c : ℝ) (h : a * c - b ^ 2 ≠ 0) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      (a * c - b ^ 2)⁻¹ • !![c, -b; -b, a] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

/-- Off-diagonal covariance normalized by its two diagonal entries. -/
theorem correlationOfFisher_two (a b c : ℝ)
    (ha : 0 < a) (hc : 0 < c) (h : 0 < a * c - b ^ 2) :
    correlationOfCov (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      -b / (Real.sqrt a * Real.sqrt c) := by
  rw [correlationOfCov, fisher_two_inv a b c (ne_of_gt h)]
  simp only [Matrix.smul_apply, smul_eq_mul]
  change ((a * c - b ^ 2)⁻¹ * -b) /
      (Real.sqrt ((a * c - b ^ 2)⁻¹ * c) * Real.sqrt ((a * c - b ^ 2)⁻¹ * a)) = _
  rw [show (a * c - b ^ 2)⁻¹ * c = c / (a * c - b ^ 2) by field_simp,
      show (a * c - b ^ 2)⁻¹ * a = a / (a * c - b ^ 2) by field_simp]
  rw [Real.sqrt_div hc.le, Real.sqrt_div ha.le]
  have hdroot : Real.sqrt (a * c - b ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h)
  have haroot : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hcroot : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  field_simp [hdroot, haroot, hcroot, ne_of_gt h]
  rw [Real.sq_sqrt h.le]

theorem linearFisher_inv (w phi : ι → ℝ)
    (hdet : moment w phi 0 * moment w phi 2 - moment w phi 1 ^ 2 ≠ 0) :
    (linearFisher w phi)⁻¹ =
      (moment w phi 0 * moment w phi 2 - moment w phi 1 ^ 2)⁻¹ •
        !![moment w phi 2, -moment w phi 1;
           -moment w phi 1, moment w phi 0] := by
  exact fisher_two_inv _ _ _ hdet

theorem linearCorrelation_eq (w phi : ι → ℝ)
    (h0 : 0 < moment w phi 0) (h2 : 0 < moment w phi 2)
    (hdet : 0 < moment w phi 0 * moment w phi 2 - moment w phi 1 ^ 2) :
    linearCorrelation w phi =
      -moment w phi 1 / (Real.sqrt (moment w phi 0) * Real.sqrt (moment w phi 2)) := by
  exact correlationOfFisher_two _ _ _ h0 h2 hdet

/-- The off-diagonal Fisher moment obeys weighted Cauchy--Schwarz. -/
theorem moment_one_sq_le (w phi : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    moment w phi 1 ^ 2 ≤ moment w phi 0 * moment w phi 2 := by
  let x : ι → ℝ := fun i => Real.sqrt (w i)
  let y : ι → ℝ := fun i => Real.sqrt (w i) * phi i
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hx : (∑ i, x i ^ 2) = moment w phi 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [x, Real.sq_sqrt (hw i)]
  have hy : (∑ i, y i ^ 2) = moment w phi 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    change (Real.sqrt (w i) * phi i) ^ 2 = w i * phi i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hxy : (∑ i, x i * y i) = moment w phi 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [x, y]
    rw [pow_one]
    calc
      _ = Real.sqrt (w i) ^ 2 * phi i := by ring
      _ = w i * phi i := by rw [Real.sq_sqrt (hw i)]
  rw [hx, hy, hxy] at hcs
  exact hcs

def phi8 : Fin 8 → ℝ := fun i => (i : ℕ) / 7

def weight8 (t : ℝ) : Fin 8 → ℝ := ![t, 1, 1, 1, 1, 1, 1, 1]

lemma moment8_zero (t : ℝ) : moment (weight8 t) phi8 0 = t + 7 := by
  norm_num [moment, weight8, phi8, Fin.sum_univ_eight]
  ring

lemma moment8_one (t : ℝ) : moment (weight8 t) phi8 1 = 4 := by
  norm_num [moment, weight8, phi8, Fin.sum_univ_eight]

lemma moment8_two (t : ℝ) : moment (weight8 t) phi8 2 = 20 / 7 := by
  norm_num [moment, weight8, phi8, Fin.sum_univ_eight]

theorem uniform8_correlation :
    linearCorrelation (weight8 1) phi8 = -Real.sqrt (7 / 10) := by
  rw [linearCorrelation_eq]
  · have hm0 : moment (weight8 1) phi8 0 = 8 := by rw [moment8_zero]; norm_num
    rw [hm0, moment8_one, moment8_two]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    rw [show (8 : ℝ) * (20 / 7) = 160 / 7 by norm_num]
    have hs : Real.sqrt (160 / 7 : ℝ) = 4 * Real.sqrt (10 / 7 : ℝ) := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 / 7)]
      norm_num
    rw [hs]
    have hs' : Real.sqrt (7 / 10 : ℝ) = 1 / Real.sqrt (10 / 7 : ℝ) := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 / 7)]
      norm_num
    rw [hs']
    have hp : Real.sqrt (10 / 7 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp [hp]
  · rw [moment8_zero]
    norm_num
  · rw [moment8_two]
    norm_num
  · rw [moment8_zero, moment8_one, moment8_two]
    norm_num

theorem concentrated8_correlation :
    linearCorrelation (weight8 133) phi8 = -1 / 5 := by
  rw [linearCorrelation_eq]
  · have hm0 : moment (weight8 133) phi8 0 = 140 := by rw [moment8_zero]; norm_num
    rw [hm0, moment8_one, moment8_two]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 140)]
    rw [show (140 : ℝ) * (20 / 7) = 400 by norm_num]
    have hs : Real.sqrt (400 : ℝ) = 20 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    rw [hs]
    norm_num
  · rw [moment8_zero]
    norm_num
  · rw [moment8_two]
    norm_num
  · rw [moment8_zero, moment8_one, moment8_two]
    norm_num

theorem B169_no_precision_floor :
    linearCorrelation (weight8 133) phi8 = -1 / 5 ∧
      -99 / 100 < linearCorrelation (weight8 133) phi8 ∧
      linearCorrelation (weight8 1) phi8 ≠ linearCorrelation (weight8 133) phi8 := by
  refine ⟨concentrated8_correlation, ?_, ?_⟩
  · rw [concentrated8_correlation]
    norm_num
  · rw [uniform8_correlation, concentrated8_correlation]
    intro h
    have hs : Real.sqrt (7 / 10 : ℝ) = 1 / 5 := by linarith
    have hsq := congrArg (fun x : ℝ => x ^ 2) hs
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 10)] at hsq
    norm_num at hsq

/-- All inverse-variance profiles used above are realizable by positive
standard deviations (`sigma_i = (w_i)^(-1/2)`). -/
theorem weight8_pos {t : ℝ} (ht : 0 < t) (i : Fin 8) : 0 < weight8 t i := by
  fin_cases i <;> simp [weight8, ht]

/-! ## Free normalization does not restore a universal floor

The following optional extension has three Jacobian columns `(1,q_i,q_i*phi_i)`:
the first belongs to a free multiplicative normalization.  Taking
`q_i = 1 + 7*phi_i = 1+i` gives a positive, increasing response on the same grid.
This is a finite linear-response model, not a claim to replay the card's
nonlinear numerical derivative.  Its full 3x3 Fisher matrix and covariance are
computed explicitly, so marginalizing the normalization is genuine. -/

/-- Positive response amplitude for the normalization-free example. -/
def response8 (i : Fin 8) : ℝ := 1 + 7 * phi8 i

lemma response8_pos (i : Fin 8) : 0 < response8 i := by
  unfold response8 phi8
  positivity

/-- Design columns `(normalization, U0, DeltaU)`. -/
def normalDesign (q phi : ι → ℝ) : ι → Fin 3 → ℝ :=
  fun i => ![1, q i, q i * phi i]

/-- The full 3x3 Fisher matrix with a free normalization column. -/
def normalFisher (w q phi : ι → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => ∑ i, w i * normalDesign q phi i j * normalDesign q phi i k

/-- Correlation of `U0` and `DeltaU` after marginalizing the normalization. -/
def normalCorrelation (w q phi : ι → ℝ) : ℝ :=
  let C := (normalFisher w q phi)⁻¹
  C 1 2 / (Real.sqrt (C 1 1) * Real.sqrt (C 2 2))

lemma normalFisher_uniform8 :
    normalFisher (weight8 1) response8 phi8 =
      !![8, 36, 24;
         36, 204, 156;
         24, 156, 6384 / 49] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalFisher, normalDesign, response8, weight8, phi8,
      Fin.sum_univ_eight]

lemma normalCovariance_uniform8 :
    (normalFisher (weight8 1) response8 phi8)⁻¹ =
      !![109 / 56, -23 / 28, 5 / 8;
         -23 / 28, 17 / 42, -1 / 3;
         5 / 8, -1 / 3, 7 / 24] := by
  rw [normalFisher_uniform8]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three]

/-- Exact normalization-free value: it is already greater than `-0.98`, hence
certainly not below a `-0.99` floor. -/
theorem normalCorrelation_uniform8 :
    normalCorrelation (weight8 1) response8 phi8 = -4 / Real.sqrt 17 := by
  rw [normalCorrelation, normalCovariance_uniform8]
  change (-1 / 3 : ℝ) / (Real.sqrt (17 / 42) * Real.sqrt (7 / 24)) = _
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 17 / 42)]
  rw [show (17 / 42 : ℝ) * (7 / 24) = 17 / 144 by norm_num]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 17)]
  have hs : Real.sqrt (144 : ℝ) = 12 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  rw [hs]
  have hp : Real.sqrt (17 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hp]
  ring

/-- The actual head-line gap, still with normalization free: there is a
positive, nonsingular Fisher model on the card's eight-point acquisition grid
whose fitted correlation lies strictly above `-99/100`. -/
theorem B169_no_precision_floor_normalization_free :
    normalCorrelation (weight8 1) response8 phi8 = -4 / Real.sqrt 17 ∧
      -99 / 100 < normalCorrelation (weight8 1) response8 phi8 := by
  refine ⟨normalCorrelation_uniform8, ?_⟩
  rw [normalCorrelation_uniform8]
  have hr : 400 / 99 < Real.sqrt (17 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 400 / 99)]
    norm_num
  have hp : 0 < Real.sqrt (17 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfrac : 4 / Real.sqrt (17 : ℝ) < 99 / 100 := by
    apply (div_lt_div_iff₀ hp (by norm_num : (0 : ℝ) < 100)).2
    nlinarith
  simpa only [neg_div] using (neg_lt_neg hfrac)

end RelationalAtlas.B169

#print axioms RelationalAtlas.B169.fisher_two_inv
#print axioms RelationalAtlas.B169.correlationOfFisher_two
#print axioms RelationalAtlas.B169.linearFisher_inv
#print axioms RelationalAtlas.B169.linearCorrelation_eq
#print axioms RelationalAtlas.B169.moment_one_sq_le
#print axioms RelationalAtlas.B169.moment8_zero
#print axioms RelationalAtlas.B169.moment8_one
#print axioms RelationalAtlas.B169.moment8_two
#print axioms RelationalAtlas.B169.uniform8_correlation
#print axioms RelationalAtlas.B169.concentrated8_correlation
#print axioms RelationalAtlas.B169.B169_no_precision_floor
#print axioms RelationalAtlas.B169.weight8_pos
#print axioms RelationalAtlas.B169.response8_pos
#print axioms RelationalAtlas.B169.normalFisher_uniform8
#print axioms RelationalAtlas.B169.normalCovariance_uniform8
#print axioms RelationalAtlas.B169.normalCorrelation_uniform8
#print axioms RelationalAtlas.B169.B169_no_precision_floor_normalization_free


/-! ## B24 — the second-order coefficients in every dimension

Integrated from `.ultramath/smwu90bch/m10/B24General.lean`.
-/

open scoped ComplexConjugate BigOperators Topology
open Filter Matrix Polynomial

noncomputable section

namespace RelationalAtlas.B24General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent of a real diagonal matrix, viewed as a complex matrix. -/
def diagonalResolvent (a : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => (a i : ℂ)⁻¹

/-- The four-factor trace in the eigenbasis, without any Hermitian hypothesis. -/
theorem trace_diagonalResolvent_mul (a : n → ℝ) (E : Matrix n n ℂ) :
    (diagonalResolvent a * E * diagonalResolvent a * E).trace =
      ∑ i, ∑ j, (a i : ℂ)⁻¹ * E i j * (a j : ℂ)⁻¹ * E j i := by
  have hRE (i j : n) : (diagonalResolvent a * E) i j = (a i : ℂ)⁻¹ * E i j := by
    rw [diagonalResolvent, Matrix.diagonal_mul]
  rw [Matrix.mul_assoc (diagonalResolvent a * E) (diagonalResolvent a) E]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hRE]
  simp only [mul_assoc]

/-- One summand after using Hermiticity to identify the reversed entry. -/
lemma hermitian_weighted_entry (a : n → ℝ) (ha : ∀ i, a i ≠ 0)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) (i j : n) :
    (a i : ℂ)⁻¹ * E i j * (a j : ℂ)⁻¹ * E j i =
      ((Complex.normSq (E i j) / (a i * a j) : ℝ) : ℂ) := by
  rw [← hE.apply j i]
  have hai : (a i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha i)
  have haj : (a j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha j)
  have hconj : E i j * star (E i j) = (Complex.normSq (E i j) : ℂ) := by
    simpa only [RCLike.star_def] using Complex.mul_conj (E i j)
  calc
    (a i : ℂ)⁻¹ * E i j * (a j : ℂ)⁻¹ * star (E i j) =
        (E i j * star (E i j)) * ((a i : ℂ)⁻¹ * (a j : ℂ)⁻¹) := by ring
    _ = (Complex.normSq (E i j) : ℂ) * ((a i : ℂ)⁻¹ * (a j : ℂ)⁻¹) := by
      rw [hconj]
    _ = ((Complex.normSq (E i j) / (a i * a j) : ℝ) : ℂ) := by
      push_cast
      field_simp

/-- **B24 in every finite dimension.** In an eigenbasis with shifted
real eigenvalues `a`, Hermiticity turns the four-factor trace into exactly
the card's double sum of modulus squares with product weights. -/
theorem trace_RERE_eq_eigenbasis_sum (a : n → ℝ) (ha : ∀ i, a i ≠ 0)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    (diagonalResolvent a * E * diagonalResolvent a * E).trace =
      ((∑ i, ∑ j, Complex.normSq (E i j) / (a i * a j) : ℝ) : ℂ) := by
  rw [trace_diagonalResolvent_mul]
  simp_rw [hermitian_weighted_entry a ha hE]
  push_cast
  rfl

/-- The displayed second-order forms, including the factor `-1/2`. -/
theorem two_c2_forms_hermitian_general (a : n → ℝ) (ha : ∀ i, a i ≠ 0)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    -(1 / 2 : ℂ) *
        (diagonalResolvent a * E * diagonalResolvent a * E).trace =
      ((-(1 / 2 : ℝ) *
        (∑ i, ∑ j, Complex.normSq (E i j) / (a i * a j)) : ℝ) : ℂ) := by
  rw [trace_RERE_eq_eigenbasis_sum a ha hE]
  push_cast
  ring

/-! ## The quadratic coefficient as a Newton trace identity -/

section SecondCoefficient
variable {R : Type*} [CommRing R]

lemma det_submatrix_pair (M : Matrix n n R) (i j : n) (hij : i ≠ j) :
    (M.submatrix (Subtype.val : ({i, j} : Finset n) → n) Subtype.val).det =
      M i i * M j j - M i j * M j i := by
  let u : Fin 2 → ({i, j} : Finset n) := fun k =>
    if k = 0 then ⟨i, by simp⟩ else ⟨j, by simp⟩
  have hu : Function.Bijective u := by
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [u, hij, Ne.symm hij]
    · intro x
      have hx : x.1 = i ∨ x.1 = j := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using x.2
      rcases hx with hx | hx
      · refine ⟨0, Subtype.ext ?_⟩
        simp [u, hx]
      · refine ⟨1, Subtype.ext ?_⟩
        simp [u, hx]
  let e : Fin 2 ≃ ({i, j} : Finset n) := Equiv.ofBijective u hu
  rw [← Matrix.det_submatrix_equiv_self e]
  rw [Matrix.det_fin_two]
  simp [e, u]


/-- A two-by-two principal minor, indexed by an ordered pair. -/
def minor (M : Matrix n n R) (i j : n) : R := M i i * M j j - M i j * M j i

section LinearOrder
variable [LinearOrder n]

/-- The principal two-minors are the sum over increasing ordered pairs. -/
lemma sum_minors_two (M : Matrix n n R) :
    (∑ s ∈ Finset.univ.powersetCard 2,
      (M.submatrix (Subtype.val : s → n) Subtype.val).det) =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : n × n => p.1 < p.2),
        minor M p.1 p.2 := by
  symm
  apply Finset.sum_bij (fun p _ => ({p.1, p.2} : Finset n))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt hp)⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp hq
    have hp1 : p.1 = q.1 ∨ p.1 = q.2 := by
      have : p.1 ∈ ({q.1, q.2} : Finset n) := by rw [← hpq]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hp2 : p.2 = q.1 ∨ p.2 = q.2 := by
      have : p.2 ∈ ({q.1, q.2} : Finset n) := by rw [← hpq]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hq1 : q.1 = p.1 ∨ q.1 = p.2 := by
      have : q.1 ∈ ({p.1, p.2} : Finset n) := by rw [hpq]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hq2 : q.2 = p.1 ∨ q.2 = p.2 := by
      have : q.2 ∈ ({p.1, p.2} : Finset n) := by rw [hpq]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    apply Prod.ext <;> grind
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs.2
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · refine ⟨(i, j), ?_, ?_⟩
      · simp [hij']
      · rfl
    · refine ⟨(j, i), ?_, ?_⟩
      · simp [hij']
      · exact Finset.pair_comm j i
  · intro p hp
    exact (det_submatrix_pair M p.1 p.2 (ne_of_lt (by simpa using hp))).symm

/-- The increasing-pair sum as an ordinary double sum with an indicator. -/
lemma lowerPairs_eq_ite_sum (M : Matrix n n R) :
    (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : n × n => p.1 < p.2),
        minor M p.1 p.2) =
      ∑ i, ∑ j, if i < j then minor M i j else 0 := by
  rw [Finset.sum_filter, Finset.sum_product]

lemma minor_swap (M : Matrix n n R) (i j : n) :
    minor M j i = minor M i j := by
  unfold minor
  ring

/-- The full ordered-pair sum is twice the increasing-triangle sum. -/
lemma sum_minor_eq_two_mul_lower (M : Matrix n n R) :
    (∑ i, ∑ j, minor M i j) =
      2 * (∑ i, ∑ j, if i < j then minor M i j else 0) := by
  have hpoint (i j : n) : minor M i j =
      (if i < j then minor M i j else 0) +
        (if j < i then minor M i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.asymm]
    · subst j
      simp [minor]
    · simp [hij, hij.asymm]
  have hupper :
      (∑ i, ∑ j, if j < i then minor M i j else 0) =
        ∑ i, ∑ j, if i < j then minor M i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, if_true]
      exact minor_swap M i j
    · simp only [hij, if_false]
  calc
    (∑ i, ∑ j, minor M i j) =
        ∑ i, ∑ j, ((if i < j then minor M i j else 0) +
          (if j < i then minor M i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint i j
    _ = (∑ i, ∑ j, if i < j then minor M i j else 0) +
        (∑ i, ∑ j, if j < i then minor M i j else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2 * (∑ i, ∑ j, if i < j then minor M i j else 0) := by
      rw [← hupper]
      ring

/-- The ordered-pair minor sum is the second Newton combination of traces. -/
lemma sum_minor_eq_trace (M : Matrix n n R) :
    (∑ i, ∑ j, minor M i j) = M.trace ^ 2 - (M * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  rw [Fintype.sum_mul_sum]
  simp_rw [← Finset.sum_sub_distrib]
  rfl

/-- The sum of all principal two-minors, in closed trace form. -/
theorem sum_minors_two_eq_trace (M : Matrix n n R) :
    2 * (∑ s ∈ Finset.univ.powersetCard 2,
      (M.submatrix (Subtype.val : s → n) Subtype.val).det) =
        M.trace ^ 2 - (M * M).trace := by
  rw [sum_minors_two, lowerPairs_eq_ite_sum, ← sum_minor_eq_two_mul_lower,
    sum_minor_eq_trace]

end LinearOrder
end SecondCoefficient

/-! ## The normalized determinant curve and its logarithm -/

/-- `det (1 + εM)` over the reals. -/
def unitDet (M : Matrix n n ℝ) (ε : ℝ) : ℝ := (1 + ε • M).det

/-- The polynomial quotient which carries all terms of degree at least two. -/
def unitQuadratic (M : Matrix n n ℝ) : Polynomial ℝ :=
  (Matrix.det (1 + (Polynomial.X : ℝ[X]) • M.map Polynomial.C)).divX.divX

/-- The exact slope of the normalized determinant curve. -/
def unitDetSlope (M : Matrix n n ℝ) (ε : ℝ) : ℝ :=
  M.trace + (unitQuadratic M).derivative.eval ε * ε ^ 2 +
    (unitQuadratic M).eval ε * (2 * ε)

lemma unitDet_eq_expansion (M : Matrix n n ℝ) (ε : ℝ) :
    unitDet M ε = 1 + M.trace * ε + (unitQuadratic M).eval ε * ε ^ 2 := by
  exact Matrix.det_one_add_smul ε M

lemma hasDerivAt_unitDet (M : Matrix n n ℝ) (ε : ℝ) :
    HasDerivAt (unitDet M) (unitDetSlope M ε) ε := by
  have hfun : unitDet M = fun ε =>
      1 + M.trace * ε + (unitQuadratic M).eval ε * ε ^ 2 := by
    funext x
    exact unitDet_eq_expansion M x
  rw [hfun]
  convert ((hasDerivAt_const ε (1 : ℝ)).add
    ((hasDerivAt_id ε).const_mul M.trace)).add
    (((unitQuadratic M).hasDerivAt ε).mul ((hasDerivAt_id ε).pow 2)) using 1 <;>
    (try ext x) <;>
    simp [unitDetSlope, id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;> ring

lemma deriv_unitDet (M : Matrix n n ℝ) :
    deriv (unitDet M) = unitDetSlope M := by
  funext ε
  exact (hasDerivAt_unitDet M ε).deriv

lemma hasDerivAt_deriv_unitDet_zero (M : Matrix n n ℝ) :
    HasDerivAt (deriv (unitDet M)) (2 * (unitQuadratic M).eval 0) 0 := by
  rw [deriv_unitDet]
  unfold unitDetSlope
  convert (hasDerivAt_const (0 : ℝ) M.trace).add
    ((((unitQuadratic M).derivative.hasDerivAt 0).mul ((hasDerivAt_id 0).pow 2)).add
      (((unitQuadratic M).hasDerivAt 0).mul ((hasDerivAt_id 0).const_mul 2))) using 1 <;>
    (try ext x) <;>
    simp [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;> ring

lemma eventually_deriv_log_unitDet (M : Matrix n n ℝ) :
    (fun ε => deriv (fun x => Real.log (unitDet M x)) ε) =ᶠ[𝓝 0]
      (fun ε => unitDetSlope M ε / unitDet M ε) := by
  have h0 : unitDet M 0 ≠ 0 := by simp [unitDet]
  filter_upwards [(hasDerivAt_unitDet M 0).continuousAt.eventually_ne h0] with ε hε
  exact ((hasDerivAt_unitDet M ε).log hε).deriv

/-- The second logarithmic derivative is twice the quadratic coefficient
minus the square of the trace. -/
theorem iteratedDeriv_two_log_unitDet (M : Matrix n n ℝ) :
    iteratedDeriv 2 (fun ε => Real.log (unitDet M ε)) 0 =
      2 * (unitQuadratic M).eval 0 - M.trace ^ 2 := by
  have h0 : unitDet M 0 ≠ 0 := by simp [unitDet]
  have hQ := (hasDerivAt_deriv_unitDet_zero M).div (hasDerivAt_unitDet M 0) h0
  have hQ' : HasDerivAt (fun ε => unitDetSlope M ε / unitDet M ε)
      (2 * (unitQuadratic M).eval 0 - M.trace ^ 2) 0 := by
    convert hQ using 1
    · rw [deriv_unitDet]
      ext ε
      rfl
    · rw [(hasDerivAt_unitDet M 0).deriv]
      simp [unitDetSlope, unitDet]
      ring
  have hL := hQ'.congr_of_eventuallyEq (eventually_deriv_log_unitDet M)
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ]
  simp only [iteratedDeriv_one]
  exact hL.deriv

lemma unitQuadratic_eval_zero (M : Matrix n n ℝ) :
    (unitQuadratic M).eval 0 =
      (Matrix.det (1 + (Polynomial.X : ℝ[X]) • M.map Polynomial.C)).coeff 2 := by
  simp [unitQuadratic, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX]

section LinearOrder
variable [LinearOrder n]

lemma two_mul_unitQuadratic_eval_zero (M : Matrix n n ℝ) :
    2 * (unitQuadratic M).eval 0 = M.trace ^ 2 - (M * M).trace := by
  rw [unitQuadratic_eval_zero, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact sum_minors_two_eq_trace M

/-- **General finite-dimensional normalized log-determinant formula.** -/
theorem iteratedDeriv_two_log_unitDet_eq_neg_trace_sq (M : Matrix n n ℝ) :
    iteratedDeriv 2 (fun ε => Real.log (unitDet M ε)) 0 = -(M * M).trace := by
  rw [iteratedDeriv_two_log_unitDet]
  have h := two_mul_unitQuadratic_eval_zero M
  linarith

end LinearOrder
namespace Bridge

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex diagonal with entries `a i`. -/
def base (a : n → ℝ) : Matrix n n ℂ := Matrix.diagonal fun i => (a i : ℂ)

/-- Positive square-root factor of `base a`. -/
def root (a : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => (Real.sqrt (a i) : ℂ)

/-- Inverse positive square-root factor of `base a`. -/
def invRoot (a : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => ((Real.sqrt (a i) : ℂ)⁻¹)

/-- Hermitian normalization of the perturbation. -/
def scaled (a : n → ℝ) (E : Matrix n n ℂ) : Matrix n n ℂ :=
  invRoot a * E * invRoot a

/-- The actual Hermitian line `D + εE` in the eigenbasis of `H + ηI`. -/
def curve (a : n → ℝ) (E : Matrix n n ℂ) (ε : ℝ) : Matrix n n ℂ :=
  base a + ε • E

lemma invRoot_mul_root (a : n → ℝ) (ha : ∀ i, 0 < a i) :
    invRoot a * root a = 1 := by
  rw [invRoot, root, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    have hs : (Real.sqrt (a i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ((Real.sqrt_ne_zero').mpr (ha i))
    simp [Matrix.diagonal, hs]
  · simp [Matrix.diagonal, h]

lemma root_mul_invRoot (a : n → ℝ) (ha : ∀ i, 0 < a i) :
    root a * invRoot a = 1 := by
  rw [invRoot, root, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    have hs : (Real.sqrt (a i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ((Real.sqrt_ne_zero').mpr (ha i))
    simp [Matrix.diagonal, hs]
  · simp [Matrix.diagonal, h]

lemma root_mul_root (a : n → ℝ) (ha : ∀ i, 0 < a i) :
    root a * root a = base a := by
  rw [root, base, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal, ← Complex.ofReal_mul, Real.mul_self_sqrt (ha i).le]
  · simp [Matrix.diagonal, h]

lemma invRoot_mul_invRoot (a : n → ℝ) (ha : ∀ i, 0 < a i) :
    invRoot a * invRoot a = diagonalResolvent a := by
  rw [invRoot, diagonalResolvent, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (ha i).le]
  · simp [Matrix.diagonal, h]

lemma curve_eq_factor (a : n → ℝ) (ha : ∀ i, 0 < a i) (E : Matrix n n ℂ) (ε : ℝ) :
    curve a E ε = root a * (1 + ε • scaled a E) * root a := by
  rw [scaled]
  symm
  calc
    root a * (1 + ε • (invRoot a * E * invRoot a)) * root a =
        root a * root a + ε • ((root a * invRoot a) * E * (invRoot a * root a)) := by
      noncomm_ring
    _ = curve a E ε := by
      rw [root_mul_root a ha, root_mul_invRoot a ha, invRoot_mul_root a ha]
      simp [curve]

lemma isHermitian_scaled (a : n → ℝ) {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    (scaled a E).IsHermitian := by
  have hT : (invRoot a)ᴴ = invRoot a := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [invRoot, Matrix.conjTranspose_apply]
    · simp [invRoot, Matrix.conjTranspose_apply, Matrix.diagonal, h, Ne.symm h]
  rw [scaled]
  simpa [hT] using Matrix.isHermitian_mul_mul_conjTranspose (invRoot a) hE

lemma det_unitary_conj (U : Matrix.unitaryGroup n ℂ) (B : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * B * star U).det = B.det := by
  calc
    ((U : Matrix n n ℂ) * B * star U).det =
        B.det * ((star U : Matrix n n ℂ) * U).det := by
      simp only [Matrix.det_mul, Unitary.coe_star]
      ring
    _ = B.det := by rw [Unitary.coe_star_mul_self, Matrix.det_one, mul_one]

lemma trace_unitary_conj (U : Matrix.unitaryGroup n ℂ) (B : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * B * star U).trace = B.trace := by
  calc
    ((U : Matrix n n ℂ) * B * star U).trace =
        ((star U : Matrix n n ℂ) * (U * B)).trace := by
      rw [Matrix.trace_mul_comm, Unitary.coe_star]
    _ = (((star U : Matrix n n ℂ) * U) * B).trace := by
      rw [Matrix.mul_assoc]
    _ = B.trace := by rw [Unitary.coe_star_mul_self, Matrix.one_mul]

/-- A real diagonal family, coerced entrywise to a complex matrix. -/
def complexDiagonal (μ : n → ℝ) : Matrix n n ℂ := Matrix.diagonal fun i => (μ i : ℂ)

lemma scaled_one_add_eq_unitary_conj (a : n → ℝ) {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (ε : ℝ) :
    let hS := isHermitian_scaled a hE
    let U := hS.eigenvectorUnitary
    1 + ε • scaled a E =
      (U : Matrix n n ℂ) * (1 + ε • complexDiagonal hS.eigenvalues) * star U := by
  intro hS U
  have hspec := hS.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  conv_lhs => rw [hspec]
  calc
    1 + ε • ((U : Matrix n n ℂ) * complexDiagonal hS.eigenvalues * star U) =
        (U : Matrix n n ℂ) * star U + ε • ((U : Matrix n n ℂ) *
          complexDiagonal hS.eigenvalues * star U) := by
      rw [Unitary.coe_star, Unitary.mul_star_self_of_mem U.prop]
    _ = (U : Matrix n n ℂ) * (1 + ε • complexDiagonal hS.eigenvalues) * star U := by
      noncomm_ring

lemma det_one_add_scaled (a : n → ℝ) {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (ε : ℝ) :
    let hS := isHermitian_scaled a hE
    (1 + ε • scaled a E).det = (1 + ε • complexDiagonal hS.eigenvalues).det := by
  intro hS
  rw [scaled_one_add_eq_unitary_conj a hE]
  exact det_unitary_conj _ _

lemma trace_RERE_eq_scaled_sq (a : n → ℝ) (ha : ∀ i, 0 < a i) (E : Matrix n n ℂ) :
    (diagonalResolvent a * E * diagonalResolvent a * E).trace =
      (scaled a E * scaled a E).trace := by
  rw [← invRoot_mul_invRoot a ha]
  calc
    (invRoot a * invRoot a * E * (invRoot a * invRoot a) * E).trace =
        (invRoot a * (invRoot a * E * (invRoot a * invRoot a) * E)).trace := by
      congr 1
      noncomm_ring
    _ = ((invRoot a * E * (invRoot a * invRoot a) * E) * invRoot a).trace := by
      rw [Matrix.trace_mul_comm]
    _ = (scaled a E * scaled a E).trace := by
      unfold scaled
      congr 1
      noncomm_ring

lemma scaled_sq_eq_unitary_conj (a : n → ℝ) {E : Matrix n n ℂ}
    (hE : E.IsHermitian) :
    let hS := isHermitian_scaled a hE
    let U := hS.eigenvectorUnitary
    scaled a E * scaled a E =
      (U : Matrix n n ℂ) *
        (complexDiagonal hS.eigenvalues * complexDiagonal hS.eigenvalues) * star U := by
  intro hS U
  have hspec := hS.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  conv_lhs => rw [hspec]
  calc
    (U : Matrix n n ℂ) * complexDiagonal hS.eigenvalues * star U *
        (U * complexDiagonal hS.eigenvalues * star U) =
      (U : Matrix n n ℂ) * complexDiagonal hS.eigenvalues * (star U * U) *
        complexDiagonal hS.eigenvalues * star U := by noncomm_ring
    _ = (U : Matrix n n ℂ) *
        (complexDiagonal hS.eigenvalues * complexDiagonal hS.eigenvalues) * star U := by
      rw [Unitary.coe_star, Unitary.coe_star_mul_self]
      noncomm_ring

lemma trace_RERE_eq_eigenvalue_sq_sum (a : n → ℝ) (ha : ∀ i, 0 < a i)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    let hS := isHermitian_scaled a hE
    (diagonalResolvent a * E * diagonalResolvent a * E).trace =
      ((∑ i, (hS.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
  intro hS
  rw [trace_RERE_eq_scaled_sq a ha, scaled_sq_eq_unitary_conj a hE,
    trace_unitary_conj, complexDiagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

lemma det_base (a : n → ℝ) :
    (base a).det = ((∏ i, a i : ℝ) : ℂ) := by
  simp [base]

lemma det_complexDiagonal_unitDet (μ : n → ℝ) (ε : ℝ) :
    (1 + ε • complexDiagonal μ).det = ((unitDet (Matrix.diagonal μ) ε : ℝ) : ℂ) := by
  have hc : 1 + ε • complexDiagonal μ = complexDiagonal (fun i => 1 + ε * μ i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [complexDiagonal, Matrix.diagonal, RCLike.real_smul_eq_coe_smul]
    · simp [complexDiagonal, Matrix.diagonal, h]
  have hr : 1 + ε • Matrix.diagonal μ = Matrix.diagonal (fun i => 1 + ε * μ i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [hc, complexDiagonal, Matrix.det_diagonal, unitDet, hr, Matrix.det_diagonal]
  push_cast
  rfl

lemma curve_det_eq_model (a : n → ℝ) (ha : ∀ i, 0 < a i)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) (ε : ℝ) :
    let hS := isHermitian_scaled a hE
    (curve a E ε).det =
      (((∏ i, a i) * unitDet (Matrix.diagonal hS.eigenvalues) ε : ℝ) : ℂ) := by
  intro hS
  rw [curve_eq_factor a ha]
  calc
    (root a * (1 + ε • scaled a E) * root a).det =
        (base a).det * (1 + ε • scaled a E).det := by
      simp only [Matrix.det_mul]
      rw [show (root a).det * (1 + ε • scaled a E).det * (root a).det =
        (root a * root a).det * (1 + ε • scaled a E).det by
          rw [Matrix.det_mul]
          ring]
      rw [root_mul_root a ha]
    _ = ((∏ i, a i : ℝ) : ℂ) * (1 + ε • complexDiagonal hS.eigenvalues).det := by
      rw [det_base, det_one_add_scaled a hE]
    _ = (((∏ i, a i) * unitDet (Matrix.diagonal hS.eigenvalues) ε : ℝ) : ℂ) := by
      rw [det_complexDiagonal_unitDet]
      push_cast
      rfl

lemma base_nonsing_inv (a : n → ℝ) (ha : ∀ i, a i ≠ 0) :
    (base a)⁻¹ = diagonalResolvent a := by
  apply Matrix.inv_eq_left_inv
  rw [base, diagonalResolvent, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    have hi : (a i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha i)
    simp [Matrix.diagonal, hi]
  · simp [Matrix.diagonal, h]

lemma eventually_log_curve (a : n → ℝ) (ha : ∀ i, 0 < a i)
    {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    let hS := isHermitian_scaled a hE
    (fun ε => Real.log ((curve a E ε).det.re)) =ᶠ[𝓝 0]
      (fun ε => Real.log (∏ i, a i) +
        Real.log (unitDet (Matrix.diagonal hS.eigenvalues) ε)) := by
  intro hS
  have h0 : unitDet (Matrix.diagonal hS.eigenvalues) 0 ≠ 0 := by simp [unitDet]
  have hP : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  filter_upwards [(hasDerivAt_unitDet (Matrix.diagonal hS.eigenvalues) 0).continuousAt.eventually_ne h0]
    with ε hε
  rw [curve_det_eq_model a ha hE]
  simp only [Complex.ofReal_re]
  exact Real.log_mul (ne_of_gt hP) hε

/-- The second derivative in the eigenbasis is the negative sum of the
squared eigenvalues of the Hermitian normalization. -/
theorem iteratedDeriv_two_log_curve_eigenvalues [LinearOrder n]
    (a : n → ℝ) (ha : ∀ i, 0 < a i) {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    let hS := isHermitian_scaled a hE
    iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 =
      -∑ i, (hS.eigenvalues i) ^ 2 := by
  intro hS
  calc
    iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 =
        iteratedDeriv 2 (fun ε => Real.log (∏ i, a i) +
          Real.log (unitDet (Matrix.diagonal hS.eigenvalues) ε)) 0 :=
      (eventually_log_curve a ha hE).iteratedDeriv_eq 2
    _ = iteratedDeriv 2 (fun ε => Real.log (unitDet (Matrix.diagonal hS.eigenvalues) ε)) 0 := by
      exact iteratedDeriv_const_add (by norm_num) _
    _ = -((Matrix.diagonal hS.eigenvalues * Matrix.diagonal hS.eigenvalues).trace) :=
      iteratedDeriv_two_log_unitDet_eq_neg_trace_sq _
    _ = -∑ i, (hS.eigenvalues i) ^ 2 := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      simp [pow_two]

/-- **General B24 derivative formula**, for every Hermitian perturbation of
an arbitrary finite-dimensional positive diagonal shift. -/
theorem iteratedDeriv_two_log_curve_eq_neg_trace [LinearOrder n]
    (a : n → ℝ) (ha : ∀ i, 0 < a i) {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    ((iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 : ℝ) : ℂ) =
      -(diagonalResolvent a * E * diagonalResolvent a * E).trace := by
  rw [iteratedDeriv_two_log_curve_eigenvalues a ha hE,
    trace_RERE_eq_eigenvalue_sq_sum a ha hE]
  push_cast
  rfl

/-- The card's two second-order forms and its second derivative, in every
finite dimension.  Here `a i = λ i + η`. -/
theorem b24_general_c2 [LinearOrder n]
    (a : n → ℝ) (ha : ∀ i, 0 < a i) {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    (1 / 2 : ℝ) * iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, Complex.normSq (E i j) / (a i * a j) := by
  have ha0 : ∀ i, a i ≠ 0 := fun i => ne_of_gt (ha i)
  have h := iteratedDeriv_two_log_curve_eq_neg_trace a ha hE
  rw [trace_RERE_eq_eigenbasis_sum a ha0 hE] at h
  have hr : iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 =
      -∑ i, ∑ j, Complex.normSq (E i j) / (a i * a j) := by
    exact_mod_cast h
  rw [hr]
  ring

/-- The trace-form derivative theorem in the canonical `N`-dimensional case. -/
theorem iteratedDeriv_two_log_curve_eq_neg_trace_fin {N : ℕ}
    (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) {E : Matrix (Fin N) (Fin N) ℂ}
    (hE : E.IsHermitian) :
    ((iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 : ℝ) : ℂ) =
      -(diagonalResolvent a * E * diagonalResolvent a * E).trace :=
  iteratedDeriv_two_log_curve_eq_neg_trace a ha hE

/-- **B24 general `n`, final form.** No auxiliary index-order hypothesis is
needed: the canonical `Fin N` order is only an internal enumeration device. -/
theorem b24_general_c2_fin {N : ℕ}
    (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) {E : Matrix (Fin N) (Fin N) ℂ}
    (hE : E.IsHermitian) :
    (1 / 2 : ℝ) * iteratedDeriv 2 (fun ε => Real.log ((curve a E ε).det.re)) 0 =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, Complex.normSq (E i j) / (a i * a j) :=
  b24_general_c2 a ha hE

end Bridge


/- Axiom audit: every proved declaration in this file. -/
#print axioms RelationalAtlas.B24General.trace_diagonalResolvent_mul
#print axioms RelationalAtlas.B24General.hermitian_weighted_entry
#print axioms RelationalAtlas.B24General.trace_RERE_eq_eigenbasis_sum
#print axioms RelationalAtlas.B24General.two_c2_forms_hermitian_general
#print axioms RelationalAtlas.B24General.det_submatrix_pair
#print axioms RelationalAtlas.B24General.sum_minors_two
#print axioms RelationalAtlas.B24General.lowerPairs_eq_ite_sum
#print axioms RelationalAtlas.B24General.minor_swap
#print axioms RelationalAtlas.B24General.sum_minor_eq_two_mul_lower
#print axioms RelationalAtlas.B24General.sum_minor_eq_trace
#print axioms RelationalAtlas.B24General.sum_minors_two_eq_trace
#print axioms RelationalAtlas.B24General.unitDet_eq_expansion
#print axioms RelationalAtlas.B24General.hasDerivAt_unitDet
#print axioms RelationalAtlas.B24General.deriv_unitDet
#print axioms RelationalAtlas.B24General.hasDerivAt_deriv_unitDet_zero
#print axioms RelationalAtlas.B24General.eventually_deriv_log_unitDet
#print axioms RelationalAtlas.B24General.iteratedDeriv_two_log_unitDet
#print axioms RelationalAtlas.B24General.unitQuadratic_eval_zero
#print axioms RelationalAtlas.B24General.two_mul_unitQuadratic_eval_zero
#print axioms RelationalAtlas.B24General.iteratedDeriv_two_log_unitDet_eq_neg_trace_sq
#print axioms RelationalAtlas.B24General.Bridge.invRoot_mul_root
#print axioms RelationalAtlas.B24General.Bridge.root_mul_invRoot
#print axioms RelationalAtlas.B24General.Bridge.root_mul_root
#print axioms RelationalAtlas.B24General.Bridge.invRoot_mul_invRoot
#print axioms RelationalAtlas.B24General.Bridge.curve_eq_factor
#print axioms RelationalAtlas.B24General.Bridge.isHermitian_scaled
#print axioms RelationalAtlas.B24General.Bridge.det_unitary_conj
#print axioms RelationalAtlas.B24General.Bridge.trace_unitary_conj
#print axioms RelationalAtlas.B24General.Bridge.scaled_one_add_eq_unitary_conj
#print axioms RelationalAtlas.B24General.Bridge.det_one_add_scaled
#print axioms RelationalAtlas.B24General.Bridge.trace_RERE_eq_scaled_sq
#print axioms RelationalAtlas.B24General.Bridge.scaled_sq_eq_unitary_conj
#print axioms RelationalAtlas.B24General.Bridge.trace_RERE_eq_eigenvalue_sq_sum
#print axioms RelationalAtlas.B24General.Bridge.det_base
#print axioms RelationalAtlas.B24General.Bridge.det_complexDiagonal_unitDet
#print axioms RelationalAtlas.B24General.Bridge.curve_det_eq_model
#print axioms RelationalAtlas.B24General.Bridge.base_nonsing_inv
#print axioms RelationalAtlas.B24General.Bridge.eventually_log_curve
#print axioms RelationalAtlas.B24General.Bridge.iteratedDeriv_two_log_curve_eigenvalues
#print axioms RelationalAtlas.B24General.Bridge.iteratedDeriv_two_log_curve_eq_neg_trace
#print axioms RelationalAtlas.B24General.Bridge.b24_general_c2
#print axioms RelationalAtlas.B24General.Bridge.iteratedDeriv_two_log_curve_eq_neg_trace_fin
#print axioms RelationalAtlas.B24General.Bridge.b24_general_c2_fin

end RelationalAtlas.B24General

