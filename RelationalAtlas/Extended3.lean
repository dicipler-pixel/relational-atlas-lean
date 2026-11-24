/-
Third batch: finite kernels and refutations for the Operator-First Relational Atlas.

This module collects the contributions of the third formalisation run (23 November 2026),
whose brief was to read each card's own displayed formula and try to break it before
proving it. Several sections are therefore *refutations* of a card as literally written,
followed by the corrected statement; each section says which it is. Nothing in
`Basic.lean`, `AtlasFormalCore.lean`, `Extended.lean` or `Extended2.lean` is modified.
-/
import Mathlib

noncomputable section


/-! ## B114 — hidden motion at order m (proof)

Integrated from `.ultramath/smwtty35w/m14/B114.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B114: the first surviving derivative of an idempotent path is tangent

The card assumes a `C^(m+1)` path of orthogonal projectors, but its displayed
identity is purely algebraic apart from differentiation.  The theorem below
uses only a path in a real normed algebra, idempotence, and `C^m` regularity at
the base point.  In particular, multiplication need not commute and the
elements need not be self-adjoint.
-/

open scoped Topology

namespace RelationalAtlas.B114

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- **B114, arbitrary first-surviving order.**  If every derivative of orders
`1, ..., m-1` of an idempotent-valued path vanishes at zero, then its `m`th
derivative satisfies the same tangent equation as a first derivative.

The hypothesis `0 < m` is essential: at `m = 0` the conclusion would say that
`P 0 = P 0 * P 0 + P 0 * P 0`, which already fails for the constant path at `1`. -/
theorem first_nonzero_iteratedDeriv_tangent
    (P : ℝ → A) (m : ℕ) (hm : 0 < m)
    (hP : ContDiffAt ℝ m P 0)
    (hid : ∀ t, P t * P t = P t)
    (hzero : ∀ k, 0 < k → k < m → iteratedDeriv k P 0 = 0) :
    iteratedDeriv m P 0 =
      P 0 * iteratedDeriv m P 0 + iteratedDeriv m P 0 * P 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hfun : P * P = P := funext hid
  calc
    iteratedDeriv (n + 1) P 0 = iteratedDeriv (n + 1) (P * P) 0 := by rw [hfun]
    _ = ∑ i ∈ Finset.range (n + 1 + 1),
        (n + 1).choose i * iteratedDeriv i P 0 * iteratedDeriv (n + 1 - i) P 0 :=
      iteratedDeriv_mul hP hP
    _ = P 0 * iteratedDeriv (n + 1) P 0 + iteratedDeriv (n + 1) P 0 * P 0 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have hinner :
          (∑ k ∈ Finset.range n,
            (n + 1).choose (k + 1) * iteratedDeriv (k + 1) P 0 *
              iteratedDeriv (n + 1 - (k + 1)) P 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        rw [hzero (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ hkn)]
        simp
      rw [hinner]
      simp only [iteratedDeriv_zero, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, Nat.choose_zero_right, zero_add]
      exact add_comm _ _

/-- The `m = 1` case is precisely the ordinary tangent equation `D = PD + DP`.
There are no lower positive orders to exclude. -/
theorem idempotent_deriv_tangent
    (P : ℝ → A) (hP : ContDiffAt ℝ 1 P 0)
    (hid : ∀ t, P t * P t = P t) :
    deriv P 0 = P 0 * deriv P 0 + deriv P 0 * P 0 := by
  rw [← iteratedDeriv_one]
  exact first_nonzero_iteratedDeriv_tangent P 1 (by decide) hP hid
    (fun k hk hkm => by omega)

/-- The literal formula is false if one silently allows `m = 0`: the constant
real path at `1` is idempotent, but the displayed order-zero tangent equation
would assert `1 = 1 + 1`. -/
theorem order_zero_literal_claim_false :
    let P : ℝ → ℝ := fun _ => 1
    (∀ t, P t * P t = P t) ∧
    ¬ (iteratedDeriv 0 P 0 =
      P 0 * iteratedDeriv 0 P 0 + iteratedDeriv 0 P 0 * P 0) := by
  simp

#print axioms RelationalAtlas.B114.first_nonzero_iteratedDeriv_tangent
#print axioms RelationalAtlas.B114.idempotent_deriv_tangent
#print axioms RelationalAtlas.B114.order_zero_literal_claim_false

end RelationalAtlas.B114


end

/-! ## B112 — the entrywise Sylvester condition (proof and compatibility witness)

Integrated from `.ultramath/smwtty35w/m7/B112.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B112 — the kernel decides whether the SLD exists

The source card displays

  `(p_i + p_j) L_ij = 2 V_ij`, and
  `p_i = p_j = 0 ⇒ V_ij must vanish`.

Its prose adds the two points that are easy to lose in a merely scalar
formalization: division solves every entry with nonzero denominator, while the
kernel--kernel block of `L` is arbitrary.  We prove the resulting existence
iff, an explicit solution with an arbitrary kernel block, uniqueness away from
that block, and Hermiticity of the solution.

Source: `atlas_cards_v7_html.zip`, `cards/html/B112.html`, SHA-256
`3f0064a5801386d55481395db5b3c374b2b5702f7f23b2bdc5dbc269d8f487b3`.
The density matrix itself is `diagonal p`; positivity of individual `p i`, trace
one, and distinctness of eigenvalues are not needed for the entrywise algebra.
-/

noncomputable section

open Matrix

namespace AtlasB112

variable {n : Type*}

/-- The explicit Sylvester solve.  `K` is the arbitrary kernel--kernel block.
On all other entries the denominator is nonzero by construction. -/
def sldSolve [DecidableEq n] (p : n → ℝ) (V K : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => if p i + p j = 0 then K i j
    else 2 * V i j / ((p i + p j : ℝ) : ℂ)

/-- Nonnegative eigenvalues have zero sum precisely on the kernel--kernel
block.  This is precisely where nonnegativity, rather than trace one or strict
positivity, is used. -/
theorem sum_eq_zero_iff_of_nonneg (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (i j : n) :
    p i + p j = 0 ↔ p i = 0 ∧ p j = 0 := by
  constructor
  · intro h
    constructor <;> linarith [hp i, hp j]
  · rintro ⟨hi, hj⟩
    rw [hi, hj, add_zero]

#print axioms sum_eq_zero_iff_of_nonneg

/-- The kernel compatibility condition is necessary for *every* complex
solution, with no nonnegativity or Hermiticity hypothesis needed. -/
theorem kernel_entry_eq_zero_of_entrywise {p : n → ℝ} {V L : Matrix n n ℂ}
    (h : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    {i j : n} (hi : p i = 0) (hj : p j = 0) : V i j = 0 := by
  have e := h i j
  simp [hi, hj] at e
  exact e

#print axioms kernel_entry_eq_zero_of_entrywise

/-- At a nonzero denominator every solution has the displayed quotient. -/
theorem eq_quotient_of_entrywise_of_sum_ne_zero {p : n → ℝ} {V L : Matrix n n ℂ}
    (h : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    {i j : n} (hij : p i + p j ≠ 0) :
    L i j = 2 * V i j / ((p i + p j : ℝ) : ℂ) := by
  have hc : ((p i : ℂ) + (p j : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr hij
  rw [Complex.ofReal_add]
  apply (eq_div_iff hc).2
  simpa [mul_comm] using h i j

#print axioms eq_quotient_of_entrywise_of_sum_ne_zero

/-- Exactly one zero eigenvalue is not an obstruction: if `p i = 0`, the
solution is `2 V ij / p j`. -/
theorem eq_quotient_of_entrywise_of_left_zero {p : n → ℝ} {V L : Matrix n n ℂ}
    (h : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    {i j : n} (hi : p i = 0) (hj : p j ≠ 0) :
    L i j = 2 * V i j / (p j : ℂ) := by
  have hc : (p j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hj
  apply (eq_div_iff hc).2
  simpa [hi, mul_comm] using h i j

#print axioms eq_quotient_of_entrywise_of_left_zero

/-- The symmetric one-zero case: if `p j = 0`, the solution is
`2 V ij / p i`.  No symmetrization or second denominator is involved. -/
theorem eq_quotient_of_entrywise_of_right_zero {p : n → ℝ} {V L : Matrix n n ℂ}
    (h : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    {i j : n} (hi : p i ≠ 0) (hj : p j = 0) :
    L i j = 2 * V i j / (p i : ℂ) := by
  have hc : (p i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
  apply (eq_div_iff hc).2
  simpa [hj, add_comm, mul_comm] using h i j

#print axioms eq_quotient_of_entrywise_of_right_zero

/-- On the kernel--kernel block the explicit solution is exactly the freely
chosen block `K`. -/
theorem sldSolve_apply_of_both_zero [DecidableEq n] (p : n → ℝ)
    (V K : Matrix n n ℂ) {i j : n} (hi : p i = 0) (hj : p j = 0) :
    sldSolve p V K i j = K i j := by
  simp [sldSolve, hi, hj]

#print axioms sldSolve_apply_of_both_zero

/-- Off the kernel--kernel block the explicit solution is the displayed
quotient. -/
theorem sldSolve_apply_of_sum_ne_zero [DecidableEq n] (p : n → ℝ)
    (V K : Matrix n n ℂ) {i j : n} (hij : p i + p j ≠ 0) :
    sldSolve p V K i j = 2 * V i j / ((p i + p j : ℝ) : ℂ) := by
  simp [sldSolve, hij]

#print axioms sldSolve_apply_of_sum_ne_zero

/-- The explicit block formula solves the card's literal entrywise equation.
Compatibility is used only on the zero-denominator branch. -/
theorem sldSolve_entrywise [DecidableEq n] (p : n → ℝ) (V K : Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i)
    (hker : ∀ i j, p i = 0 → p j = 0 → V i j = 0) (i j : n) :
    ((p i : ℂ) + (p j : ℂ)) * sldSolve p V K i j = 2 * V i j := by
  by_cases hij : p i + p j = 0
  · have hz := (sum_eq_zero_iff_of_nonneg p hp i j).1 hij
    simp [sldSolve, hz.1, hz.2, hker i j hz.1 hz.2]
  · have hc : (((p i + p j : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hij
    simp only [sldSolve, hij, ↓reduceIte]
    rw [← Complex.ofReal_add]
    field_simp

#print axioms sldSolve_entrywise

/-- Matrix form of the same theorem: with `ρ = diagonal p`, the SLD convention
is `ρ L + L ρ = 2 V`. -/
theorem sldSolve_matrix [Fintype n] [DecidableEq n] (p : n → ℝ)
    (V K : Matrix n n ℂ) (hp : ∀ i, 0 ≤ p i)
    (hker : ∀ i j, p i = 0 → p j = 0 → V i j = 0) :
    Matrix.diagonal (fun i => (p i : ℂ)) * sldSolve p V K +
        sldSolve p V K * Matrix.diagonal (fun i => (p i : ℂ)) = (2 : ℂ) • V := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm (sldSolve p V K i j) (p j : ℂ), ← add_mul]
  exact sldSolve_entrywise p V K hp hker i j

#print axioms sldSolve_matrix

/-- The literal existence claim is an iff: kernel--kernel compatibility is
both necessary and sufficient.  In particular an incompatible kernel entry is
a genuine obstruction, not something repairable by choosing another `L`. -/
theorem exists_entrywise_sld_iff [DecidableEq n] (p : n → ℝ) (V : Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) :
    (∃ L : Matrix n n ℂ,
      ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j) ↔
      ∀ i j, p i = 0 → p j = 0 → V i j = 0 := by
  constructor
  · rintro ⟨L, hL⟩ i j hi hj
    exact kernel_entry_eq_zero_of_entrywise hL hi hj
  · intro hker
    exact ⟨sldSolve p V 0, sldSolve_entrywise p V 0 hp hker⟩

#print axioms exists_entrywise_sld_iff

/-- Away from the zero denominators the solution is unique; the arbitrary
block `K` therefore parametrizes exactly the remaining freedom. -/
theorem eq_sldSolve_of_entrywise_of_sum_ne_zero [DecidableEq n]
    {p : n → ℝ} {V L K : Matrix n n ℂ}
    (hL : ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j)
    {i j : n} (hij : p i + p j ≠ 0) :
    L i j = sldSolve p V K i j := by
  rw [sldSolve_apply_of_sum_ne_zero p V K hij]
  exact eq_quotient_of_entrywise_of_sum_ne_zero hL hij

#print axioms eq_sldSolve_of_entrywise_of_sum_ne_zero

/-- If `V` and the freely chosen kernel block are Hermitian, so is the explicit
complex solution.  The real denominator is unchanged by conjugation. -/
theorem sldSolve_isHermitian [DecidableEq n] (p : n → ℝ) {V K : Matrix n n ℂ}
    (hV : V.IsHermitian) (hK : K.IsHermitian) :
    (sldSolve p V K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : p i + p j = 0
  · have hji : p j + p i = 0 := by rwa [add_comm]
    simp [sldSolve, hij, hji, hK.apply i j]
  · have hji : p j + p i ≠ 0 := by rwa [add_comm]
    simp only [sldSolve, hij, hji, ↓reduceIte]
    rw [add_comm (p j) (p i)]
    change (starRingEnd ℂ) (2 * V j i / (((p i + p j : ℝ) : ℂ))) = _
    rw [map_div₀, map_mul, Complex.conj_ofReal]
    norm_num only [map_ofNat]
    exact congrArg (fun z : ℂ => 2 * z / (((p i + p j : ℝ) : ℂ))) (hV.apply i j)

#print axioms sldSolve_isHermitian

/-- The exact SLD existence theorem, including its Hermitian requirement.
Hermitian `V` is needed only for the converse construction of a Hermitian `L`;
it is not needed for the obstruction direction or for an arbitrary complex
solution. -/
theorem exists_isHermitian_entrywise_sld_iff [DecidableEq n]
    (p : n → ℝ) {V : Matrix n n ℂ} (hp : ∀ i, 0 ≤ p i) (hV : V.IsHermitian) :
    (∃ L : Matrix n n ℂ, L.IsHermitian ∧
      ∀ i j, ((p i : ℂ) + (p j : ℂ)) * L i j = 2 * V i j) ↔
      ∀ i j, p i = 0 → p j = 0 → V i j = 0 := by
  constructor
  · rintro ⟨L, -, hL⟩ i j hi hj
    exact kernel_entry_eq_zero_of_entrywise hL hi hj
  · intro hker
    refine ⟨sldSolve p V 0, ?_, sldSolve_entrywise p V 0 hp hker⟩
    apply sldSolve_isHermitian p hV
    exact Matrix.IsHermitian.ext (by simp)

#print axioms exists_isHermitian_entrywise_sld_iff

/-- A one-dimensional incompatible witness: `p = 0`, `V = 1` has no SLD.
This certifies that the extra compatibility condition cannot be deleted. -/
theorem no_sld_zero_state_unit_variation :
    ¬ ∃ L : Matrix (Fin 1) (Fin 1) ℂ,
      ((0 : ℝ) : ℂ) * L 0 0 = 2 * (1 : ℂ) := by
  rintro ⟨L, h⟩
  norm_num at h

#print axioms no_sld_zero_state_unit_variation

end AtlasB112


end

/-! ## B15 — the raw log-det comparator is not subadditive (REFUTATION)

Integrated from `.ultramath/smwtty35w/m1/B15.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B15: raw log-det divergence is not subadditive

The scalar case of the comparator recorded in `atlas/coverage/coverage.json` is
`S a b = log ((a+b)/2) - (log a)/2 - (log b)/2`.
-/

namespace AtlasB15

/-- Scalar restriction of the card's symmetric log-determinant comparator. -/
noncomputable def S (a b : ℝ) : ℝ :=
  Real.log ((a + b) / 2) - Real.log a / 2 - Real.log b / 2

/-- The one-step cost from `1` to `4` is exactly `log (5/4)`. -/
theorem direct_cost : S 1 4 = Real.log (5 / 4) := by
  have log4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num [S, Real.log_div, Real.log_mul]
  rw [log4]
  ring

/-- The sum of the costs from `1` to `2` and from `2` to `4` is exactly
`log (9/8)`. -/
theorem split_cost : S 1 2 + S 2 4 = Real.log (9 / 8) := by
  have log4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have log9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have log8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  norm_num [S, Real.log_div, Real.log_mul]
  rw [log4, log9, log8]
  ring

/-- The two pieces are equal: `2` is the geometric midpoint of `1` and `4`.
The counterexample is a two-step scalar affine-invariant geodesic, not an
arbitrary off-geodesic triangle. -/
theorem equal_geodesic_steps : S 1 2 = S 2 4 := by
  have log4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num [S, Real.log_div, Real.log_mul]
  rw [log4]
  ring

/-- Finite counterexample to triangle subadditivity of the raw comparator. -/
theorem split_lt_direct : S 1 2 + S 2 4 < S 1 4 := by
  rw [split_cost, direct_cost]
  apply Real.log_lt_log <;> norm_num

/-- The universal scalar triangle-subadditivity assertion is false. -/
theorem not_subadditive :
    ¬ (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → S a c ≤ S a b + S b c) := by
  intro h
  have := h 1 2 4 (by norm_num) (by norm_num) (by norm_num)
  exact (not_le_of_gt split_lt_direct) this

#print axioms direct_cost
#print axioms split_cost
#print axioms equal_geodesic_steps
#print axioms split_lt_direct
#print axioms not_subadditive

end AtlasB15


end

/-! ## B119 — Christoffel normalisation and the Killing hypothesis (proof; two traps)

Integrated from `.ultramath/smwtty35w/m8/B119.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B119 — the metric dipole also bends the path

The published display is
`Γ_ij,k = ½(G_ik,j + G_jk,i − G_ij,k)`, where
`G_ij,k = ∂_k g_ij`, together with the transverse coefficient
`−½ ∂_y g_xx`. Its witness is `g_xx = (9/4) sin² y`, with
`Γ_xx,y = −(9/4) sin y cos y` and value `−9/8` at `y = π/4`.

`christoffelFirst` below is a first-kind Christoffel symbol. The argument
`D a b c` is the derivative `∂_a g_bc`; values of the metric itself are not
needed for this algebraic identity. No symmetry or nondegeneracy assumption
is hidden in this definition.
-/

namespace AtlasB119

noncomputable section

/-- First-kind Christoffel data, exactly with the card's ordering of indices. -/
def christoffelFirst {ι : Type*} (D : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  (1 / 2 : ℝ) * (D j i k + D i j k - D k i j)

/-- Symmetry in the two lower indices before the comma uses symmetry of the
metric, here expressed as `D k i j = D k j i`; it is not an identity of an
arbitrary derivative array. -/
theorem christoffelFirst_sym {ι : Type*} (D : ι → ι → ι → ℝ) (i j k : ι)
    (h : D k i j = D k j i) :
    christoffelFirst D i j k = christoffelFirst D j i k := by
  unfold christoffelFirst
  rw [h]
  ring

/-- The two equal first terms in the `(xx,y)` specialization combine to one
`∂_x g_xy`, rather than being silently discarded. -/
theorem christoffelFirst_xx_y_expanded {ι : Type*}
    (D : ι → ι → ι → ℝ) (x y : ι) :
    christoffelFirst D x x y = D x x y - (1 / 2 : ℝ) * D y x x := by
  unfold christoffelFirst
  ring

/-- If `x` is a Killing direction, then in particular `∂_x g_xy = 0`.
The displayed transverse formula follows with exactly the card's factor
`−1/2`. Neither `x ≠ y` nor nondegeneracy is needed for this first-kind
identity. -/
theorem christoffelFirst_xx_y_of_killing {ι : Type*}
    (D : ι → ι → ι → ℝ) (x y : ι)
    (hx : D x x y = 0) :
    christoffelFirst D x x y = -(1 / 2 : ℝ) * D y x x := by
  rw [christoffelFirst_xx_y_expanded, hx]
  ring

/-- A genuine Killing direction (all `x`-derivatives of metric entries vanish)
supplies the hypothesis used above. -/
theorem christoffelFirst_xx_y_of_killing_all {ι : Type*}
    (D : ι → ι → ι → ℝ) (x y : ι)
    (hx : ∀ a b, D x a b = 0) :
    christoffelFirst D x x y = -(1 / 2 : ℝ) * D y x x :=
  christoffelFirst_xx_y_of_killing D x y (hx x y)

/-- The transverse coefficient for a metric depending on coordinates `x,y`.
Only the mixed entry can depend on `x` in this declaration; `gxx` is already
written as a function of `y`, as it can be after imposing the Killing
condition. -/
def transverseCoefficient (gxy : ℝ → ℝ → ℝ) (gxx : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => gxy t y) x - (1 / 2 : ℝ) * deriv gxx y

/-- Vanishing of the actual `x`-derivative, not merely vanishing of the value
`gxy x y`, gives the transverse formula. -/
theorem transverseCoefficient_of_deriv_x_gxy_eq_zero
    (gxy : ℝ → ℝ → ℝ) (gxx : ℝ → ℝ) (x y : ℝ)
    (h : deriv (fun t => gxy t y) x = 0) :
    transverseCoefficient gxy gxx x y = -(1 / 2 : ℝ) * deriv gxx y := by
  simp [transverseCoefficient, h]

/-- The card's `g_xx(y) = (9/4) sin² y`. -/
def cardGxx (y : ℝ) : ℝ := (9 / 4 : ℝ) * Real.sin y ^ 2

/-- Its mixed entry is identically zero. -/
def cardGxy (_x _y : ℝ) : ℝ := 0

/-- The card's transverse coefficient, before evaluating its derivative. -/
def cardTransverse (y : ℝ) : ℝ :=
  transverseCoefficient cardGxy cardGxx 0 y

/-- Derivative of the card's metric entry: `(9/4)(sin²y)' = (9/2)sin y cos y`. -/
theorem deriv_cardGxx (y : ℝ) :
    deriv cardGxx y = (9 / 2 : ℝ) * Real.sin y * Real.cos y := by
  have h := ((Real.hasDerivAt_sin y).pow 2).const_mul (9 / 4 : ℝ)
  rw [show deriv cardGxx y = _ from h.deriv]
  ring

/-- The two readings in the card agree exactly, including `9/4`, not `9/2`,
in the final coefficient. -/
theorem cardTransverse_eq (y : ℝ) :
    cardTransverse y = -(9 / 4 : ℝ) * Real.sin y * Real.cos y := by
  rw [cardTransverse, transverseCoefficient_of_deriv_x_gxy_eq_zero]
  · rw [deriv_cardGxx]
    ring
  · simp [cardGxy]

/-- The displayed value at `π/4` is exactly `−9/8`. -/
theorem cardTransverse_pi_div_four : cardTransverse (Real.pi / 4) = -9 / 8 := by
  rw [cardTransverse_eq, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- In fact the displayed point is a global minimum, so the figure's word
"deepest" is justified rather than merely a sampled value. -/
theorem neg_nine_div_eight_le_cardTransverse (y : ℝ) :
    -9 / 8 ≤ cardTransverse y := by
  rw [cardTransverse_eq]
  have htrig := Real.sin_sq_add_cos_sq y
  have hsq := sq_nonneg (Real.sin y - Real.cos y)
  nlinarith

/-!
## The two normalizations

For a diagonal two-dimensional metric, raising the final index multiplies the
first-kind coefficient by `g^{yy} = 1 / g_yy`.  Thus the card's response
coefficient is the coordinate acceleration coefficient without further ado
only when `g_yy = 1`; in general the inverse-metric factor must be retained.
-/

/-- The `(xx,y)` coefficient after raising `y` in a diagonal metric. -/
def raisedDiagonal (gyy lower : ℝ) : ℝ := lower / gyy

/-- The unit transverse metric removes precisely the extra normalization. -/
theorem raisedDiagonal_gyy_eq_one (lower : ℝ) :
    raisedDiagonal 1 lower = lower := by
  simp [raisedDiagonal]

/-- Raising an index is not the identity away from the `g_yy = 1`
normalization.  At the card's witness point, `g_yy = 4` gives `−9/32`, in
contrast to the first-kind value `−9/8`. -/
theorem raised_card_pi_div_four_gyy_four :
    raisedDiagonal 4 (cardTransverse (Real.pi / 4)) = -9 / 32 := by
  rw [cardTransverse_pi_div_four]
  norm_num [raisedDiagonal]

/-!
## Why the Killing derivative, rather than `g_xy = 0`, matters

The following metric is positive definite at `(0,1)`:
`g = [[1, x*y], [x*y, 2]]`.  There its mixed entry is zero, but
`∂_x g_xy = y = 1`.  Since `g_xx = 1`, the right side of the transverse
formula is zero while the actual first-kind coefficient is one.  This is not
a counterexample to the card (which assumes a Killing direction); it rules
out replacing that assumption by pointwise vanishing of `g_xy`.
-/

/-- A mixed metric entry whose value and `x`-derivative behave differently. -/
def probeGxy (x y : ℝ) : ℝ := x * y

/-- Constant nonzero `g_xx` for the probe. -/
def probeGxx (_y : ℝ) : ℝ := 1

/-- The probe's mixed entry vanishes at `(0,1)`. -/
theorem probeGxy_zero : probeGxy 0 1 = 0 := by
  norm_num [probeGxy]

/-- The probe metric is nondegenerate at `(0,1)`: its determinant is two. -/
theorem probe_metric_det_at_zero_one :
    probeGxx 1 * 2 - probeGxy 0 1 * probeGxy 0 1 = 2 := by
  norm_num [probeGxx, probeGxy]

/-- In fact the determinant is positive at that point, with positive diagonal
entries, so this is a positive-definite probe rather than a fold artifact. -/
theorem probe_metric_positive_definite_at_zero_one :
    0 < probeGxx 1 ∧ 0 < (2 : ℝ) ∧
      0 < probeGxx 1 * 2 - probeGxy 0 1 * probeGxy 0 1 := by
  norm_num [probeGxx, probeGxy]

/-- The literal pointwise-`g_xy = 0` version of the implication is false. -/
theorem probe_not_transverse_formula :
    transverseCoefficient probeGxy probeGxx 0 1 ≠
      -(1 / 2 : ℝ) * deriv probeGxx 1 := by
  norm_num [transverseCoefficient, probeGxy, probeGxx]

/-- The complete finite witness in one statement: nondegeneracy (indeed
positive-definiteness), pointwise vanishing of the mixed entry, and failure of
the transverse formula without the Killing-derivative hypothesis. -/
theorem pointwise_vanishing_gxy_is_insufficient :
    probeGxy 0 1 = 0 ∧
      0 < probeGxx 1 ∧
      0 < probeGxx 1 * 2 - probeGxy 0 1 * probeGxy 0 1 ∧
      transverseCoefficient probeGxy probeGxx 0 1 ≠
        -(1 / 2 : ℝ) * deriv probeGxx 1 := by
  exact ⟨probeGxy_zero, by norm_num [probeGxx],
    by norm_num [probeGxx, probeGxy], probe_not_transverse_formula⟩

#print axioms christoffelFirst_sym
#print axioms christoffelFirst_xx_y_expanded
#print axioms christoffelFirst_xx_y_of_killing
#print axioms christoffelFirst_xx_y_of_killing_all
#print axioms transverseCoefficient_of_deriv_x_gxy_eq_zero
#print axioms deriv_cardGxx
#print axioms cardTransverse_eq
#print axioms cardTransverse_pi_div_four
#print axioms neg_nine_div_eight_le_cardTransverse
#print axioms raisedDiagonal_gyy_eq_one
#print axioms raised_card_pi_div_four_gyy_four
#print axioms probeGxy_zero
#print axioms probe_metric_det_at_zero_one
#print axioms probe_metric_positive_definite_at_zero_one
#print axioms probe_not_transverse_formula
#print axioms pointwise_vanishing_gxy_is_insufficient

end
end AtlasB119


end

/-! ## B86 — norm, sign and the three determinant readings (completion; ledger corrected)

Integrated from `.ultramath/smwtty35w/m5/B86Completion.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B86 completion: the norm and what reciprocity does (not) imply

The HTML display is `AᵀB = BA`, `B = diag(t/g)`, and
`‖B‖ = maxᵢ tᵢ/gᵢ`.  The ledger also gives
`M = 2(Dt − g tᵀ)` and the Check hypothesis `∀ i, 0 < g i`, and says that
reciprocity forces `det g ≤ 0` for symmetric probes.  The current HTML prose
makes the stronger statement `det g ≡ 0` on the regular stratum.

This file keeps the following issues separate.

* The operator norm of a real diagonal matrix is the maximum of the
  **absolute values** of its entries.  The displayed formula therefore needs
  nonnegativity of `t/g`; `g i > 0` alone is insufficient.  We prove the
  corrected formula under `0 ≤ t i` and give a one-coordinate signed witness.
* Mere symmetry of a real two-by-two probe does not imply nonpositive
  determinant: the identity matrix is a counterexample, even in the presence
  of a concrete regular B86 reciprocity pairing.
* For the actual bilinear probe `Re(u uᵀ)` (no conjugate), the determinant is
  the negative square `-Im(conj u₁ u₂)²`; no sign condition has to be added.
  This is a property of the bilinear probe, not a consequence of reciprocity.
  A generic such probe has nonzero determinant while all the regular B86
  pairing hypotheses hold, refuting the stronger HTML `det g ≡ 0` wording.
  It vanishes exactly when the two amplitudes are real-parallel.

The norm is the genuine `ℓ² → ℓ²` operator norm from
`Matrix.Norms.L2Operator`, not an entrywise or Frobenius norm.
-/

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace AtlasB86Completion

/-- The maximum of a real-valued function on a nonempty finite type. -/
def fmax {n : Type*} [Fintype n] [Nonempty n] (f : n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- On a subsingleton index type, finite maximum is evaluation. -/
theorem fmax_subsingleton {n : Type*} [Fintype n] [Nonempty n] [Subsingleton n]
    (f : n → ℝ) : fmax f = f (Classical.choice inferInstance) := by
  apply Finset.sup'_eq_of_forall
  intro i hi
  congr
  exact Subsingleton.elim _ _

#print axioms fmax_subsingleton

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Exact `ℓ²` operator norm of a real diagonal matrix: a finite maximum of
absolute diagonal entries. -/
theorem l2_norm_diagonal_eq_fmax_abs (v : n → ℝ) :
    ‖(diagonal v : Matrix n n ℝ)‖ = fmax (fun i => |v i|) := by
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonempty v).2 (fun i => by
      rw [Real.norm_eq_abs]
      exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i))
  · apply Finset.sup'_le
    intro i hi
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v i

#print axioms l2_norm_diagonal_eq_fmax_abs

/-- Absolute values disappear exactly on nonnegative data. -/
theorem fmax_abs_of_nonneg (v : n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    fmax (fun i => |v i|) = fmax v := by
  apply congrArg
  funext i
  exact abs_of_nonneg (hv i)

#print axioms fmax_abs_of_nonneg

/-- **Corrected B86 norm formula.**  With positive denominators and
nonnegative numerators, the operator norm is the displayed maximum. -/
theorem norm_pairing (t g : n → ℝ) (ht : ∀ i, 0 ≤ t i) (hg : ∀ i, 0 < g i) :
    ‖(diagonal (fun i => t i / g i) : Matrix n n ℝ)‖ = fmax (fun i => t i / g i) := by
  rw [l2_norm_diagonal_eq_fmax_abs]
  exact fmax_abs_of_nonneg _ (fun i => div_nonneg (ht i) (hg i).le)

#print axioms norm_pairing

/-- Signed numerator data not excluded by the card's Check `g i > 0`. -/
def signedT : Fin 1 → ℝ := ![-2]

/-- Unit positive denominators for the signed counterexample. -/
def signedG : Fin 1 → ℝ := ![1]

/-- The signed witness satisfies the card's positive-denominator hypothesis. -/
theorem signedG_positive : ∀ i, 0 < signedG i := by
  intro i
  fin_cases i
  norm_num [signedG]

#print axioms signedG_positive

/-- **Counterexample to the literal norm display without a sign hypothesis.**
The left side is `2`, whereas the displayed right side is `-2`. -/
theorem signed_norm_counterexample :
    ‖(diagonal (fun i => signedT i / signedG i) : Matrix (Fin 1) (Fin 1) ℝ)‖ = 2 ∧
      fmax (fun i => signedT i / signedG i) = -2 := by
  constructor
  · rw [l2_norm_diagonal_eq_fmax_abs, fmax_subsingleton]
    norm_num [signedT, signedG]
  · rw [fmax_subsingleton]
    norm_num [signedT, signedG]

#print axioms signed_norm_counterexample

/-- Direct refutation of the literal equality at the signed witness. -/
theorem signed_norm_formula_ne :
    ‖(diagonal (fun i => signedT i / signedG i) : Matrix (Fin 1) (Fin 1) ℝ)‖ ≠
      fmax (fun i => signedT i / signedG i) := by
  rw [signed_norm_counterexample.1, signed_norm_counterexample.2]
  norm_num

#print axioms signed_norm_formula_ne

/-- The real part of the complex bilinear rank-one probe `u uᵀ`, where
`u = (u₁,u₂)` and there is deliberately no conjugate in `uᵀ`. -/
def bilinearProbe (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(u * u).re, (u * v).re; (u * v).re, (v * v).re]

/-- Exact determinant of the bilinear probe, in real and imaginary
coordinates. -/
theorem bilinearProbe_det (u v : ℂ) :
    (bilinearProbe u v).det = -(u.re * v.im - u.im * v.re) ^ 2 := by
  simp [bilinearProbe, Matrix.det_fin_two, Complex.mul_re]
  ring

#print axioms bilinearProbe_det

/-- The displayed B85/B86 expression is precisely the previous negative
square, now written using `Im(conj u v)`. -/
theorem bilinearProbe_det_conj (u v : ℂ) :
    (bilinearProbe u v).det = -((starRingEnd ℂ) u * v).im ^ 2 := by
  rw [bilinearProbe_det]
  simp [Complex.mul_im]
  ring

#print axioms bilinearProbe_det_conj

/-- **B86 sign clause, with the actual meaning of ‘bilinear symmetric probe’.**
No additional sign condition is needed; the rank-one bilinear structure is
essential, and reciprocity is not used in this algebraic implication. -/
theorem bilinearProbe_det_nonpos (u v : ℂ) : (bilinearProbe u v).det ≤ 0 := by
  rw [bilinearProbe_det]
  exact neg_nonpos.mpr (sq_nonneg _)

#print axioms bilinearProbe_det_nonpos

/-- The determinant vanishes exactly on real parallelism, not for every
complex-symmetric probe. -/
theorem bilinearProbe_det_zero_iff (u v : ℂ) :
    (bilinearProbe u v).det = 0 ↔ u.re * v.im = u.im * v.re := by
  rw [bilinearProbe_det, neg_eq_zero, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
    sub_eq_zero]

#print axioms bilinearProbe_det_zero_iff

/-- The transport block named in the B86 ledger: `2(Dt − g tᵀ)`. -/
def transport (t g : n → ℝ) : Matrix n n ℝ :=
  2 • (diagonal t - Matrix.of fun i j => g i * t j)

/-- The diagonal B86 pairing. -/
def pairing (t g : n → ℝ) : Matrix n n ℝ := diagonal (fun i => t i / g i)

/-- Positive numerator data for a regular two-state witness. -/
def regularT : Fin 2 → ℝ := ![2, 4]

/-- Positive denominator data for a regular two-state witness. -/
def regularG : Fin 2 → ℝ := ![1, 1]

/-- The associated concrete transport block. -/
def regularM : Matrix (Fin 2) (Fin 2) ℝ := transport regularT regularG

/-- The concrete transport block, with every entry evaluated. -/
theorem regularM_matrix : regularM = !![0, -8; -4, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [regularM, transport, regularT, regularG, Matrix.diagonal_apply]

#print axioms regularM_matrix

/-- The regular witness obeys the ledger's Check hypothesis. -/
theorem regularG_positive : ∀ i, 0 < regularG i := by
  intro i
  fin_cases i <;> norm_num [regularG]

#print axioms regularG_positive

/-- Reciprocity holds for the concrete regular transport and pairing. -/
theorem regular_reciprocity :
    regularMᵀ * pairing regularT regularG = pairing regularT regularG * regularM := by
  rw [regularM_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairing, regularT, regularG, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]

#print axioms regular_reciprocity

/-- Mere real symmetry does not supply the claimed determinant sign.  The
identity probe has positive determinant alongside a fully regular B86
reciprocity witness. -/
theorem symmetric_alone_does_not_imply_det_nonpos :
    ∃ (t g : Fin 2 → ℝ) (M G : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ i, 0 < g i) ∧ Mᵀ * pairing t g = pairing t g * M ∧
      Gᵀ = G ∧ 0 < G.det := by
  refine ⟨regularT, regularG, regularM, 1, regularG_positive,
    regular_reciprocity, Matrix.transpose_one, ?_⟩
  norm_num

#print axioms symmetric_alone_does_not_imply_det_nonpos

/-- A generic, not real-parallel, pair of complex amplitudes. -/
def genericU : ℂ := 1 + Complex.I

/-- The second generic amplitude. -/
def genericV : ℂ := Complex.I

/-- The generic bilinear probe has determinant `-1`, not zero. -/
theorem generic_bilinearProbe_det : (bilinearProbe genericU genericV).det = -1 := by
  rw [bilinearProbe_det]
  norm_num [genericU, genericV]

#print axioms generic_bilinearProbe_det

/-- **Refutation of the stronger HTML `det g ≡ 0` reading.**  All the regular
B86 pairing hypotheses can hold while a generic symmetric bilinear probe has
strictly negative (in particular nonzero) determinant. -/
theorem reciprocity_does_not_force_generic_probe_det_zero :
    ∃ (t g : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (u v : ℂ),
      (∀ i, 0 < g i) ∧ Mᵀ * pairing t g = pairing t g * M ∧
      (bilinearProbe u v).det = -1 := by
  exact ⟨regularT, regularG, regularM, genericU, genericV,
    regularG_positive, regular_reciprocity, generic_bilinearProbe_det⟩

#print axioms reciprocity_does_not_force_generic_probe_det_zero

end AtlasB86Completion


end

/-! ## B54 — det g > 0 does not certify a metric (strong-reading refutation plus the true clause)

Integrated from `.ultramath/smwtty35w/m15/B54.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B54: what determinant signs do, and do not, imply

The displayed HTML formula is

  `det g > 0 : |Ω|² overruns     det g < 0 : no metric at all`.

We read "overruns" as strict failure of the B1 bound, namely
`4 * det g < |Ω|²`.  The second argument below is the already-squared real
curvature magnitude; its nonnegativity is stated explicitly.  We do not
infer any property of `g` from the determinant unless it is proved below.
-/

namespace RelationalAtlas.B54

open Matrix

abbrev Metric2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Strict failure `4 det g < |Ω|²` of B1's `4 det g ≥ |Ω|²`
when `omegaSq = |Ω|²`. -/
def BoundFails (g : Metric2) (omegaSq : ℝ) : Prop :=
  4 * g.det < omegaSq

/-- The literal universal reading of the first displayed clause.  Requiring
`0 ≤ omegaSq` is not an extra geometric assumption: it says only that the
argument is a squared curvature magnitude. -/
def FirstDisplayedClause : Prop :=
  ∀ (g : Metric2) (omegaSq : ℝ),
    0 ≤ omegaSq → 0 < g.det → BoundFails g omegaSq

/-- The second displayed clause when "metric" means positive definite. -/
def SecondDisplayedClause : Prop :=
  ∀ g : Metric2, g.det < 0 → ¬ g.PosDef

/-- The identity metric, used with zero curvature. -/
def positiveFlatWitness : Metric2 := !![1, 0; 0, 1]

/-- A positive-determinant symmetric form which is not positive definite. -/
def negativeFlatWitness : Metric2 := !![-1, 0; 0, -1]

/-- A one-parameter symmetric form crossing the two determinant signs. -/
def determinantPath (t : ℝ) : Metric2 := !![1, 0; 0, t]

@[simp] theorem det_positiveFlatWitness : positiveFlatWitness.det = 1 := by
  simp [positiveFlatWitness, Matrix.det_fin_two_of]

@[simp] theorem det_negativeFlatWitness : negativeFlatWitness.det = 1 := by
  simp [negativeFlatWitness, Matrix.det_fin_two_of]

@[simp] theorem det_determinantPath (t : ℝ) : (determinantPath t).det = t := by
  simp [determinantPath, Matrix.det_fin_two_of]

/-- Direct, positive-definite counterexample to reading the first displayed
clause as `det g > 0 → 4 det g < |Ω|²`: all hypotheses hold but the bound is
strictly satisfied. -/
theorem positive_det_does_not_force_overrun :
    ∃ g : Metric2, ∃ omegaSq : ℝ,
      g.PosDef ∧ 0 < g.det ∧ 0 ≤ omegaSq ∧ ¬ BoundFails g omegaSq := by
  refine ⟨positiveFlatWitness, 0, ?_, by simp, by norm_num, ?_⟩
  · have hp : positiveFlatWitness = (1 : Metric2) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [positiveFlatWitness]
    rw [hp]
    exact Matrix.PosDef.one
  · simp [BoundFails]

/-- Formal refutation of the first displayed clause itself. -/
theorem b54_first_displayed_clause_false : ¬ FirstDisplayedClause := by
  intro h
  have hfail := h positiveFlatWitness 0 (by norm_num) (by simp)
  norm_num [BoundFails] at hfail

/-- A more explicit statement of the actual witness values. -/
theorem positiveFlatWitness_bound_holds_strictly :
    positiveFlatWitness.det = 1 ∧
    4 * positiveFlatWitness.det > (0 : ℝ) ∧
    ¬ BoundFails positiveFlatWitness 0 := by
  simp [BoundFails]

/-- The `det g > 0` side of the display does not by itself certify a metric.
Here `g = -I` has determinant one but is not positive definite. -/
theorem positive_det_does_not_imply_positiveDef :
    ∃ g : Metric2, 0 < g.det ∧ ¬ g.PosDef := by
  refine ⟨negativeFlatWitness, by simp, ?_⟩
  intro h
  have hone := h.2 (x := Finsupp.single (0 : Fin 2) (1 : ℝ)) (by simp)
  norm_num [negativeFlatWitness, Finsupp.sum_single_index] at hone

/-- The valid negative-determinant clause, with no symmetry or definiteness
assumption on `g`. -/
theorem negative_det_forces_bound_failure
    (g : Metric2) (omegaSq : ℝ)
    (homega : 0 ≤ omegaSq) (hdet : g.det < 0) :
    BoundFails g omegaSq := by
  dsimp [BoundFails]
  nlinarith

/-- Positive definiteness already excludes a negative determinant, so the
second displayed clause is correct when "metric" means `Matrix.PosDef`. -/
theorem negative_det_excludes_positiveDef
    {g : Metric2} (hdet : g.det < 0) : ¬ g.PosDef := by
  intro hg
  exact (not_lt_of_ge (le_of_lt hg.det_pos)) hdet

/-- The second displayed clause is true exactly as a positive-definiteness
statement; no additional restriction on `g` is needed. -/
theorem b54_second_displayed_clause : SecondDisplayedClause := by
  intro g hdet
  exact negative_det_excludes_positiveDef hdet

/-- The zero-curvature family from the prose can indeed cross `det g = 0`:
on its negative side the bound fails although `|Ω|² = 0` throughout. -/
theorem flat_path_violates_after_zero {t : ℝ} (ht : t < 0) :
    (determinantPath t).det < 0 ∧ BoundFails (determinantPath t) 0 := by
  constructor
  · simpa using ht
  · dsimp [BoundFails]
    rw [det_determinantPath]
    nlinarith

/-- On the positive side of the same flat path there is no overrun.  This
also exposes why the card's two displayed regions must not be interchanged. -/
theorem flat_path_holds_before_zero {t : ℝ} (ht : 0 < t) :
    0 < (determinantPath t).det ∧ ¬ BoundFails (determinantPath t) 0 := by
  constructor
  · simpa using ht
  · simp [BoundFails, ht.le]

/-- At the determinant-zero seam the flat path satisfies the B1 bound with
exact equality, rather than already violating it strictly. -/
theorem flat_path_saturates_at_zero :
    (determinantPath 0).det = 0 ∧
    4 * (determinantPath 0).det = (0 : ℝ) := by
  simp

#print axioms det_positiveFlatWitness
#print axioms det_negativeFlatWitness
#print axioms det_determinantPath
#print axioms positive_det_does_not_force_overrun
#print axioms b54_first_displayed_clause_false
#print axioms positiveFlatWitness_bound_holds_strictly
#print axioms positive_det_does_not_imply_positiveDef
#print axioms negative_det_forces_bound_failure
#print axioms negative_det_excludes_positiveDef
#print axioms b54_second_displayed_clause
#print axioms flat_path_violates_after_zero
#print axioms flat_path_holds_before_zero
#print axioms flat_path_saturates_at_zero

end RelationalAtlas.B54


end

/-! ## B154 — a single beta needs a Hermitian K (proof; missing hypothesis exhibited)

Integrated from `.ultramath/smwtty35w/m3/B154Full.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B154: one temperature on all traceless Hermitian directions

The card's quantifier is over *Hermitian* traceless variations, not all
matrices.  This file proves both the real symmetric and complex Hermitian
forms, and also gives the explicit skew real counterexample obtained if the
symmetry hypothesis on `K` is discarded.  In the complex statement the trace
pairing is real-valued, so it is written as the real part of the complex trace.
-/

namespace RelationalAtlas.ThirdBatch.B154

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric matrix killing every symmetric traceless matrix under the trace
pairing is a scalar multiple of the identity.  Empty and one-dimensional index
types are allowed. -/
theorem exists_isScalar_of_trace_mul_eq_zero_on_symm_traceless
    (R : Matrix n n ℝ) (hR : R.IsSymm)
    (h : ∀ C : Matrix n n ℝ, C.IsSymm → C.trace = 0 → (R * C).trace = 0) :
    ∃ lam : ℝ, R = lam • (1 : Matrix n n ℝ) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
      refine ⟨0, ?_⟩
      ext i
      exact isEmptyElim i
  | inr hn =>
      let i0 : n := Classical.choice hn
      have offdiag : ∀ i j : n, i ≠ j → R i j = 0 := by
        intro i j hij
        let C : Matrix n n ℝ := single i j 1 + single j i 1
        have hCs : C.IsSymm := by
          dsimp [C]
          simpa [add_comm] using (isSymm_add_transpose_self (single i j (1 : ℝ)))
        have hCt : C.trace = 0 := by
          simp [C, Matrix.trace_add, hij, hij.symm]
        have hz := h C hCs hCt
        have htrace : (R * C).trace = R j i + R i j := by
          simp [C, mul_add, Matrix.trace_mul_single]
        rw [htrace] at hz
        have hji : R j i = R i j := hR.apply i j
        rw [hji] at hz
        linarith
      have diag : ∀ i : n, R i i = R i0 i0 := by
        intro i
        let C : Matrix n n ℝ := single i i 1 - single i0 i0 1
        have hCs : C.IsSymm := by
          dsimp [C]
          rw [← diagonal_single, ← diagonal_single]
          exact (isSymm_diagonal _).sub (isSymm_diagonal _)
        have hCt : C.trace = 0 := by simp [C, Matrix.trace_sub]
        have hz := h C hCs hCt
        have htrace : (R * C).trace = R i i - R i0 i0 := by
          simp [C, mul_sub, Matrix.trace_mul_single]
        rw [htrace] at hz
        linarith
      refine ⟨R i0 i0, ?_⟩
      ext i j
      by_cases hij : i = j
      · subst j
        simp [diag i]
      · simp [Matrix.one_apply, hij, offdiag i j hij]

/-- **B154, real symmetric form.**  A single real `β` works on every traceless
symmetric variation exactly when `K - β • hA` is a real multiple of the identity.
No nonzero or dimension-at-least-two assumption is needed. -/
theorem one_temperature_iff_real
    (K hA : Matrix n n ℝ) (β : ℝ) (hK : K.IsSymm) (hh : hA.IsSymm) :
    (∀ C : Matrix n n ℝ, C.IsSymm → C.trace = 0 →
      (K * C).trace = β * (hA * C).trace) ↔
      ∃ lam : ℝ, K - β • hA = lam • (1 : Matrix n n ℝ) := by
  constructor
  · intro h
    apply exists_isScalar_of_trace_mul_eq_zero_on_symm_traceless
      (K - β • hA) (hK.sub (hh.smul β))
    intro C hCs hCt
    have hKC := h C hCs hCt
    simp only [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
      smul_eq_mul]
    rw [hKC]
    ring
  · rintro ⟨lam, hlam⟩ C hCs hCt
    have hKexpr : K = β • hA + lam • (1 : Matrix n n ℝ) := by
      rw [← hlam]
      abel
    rw [hKexpr]
    simp [add_mul, Matrix.trace_add, Matrix.trace_smul, hCt]

/-- The explicit `2 × 2` skew matrix used to test whether Hermitian symmetry
of `K` is actually necessary when only symmetric variations are admitted. -/
def skewWitness : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Without symmetry of `K`, the displayed converse is false: this nonzero skew
part is invisible to every symmetric `C` (indeed, even without `trace C = 0`),
but it is not a scalar matrix. -/
theorem skewWitness_refutes_dropping_symmetry :
    (∀ C : Matrix (Fin 2) (Fin 2) ℝ, C.IsSymm → C.trace = 0 →
      (skewWitness * C).trace = (1 : ℝ) * ((0 : Matrix (Fin 2) (Fin 2) ℝ) * C).trace) ∧
    ¬ ∃ lam : ℝ, skewWitness - (1 : ℝ) • (0 : Matrix (Fin 2) (Fin 2) ℝ) =
      lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · intro C hCs _
    have hC : C 1 0 = C 0 1 := hCs.apply 0 1
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [skewWitness, hC]
  · rintro ⟨lam, hlam⟩
    have hentry := congrFun (congrFun hlam 0) 1
    norm_num [skewWitness, Matrix.one_apply] at hentry

#print axioms exists_isScalar_of_trace_mul_eq_zero_on_symm_traceless
#print axioms one_temperature_iff_real
#print axioms skewWitness_refutes_dropping_symmetry

end RelationalAtlas.ThirdBatch.B154

namespace RelationalAtlas.ThirdBatch.B154

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex Hermitian version with the real trace pairing used for physical
Hamiltonians. -/
theorem exists_real_isScalar_of_re_trace_mul_eq_zero_on_hermitian_traceless
    (R : Matrix n n ℂ) (hR : R.IsHermitian)
    (h : ∀ C : Matrix n n ℂ, C.IsHermitian → C.trace = 0 →
      (R * C).trace.re = 0) :
    ∃ lam : ℝ, R = lam • (1 : Matrix n n ℂ) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
      refine ⟨0, ?_⟩
      ext i
      exact isEmptyElim i
  | inr hn =>
      let i0 : n := Classical.choice hn
      have him_diag : ∀ i : n, (R i i).im = 0 := by
        intro i
        have hi := congrArg Complex.im (hR.apply i i)
        simp only [Complex.star_def, Complex.conj_im] at hi
        linarith
      have offdiag : ∀ i j : n, i ≠ j → R i j = 0 := by
        intro i j hij
        have hji : R j i = star (R i j) := (hR.apply j i).symm
        let C : Matrix n n ℂ := single i j 1 + single j i 1
        have hCs : C.IsHermitian := by
          dsimp [C]
          simpa using (Matrix.isHermitian_add_transpose_self (single i j (1 : ℂ)))
        have hCt : C.trace = 0 := by
          simp [C, Matrix.trace_add, hij, hij.symm]
        have hz := h C hCs hCt
        have htrace : (R * C).trace = R j i + R i j := by
          simp [C, mul_add, Matrix.trace_mul_single]
        rw [htrace, hji] at hz
        have hre : (R i j).re = 0 := by
          simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hz
          linarith
        let Ci : Matrix n n ℂ := single i j Complex.I + single j i (-Complex.I)
        have hCis : Ci.IsHermitian := by
          dsimp [Ci]
          simpa using (Matrix.isHermitian_add_transpose_self (single i j Complex.I))
        have hCit : Ci.trace = 0 := by
          simp [Ci, Matrix.trace_add, hij, hij.symm]
        have hzi := h Ci hCis hCit
        have htracei : (R * Ci).trace = Complex.I * R j i + (-Complex.I) * R i j := by
          simp [Ci, mul_add, Matrix.trace_mul_single]
          ring
        rw [htracei, hji] at hzi
        have him : (R i j).im = 0 := by
          simp [Complex.mul_re, Complex.star_def] at hzi
          linarith
        apply Complex.ext
        · simpa using hre
        · simpa using him
      have diag : ∀ i : n, R i i = R i0 i0 := by
        intro i
        have hs (a : n) : (single a a (1 : ℂ)).IsHermitian := by
          apply Matrix.IsHermitian.ext
          intro b c
          simp [Matrix.single_apply, and_comm]
        let C : Matrix n n ℂ := single i i 1 - single i0 i0 1
        have hCs : C.IsHermitian := (hs i).sub (hs i0)
        have hCt : C.trace = 0 := by simp [C, Matrix.trace_sub]
        have hz := h C hCs hCt
        have htrace : (R * C).trace = R i i - R i0 i0 := by
          simp [C, mul_sub, Matrix.trace_mul_single]
        rw [htrace] at hz
        apply Complex.ext
        · simp only [Complex.sub_re] at hz
          linarith
        · simp [him_diag]
      refine ⟨(R i0 i0).re, ?_⟩
      ext i j
      by_cases hij : i = j
      · subst j
        apply Complex.ext
        · simp [diag i]
        · simp [diag i, him_diag]
      · simp [Matrix.one_apply, hij, offdiag i j hij]

/-- **B154, complex Hermitian form.**  Here `β` and the unobservable offset
`lam` are real, as they are for physical Hamiltonians. -/
theorem one_temperature_iff_complex
    (K hA : Matrix n n ℂ) (β : ℝ) (hK : K.IsHermitian) (hh : hA.IsHermitian) :
    (∀ C : Matrix n n ℂ, C.IsHermitian → C.trace = 0 →
      (K * C).trace.re = β * (hA * C).trace.re) ↔
      ∃ lam : ℝ, K - β • hA = lam • (1 : Matrix n n ℂ) := by
  constructor
  · intro h
    apply exists_real_isScalar_of_re_trace_mul_eq_zero_on_hermitian_traceless
      (K - β • hA) (hK.sub (hh.smul (IsSelfAdjoint.all β)))
    intro C hCs hCt
    have hKC := h C hCs hCt
    simp only [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
      Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [hKC]
    ring
  · rintro ⟨lam, hlam⟩ C hCs hCt
    have hKexpr : K = β • hA + lam • (1 : Matrix n n ℂ) := by
      rw [← hlam]
      abel
    rw [hKexpr]
    simp [add_mul, Matrix.trace_add, Matrix.trace_smul, hCt, Complex.real_smul]

#print axioms exists_real_isScalar_of_re_trace_mul_eq_zero_on_hermitian_traceless
#print axioms one_temperature_iff_complex

end RelationalAtlas.ThirdBatch.B154


end

/-! ## B200 — Koide Q = 2/3 is the nilpotency of the centred matrix (proof)

Integrated from `.ultramath/smwtty35w/m6/B200.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B200: the algebraic core of the Koide card

For positive masses `m₁,m₂,m₃`, put `xᵢ = √mᵢ`.  The card's
normalization is

* `Q = (m₁+m₂+m₃)/(x₁+x₂+x₃)^2`;
* `3s^2 = (x₁+x₂+x₃)^2`;
* `h^2+s^2 = m₁+m₂+m₃`, with `h ≥ 0`.

Thus `h^2/s^2 = 3Q-1`.  The hypotheses below are exactly the positive-mass
hypotheses in the card's Carry section.  In particular they make the
 denominator of `Q` nonzero and `s > 0`.

On the centered plane we use the real Pauli matrices and the quarter-turn
`J = [[0,1],[-1,0]]` (equivalently `iσ_y` in a complex Pauli basis).
Consequently `Z = h₁σ_z+h₂σ_x+sJ` is
`[[h₁,h₂+s],[h₂-s,-h₁]]`, whose square is `(h₁²+h₂²-s²)I`.
-/

namespace AtlasFormal.B200

noncomputable section

open Matrix

/-- The real matrix `σ_z` on the centered plane. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The real matrix `σ_x` on the centered plane. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The centered-plane quarter-turn, with `J^2 = -I`. -/
def centeredJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- `Z = h₁σ_z+h₂σ_x+sJ`, expanded into entries. -/
def koideZ (h₁ h₂ s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  h₁ • sigmaZ + h₂ • sigmaX + s • centeredJ

lemma koideZ_eq (h₁ h₂ s : ℝ) :
    koideZ h₁ h₂ s = !![h₁, h₂+s; h₂-s, -h₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [koideZ, sigmaZ, sigmaX, centeredJ] <;> ring

/-- The card's displayed matrix identity, with `h² = h₁²+h₂²`. -/
theorem koideZ_sq (h₁ h₂ s : ℝ) :
    (koideZ h₁ h₂ s)^2 = (h₁^2+h₂^2-s^2) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [koideZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The rotation normalization is the one that gives the minus sign in
`Z^2 = (h^2-s^2)I`. -/
theorem centeredJ_sq :
    (centeredJ)^2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [centeredJ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- A nonzero democratic component alone prevents `Z` from being zero. -/
theorem koideZ_ne_zero_of_s_ne_zero {h₁ h₂ s : ℝ} (hs : s ≠ 0) :
    koideZ h₁ h₂ s ≠ 0 := by
  intro hzero
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hzero
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hzero
  rw [koideZ_eq] at h01 h10
  simp at h01 h10
  apply hs
  linarith

/-- The exact Koide quotient for three masses. -/
def koideQ (m₁ m₂ m₃ : ℝ) : ℝ :=
  (m₁+m₂+m₃) / (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃)^2

/-- The democratic magnitude, normalized by `3s^2 = (∑√m)^2`. -/
def koideS (m₁ m₂ m₃ : ℝ) : ℝ :=
  (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃) / Real.sqrt 3

/-- The squared centered magnitude, normalized by `h^2+s^2 = ∑m`. -/
def koideHSq (m₁ m₂ m₃ : ℝ) : ℝ :=
  (m₁+m₂+m₃) - (koideS m₁ m₂ m₃)^2

/-- The nonnegative centered magnitude `h`. -/
def koideH (m₁ m₂ m₃ : ℝ) : ℝ := Real.sqrt (koideHSq m₁ m₂ m₃)


lemma koideS_pos {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    0 < koideS m₁ m₂ m₃ := by
  unfold koideS
  have hx : 0 < Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃ := by
    have h₁ : 0 < Real.sqrt m₁ := Real.sqrt_pos.mpr hm₁
    have h₂ : 0 < Real.sqrt m₂ := Real.sqrt_pos.mpr hm₂
    have h₃ : 0 < Real.sqrt m₃ := Real.sqrt_pos.mpr hm₃
    linarith
  exact div_pos hx (Real.sqrt_pos.mpr (by norm_num))

/-- The card's democratic normalization `3s^2 = (∑√m)^2`. -/
lemma three_mul_koideS_sq (m₁ m₂ m₃ : ℝ) :
    3 * (koideS m₁ m₂ m₃)^2 =
      (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃)^2 := by
  rw [koideS, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

/-- Nonnegativity of the centered magnitude is the three-variable
Cauchy--Schwarz inequality, here in the exact sum-of-squares form. -/
lemma koideHSq_nonneg {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm₃ : 0 ≤ m₃) :
    0 ≤ koideHSq m₁ m₂ m₃ := by
  have h₁ : (Real.sqrt m₁)^2 = m₁ := Real.sq_sqrt hm₁
  have h₂ : (Real.sqrt m₂)^2 = m₂ := Real.sq_sqrt hm₂
  have h₃ : (Real.sqrt m₃)^2 = m₃ := Real.sq_sqrt hm₃
  have hs := three_mul_koideS_sq m₁ m₂ m₃
  unfold koideHSq
  nlinarith [sq_nonneg (Real.sqrt m₁ - Real.sqrt m₂),
    sq_nonneg (Real.sqrt m₁ - Real.sqrt m₃),
    sq_nonneg (Real.sqrt m₂ - Real.sqrt m₃)]

lemma koideH_nonneg (m₁ m₂ m₃ : ℝ) : 0 ≤ koideH m₁ m₂ m₃ := by
  exact Real.sqrt_nonneg _

lemma koideH_sq {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm₃ : 0 ≤ m₃) :
    (koideH m₁ m₂ m₃)^2 = koideHSq m₁ m₂ m₃ := by
  exact Real.sq_sqrt (koideHSq_nonneg hm₁ hm₂ hm₃)

/-- The orthogonal decomposition in the card: `s²+h² = ∑m`. -/
lemma koide_decomposition {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm₃ : 0 ≤ m₃) :
    (koideS m₁ m₂ m₃)^2 + (koideH m₁ m₂ m₃)^2 = m₁+m₂+m₃ := by
  rw [koideH_sq hm₁ hm₂ hm₃]
  unfold koideHSq
  ring

/-- The card's equivalent formula `Q = (s²+h²)/(3s²)`. -/
lemma koideQ_eq_s_h {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm₃ : 0 ≤ m₃) :
    koideQ m₁ m₂ m₃ =
      ((koideS m₁ m₂ m₃)^2 + (koideH m₁ m₂ m₃)^2) /
        (3 * (koideS m₁ m₂ m₃)^2) := by
  unfold koideQ
  rw [← three_mul_koideS_sq m₁ m₂ m₃]
  rw [koide_decomposition hm₁ hm₂ hm₃]

/-- **B200's displayed scalar identity.**  Positive masses are used only to
ensure that the displayed denominator is nonzero. -/
theorem koide_spread_ratio {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    (koideH m₁ m₂ m₃)^2 / (koideS m₁ m₂ m₃)^2 =
      3 * koideQ m₁ m₂ m₃ - 1 := by
  rw [koideQ_eq_s_h hm₁.le hm₂.le hm₃.le]
  have hs : koideS m₁ m₂ m₃ ≠ 0 := ne_of_gt (koideS_pos hm₁ hm₂ hm₃)
  field_simp [hs]
  ring

/-- Koide's value is exactly equality of the *squared* magnitudes. -/
theorem koideQ_eq_two_thirds_iff_sq {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    koideQ m₁ m₂ m₃ = 2/3 ↔
      (koideH m₁ m₂ m₃)^2 = (koideS m₁ m₂ m₃)^2 := by
  have hratio := koide_spread_ratio hm₁ hm₂ hm₃
  have hs : koideS m₁ m₂ m₃ ≠ 0 := ne_of_gt (koideS_pos hm₁ hm₂ hm₃)
  have hs2 : (koideS m₁ m₂ m₃)^2 ≠ 0 := pow_ne_zero 2 hs
  constructor
  · intro hQ
    rw [hQ] at hratio
    norm_num at hratio
    exact (div_eq_one_iff_eq hs2).mp hratio
  · intro heq
    rw [heq, div_self hs2] at hratio
    linarith

/-- Since the card's `h` and `s` are nonnegative magnitudes, the squared
statement is equivalent to its prose statement `Q = 2/3 iff h = s`. -/
theorem koideQ_eq_two_thirds_iff_h_eq_s {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    koideQ m₁ m₂ m₃ = 2/3 ↔ koideH m₁ m₂ m₃ = koideS m₁ m₂ m₃ := by
  rw [koideQ_eq_two_thirds_iff_sq hm₁ hm₂ hm₃]
  exact sq_eq_sq₀ (koideH_nonneg _ _ _) (koideS_pos hm₁ hm₂ hm₃).le


/-- Repeated masses give the degenerate centered case: there is no spread,
and the Koide quotient is `1/3`, not `2/3`. -/
theorem koide_equal_masses {m : ℝ} (hm : 0 < m) :
    koideH m m m = 0 ∧ koideQ m m m = 1/3 := by
  have hr : (Real.sqrt m)^2 = m := Real.sq_sqrt hm.le
  have hr0 : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  have hs := three_mul_koideS_sq m m m
  have hs_sq : (koideS m m m)^2 = 3*m := by
    nlinarith
  have hHsq : koideHSq m m m = 0 := by
    unfold koideHSq
    nlinarith
  constructor
  · simp [koideH, hHsq]
  · unfold koideQ
    field_simp [hr0, hm.ne']
    nlinarith

/-- The minimally passive shift has the same displayed square, since
`ζ = h/s` and `s ≠ 0`. -/
theorem koide_zeta_sq {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    (koideH m₁ m₂ m₃ / koideS m₁ m₂ m₃)^2 =
      3 * koideQ m₁ m₂ m₃ - 1 := by
  rw [div_pow]
  exact koide_spread_ratio hm₁ hm₂ hm₃

/-- With `h₁²+h₂² = h²`, the matrix identity takes the card's exact
scalar form `(h²-s²)I`. -/
theorem koideZ_sq_of_hrepr {m₁ m₂ m₃ h₁ h₂ : ℝ}
    (hrepr : h₁^2+h₂^2 = (koideH m₁ m₂ m₃)^2) :
    (koideZ h₁ h₂ (koideS m₁ m₂ m₃))^2 =
      ((koideH m₁ m₂ m₃)^2-(koideS m₁ m₂ m₃)^2) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [koideZ_sq, hrepr]

/-- At the Koide value the matrix is square-zero precisely when its two
spread coordinates represent the card's `h`.  This is an iff, not just the
forward implication stated in the prose. -/
theorem koideQ_eq_two_thirds_iff_Z_sq_zero {m₁ m₂ m₃ h₁ h₂ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃)
    (hrepr : h₁^2+h₂^2 = (koideH m₁ m₂ m₃)^2) :
    koideQ m₁ m₂ m₃ = 2/3 ↔
      (koideZ h₁ h₂ (koideS m₁ m₂ m₃))^2 = 0 := by
  rw [koideQ_eq_two_thirds_iff_sq hm₁ hm₂ hm₃, koideZ_sq]
  constructor
  · intro heq
    have hscalar : h₁^2+h₂^2-(koideS m₁ m₂ m₃)^2 = 0 := by
      rw [hrepr, heq]
      ring
    rw [hscalar, zero_smul]
  · intro hz
    have hentry := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hz
    simp at hentry
    rw [← hrepr]
    linarith

/-- In particular, at `Q = 2/3` the card's `Z` is a *nonzero* nilpotent.
No unequal-roots hypothesis has to be added separately: positive masses and
`s ≠ 0` already give `Z ≠ 0` for every representing pair `(h₁,h₂)`. -/
theorem koide_nonzero_nilpotent_at_value {m₁ m₂ m₃ h₁ h₂ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃)
    (hrepr : h₁^2+h₂^2 = (koideH m₁ m₂ m₃)^2)
    (hQ : koideQ m₁ m₂ m₃ = 2/3) :
    koideZ h₁ h₂ (koideS m₁ m₂ m₃) ≠ 0 ∧
      IsNilpotent (koideZ h₁ h₂ (koideS m₁ m₂ m₃)) := by
  refine ⟨koideZ_ne_zero_of_s_ne_zero
    (ne_of_gt (koideS_pos hm₁ hm₂ hm₃)), 2, ?_⟩
  exact (koideQ_eq_two_thirds_iff_Z_sq_zero hm₁ hm₂ hm₃ hrepr).mp hQ

/-- A canonical choice `h₁ = h, h₂ = 0` removes the representation
hypothesis from the preceding matrix characterization. -/
theorem koideQ_eq_two_thirds_iff_canonical_Z_sq_zero {m₁ m₂ m₃ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) :
    koideQ m₁ m₂ m₃ = 2/3 ↔
      (koideZ (koideH m₁ m₂ m₃) 0 (koideS m₁ m₂ m₃))^2 = 0 := by
  apply koideQ_eq_two_thirds_iff_Z_sq_zero hm₁ hm₂ hm₃
  ring

/-- Concrete non-vacuity of the matrix normal form: at `h₁ = s = 1` and
`h₂ = 0`, the square is zero but the matrix is not. -/
example : koideZ 1 0 1 ≠ 0 ∧ (koideZ 1 0 1)^2 = 0 := by
  constructor
  · apply koideZ_ne_zero_of_s_ne_zero
    norm_num
  · rw [koideZ_sq]
    norm_num


end

end AtlasFormal.B200


#print axioms AtlasFormal.B200.koideZ_eq
#print axioms AtlasFormal.B200.koideZ_sq
#print axioms AtlasFormal.B200.centeredJ_sq
#print axioms AtlasFormal.B200.koideZ_ne_zero_of_s_ne_zero
#print axioms AtlasFormal.B200.koideS_pos
#print axioms AtlasFormal.B200.three_mul_koideS_sq
#print axioms AtlasFormal.B200.koideHSq_nonneg
#print axioms AtlasFormal.B200.koideH_nonneg
#print axioms AtlasFormal.B200.koideH_sq
#print axioms AtlasFormal.B200.koide_decomposition
#print axioms AtlasFormal.B200.koideQ_eq_s_h
#print axioms AtlasFormal.B200.koide_spread_ratio
#print axioms AtlasFormal.B200.koideQ_eq_two_thirds_iff_sq
#print axioms AtlasFormal.B200.koideQ_eq_two_thirds_iff_h_eq_s
#print axioms AtlasFormal.B200.koide_zeta_sq
#print axioms AtlasFormal.B200.koideZ_sq_of_hrepr
#print axioms AtlasFormal.B200.koideQ_eq_two_thirds_iff_Z_sq_zero
#print axioms AtlasFormal.B200.koide_nonzero_nilpotent_at_value
#print axioms AtlasFormal.B200.koideQ_eq_two_thirds_iff_canonical_Z_sq_zero
#print axioms AtlasFormal.B200.koide_equal_masses


end

/-! ## B132 — the identifiability dichotomy needs F symmetric (REFUTATION and repair)

Integrated from `.ultramath/smwtty35w/m16/B132.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B132: probe identifiability, including a literal counterexample

The displayed implication and reconstruction formula are correct.  The displayed
"otherwise" clause is not correct for an arbitrary real matrix target: a nonzero
skew-symmetric part cannot be detected by pairing with a symmetric matrix.  The
zero-probe, two-dimensional witness below makes this precise.  With the added
hypothesis `F = Fᵀ`, the full dichotomy is proved using Frobenius-orthogonal
projection.  No nonzero, distinctness, or independence condition on probes is used.
-/

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open scoped Matrix InnerProductSpace BigOperators

namespace B132

noncomputable section

variable {n ι : Type*}

/-- The quadratic reading of `R` in the probe direction `u`. -/
def q [Fintype n] (R : Matrix n n ℝ) (u : n → ℝ) : ℝ := u ⬝ᵥ R *ᵥ u

/-- The real span of the displayed rank-one probe matrices. -/
def probeSpan (u : ι → n → ℝ) : Submodule ℝ (Matrix n n ℝ) :=
  Submodule.span ℝ (Set.range fun i => Matrix.vecMulVec (u i) (u i))

lemma trace_mul_vecMulVec [Fintype n] (R : Matrix n n ℝ) (u : n → ℝ) :
    (R * Matrix.vecMulVec u u).trace = q R u := by
  simp [Matrix.trace, Matrix.mul_apply, q, dotProduct, Matrix.mulVec,
    Matrix.vecMulVec_apply, Finset.mul_sum, mul_left_comm, mul_comm]

/-- The exact displayed reconstruction identity, for a specified representation. -/
theorem trace_reconstruction [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (a : ι → ℝ) (F R : Matrix n n ℝ)
    (hF : ∑ i, a i • Matrix.vecMulVec (u i) (u i) = F) :
    (R * F).trace = ∑ i, a i * q R (u i) := by
  rw [← hF, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_mul_vecMulVec]

/-- Membership in the probe span supplies the coefficients in the display. -/
theorem exists_reconstruction [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (F : Matrix n n ℝ) (hF : F ∈ probeSpan u) :
    ∃ a : ι → ℝ, (∑ i, a i • Matrix.vecMulVec (u i) (u i) = F) ∧
      ∀ R : Matrix n n ℝ, (R * F).trace = ∑ i, a i * q R (u i) := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hF
  exact ⟨a, ha, fun R => trace_reconstruction u a F R ha⟩

/-- Frobenius space, with pairs of matrix indices as Euclidean coordinates. -/
private abbrev Frob (n : Type*) := EuclideanSpace ℝ (n × n)

/-- The entry-preserving linear equivalence between matrices and Frobenius space. -/
private def matrixEquiv : Matrix n n ℝ ≃ₗ[ℝ] Frob n where
  toFun A := WithLp.toLp 2 fun ij => A ij.1 ij.2
  invFun X := fun i j => X.ofLp (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma inner_matrixEquiv [Fintype n] (A B : Matrix n n ℝ) :
    ⟪matrixEquiv A, matrixEquiv B⟫_ℝ = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  change (∑ ij : n × n, B ij.1 ij.2 * A ij.1 ij.2) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_comm]

private lemma trace_mul_transpose_eq_inner [Fintype n] (A B : Matrix n n ℝ) :
    (A * Bᵀ).trace = ⟪matrixEquiv A, matrixEquiv B⟫_ℝ := by
  rw [inner_matrixEquiv]
  simp [Matrix.trace, Matrix.mul_apply]

private lemma trace_mul_vecMulVec_eq_inner [Fintype n] (A : Matrix n n ℝ) (u : n → ℝ) :
    (A * Matrix.vecMulVec u u).trace =
      ⟪matrixEquiv A, matrixEquiv (Matrix.vecMulVec u u)⟫_ℝ := by
  rw [inner_matrixEquiv]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, mul_comm]

private lemma vecMulVec_self_symmetric (u : n → ℝ) :
    Matrix.vecMulVec u u = (Matrix.vecMulVec u u)ᵀ := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

private lemma symmetric_of_mem_probeSpan {u : ι → n → ℝ} {X : Matrix n n ℝ}
    (hX : X ∈ probeSpan u) : X = Xᵀ := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨i, rfl⟩ := hX
      exact vecMulVec_self_symmetric (u i)
  | zero => ext; simp
  | add X Y hX hY hXs hYs =>
      rw [Matrix.transpose_add, ← hXs, ← hYs]
  | smul a X hX hXs =>
      rw [Matrix.transpose_smul, ← hXs]

/-- The repaired "otherwise" branch.  The missing literal hypothesis is `F = Fᵀ`. -/
theorem exists_invisible_direction_of_symmetric [Fintype n]
    (u : ι → n → ℝ) (F : Matrix n n ℝ) (hF : F = Fᵀ)
    (hout : F ∉ probeSpan u) :
    ∃ H : Matrix n n ℝ, H = Hᵀ ∧ (∀ i, q H (u i) = 0) ∧ (H * F).trace ≠ 0 := by
  let S : Submodule ℝ (Matrix n n ℝ) := probeSpan u
  let T : Submodule ℝ (Frob n) := S.map matrixEquiv.toLinearMap
  haveI : CompleteSpace T := FiniteDimensional.complete ℝ T
  let P : Frob n := T.starProjection (matrixEquiv F)
  let K : Frob n := matrixEquiv F - P
  let H : Matrix n n ℝ := matrixEquiv.symm K
  have hPT : P ∈ T := Submodule.starProjection_apply_mem T (matrixEquiv F)
  have hPS : matrixEquiv.symm P ∈ S := (Submodule.mem_map_equiv S).mp hPT
  have hPsymm : matrixEquiv.symm P = (matrixEquiv.symm P)ᵀ :=
    symmetric_of_mem_probeSpan hPS
  have hKorth : K ∈ Tᗮ := by
    simpa [K, P] using T.sub_starProjection_mem_orthogonal (matrixEquiv F)
  have hFnotT : matrixEquiv F ∉ T := by
    intro hin
    have hs : matrixEquiv.symm (matrixEquiv F) ∈ S := (Submodule.mem_map_equiv S).mp hin
    exact hout (by simpa [S] using hs)
  have hKne : K ≠ 0 := by
    intro hK
    have heq : matrixEquiv F = P := sub_eq_zero.mp hK
    have hproj : P = matrixEquiv F := heq.symm
    have hin : matrixEquiv F ∈ T := T.starProjection_eq_self_iff.mp hproj
    exact hFnotT hin
  have hHsymm : H = Hᵀ := by
    have hs := congrArg₂ (fun A B : Matrix n n ℝ => A - B) hF hPsymm
    simpa [H, K, Matrix.transpose_sub] using hs
  have hprobe : ∀ i, q H (u i) = 0 := by
    intro i
    have houterT : matrixEquiv (Matrix.vecMulVec (u i) (u i)) ∈ T := by
      apply Submodule.mem_map.mpr
      exact ⟨Matrix.vecMulVec (u i) (u i), Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    calc
      q H (u i) = (H * Matrix.vecMulVec (u i) (u i)).trace :=
        (trace_mul_vecMulVec H (u i)).symm
      _ = ⟪matrixEquiv H,
          matrixEquiv (Matrix.vecMulVec (u i) (u i))⟫_ℝ :=
        trace_mul_vecMulVec_eq_inner H (u i)
      _ = ⟪K, matrixEquiv (Matrix.vecMulVec (u i) (u i))⟫_ℝ := by
        rw [show matrixEquiv H = K from matrixEquiv.apply_symm_apply K]
      _ = 0 := (T.mem_orthogonal' K).mp hKorth _ houterT
  have hinner : ⟪K, matrixEquiv F⟫_ℝ = ⟪K, K⟫_ℝ := by
    have hdecomp : matrixEquiv F = K + P := by simp [K]
    rw [hdecomp, inner_add_right, (T.mem_orthogonal' K).mp hKorth P hPT, add_zero]
  have htrace : (H * F).trace = ⟪K, matrixEquiv F⟫_ℝ := by
    calc
      (H * F).trace = (H * Fᵀ).trace := congrArg (fun X => (H * X).trace) hF
      _ = ⟪matrixEquiv H, matrixEquiv F⟫_ℝ := trace_mul_transpose_eq_inner H F
      _ = ⟪K, matrixEquiv F⟫_ℝ := by
        rw [show matrixEquiv H = K from matrixEquiv.apply_symm_apply K]
  exact ⟨H, hHsymm, hprobe, by rw [htrace, hinner]; exact inner_self_ne_zero.mpr hKne⟩

/-- The prose's "exactly when", after adding symmetry of the target. -/
theorem identifiability_iff_of_symmetric [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (F : Matrix n n ℝ) (hF : F = Fᵀ) :
    F ∈ probeSpan u ↔ ∃ a : ι → ℝ,
      ∀ R : Matrix n n ℝ, (R * F).trace = ∑ i, a i * q R (u i) := by
  constructor
  · intro hin
    obtain ⟨a, ha, hrec⟩ := exists_reconstruction u F hin
    exact ⟨a, hrec⟩
  · rintro ⟨a, ha⟩
    by_contra hout
    obtain ⟨H, hHs, hprobe, hne⟩ := exists_invisible_direction_of_symmetric u F hF hout
    have hzero : ∑ i, a i * q H (u i) = 0 := by simp [hprobe]
    have := ha H
    rw [hzero] at this
    exact hne this

/-! ## Literal refutation: one zero probe and a skew-symmetric target -/

/-- The zero probe used in the counterexample. -/
def zeroProbe : Fin 1 → Fin 2 → ℝ := fun _ _ => 0

/-- A skew-symmetric target outside the zero probe's span. -/
def skewTarget : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

lemma skewTarget_not_mem_span : skewTarget ∉ probeSpan zeroProbe := by
  intro hF
  have hz : ∀ X ∈ probeSpan zeroProbe, X = 0 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨i, rfl⟩ := hX
        ext i j
        simp [zeroProbe, Matrix.vecMulVec_apply]
    | zero => rfl
    | add X Y hX hY hX0 hY0 => simp [hX0, hY0]
    | smul a X hX hX0 => simp [hX0]
  have h0 := hz skewTarget hF
  have he := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 1) h0
  norm_num [skewTarget] at he

lemma trace_symmetric_mul_skewTarget (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H = Hᵀ) : (H * skewTarget).trace = 0 := by
  have he := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 1) hH
  have h01 : H 0 1 = H 1 0 := by simpa using he
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, skewTarget]
  linarith

/-- The literal `F ∉ span ⇒ ∃ symmetric invisible H` clause is false.
All probe readings vanish, `skewTarget` is outside the span, but no symmetric `H`
has nonzero trace pairing with it. -/
theorem literal_otherwise_clause_counterexample :
    skewTarget ∉ probeSpan zeroProbe ∧
      ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℝ,
        H = Hᵀ ∧ (∀ i, q H (zeroProbe i) = 0) ∧ (H * skewTarget).trace ≠ 0 := by
  refine ⟨skewTarget_not_mem_span, ?_⟩
  rintro ⟨H, hHs, hprobe, hne⟩
  exact hne (trace_symmetric_mul_skewTarget H hHs)

#print axioms trace_reconstruction
#print axioms exists_reconstruction
#print axioms exists_invisible_direction_of_symmetric
#print axioms identifiability_iff_of_symmetric
#print axioms skewTarget_not_mem_span
#print axioms trace_symmetric_mul_skewTarget
#print axioms literal_otherwise_clause_counterexample

end
end B132


end

/-! ## B44 — the squared lift inequality is false (REFUTATION; ledger transcription error)

Integrated from `.ultramath/smwtty35w/m4/B44.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B44: the squared transient-growth headline is false

The ledger version of B44 reads
`max_t ‖exp(tA)‖ ≥ (max_t ‖exp(tJ)‖)^2` when `J` is a damped defective
block on an invariant subspace.  We take `A = J`, with the whole space as the
invariant subspace.  Thus the isometric intertwining hypothesis is as strong
as possible, not a spoiling hypothesis.

On `ℝ × ℝ` with the product (maximum) norm, put
`J(x,y) = (-x/2 + y, -y/2)`.  This is the Jordan block
`[[-1/2, 1], [0, -1/2]]`.  Its positive-time transient maximum is
`2 * exp(-1/2)`, attained at `t = 1`.  This value is strictly greater than one,
so it is strictly smaller than its square.
-/

noncomputable section

namespace AtlasB44SquaredCounterexample

abbrev State := ℝ × ℝ
abbrev Op := State →L[ℝ] State

/-- The strictly upper-triangular Jordan part. -/
def shear : Op := ContinuousLinearMap.prod (ContinuousLinearMap.snd ℝ ℝ ℝ) 0

@[simp] theorem shear_apply (x : State) : shear x = (x.2, 0) := rfl

/-- The damped Jordan block `[[-1/2, 1], [0, -1/2]]`. -/
def jordan : Op := (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ State + shear

@[simp] theorem jordan_apply (x : State) :
    jordan x = (-x.1 / 2 + x.2, -x.2 / 2) := by
  apply Prod.ext <;> simp [jordan] <;> ring

/-- The Jordan block really is scalar-plus-nonzero-nilpotent. -/
theorem jordan_eq_scalar_add_shear :
    jordan = (-(1 / 2 : ℝ)) • (1 : Op) + shear := rfl

theorem shear_sq : shear * shear = 0 := by
  ext x <;> simp

theorem shear_ne_zero : shear ≠ 0 := by
  intro h
  have h' := congr_arg (fun L : Op => L (0, 1)) h
  norm_num at h'

/-- The eigenvalue is strictly negative: the Jordan perturbation does not
change the scalar part `-1/2`. -/
theorem jordan_eigenvector : jordan (1, 0) = (-(1 / 2 : ℝ)) • (1, 0) := by
  norm_num

/-- The whole-space identity isometrically intertwines `A = jordan` with
`J = jordan`; the counterexample does not depend on a bad embedding. -/
theorem jordan_self_intertwines (x : State) :
    jordan ((LinearIsometry.id : State →ₗᵢ[ℝ] State) x) =
      (LinearIsometry.id : State →ₗᵢ[ℝ] State) (jordan x) := rfl

/-- The exponential of a square-zero operator truncates after its linear term. -/
theorem exp_smul_of_sq_zero (N : Op) (hN : N * N = 0) (t : ℝ) :
    NormedSpace.exp (t • N) = 1 + t • N := by
  have hNpow : N ^ 2 = 0 := by rw [pow_two, hN]
  rw [NormedSpace.exp_eq_tsum_rat]
  change (∑' k : ℕ, (k.factorial : ℚ)⁻¹ • (t • N) ^ k) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · norm_num [Finset.sum_range_succ, smul_pow, hNpow]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [smul_pow, pow_eq_zero_of_le hk hNpow, smul_zero]
    simp

/-- Exact flow of the damped Jordan block. -/
theorem exp_jordan (t : ℝ) :
    NormedSpace.exp (t • jordan) =
      Real.exp (-t / 2) • ((1 : Op) + t • shear) := by
  let +nondep : NormedAlgebra ℚ Op := .restrictScalars ℚ ℝ Op
  have hdecomp : t • jordan = (-t / 2 : ℝ) • (1 : Op) + t • shear := by
    rw [jordan_eq_scalar_add_shear]
    module
  have hcomm : Commute ((-t / 2 : ℝ) • (1 : Op)) (t • shear) := by
    show ((-t / 2 : ℝ) • (1 : Op)) * (t • shear) =
      (t • shear) * ((-t / 2 : ℝ) • (1 : Op))
    ext x <;> simp <;> ring
  have hscalar : NormedSpace.exp ((-t / 2 : ℝ) • (1 : Op)) =
      Real.exp (-t / 2) • (1 : Op) := by
    rw [Algebra.smul_def, mul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Real.exp_eq_exp_ℝ]
    rfl
  rw [hdecomp, NormedSpace.exp_add_of_commute hcomm, hscalar,
    exp_smul_of_sq_zero shear shear_sq]
  simp [smul_mul_assoc]

@[simp] theorem exp_jordan_apply (t : ℝ) (x : State) :
    NormedSpace.exp (t • jordan) x =
      (Real.exp (-t / 2) * (x.1 + t * x.2), Real.exp (-t / 2) * x.2) := by
  rw [exp_jordan]
  apply Prod.ext <;> simp <;> ring

end AtlasB44SquaredCounterexample

namespace AtlasB44SquaredCounterexample

/-- For `t ≥ 0`, the Jordan flow has operator norm at most
`exp(-t/2) * (1+t)` in the product norm. -/
theorem opNorm_exp_jordan_le (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • jordan)‖ ≤ Real.exp (-t / 2) * (1 + t) := by
  apply (NormedSpace.exp (t • jordan)).opNorm_le_bound (by positivity)
  intro x
  have hx1 : |x.1| ≤ ‖x‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hx2 : |x.2| ≤ ‖x‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  rw [exp_jordan_apply, Prod.norm_mk]
  simp only [Real.norm_eq_abs]
  apply max_le
  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * |x.1 + t * x.2| ≤
          Real.exp (-t / 2) * (|x.1| + |t * x.2|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (Real.exp_nonneg _)
      _ = Real.exp (-t / 2) * (|x.1| + t * |x.2|) := by
        rw [abs_mul, abs_of_nonneg ht]
      _ ≤ Real.exp (-t / 2) * (|x.1| + t * ‖x‖) := by gcongr
      _ ≤ Real.exp (-t / 2) * (‖x‖ + t * ‖x‖) := by gcongr
      _ = Real.exp (-t / 2) * (1 + t) * ‖x‖ := by ring
  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * |x.2| ≤ Real.exp (-t / 2) * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx2 (Real.exp_nonneg _)
      _ = Real.exp (-t / 2) * 1 * ‖x‖ := by ring
      _ ≤ Real.exp (-t / 2) * (1 + t) * ‖x‖ := by
        gcongr <;> linarith [Real.exp_pos (-t / 2), norm_nonneg x]

/-- The input `(1,1)` realizes the lower bound `2 exp(-1/2)` at time one. -/
theorem peak_le_opNorm_exp_jordan_one :
    2 * Real.exp (-(1 : ℝ) / 2) ≤ ‖NormedSpace.exp ((1 : ℝ) • jordan)‖ := by
  have h := (NormedSpace.exp ((1 : ℝ) • jordan)).le_opNorm (1, 1)
  have hnorm : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by
    norm_num [Prod.norm_def]
  rw [hnorm, mul_one, exp_jordan_apply, Prod.norm_mk] at h
  norm_num [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-(1 : ℝ) / 2))] at h
  simpa only [one_smul, mul_comm, neg_div] using h.1

/-- The scalar growth factor peaks at `t = 1`.  The proof uses only
`1+x ≤ exp x`; no numerical approximation of the exponential is involved. -/
theorem growth_factor_le_peak (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t / 2) * (1 + t) ≤ 2 * Real.exp (-(1 : ℝ) / 2) := by
  have hlin : (t - 1) / 2 + 1 ≤ Real.exp ((t - 1) / 2) :=
    Real.add_one_le_exp ((t - 1) / 2)
  calc
    Real.exp (-t / 2) * (1 + t) =
        2 * Real.exp (-t / 2) * ((t - 1) / 2 + 1) := by ring
    _ ≤ 2 * Real.exp (-t / 2) * Real.exp ((t - 1) / 2) := by
      exact mul_le_mul_of_nonneg_left hlin (by positivity)
    _ = 2 * (Real.exp (-t / 2) * Real.exp ((t - 1) / 2)) := by ring
    _ = 2 * Real.exp (-(1 : ℝ) / 2) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Values whose supremum is the transient maximum.  Nonnegative time is the
only added convention; without it, a damped Jordan block is unbounded as
`t → -∞`, so the displayed `max_t` cannot mean a finite maximum over all `ℝ`. -/
def transientValues {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) : Set ℝ :=
  Set.range (fun t : {t : ℝ // 0 ≤ t} => ‖NormedSpace.exp ((t : ℝ) • A)‖)

def transientMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) : ℝ := sSup (transientValues A)

theorem transientValues_jordan_bddAbove : BddAbove (transientValues jordan) := by
  refine ⟨2 * Real.exp (-(1 : ℝ) / 2), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (opNorm_exp_jordan_le t.1 t.2).trans (growth_factor_le_peak t.1 t.2)

/-- The exact positive-time transient maximum, attained at `t = 1`. -/
theorem transientMax_jordan : transientMax jordan = 2 * Real.exp (-(1 : ℝ) / 2) := by
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro _ ⟨t, rfl⟩
      exact (opNorm_exp_jordan_le t.1 t.2).trans (growth_factor_le_peak t.1 t.2)
  · have hmem : ‖NormedSpace.exp ((1 : ℝ) • jordan)‖ ∈ transientValues jordan := by
      refine ⟨⟨1, by norm_num⟩, ?_⟩
      rfl
    exact peak_le_opNorm_exp_jordan_one.trans
      (le_csSup transientValues_jordan_bddAbove hmem)

/-- The peak is genuinely greater than one, again by `1+x < exp x`. -/
theorem one_lt_transientMax_jordan : 1 < transientMax jordan := by
  rw [transientMax_jordan]
  have h := Real.add_one_lt_exp (show -(1 : ℝ) / 2 ≠ 0 by norm_num)
  linarith

/-- The literal squared B44 inequality already fails for `A = J` and the
identity isometric embedding of the whole space into itself. -/
theorem transientMax_lt_transientMax_sq :
    transientMax jordan < (transientMax jordan) ^ 2 := by
  have h := one_lt_transientMax_jordan
  nlinarith

/-- The displayed squared relation, written in the same left-to-right form
as the ledger. -/
def SquaredB44Claim (A J : Op) : Prop := transientMax A ≥ (transientMax J) ^ 2

/-- A formal refutation of the literal squared claim, with the admissible
self-block witness `A = J = [[-1/2,1],[0,-1/2]]`. -/
theorem literal_squared_B44_claim_is_false : ¬ SquaredB44Claim jordan jordan := by
  exact not_le_of_gt transientMax_lt_transientMax_sq

/-- The counterexample also satisfies the ledger's literal restricted-flow
premise `exp(tA)|V = exp(tJ)`, not merely its generator version. -/
theorem jordan_self_flow_restriction (t : ℝ) (x : State) :
    NormedSpace.exp (t • jordan) ((LinearIsometry.id : State →ₗᵢ[ℝ] State) x) =
      (LinearIsometry.id : State →ₗᵢ[ℝ] State) (NormedSpace.exp (t • jordan) x) :=
  rfl

section CorrectUnsquaredForm

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Correct form of B44.**  The actual flow-restriction premise and an
isometric embedding give the pointwise bound with no square. -/
theorem opNorm_exp_le_of_flow_restriction (A : E →L[ℝ] E) (J : V →L[ℝ] V)
    (ι : V →ₗᵢ[ℝ] E) (t : ℝ)
    (hflow : ∀ x, NormedSpace.exp (t • A) (ι x) = ι (NormedSpace.exp (t • J) x)) :
    ‖NormedSpace.exp (t • J)‖ ≤ ‖NormedSpace.exp (t • A)‖ := by
  apply (NormedSpace.exp (t • J)).opNorm_le_bound (norm_nonneg _)
  intro x
  calc
    ‖NormedSpace.exp (t • J) x‖ = ‖ι (NormedSpace.exp (t • J) x)‖ :=
      (ι.norm_map _).symm
    _ = ‖NormedSpace.exp (t • A) (ι x)‖ := by rw [hflow]
    _ ≤ ‖NormedSpace.exp (t • A)‖ * ‖ι x‖ :=
      (NormedSpace.exp (t • A)).le_opNorm _
    _ = ‖NormedSpace.exp (t • A)‖ * ‖x‖ := by rw [ι.norm_map]

/-- Consequently the nonnegative-time maxima satisfy the *unsquared*
inequality, provided the ambient family has a finite supremum.  Boundedness
is needed to interpret `sSup`; the counterexample itself is bounded. -/
theorem transientMax_le_of_flow_restriction (A : E →L[ℝ] E) (J : V →L[ℝ] V)
    (ι : V →ₗᵢ[ℝ] E)
    (hflow : ∀ (t : {t : ℝ // 0 ≤ t}) x,
      NormedSpace.exp ((t : ℝ) • A) (ι x) = ι (NormedSpace.exp ((t : ℝ) • J) x))
    (hA : BddAbove (transientValues A)) :
    transientMax J ≤ transientMax A := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨t, rfl⟩
  calc
    ‖NormedSpace.exp ((t : ℝ) • J)‖ ≤ ‖NormedSpace.exp ((t : ℝ) • A)‖ :=
      opNorm_exp_le_of_flow_restriction A J ι (t : ℝ) (hflow t)
    _ ≤ transientMax A := le_csSup hA ⟨t, rfl⟩

end CorrectUnsquaredForm

#print axioms shear_apply
#print axioms jordan_apply
#print axioms shear_sq
#print axioms shear_ne_zero
#print axioms jordan_eq_scalar_add_shear
#print axioms jordan_eigenvector
#print axioms jordan_self_intertwines
#print axioms exp_smul_of_sq_zero
#print axioms exp_jordan
#print axioms exp_jordan_apply
#print axioms opNorm_exp_jordan_le
#print axioms peak_le_opNorm_exp_jordan_one
#print axioms growth_factor_le_peak
#print axioms transientValues_jordan_bddAbove
#print axioms transientMax_jordan
#print axioms one_lt_transientMax_jordan
#print axioms transientMax_lt_transientMax_sq
#print axioms literal_squared_B44_claim_is_false
#print axioms jordan_self_flow_restriction
#print axioms opNorm_exp_le_of_flow_restriction
#print axioms transientMax_le_of_flow_restriction

end AtlasB44SquaredCounterexample


end

/-! ## B206 — the Born-overlap hierarchy and the three-projector trace (proof)

Integrated from `.ultramath/smwtty35w/m9/B206.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B206 — overlap hierarchy and a three-ray Bargmann witness

The source display is
`ρ = (1/k)Σc_a`, `F = ((1/k)Σ√c_a)²`, `D = Πc_a`,
`D^(1/k) ≤ F ≤ ρ`, `ρ − F = Var(√c_a)`, and
`Tr(P₀P₁P₂±) = (1 ± i)/4` with every pairwise overlap `1/2`.

Here `rootVariance` is the population variance (the normalization used by the
card), and `IsRayProjector P` explicitly says that `P = vv*` for a unit vector
`v`.  The loop matrices are the exact projectors for the card's rays
`(1,0)`, `(1,1)/√2`, and `(1,±i)/√2`.
-/

open scoped BigOperators Matrix
open Finset Matrix

namespace B206

noncomputable section


variable {k : ℕ}

def born (c : Fin k → ℝ) : ℝ := (∑ i, c i) / k

def fidelity (c : Fin k → ℝ) : ℝ := ((∑ i, Real.sqrt (c i)) / k) ^ 2

def slater (c : Fin k → ℝ) : ℝ := ∏ i, c i

def rootVariance (c : Fin k → ℝ) : ℝ :=
  (∑ i, (Real.sqrt (c i) - (∑ j, Real.sqrt (c j)) / k) ^ 2) / k

lemma geometric_root_le_arithmetic_root (hk : 0 < k) (c : Fin k → ℝ) :
    (∏ i, Real.sqrt (c i)) ^ ((k : ℝ)⁻¹) ≤ (∑ i, Real.sqrt (c i)) / k := by
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin k))
    (fun _ => (1 : ℝ)) (fun i => Real.sqrt (c i))
    (by simp) (by simp; exact_mod_cast hk) (by simp [Real.sqrt_nonneg])
  simpa using h

lemma slater_root_le_fidelity (hk : 0 < k) (c : Fin k → ℝ)
    (hc : ∀ i, 0 ≤ c i) : (slater c) ^ (1 / (k : ℝ)) ≤ fidelity c := by
  let r : ℝ := ∏ i, Real.sqrt (c i)
  have hr : 0 ≤ r := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hD : slater c = r ^ 2 := by
    dsimp [slater, r]
    rw [← Real.sqrt_prod Finset.univ (fun i _ => hc i)]
    exact (Real.sq_sqrt (Finset.prod_nonneg fun i _ => hc i)).symm
  have hroot : (slater c) ^ (1 / (k : ℝ)) = (r ^ ((k : ℝ)⁻¹)) ^ 2 := by
    rw [hD, one_div]
    exact (Real.rpow_pow_comm hr ((k : ℝ)⁻¹) 2).symm
  rw [hroot]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hr _) (geometric_root_le_arithmetic_root hk c) 2

lemma fidelity_le_born (c : Fin k → ℝ) (hc : ∀ i, 0 ≤ c i) :
    fidelity c ≤ born c := by
  simpa only [fidelity, born, Finset.card_univ, Fintype.card_fin, Real.sq_sqrt (hc _)] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset (Fin k))) (f := fun i => Real.sqrt (c i)))

lemma born_sub_fidelity (hk : 0 < k) (c : Fin k → ℝ) (hc : ∀ i, 0 ≤ c i) :
    born c - fidelity c = rootVariance c := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  let x : Fin k → ℝ := fun i => Real.sqrt (c i)
  let m : ℝ := (∑ i, x i) / k
  have hx : ∀ i, x i ^ 2 = c i := fun i => Real.sq_sqrt (hc i)
  have hsum : (∑ i, (x i - m) ^ 2) = (∑ i, c i) - (∑ i, x i) ^ 2 / k := by
    calc
      (∑ i, (x i - m) ^ 2) = (∑ i, x i ^ 2) - 2 * m * (∑ i, x i) + k * m ^ 2 := by
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ = (∑ i, c i) - (∑ i, x i) ^ 2 / k := by
        simp_rw [hx]
        dsimp [m]
        field_simp
        ring
  dsimp [born, fidelity, rootVariance]
  change (∑ i, c i) / k - ((∑ i, x i) / k) ^ 2 =
    (∑ i, (x i - m) ^ 2) / k
  rw [hsum]
  field_simp



/-- The displayed scalar hierarchy and its variance identity, under the card's
unit-interval hypothesis on squared principal cosines. -/
theorem card_hierarchy_unit_interval {k : ℕ} (hk : 0 < k) (c : Fin k → ℝ)
    (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) :
    (slater c) ^ (1 / (k : ℝ)) ≤ fidelity c ∧ fidelity c ≤ born c ∧
      born c - fidelity c = rootVariance c :=
  ⟨slater_root_le_fidelity hk c (fun i => (hc i).1),
    fidelity_le_born c (fun i => (hc i).1),
    born_sub_fidelity hk c (fun i => (hc i).1)⟩

/-- Same display with only the hypotheses actually used by the algebra. -/
theorem card_hierarchy {k : ℕ} (hk : 0 < k) (c : Fin k → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (slater c) ^ (1 / (k : ℝ)) ≤ fidelity c ∧ fidelity c ≤ born c ∧
      born c - fidelity c = rootVariance c :=
  ⟨slater_root_le_fidelity hk c hc, fidelity_le_born c hc, born_sub_fidelity hk c hc⟩

def cSplit : Fin 2 → ℝ := ![1, 0]
def cEqual : Fin 2 → ℝ := ![1 / 2, 1 / 2]

lemma published_witness_split :
    born cSplit = 1 / 2 ∧ fidelity cSplit = 1 / 4 ∧ slater cSplit = 0 := by
  norm_num [cSplit, born, fidelity, slater, Fin.sum_univ_two, Fin.prod_univ_two]

lemma published_witness_equal :
    born cEqual = 1 / 2 ∧ fidelity cEqual = 1 / 2 ∧ slater cEqual = 1 / 4 := by
  have hs : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  norm_num [cEqual, born, fidelity, slater, Fin.sum_univ_two, Fin.prod_univ_two]



abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ

def IsRayProjector (P : C2) : Prop :=
  ∃ v : Fin 2 → ℂ, P = Matrix.vecMulVec v (star v) ∧ (star v) ⬝ᵥ v = 1

def q : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
def v0 : Fin 2 → ℂ := ![1, 0]
def v1 : Fin 2 → ℂ := ![q, q]
def vPlus : Fin 2 → ℂ := ![q, q * Complex.I]
def vMinus : Fin 2 → ℂ := ![q, -(q * Complex.I)]

lemma star_q : star q = q := by simp [q]
lemma conj_q : (starRingEnd ℂ) q = q := star_q
lemma q_sq : q ^ 2 = (1 / 2 : ℂ) := by
  rw [q, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def ray0 : C2 := !![1, 0; 0, 0]
def ray1 : C2 := !![1/2, 1/2; 1/2, 1/2]
def rayPlus : C2 := !![1/2, -Complex.I/2; Complex.I/2, 1/2]
def rayMinus : C2 := !![1/2, Complex.I/2; -Complex.I/2, 1/2]

lemma ray0_isRayProjector : IsRayProjector ray0 := by
  refine ⟨v0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ray0, v0, Matrix.vecMulVec_apply]
  · simp [v0, dotProduct, Fin.sum_univ_two]

lemma ray1_isRayProjector : IsRayProjector ray1 := by
  refine ⟨v1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ray1, v1, star_q, Matrix.vecMulVec_apply] <;> ring_nf <;> simp [q_sq]
  · simp [v1, conj_q, dotProduct, Fin.sum_univ_two]
    ring_nf
    simp [q_sq]

lemma rayPlus_isRayProjector : IsRayProjector rayPlus := by
  refine ⟨vPlus, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rayPlus, vPlus, star_q, Matrix.vecMulVec_apply] <;> ring_nf <;> simp [q_sq]
    all_goals ring
  · simp [vPlus, conj_q, dotProduct, Fin.sum_univ_two]
    ring_nf
    simp [q_sq, Complex.I_sq]
    all_goals ring

lemma rayMinus_isRayProjector : IsRayProjector rayMinus := by
  refine ⟨vMinus, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rayMinus, vMinus, star_q, Matrix.vecMulVec_apply] <;> ring_nf <;> simp [q_sq]
    all_goals ring
  · simp [vMinus, conj_q, dotProduct, Fin.sum_univ_two]
    ring_nf
    simp [q_sq, Complex.I_sq]
    all_goals ring

lemma IsRayProjector.hermitian {P : C2} (h : IsRayProjector P) : Pᴴ = P := by
  obtain ⟨v, rfl, hv⟩ := h
  simp [Matrix.conjTranspose_vecMulVec]

lemma IsRayProjector.idempotent {P : C2} (h : IsRayProjector P) : P * P = P := by
  obtain ⟨v, rfl, hv⟩ := h
  rw [Matrix.vecMulVec_mul_vecMulVec, hv]
  simp


lemma IsRayProjector.trace {P : C2} (h : IsRayProjector P) : Matrix.trace P = 1 := by
  obtain ⟨v, rfl, hv⟩ := h
  rw [Matrix.trace_vecMulVec]
  simpa [dotProduct, mul_comm] using hv

lemma overlap01 : Matrix.trace (ray0 * ray1) = (1 / 2 : ℂ) := by
  norm_num [ray0, ray1, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma overlap0Plus : Matrix.trace (ray0 * rayPlus) = (1 / 2 : ℂ) := by
  norm_num [ray0, rayPlus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma overlap0Minus : Matrix.trace (ray0 * rayMinus) = (1 / 2 : ℂ) := by
  norm_num [ray0, rayMinus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma overlap1Plus : Matrix.trace (ray1 * rayPlus) = (1 / 2 : ℂ) := by
  norm_num [ray1, rayPlus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma overlap1Minus : Matrix.trace (ray1 * rayMinus) = (1 / 2 : ℂ) := by
  norm_num [ray1, rayMinus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma bargmann_plus :
    Matrix.trace (ray0 * ray1 * rayPlus) = (1 + Complex.I) / 4 := by
  norm_num [ray0, ray1, rayPlus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]

lemma bargmann_minus :
    Matrix.trace (ray0 * ray1 * rayMinus) = (1 - Complex.I) / 4 := by
  norm_num [ray0, ray1, rayMinus, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im]


#print axioms geometric_root_le_arithmetic_root
#print axioms slater_root_le_fidelity
#print axioms fidelity_le_born
#print axioms born_sub_fidelity
#print axioms card_hierarchy_unit_interval
#print axioms card_hierarchy
#print axioms published_witness_split
#print axioms published_witness_equal
#print axioms star_q
#print axioms conj_q
#print axioms q_sq
#print axioms ray0_isRayProjector
#print axioms ray1_isRayProjector
#print axioms rayPlus_isRayProjector
#print axioms rayMinus_isRayProjector
#print axioms IsRayProjector.hermitian
#print axioms IsRayProjector.idempotent
#print axioms IsRayProjector.trace
#print axioms overlap01
#print axioms overlap0Plus
#print axioms overlap0Minus
#print axioms overlap1Plus
#print axioms overlap1Minus
#print axioms bargmann_plus
#print axioms bargmann_minus

end
end B206


end

/-! ## B138 — join edges force thickness three (proof, conditional on the planar budget)

Integrated from `.ultramath/smwtty35w/m12/B138.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B138: join edges force thickness three

The card displays `Θ(Cₙ[Kᵣ]) ≥ 3 (n,r ≥ 4)`, together with
`triangle-free H ⊆ biplanar G on N vertices: |E(H)| ≤ 4N − 8` and
`join edges: nr² > 4nr − 8`.

Mathlib has no planarity or Euler-face-edge API. `PlanarTriangleFreeBudget`
below is therefore the *exact combinatorial consequence* of planarity used by
the card, including the necessary `N ≥ 3` qualification. We prove the rest of
the argument: the two-layer union bound, triangle-freeness and the edge count
of every lifted cycle-join graph, and the contradiction with the arithmetic.
No geometric embedding, Euler formula, exact-thickness upper bound, or
arboricity assertion is assumed or claimed here.
-/

open Classical
open Finset Fintype

namespace RelationalAtlas.B138

universe u

/-- Triangle-freeness in the elementary form used in the card's argument. -/
def TriangleFree {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False

/-- The exact Euler consequence needed from a planar layer.
The qualification is essential: for `N = 2`, the one-edge graph is a
counterexample to `|E| ≤ 2N - 4`. Integer subtraction avoids truncated `ℕ`
subtraction. -/
def PlanarTriangleFreeBudget {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V →
    ∀ K : SimpleGraph V, K ≤ G → TriangleFree K →
      (K.edgeSet.ncard : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 4

theorem TriangleFree.mono {V : Type u} {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : TriangleFree H) : TriangleFree G := by
  intro x y z hxy hyz hzx
  exact hH x y z (hGH hxy) (hGH hyz) (hGH hzx)

/-- A triangle-free graph covered by two graphs satisfying the planar
triangle-free budget has at most `4N - 8` edges. Edges common to both layers
are counted twice, which is harmless. -/
theorem triangleFree_edge_card_le_two_layers {V : Type u} [Fintype V]
    (H P Q : SimpleGraph V) (hN : 3 ≤ Fintype.card V)
    (hP : PlanarTriangleFreeBudget P) (hQ : PlanarTriangleFreeBudget Q)
    (hcover : H ≤ P ⊔ Q) (hfree : TriangleFree H) :
    (H.edgeSet.ncard : ℤ) ≤ 4 * (Fintype.card V : ℤ) - 8 := by
  let HP := H ⊓ P
  let HQ := H ⊓ Q
  have hHPfree : TriangleFree HP := TriangleFree.mono inf_le_left hfree
  have hHQfree : TriangleFree HQ := TriangleFree.mono inf_le_left hfree
  have hHPbound : (HP.edgeSet.ncard : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 4 :=
    hP hN HP inf_le_right hHPfree
  have hHQbound : (HQ.edgeSet.ncard : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 4 :=
    hQ hN HQ inf_le_right hHQfree
  have hdecomp : H = HP ⊔ HQ := by
    apply le_antisymm
    · intro x y hxy
      rcases hcover hxy with hp | hq
      · exact Or.inl ⟨hxy, hp⟩
      · exact Or.inr ⟨hxy, hq⟩
    · exact sup_le inf_le_left inf_le_left
  have hcardNat : H.edgeSet.ncard ≤ HP.edgeSet.ncard + HQ.edgeSet.ncard := by
    rw [hdecomp, SimpleGraph.edgeSet_sup]
    exact Set.ncard_union_le _ _
  have hcardInt : (H.edgeSet.ncard : ℤ) ≤
      (HP.edgeSet.ncard : ℤ) + (HQ.edgeSet.ncard : ℤ) := by
    exact_mod_cast hcardNat
  linarith

/-- Only the join edges of the lexicographic blow-up: fibre labels are ignored,
and there are no edges within a fibre or between nonadjacent base vertices. -/
def joinBlowup {V : Type u} (C : SimpleGraph V) (r : ℕ) : SimpleGraph (V × Fin r) where
  Adj x y := C.Adj x.1 y.1
  symm := by
    constructor
    intro x y h
    exact C.adj_symm h
  loopless := by
    constructor
    intro x h
    exact C.irrefl h

theorem joinBlowup_triangleFree {V : Type u} {C : SimpleGraph V} (r : ℕ)
    (hC : TriangleFree C) : TriangleFree (joinBlowup C r) := by
  intro x y z hxy hyz hzx
  exact hC x.1 y.1 z.1 hxy hyz hzx

/-- Oriented lifted edges are oriented base edges with two fibre labels. -/
def joinDartEquiv {V : Type u} (C : SimpleGraph V) (r : ℕ) :
    (C.Dart × Fin r × Fin r) ≃ (joinBlowup C r).Dart where
  toFun x := ⟨((x.1.fst, x.2.1), (x.1.snd, x.2.2)), x.1.adj⟩
  invFun d := (⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2, d.snd.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bridge the canonical set cardinality and any `edgeFinset` instance. -/
theorem card_edgeFinset_eq_ncard {V : Type u} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeFinset.card = G.edgeSet.ncard := by
  change G.edgeSet.toFinset.card = G.edgeSet.ncard
  rw [Set.toFinset_card]
  exact Nat.card_eq_fintype_card.symm

/-- The lifted join graph has exactly `|E(C)| r²` edges. -/
theorem ncard_edgeSet_joinBlowup {V : Type u} [Fintype V] (C : SimpleGraph V)
    (r : ℕ) :
    (joinBlowup C r).edgeSet.ncard = C.edgeSet.ncard * r ^ 2 := by
  have hdarts : Fintype.card (joinBlowup C r).Dart =
      Fintype.card C.Dart * r * r := by
    have h := (Fintype.card_congr (joinDartEquiv C r)).symm
    simpa [mul_assoc] using h
  have hc : Fintype.card C.Dart = 2 * C.edgeSet.ncard := by
    simpa only [card_edgeFinset_eq_ncard] using C.dart_card_eq_twice_card_edges
  have hj : Fintype.card (joinBlowup C r).Dart =
      2 * (joinBlowup C r).edgeSet.ncard := by
    simpa only [card_edgeFinset_eq_ncard] using
      (joinBlowup C r).dart_card_eq_twice_card_edges
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
  calc
    2 * (joinBlowup C r).edgeSet.ncard = Fintype.card (joinBlowup C r).Dart := hj.symm
    _ = Fintype.card C.Dart * r * r := hdarts
    _ = (2 * C.edgeSet.ncard) * r * r := by rw [hc]
    _ = 2 * (C.edgeSet.ncard * r ^ 2) := by ring

/-- Adjacency in `cycleGraph n` gives one of four signed integer relations.
The alternative `1 - n` is the wraparound edge. -/
theorem cycleGraph_adj_int_cases {n : ℕ} (_hn : 4 ≤ n) {u v : Fin n}
    (h : (SimpleGraph.cycleGraph n).Adj u v) :
    (u.val : ℤ) - v.val = 1 ∨ (u.val : ℤ) - v.val = 1 - (n : ℤ) ∨
      (v.val : ℤ) - u.val = 1 ∨ (v.val : ℤ) - u.val = 1 - (n : ℤ) := by
  have aux : ∀ {a b : Fin n}, (a - b).val = 1 →
      (a.val : ℤ) - b.val = 1 ∨ (a.val : ℤ) - b.val = 1 - (n : ℤ) := by
    intro a b hab
    have hi : (((a - b).val : ℕ) : ℤ) = 1 := by exact_mod_cast hab
    rw [Fin.intCast_val_sub_eq_sub_add_ite] at hi
    by_cases hba : b ≤ a
    · simp [hba] at hi
      left
      linarith
    · simp [hba] at hi
      right
      linarith
  rcases SimpleGraph.cycleGraph_adj'.mp h with huv | hvu
  · rcases aux huv with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases aux hvu with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

/-- A cycle of length at least four has no triangle. -/
theorem cycleGraph_triangleFree {n : ℕ} (hn : 4 ≤ n) :
    TriangleFree (SimpleGraph.cycleGraph n) := by
  intro x y z hxy hyz hzx
  have hx := cycleGraph_adj_int_cases hn hxy
  have hy := cycleGraph_adj_int_cases hn hyz
  have hz := cycleGraph_adj_int_cases hn hzx
  rcases hx with hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy <;>
      rcases hz with hz | hz | hz | hz <;> omega

/-- The standard cycle on `n ≥ 3` vertices has `n` edges. -/
theorem ncard_edgeSet_cycleGraph {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).edgeSet.ncard = n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hsum : ∑ v, (SimpleGraph.cycleGraph (k + 3)).degree v =
      2 * (SimpleGraph.cycleGraph (k + 3)).edgeSet.ncard := by
    simpa only [card_edgeFinset_eq_ncard] using
      (SimpleGraph.cycleGraph (k + 3)).sum_degrees_eq_twice_card_edges
  simp_rw [SimpleGraph.cycleGraph_degree_three_le] at hsum
  simp at hsum
  omega

/-- The join-edge subgraph of `Cₙ[Kᵣ]`. -/
def joinEdges (n r : ℕ) : SimpleGraph (Fin n × Fin r) :=
  joinBlowup (SimpleGraph.cycleGraph n) r

theorem joinEdges_triangleFree {n r : ℕ} (hn : 4 ≤ n) :
    TriangleFree (joinEdges n r) := by
  exact joinBlowup_triangleFree r (cycleGraph_triangleFree hn)

theorem ncard_edgeSet_joinEdges {n r : ℕ} (hn : 3 ≤ n) :
    (joinEdges n r).edgeSet.ncard = n * r ^ 2 := by
  rw [joinEdges, ncard_edgeSet_joinBlowup, ncard_edgeSet_cycleGraph hn]

/-- The card's strict count, including equality `nr² = 4nr` at `r = 4`.
Only `r ≥ 4` is needed for this arithmetic step. -/
theorem join_count_gt_two_layer_budget (n r : ℕ) (hr : 4 ≤ r) :
    4 * ((n * r : ℕ) : ℤ) - 8 < ((n * r ^ 2 : ℕ) : ℤ) := by
  have hr' : (4 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hprod : 0 ≤ (n : ℤ) * (r : ℤ) * ((r : ℤ) - 4) :=
    mul_nonneg (mul_nonneg hn0 hr0) (sub_nonneg.mpr hr')
  push_cast at hprod ⊢
  nlinarith

/-- Main lower-bound kernel: for every `n,r ≥ 4`, the join-edge subgraph of
`Cₙ[Kᵣ]` cannot be covered by any two layers having the planar triangle-free
budget. This is precisely the obstruction to thickness two used by B138. -/
theorem joinEdges_not_two_planar_layers {n r : ℕ} (hn : 4 ≤ n) (hr : 4 ≤ r)
    (P Q : SimpleGraph (Fin n × Fin r))
    (hP : PlanarTriangleFreeBudget P) (hQ : PlanarTriangleFreeBudget Q)
    (hcover : joinEdges n r ≤ P ⊔ Q) : False := by
  have hN : 3 ≤ Fintype.card (Fin n × Fin r) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hbudget := triangleFree_edge_card_le_two_layers
    (joinEdges n r) P Q hN hP hQ hcover (joinEdges_triangleFree hn)
  have hNcard : Fintype.card (Fin n × Fin r) = n * r := by simp
  rw [hNcard, ncard_edgeSet_joinEdges (by omega : 3 ≤ n)] at hbudget
  have hgt := join_count_gt_two_layer_budget n r hr
  exact (not_le_of_gt hgt) (by simpa [Nat.cast_mul, Nat.cast_pow] using hbudget)

/-- Boundary check at the smallest parameters: `64 > 56`. -/
theorem arithmetic_n4_r4 :
    4 * ((4 * 4 : ℕ) : ℤ) - 8 < ((4 * 4 ^ 2 : ℕ) : ℤ) := by
  norm_num

/-- The card's displayed `C₇[K₄]` arithmetic: `112 > 104`. -/
theorem arithmetic_n7_r4 :
    4 * ((7 * 4 : ℕ) : ℤ) - 8 < ((7 * 4 ^ 2 : ℕ) : ℤ) := by
  norm_num

/-- The graph itself, not merely its formula, has the card's 112 join edges. -/
theorem ncard_joinEdges_n7_r4 : (joinEdges 7 4).edgeSet.ncard = 112 := by
  rw [ncard_edgeSet_joinEdges (by norm_num : 3 ≤ 7)]
  norm_num

/-- At the smallest parameters the graph has 64 join edges, against budget 56. -/
theorem ncard_joinEdges_n4_r4 : (joinEdges 4 4).edgeSet.ncard = 64 := by
  rw [ncard_edgeSet_joinEdges (by norm_num : 3 ≤ 4)]
  norm_num

/-- The one-edge graph on two vertices is triangle-free. -/
theorem top_fin_two_triangleFree : TriangleFree (⊤ : SimpleGraph (Fin 2)) := by
  unfold TriangleFree
  decide

/-- Hence the unqualified planar triangle-free bound `2N - 4` is false at
`N = 2`, even though its one-edge witness is manifestly planar. -/
theorem planar_budget_fails_at_N2 :
    2 * (Fintype.card (Fin 2) : ℤ) - 4 <
      ((⊤ : SimpleGraph (Fin 2)).edgeSet.ncard : ℤ) := by
  rw [← card_edgeFinset_eq_ncard, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

#print axioms TriangleFree.mono
#print axioms triangleFree_edge_card_le_two_layers
#print axioms joinBlowup_triangleFree
#print axioms card_edgeFinset_eq_ncard
#print axioms ncard_edgeSet_joinBlowup
#print axioms cycleGraph_adj_int_cases
#print axioms cycleGraph_triangleFree
#print axioms ncard_edgeSet_cycleGraph
#print axioms joinEdges_triangleFree
#print axioms ncard_edgeSet_joinEdges
#print axioms join_count_gt_two_layer_budget
#print axioms joinEdges_not_two_planar_layers
#print axioms arithmetic_n4_r4
#print axioms arithmetic_n7_r4
#print axioms ncard_joinEdges_n7_r4
#print axioms ncard_joinEdges_n4_r4
#print axioms top_fin_two_triangleFree
#print axioms planar_budget_fails_at_N2

end RelationalAtlas.B138


end

/-! ## B145 — the exact pseudospectral disk (proof)

Integrated from `.ultramath/smwtty35w/m13/B145.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexConjugate BigOperators

namespace RelationalAtlas.B145

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- The Jordan block on the B145 card. -/
def jordan (b μ : ℂ) : Mat := !![b, μ; 0, b]

/-- `zI - Jμ`, with `w = z - b`. -/
def shifted (w μ : ℂ) : Mat := !![w, -μ; 0, w]

/-- The explicit inverse of `shifted w μ` when `w ≠ 0`. -/
noncomputable def resolvent (w μ : ℂ) : Mat := (w ^ 2)⁻¹ • !![w, μ; 0, w]

lemma shifted_mul_resolvent {w : ℂ} (hw : w ≠ 0) (μ : ℂ) :
    shifted w μ * resolvent w μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted, resolvent, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hw]; ring

lemma resolvent_mul_shifted {w : ℂ} (hw : w ≠ 0) (μ : ℂ) :
    resolvent w μ * shifted w μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted, resolvent, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hw]; ring

lemma shifted_eq_smul_one_sub_jordan (z b μ : ℂ) :
    shifted (z - b) μ = z • (1 : Mat) - jordan b μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted, jordan]

lemma shifted_zero_not_isUnit (μ : ℂ) : ¬IsUnit (shifted 0 μ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [shifted, Matrix.det_fin_two]

/-- Within the displayed one-parameter family, normality is exactly the
uncoupled case. -/
lemma jordan_normal_iff (b μ : ℂ) : IsStarNormal (jordan b μ) ↔ μ = 0 := by
  rw [isStarNormal_iff]
  change (star (jordan b μ) * jordan b μ = jordan b μ * star (jordan b μ)) ↔ μ = 0
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [jordan, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.star_def, RCLike.conj_mul, RCLike.mul_conj] at h00
    exact h00
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordan, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- For a `2 × 2` complex matrix, the squared spectral norm is the larger
real characteristic root of `Rᴴ * R`.  This formulation keeps all spectral
radius coercions out of the subsequent calculation. -/
lemma norm_sq_eq_largest_char_root (R : Mat) (t δ : ℝ)
    (htrace : (star R * R).trace = (t : ℂ))
    (hdet : (star R * R).det = (δ : ℂ))
    (hdisc : 0 ≤ t ^ 2 - 4 * δ) :
    ‖R‖ ^ 2 = (t + Real.sqrt (t ^ 2 - 4 * δ)) / 2 := by
  let s := Real.sqrt (t ^ 2 - 4 * δ)
  let lp := (t + s) / 2
  let lm := (t - s) / 2
  have hs : s ^ 2 = t ^ 2 - 4 * δ := by
    exact Real.sq_sqrt hdisc
  have hnorm_real : ‖star R * R‖ ∈ spectrum ℝ (star R * R) := by
    exact CStarAlgebra.norm_mem_spectrum_of_nonneg _ (by cfc_tac)
  have hnorm_complex : ((‖star R * R‖ : ℝ) : ℂ) ∈ spectrum ℂ (star R * R) := by
    simpa using spectrum.algebraMap_mem ℂ hnorm_real
  have hnorm_root : (star R * R).charpoly.IsRoot ((‖star R * R‖ : ℝ) : ℂ) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp hnorm_complex
  change Polynomial.eval ((‖star R * R‖ : ℝ) : ℂ) (star R * R).charpoly = 0 at hnorm_root
  have hnorm_root_real : ‖star R * R‖ ^ 2 - t * ‖star R * R‖ + δ = 0 := by
    simp [Matrix.charpoly_fin_two, htrace, hdet] at hnorm_root
    exact_mod_cast hnorm_root
  have hfactor (x : ℝ) : (x - lm) * (x - lp) = x ^ 2 - t * x + δ := by
    dsimp [lm, lp]
    nlinarith [hs]
  have hzero : (‖star R * R‖ - lm) * (‖star R * R‖ - lp) = 0 := by
    rw [hfactor]
    exact hnorm_root_real
  have hlm_le : lm ≤ lp := by
    dsimp [lm, lp]
    linarith [Real.sqrt_nonneg (t ^ 2 - 4 * δ)]
  have hnorm_le : ‖star R * R‖ ≤ lp := by
    rcases mul_eq_zero.mp hzero with h | h
    · have heq : ‖star R * R‖ = lm := by linarith
      linarith
    · linarith
  have hlp_root_real : lp ^ 2 - t * lp + δ = 0 := by
    calc
      lp ^ 2 - t * lp + δ = (lp - lm) * (lp - lp) := (hfactor lp).symm
      _ = 0 := by ring
  have hlp_root_complex : (star R * R).charpoly.IsRoot ((lp : ℂ)) := by
    change Polynomial.eval (lp : ℂ) (star R * R).charpoly = 0
    simp [Matrix.charpoly_fin_two, htrace, hdet]
    exact_mod_cast hlp_root_real
  have hlp_complex : (lp : ℂ) ∈ spectrum ℂ (star R * R) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hlp_root_complex
  have hlp_real : lp ∈ spectrum ℝ (star R * R) := by
    exact spectrum.of_algebraMap_mem ℂ hlp_complex
  have hlp_nonneg : 0 ≤ lp := spectrum_star_mul_self_nonneg lp hlp_real
  have hle_norm : lp ≤ ‖star R * R‖ := by
    have h := spectrum.norm_le_norm_of_mem hlp_real
    simpa [Real.norm_eq_abs, abs_of_nonneg hlp_nonneg] using h
  have hnorm_eq : ‖star R * R‖ = lp := le_antisymm hnorm_le hle_norm
  calc
    ‖R‖ ^ 2 = ‖star R * R‖ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
      simp [pow_two]
    _ = lp := hnorm_eq
    _ = (t + Real.sqrt (t ^ 2 - 4 * δ)) / 2 := rfl

lemma equalDiagonal_star_mul_self_trace (c d : ℂ) :
    (star (!![c, d; 0, c] : Mat) * !![c, d; 0, c]).trace =
      ((2 * ‖c‖ ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    RCLike.star_def, RCLike.conj_mul]
  ring

lemma equalDiagonal_star_mul_self_det (c d : ℂ) :
    (star (!![c, d; 0, c] : Mat) * !![c, d; 0, c]).det =
      (((‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [RCLike.star_def, RCLike.conj_mul]
  simp [Matrix.det_fin_two]
  ring

lemma norm_sq_equalDiagonal (c d : ℂ) :
    ‖(!![c, d; 0, c] : Mat)‖ ^ 2 =
      (2 * ‖c‖ ^ 2 + ‖d‖ ^ 2 +
        Real.sqrt ((2 * ‖c‖ ^ 2 + ‖d‖ ^ 2) ^ 2 - 4 * (‖c‖ ^ 2) ^ 2)) / 2 := by
  apply norm_sq_eq_largest_char_root
  · exact equalDiagonal_star_mul_self_trace c d
  · exact equalDiagonal_star_mul_self_det c d
  · have hid : (2 * ‖c‖ ^ 2 + ‖d‖ ^ 2) ^ 2 - 4 * (‖c‖ ^ 2) ^ 2 =
        ‖d‖ ^ 4 + 4 * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by ring
    rw [hid]
    positivity

lemma resolvent_eq_equalDiagonal {w : ℂ} (hw : w ≠ 0) (μ : ℂ) :
    resolvent w μ = !![w⁻¹, (w ^ 2)⁻¹ * μ; 0, w⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [resolvent] <;>
    field_simp [hw, pow_two]

lemma resolvent_norm_sq {w : ℂ} (hw : w ≠ 0) (μ : ℂ) :
    ‖resolvent w μ‖ ^ 2 =
      ((‖μ‖ + Real.sqrt (‖μ‖ ^ 2 + 4 * ‖w‖ ^ 2)) /
        (2 * ‖w‖ ^ 2)) ^ 2 := by
  let q := ‖w‖ ^ 2
  let a := ‖μ‖
  let s := Real.sqrt (a ^ 2 + 4 * q)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have ha : 0 ≤ a := by positivity
  have hs : s ^ 2 = a ^ 2 + 4 * q := by
    exact Real.sq_sqrt (by positivity)
  have hc : ‖w⁻¹‖ ^ 2 = q⁻¹ := by
    simp [q, norm_inv]
  have hd : ‖(w ^ 2)⁻¹ * μ‖ ^ 2 = a ^ 2 * (q ^ 2)⁻¹ := by
    simp [a, q, norm_inv, norm_pow]
    ring
  have hrad : (2 * q⁻¹ + a ^ 2 * (q ^ 2)⁻¹) ^ 2 - 4 * (q⁻¹) ^ 2 =
      (a * s / q ^ 2) ^ 2 := by
    field_simp [ne_of_gt hq]
    nlinarith [hs]
  rw [resolvent_eq_equalDiagonal hw μ, norm_sq_equalDiagonal, hc, hd]
  change _ = ((a + s) / (2 * q)) ^ 2
  rw [hrad, Real.sqrt_sq (by positivity : 0 ≤ a * s / q ^ 2)]
  field_simp [ne_of_gt hq]
  nlinarith [hs]

lemma resolvent_norm {w : ℂ} (hw : w ≠ 0) (μ : ℂ) :
    ‖resolvent w μ‖ =
      (‖μ‖ + Real.sqrt (‖μ‖ ^ 2 + 4 * ‖w‖ ^ 2)) /
        (2 * ‖w‖ ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  exact resolvent_norm_sq hw μ

/-- The exact real inequality at the heart of B145.  There is no
small-`ε` or large-`μ` hypothesis. -/
lemma resolvent_threshold {ε q a : ℝ} (hε : 0 < ε) (hq : 0 < q) (ha : 0 ≤ a) :
    ε⁻¹ < (a + Real.sqrt (a ^ 2 + 4 * q)) / (2 * q) ↔
      q < ε * a + ε ^ 2 := by
  let s := Real.sqrt (a ^ 2 + 4 * q)
  have hs : s ^ 2 = a ^ 2 + 4 * q := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hsa : 0 < s + a := by positivity
  change ε⁻¹ < (a + s) / (2 * q) ↔ q < ε * a + ε ^ 2
  have hleft : ε⁻¹ < (a + s) / (2 * q) ↔ 2 * q < ε * (a + s) := by
    constructor
    · intro h
      have h' := (lt_div_iff₀ (by positivity : 0 < 2 * q)).mp h
      have h'' := mul_lt_mul_of_pos_left h' hε
      have heq : ε * (ε⁻¹ * (2 * q)) = 2 * q := by
        field_simp [ne_of_gt hε]
      rw [heq] at h''
      exact h''
    · intro h
      apply (lt_div_iff₀ (by positivity : 0 < 2 * q)).mpr
      have h' := mul_lt_mul_of_pos_left h (inv_pos.mpr hε)
      have heq : ε⁻¹ * (ε * (a + s)) = a + s := by
        field_simp [ne_of_gt hε]
      rw [heq] at h'
      exact h'
  rw [hleft]
  constructor
  · intro h
    have hprod : (s - a) * (s + a) < (2 * ε) * (s + a) := by
      nlinarith [hs]
    have hslt : s - a < 2 * ε := (mul_lt_mul_iff_left₀ hsa).mp hprod
    have hsquare : s ^ 2 < (a + 2 * ε) ^ 2 :=
      (sq_lt_sq₀ hs0 (by positivity)).mpr (by linarith)
    nlinarith [hs]
  · intro h
    have hsquare : s ^ 2 < (a + 2 * ε) ^ 2 := by
      nlinarith [hs]
    have hslt : s < a + 2 * ε := (sq_lt_sq₀ hs0 (by positivity)).mp hsquare
    have hprod : (s - a) * (s + a) < (2 * ε) * (s + a) :=
      (mul_lt_mul_iff_left₀ hsa).mpr (by linarith)
    nlinarith [hs]

lemma resolvent_norm_gt_inv_iff {w : ℂ} (hw : w ≠ 0) (μ : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ε⁻¹ < ‖resolvent w μ‖ ↔
      ‖w‖ < Real.sqrt (ε * ‖μ‖ + ε ^ 2) := by
  rw [resolvent_norm hw μ]
  rw [resolvent_threshold hε (by positivity) (norm_nonneg μ)]
  exact (Real.lt_sqrt (norm_nonneg w)).symm

/-- Resolvent pseudospectrum: the double eigenvalue is included separately;
away from it, the condition is the usual strict spectral-resolvent bound. -/
def pseudoSpectrum (ε : ℝ) (b μ : ℂ) : Set ℂ :=
  {z | z = b ∨ (z - b ≠ 0 ∧ ε⁻¹ < ‖resolvent (z - b) μ‖)}

/-- B145, with the perturbation size made positive.  The displayed set is an
open disk, including at `μ = 0`; no square-root approximation is involved. -/
theorem mem_pseudoSpectrum_iff {ε : ℝ} (hε : 0 < ε) (b μ z : ℂ) :
    z ∈ pseudoSpectrum ε b μ ↔
      ‖z - b‖ < Real.sqrt (ε * ‖μ‖ + ε ^ 2) := by
  change (z = b ∨ (z - b ≠ 0 ∧ ε⁻¹ < ‖resolvent (z - b) μ‖)) ↔ _
  by_cases hz : z = b
  · subst z
    have hr : 0 < Real.sqrt (ε * ‖μ‖ + ε ^ 2) := by positivity
    simp [hr]
  · have hw : z - b ≠ 0 := sub_ne_zero.mpr hz
    simp only [hz, false_or]
    rw [and_iff_right hw]
    exact resolvent_norm_gt_inv_iff hw μ hε

theorem pseudoSpectrum_eq_disk {ε : ℝ} (hε : 0 < ε) (b μ : ℂ) :
    pseudoSpectrum ε b μ = {z | ‖z - b‖ < Real.sqrt (ε * ‖μ‖ + ε ^ 2)} := by
  ext z
  exact mem_pseudoSpectrum_iff hε b μ z

/-- The card's normal comparison is the `μ = 0` instance of the same formula:
the radius is exactly `ε`, and the inequality remains strict. -/
theorem pseudoSpectrum_uncoupled {ε : ℝ} (hε : 0 < ε) (b : ℂ) :
    pseudoSpectrum ε b 0 = Metric.ball b ε := by
  rw [pseudoSpectrum_eq_disk hε]
  ext z
  simp [Metric.mem_ball, dist_eq_norm, Real.sqrt_sq hε.le]

/-- The displayed disk is genuinely open: its boundary is excluded. -/
theorem not_mem_pseudoSpectrum_boundary {ε : ℝ} (hε : 0 < ε) (b μ z : ℂ)
    (hz : ‖z - b‖ = Real.sqrt (ε * ‖μ‖ + ε ^ 2)) :
    z ∉ pseudoSpectrum ε b μ := by
  rw [mem_pseudoSpectrum_iff hε]
  rw [hz]
  exact lt_irrefl _


-- Required axiom audit (only propext, Classical.choice, Quot.sound are permitted).
#print axioms shifted_mul_resolvent
#print axioms resolvent_mul_shifted
#print axioms shifted_eq_smul_one_sub_jordan
#print axioms shifted_zero_not_isUnit
#print axioms jordan_normal_iff
#print axioms norm_sq_eq_largest_char_root
#print axioms equalDiagonal_star_mul_self_trace
#print axioms equalDiagonal_star_mul_self_det
#print axioms norm_sq_equalDiagonal
#print axioms resolvent_eq_equalDiagonal
#print axioms resolvent_norm_sq
#print axioms resolvent_norm
#print axioms resolvent_threshold
#print axioms resolvent_norm_gt_inv_iff
#print axioms mem_pseudoSpectrum_iff
#print axioms pseudoSpectrum_eq_disk
#print axioms pseudoSpectrum_uncoupled
#print axioms not_mem_pseudoSpectrum_boundary

end RelationalAtlas.B145


end

/-! ## B171 — the compressed scaling, and the hidden block is only line-valued (proof and correction)

Integrated from `.ultramath/smwtty35w/m11/B171.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


open scoped BigOperators Matrix
open Finset

noncomputable section

namespace RelationalAtlas.B171

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The free scaling operator on real square matrices. -/
def D (t : n → ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal t * H + H * Matrix.diagonal t

/-- The card's trace-zero projection, with `W = diagonal w`. -/
def P (w : n → ℝ) (Z : Matrix n n ℝ) : Matrix n n ℝ :=
  Z - Matrix.trace Z • Matrix.diagonal w

/-- The complementary projection. -/
def Q (w : n → ℝ) (Z : Matrix n n ℝ) : Matrix n n ℝ :=
  Z - P w Z

/-- The card's kinetic pairing (no complex conjugation: these are real matrices). -/
def g (w : n → ℝ) (H K : Matrix n n ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, H i j * K i j / (w i + w j)

/-- The compressed transport. -/
def A (t w : n → ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ :=
  P w (D t (P w H))

/-- The off-diagonal block whose adjoint-square is the hidden block. -/
def C (t w : n → ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ :=
  Q w (D t (P w H))

/-- The adjoint off-diagonal block. -/
def Cad (t w : n → ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ :=
  P w (D t (Q w H))

/-- `P D² P - A²`, literally the hidden block in the card. -/
def hidden (t w : n → ℝ) (H : Matrix n n ℝ) : Matrix n n ℝ :=
  P w (D t (D t (P w H))) - A t w (A t w H)

@[simp] theorem D_apply (t : n → ℝ) (H : Matrix n n ℝ) (i j : n) :
    D t H i j = t i * H i j + H i j * t j := by
  simp [D]

@[simp] theorem P_trace (w : n → ℝ) (hw : ∑ i, w i = 1)
    (Z : Matrix n n ℝ) : Matrix.trace (P w Z) = 0 := by
  simp [P, Matrix.trace_diagonal, hw]

theorem P_idem (w : n → ℝ) (hw : ∑ i, w i = 1)
    (Z : Matrix n n ℝ) : P w (P w Z) = P w Z := by
  change P w Z - Matrix.trace (P w Z) • Matrix.diagonal w = P w Z
  rw [P_trace w hw]
  simp

theorem P_on_trace_zero (w : n → ℝ) (H : Matrix n n ℝ)
    (hH : Matrix.trace H = 0) : P w H = H := by
  simp [P, hH]

theorem Q_eq (w : n → ℝ) (Z : Matrix n n ℝ) :
    Q w Z = Matrix.trace Z • Matrix.diagonal w := by
  simp [Q, P]

theorem Q_idem (w : n → ℝ) (hw : ∑ i, w i = 1)
    (Z : Matrix n n ℝ) : Q w (Q w Z) = Q w Z := by
  rw [Q_eq, Q_eq]
  simp [Matrix.trace_diagonal, hw]

@[simp] theorem Q_P (w : n → ℝ) (hw : ∑ i, w i = 1)
    (Z : Matrix n n ℝ) : Q w (P w Z) = 0 := by
  rw [Q_eq, P_trace w hw]
  simp

@[simp] theorem P_Q (w : n → ℝ) (hw : ∑ i, w i = 1)
    (Z : Matrix n n ℝ) : P w (Q w Z) = 0 := by
  rw [Q_eq]
  simp [P, Matrix.trace_diagonal, hw]

theorem g_sub_left (w : n → ℝ) (X Y K : Matrix n n ℝ) :
    g w (X - Y) K = g w X K - g w Y K := by
  simp only [g, Matrix.sub_apply, sub_mul, sub_div]
  simp_rw [Finset.sum_sub_distrib]
  ring

theorem g_sub_right (w : n → ℝ) (H X Y : Matrix n n ℝ) :
    g w H (X - Y) = g w H X - g w H Y := by
  simp only [g, Matrix.sub_apply, mul_sub, sub_div]
  simp_rw [Finset.sum_sub_distrib]
  ring

theorem g_smul_left (w : n → ℝ) (c : ℝ) (X K : Matrix n n ℝ) :
    g w (c • X) K = c * g w X K := by
  simp only [g, Matrix.smul_apply, smul_eq_mul]
  have h (i : n) :
      (∑ j, (c * X i j) * K i j / (w i + w j)) =
        c * ∑ j, X i j * K i j / (w i + w j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

theorem g_smul_right (w : n → ℝ) (c : ℝ) (H X : Matrix n n ℝ) :
    g w H (c • X) = c * g w H X := by
  simp only [g, Matrix.smul_apply, smul_eq_mul]
  have h (i : n) :
      (∑ j, H i j * (c * X i j) / (w i + w j)) =
        c * ∑ j, H i j * X i j / (w i + w j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

/-- The card's auxiliary identity `g_W(W,H) = ¼ Tr H`. -/
theorem g_diagonal (w : n → ℝ) (hw : ∀ i, w i ≠ 0)
    (H : Matrix n n ℝ) :
    g w (Matrix.diagonal w) H = (1 / 4 : ℝ) * Matrix.trace H := by
  classical
  simp only [g, Matrix.diagonal_apply]
  have hsum :
      (∑ i, ∑ j, (if i = j then w i else 0) * H i j / (w i + w j)) =
        ∑ i, w i * H i i / (w i + w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · simp
  rw [hsum]
  change (1 / 2 : ℝ) * (∑ i, w i * H i i / (w i + w i)) =
    (1 / 4 : ℝ) * ∑ i, H i i
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hw i]
  ring

theorem g_comm (w : n → ℝ) (H K : Matrix n n ℝ) : g w H K = g w K H := by
  simp only [g]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem g_diagonal_right (w : n → ℝ) (hw : ∀ i, w i ≠ 0)
    (H : Matrix n n ℝ) :
    g w H (Matrix.diagonal w) = (1 / 4 : ℝ) * Matrix.trace H := by
  rw [g_comm, g_diagonal w hw]

/-- `P` is symmetric for the kinetic pairing. -/
theorem g_P (w : n → ℝ) (hw : ∀ i, w i ≠ 0) (H K : Matrix n n ℝ) :
    g w (P w H) K = g w H (P w K) := by
  unfold P
  rw [g_sub_left, g_sub_right, g_smul_left, g_smul_right,
    g_diagonal w hw, g_diagonal_right w hw]
  ring

/-- The free scaling is symmetric for the kinetic pairing; no distinctness of weights is used. -/
theorem g_D (t w : n → ℝ) (H K : Matrix n n ℝ) :
    g w (D t H) K = g w H (D t K) := by
  simp only [g, D_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Orthogonality of the complementary projection. -/
theorem g_Q (w : n → ℝ) (hw : ∀ i, w i ≠ 0) (H K : Matrix n n ℝ) :
    g w (Q w H) K = g w H (Q w K) := by
  unfold Q
  rw [g_sub_left, g_sub_right, g_P w hw]

/-- The compression is self-adjoint in exactly the card's pairing. -/
theorem g_A (t w : n → ℝ) (hw : ∀ i, w i ≠ 0) (H K : Matrix n n ℝ) :
    g w (A t w H) K = g w H (A t w K) := by
  simp only [A]
  rw [g_P w hw, g_D, g_P w hw]

/-- On trace-zero tangents the compression has the card's displayed entrywise formula. -/
theorem A_of_trace_zero (t w : n → ℝ)
    (H : Matrix n n ℝ) (hH : Matrix.trace H = 0) :
    A t w H = D t H - (2 * Matrix.trace (Matrix.diagonal t * H)) • Matrix.diagonal w := by
  have hp : P w H = H := P_on_trace_zero w H hH
  have htrace : Matrix.trace (D t H) =
      2 * Matrix.trace (Matrix.diagonal t * H) := by
    rw [D, Matrix.trace_add, Matrix.trace_mul_comm H]
    ring
  unfold A
  rw [hp]
  unfold P
  rw [htrace]

/-- The kinetic pairing is positive for positive weights. -/
theorem g_self_nonneg (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (H : Matrix n n ℝ) : 0 ≤ g w H H := by
  unfold g
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (mul_self_nonneg _) (by linarith [hw i, hw j])

/-- Positive weights also make the pairing definite, including when weights repeat. -/
theorem g_self_eq_zero (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (H : Matrix n n ℝ) (h : g w H H = 0) : H = 0 := by
  unfold g at h
  have htotal : (∑ i, ∑ j, H i j * H i j / (w i + w j)) = 0 := by
    linarith
  ext i j
  have houter_nonneg : ∀ k ∈ (Finset.univ : Finset n),
      0 ≤ ∑ l, H k l * H k l / (w k + w l) := by
    intro k hk
    apply Finset.sum_nonneg
    intro l hl
    exact div_nonneg (mul_self_nonneg _) (by linarith [hw k, hw l])
  have hi := (Finset.sum_eq_zero_iff_of_nonneg houter_nonneg).mp htotal
    i (Finset.mem_univ i)
  have hinner_nonneg : ∀ l ∈ (Finset.univ : Finset n),
      0 ≤ H i l * H i l / (w i + w l) := by
    intro l hl
    exact div_nonneg (mul_self_nonneg _) (by linarith [hw i, hw l])
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).mp hi
    j (Finset.mem_univ j)
  have hden : w i + w j ≠ 0 := ne_of_gt (by linarith [hw i, hw j])
  have hnum : H i j * H i j = 0 :=
    ((div_eq_zero_iff).mp hterm).resolve_right hden
  exact mul_self_eq_zero.mp hnum

@[simp] theorem P_zero (w : n → ℝ) : P w 0 = 0 := by
  simp [P]

@[simp] theorem Q_zero (w : n → ℝ) : Q w 0 = 0 := by
  simp [Q]

@[simp] theorem D_zero (t : n → ℝ) : D t 0 = 0 := by
  simp [D]

theorem P_add (w : n → ℝ) (X Y : Matrix n n ℝ) :
    P w (X + Y) = P w X + P w Y := by
  simp only [P, Matrix.trace_add, add_smul]
  abel

theorem D_add (t : n → ℝ) (X Y : Matrix n n ℝ) :
    D t (X + Y) = D t X + D t Y := by
  simp only [D, mul_add, add_mul]
  abel

theorem P_smul (w : n → ℝ) (c : ℝ) (X : Matrix n n ℝ) :
    P w (c • X) = c • P w X := by
  simp only [P, Matrix.trace_smul, smul_eq_mul, smul_sub, smul_smul, mul_comm]

theorem D_smul (t : n → ℝ) (c : ℝ) (X : Matrix n n ℝ) :
    D t (c • X) = c • D t X := by
  ext i j
  simp only [D_apply, Matrix.smul_apply, smul_eq_mul, mul_add]
  ring

theorem Cad_smul (t w : n → ℝ) (c : ℝ) (X : Matrix n n ℝ) :
    Cad t w (c • X) = c • Cad t w X := by
  unfold Cad
  have hQ : Q w (c • X) = c • Q w X := by
    simp only [Q, P_smul, smul_sub]
  rw [hQ, D_smul, P_smul]

@[simp] theorem Cad_zero (t w : n → ℝ) : Cad t w 0 = 0 := by
  simp [Cad]

theorem P_add_Q (w : n → ℝ) (Z : Matrix n n ℝ) : P w Z + Q w Z = Z := by
  simp [Q]

theorem D_decomp (t w : n → ℝ) (Z : Matrix n n ℝ) :
    D t Z = D t (P w Z) + D t (Q w Z) := by
  rw [← D_add, P_add_Q]

/-- The exact hidden-block factorization.  Its rank is therefore **at most** one. -/
theorem hidden_eq_Cad_C (t w : n → ℝ) (hw : ∑ i, w i = 1)
    (H : Matrix n n ℝ) :
    hidden t w H = Cad t w (C t w H) := by
  have hdecomp := D_decomp t w (D t (P w H))
  simp only [hidden, Cad, C, A]
  rw [hdecomp, P_add, P_idem w hw, Q_idem w hw]
  abel

/-- The factor `C` and `Cad` are adjoints, so the hidden block is positive. -/
theorem g_hidden (t w : n → ℝ) (hw : ∀ i, w i ≠ 0)
    (hsum : ∑ i, w i = 1) (H K : Matrix n n ℝ) :
    g w (hidden t w H) K = g w (C t w H) (C t w K) := by
  rw [hidden_eq_Cad_C t w hsum]
  simp only [Cad, C]
  rw [g_P w hw, g_D, g_Q w hw]

/-- Positivity of the hidden block in the card's own metric. -/
theorem hidden_positive (t w : n → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (H : Matrix n n ℝ) :
    0 ≤ g w H (hidden t w H) := by
  rw [g_comm w H (hidden t w H),
    g_hidden t w (fun i => (hw i).ne') hsum]
  exact g_self_nonneg w hw _

/-- Every value of the hidden block lies in one fixed line. -/
theorem hidden_rank_le_one (t w : n → ℝ) (hw : ∑ i, w i = 1)
    (H : Matrix n n ℝ) :
    hidden t w H = Matrix.trace (D t (P w H)) • Cad t w (Matrix.diagonal w) := by
  rw [hidden_eq_Cad_C t w hw]
  unfold C
  rw [Q_eq, Cad_smul]

/-- A scalar `T` makes the off-diagonal block vanish. -/
theorem C_scalar (w : n → ℝ) (hw : ∑ i, w i = 1) (c : ℝ)
    (H : Matrix n n ℝ) : C (fun _ => c) w H = 0 := by
  have hD : D (fun _ : n => c) (P w H) = (2 * c) • P w H := by
    ext i j
    simp [mul_add, add_mul]
    ring
  unfold C
  rw [hD, Q_eq, Matrix.trace_smul, P_trace w hw]
  simp

/-- **Counterexample to the card's unconditional rank-one clause.**  If `T = cI`,
the hidden block is the zero operator, although all interior hypotheses hold. -/
theorem hidden_scalar (w : n → ℝ) (hw : ∑ i, w i = 1) (c : ℝ)
    (H : Matrix n n ℝ) : hidden (fun _ => c) w H = 0 := by
  rw [hidden_eq_Cad_C _ w hw, C_scalar w hw, Cad_zero]

/-- The exact nondegeneracy condition distinguishing rank zero from rank one. -/
theorem hidden_eq_zero_iff_C_eq_zero (t w : n → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (H : Matrix n n ℝ) :
    hidden t w H = 0 ↔ C t w H = 0 := by
  constructor
  · intro hh
    apply g_self_eq_zero w hw
    rw [← g_hidden t w (fun i => (hw i).ne') hsum, hh]
    simp [g]
  · intro hC
    rw [hidden_eq_Cad_C t w hsum, hC, Cad_zero]

/-- Concrete valid weights `(1/2,1/2)` and scalar `T = I` for the refutation. -/
def w2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]
def t2 : Fin 2 → ℝ := ![1, 1]
def H2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem w2_pos (i : Fin 2) : 0 < w2 i := by
  fin_cases i <;> norm_num [w2]

theorem w2_sum : ∑ i, w2 i = 1 := by
  norm_num [w2, Fin.sum_univ_two]

theorem t2_eq_one : t2 = fun _ => (1 : ℝ) := by
  ext i
  fin_cases i <;> rfl

theorem t2_pos (i : Fin 2) : 0 < t2 i := by
  fin_cases i <;> norm_num [t2]

theorem H2_trace : Matrix.trace H2 = 0 := by
  norm_num [H2, Matrix.trace, Fin.sum_univ_two]

theorem H2_ne_zero : H2 ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [H2] at h00

/-- The counterexample has a nonzero trace-zero tangent and still has zero hidden
block everywhere: the literal rank-one assertion is false, not vacuous. -/
theorem literal_rank_one_counterexample :
    (∀ i, 0 < w2 i) ∧ (∀ i, 0 < t2 i) ∧ (∑ i, w2 i = 1) ∧
      Matrix.trace H2 = 0 ∧ H2 ≠ 0 ∧ ∀ H, hidden t2 w2 H = 0 := by
  refine ⟨w2_pos, t2_pos, w2_sum, H2_trace, H2_ne_zero, ?_⟩
  intro H
  rw [t2_eq_one]
  exact hidden_scalar w2 w2_sum 1 H

#print axioms D_apply
#print axioms P_trace
#print axioms P_idem
#print axioms P_on_trace_zero
#print axioms Q_eq
#print axioms Q_idem
#print axioms Q_P
#print axioms P_Q
#print axioms g_sub_left
#print axioms g_sub_right
#print axioms g_smul_left
#print axioms g_smul_right
#print axioms g_diagonal
#print axioms g_comm
#print axioms g_diagonal_right
#print axioms g_P
#print axioms g_D
#print axioms g_Q
#print axioms g_A
#print axioms A_of_trace_zero
#print axioms g_self_nonneg
#print axioms g_self_eq_zero
#print axioms P_zero
#print axioms Q_zero
#print axioms D_zero
#print axioms P_add
#print axioms D_add
#print axioms P_smul
#print axioms D_smul
#print axioms Cad_smul
#print axioms Cad_zero
#print axioms P_add_Q
#print axioms D_decomp
#print axioms hidden_eq_Cad_C
#print axioms g_hidden
#print axioms hidden_positive
#print axioms hidden_rank_le_one
#print axioms C_scalar
#print axioms hidden_scalar
#print axioms hidden_eq_zero_iff_C_eq_zero
#print axioms w2_pos
#print axioms w2_sum
#print axioms t2_eq_one
#print axioms t2_pos
#print axioms H2_trace
#print axioms H2_ne_zero
#print axioms literal_rank_one_counterexample

end RelationalAtlas.B171


end

/-! ## B183 / B184 — the unitary-connection energy identities (proof; the hypothesis is load-bearing)

Integrated from `.ultramath/smwtty35w/m2/B183B184.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B183/B184: the opposite connection energy and its two trace books

The Frobenius norm is used throughout.  `oppositeEnergy` is half the sum over
ordered adjacent pairs, hence the sum over undirected edges; this is exactly the
convention in the B183 display.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace AtlasB183B184

/-- Squared Frobenius norm as an entry sum. -/
theorem norm_sq_eq_sum {m n α : Type*} [Fintype m] [Fintype n]
    [SeminormedAddCommGroup α] (X : Matrix m n α) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- Real part commutes with a finite sum of complex numbers. -/
theorem complex_re_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

/-- Frobenius energy is the real part of the Gram trace. -/
theorem norm_sq_eq_re_trace {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]
    (X : Matrix m n 𝕜) : ‖X‖ ^ 2 = RCLike.re (trace (Xᴴ * X)) := by
  rw [norm_sq_eq_sum, Finset.sum_comm]
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Left multiplication by a unitary preserves Frobenius norm. -/
theorem norm_unitary_mul {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]
    [DecidableEq m] {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜)
    (X : Matrix m n 𝕜) : ‖U * X‖ = ‖X‖ := by
  have hsq : ‖U * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [norm_sq_eq_re_trace, norm_sq_eq_re_trace, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Right multiplication by a unitary preserves Frobenius norm. -/
theorem norm_mul_unitary {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]
    [DecidableEq n] (X : Matrix m n 𝕜) {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖X * U‖ = ‖X‖ := by
  rw [← frobenius_norm_conjTranspose (X * U), conjTranspose_mul, ← star_eq_conjTranspose U,
    norm_unitary_mul (Unitary.star_mem hU), frobenius_norm_conjTranspose]

/-- A real scalar scales squared Frobenius energy by its square. -/
theorem norm_sq_real_smul {m n α : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup α] [NormedSpace ℝ α] (r : ℝ) (X : Matrix m n α) :
    ‖r • X‖ ^ 2 = r ^ 2 * ‖X‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

section Algebra

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The displayed B183 algebraic identity, before taking Frobenius norms. -/
theorem square_sub_starSquare_diagonal_add [StarRing R] (D : ι → R)
    (hD : ∀ i, star (D i) = D i) (A : Matrix ι ι R) (hA : Aᴴ = -A) :
    (diagonal D + A) ^ 2 - (diagonal D + A)ᴴ ^ 2 =
      2 • (diagonal D * A + A * diagonal D) := by
  have hstar : star D = D := funext hD
  rw [conjTranspose_add, diagonal_conjTranspose, hstar, hA]
  noncomm_ring

@[simp] theorem diagonal_mul_add_mul_diagonal_apply (D : ι → R)
    (A : Matrix ι ι R) (i j : ι) :
    (diagonal D * A + A * diagonal D) i j = D i * A i j + A i j * D j := by
  simp [diagonal_mul, mul_diagonal]

end Algebra

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

/-- The full square comparison has four times the ordered anti-commutator energy. -/
theorem norm_sq_square_sub_starSquare (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) :
    ‖(diagonal D + A) ^ 2 - (diagonal D + A)ᴴ ^ 2‖ ^ 2 =
      4 * ∑ i, ∑ j, ‖D i * A i j + A i j * D j‖ ^ 2 := by
  rw [square_sub_starSquare_diagonal_add D (fun i => hD i) A hA, norm_sq_eq_sum]
  simp only [Matrix.smul_apply, diagonal_mul_add_mul_diagonal_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [norm_sq_real_smul]
  norm_num

/-- A unitary connection, with the same support, skew and unitary-block
hypotheses as B183. -/
structure IsUnitaryConnection (G : SimpleGraph ι)
    (A : Matrix ι ι (Matrix m m ℂ)) : Prop where
  conjTranspose_eq_neg : Aᴴ = -A
  eq_zero_of_not_adj : ∀ i j, ¬G.Adj i j → A i j = 0
  mem_unitaryGroup : ∀ i j, G.Adj i j → A i j ∈ unitaryGroup m ℂ

/-- Anti-parallel transport on every edge. -/
def IsAntiParallel (G : SimpleGraph ι) (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) : Prop :=
  ∀ i j, G.Adj i j → D i + A i j * D j * (A i j)ᴴ = 0

/-- B183's edge sum, written as half the sum over ordered adjacent pairs. -/
noncomputable def oppositeEnergy (G : SimpleGraph ι) [DecidableRel G.Adj]
    (A : Matrix ι ι (Matrix m m ℂ)) (D : ι → Matrix m m ℂ) : ℝ :=
  (∑ i, ∑ j, if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) / 2

variable {G : SimpleGraph ι}

omit [Fintype ι] [DecidableEq ι] in
theorem IsUnitaryConnection.apply_eq_neg_conjTranspose
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) (j i : ι) :
    A j i = -(A i j)ᴴ := by
  have h := congrFun (congrFun hA.conjTranspose_eq_neg j) i
  rw [conjTranspose_apply, Matrix.neg_apply] at h
  rw [← star_eq_conjTranspose, h, neg_neg]

/-- Right multiplication by a unitary block identifies the two local energies. -/
theorem norm_mul_add_mul_eq_of_mem_unitaryGroup {U : Matrix m m ℂ}
    (hU : U ∈ unitaryGroup m ℂ) (X Y : Matrix m m ℂ) :
    ‖X * U + U * Y‖ = ‖X + U * Y * Uᴴ‖ := by
  have h : X * U + U * Y = (X + U * Y * Uᴴ) * U := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * Y), ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.mul_one]
  rw [h, norm_mul_unitary _ hU]


/-- **B183, ordered-pair form.**  The factor `8` is exactly four from the
leading two in the square comparison and two from the ordered orientations. -/
theorem b183_oppositeEnergy [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) ^ 2 - (diagonal D + A)ᴴ ^ 2‖ ^ 2 / 8 =
      oppositeEnergy G A D := by
  rw [norm_sq_square_sub_starSquare D hD A hA.conjTranspose_eq_neg, oppositeEnergy]
  have h : ∀ i j, ‖D i * A i j + A i j * D j‖ ^ 2 =
      if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rw [norm_mul_add_mul_eq_of_mem_unitaryGroup (hA.mem_unitaryGroup i j hij)]
    · simp [hA.eq_zero_of_not_adj i j hij]
  simp_rw [h]
  ring



omit [Fintype ι] [DecidableEq ι] in
/-- The ordered anti-commutator summand is independent of orientation. -/
theorem IsUnitaryConnection.norm_mul_add_mul_comm
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) (i j : ι) :
    ‖D j * A j i + A j i * D i‖ = ‖D i * A i j + A i j * D j‖ := by
  rw [hA.apply_eq_neg_conjTranspose j i]
  generalize A i j = U
  have h : D j * (-Uᴴ) + (-Uᴴ) * D i = -((D i * U + U * D j)ᴴ) := by
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
      (hD i).eq, (hD j).eq]
    noncomm_ring
  rw [h, norm_neg, frobenius_norm_conjTranspose]

/-- Summing a symmetric function over ordered adjacent pairs counts every
undirected edge exactly twice. -/
theorem sum_sum_ite_adj_eq_two_mul_sum_edgeFinset [DecidableRel G.Adj]
    {M : Type*} [AddCommMonoid M] (f : ι → ι → M) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if G.Adj i j then f i j else 0) =
      2 • ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, hf⟩ e := by
  classical
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then f i j else 0),
    ← Finset.sum_filter, Finset.smul_sum]
  have hmaps : ∀ p ∈ {p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι) |
      G.Adj p.1 p.2}, s(p.1, p.2) ∈ G.edgeFinset := by
    intro p hp
    simpa using (Finset.mem_filter.1 hp).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
  have hab : G.Adj a b := by simpa using he
  have hfib : {p ∈ {p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι) |
      G.Adj p.1 p.2} | s(p.1, p.2) = s(a, b)} = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hab.symm, Or.inr ⟨rfl, rfl⟩⟩
  have hne : (a, b) ≠ (b, a) := fun h => hab.ne (Prod.mk.inj h).1
  rw [hfib, Finset.sum_pair hne, Sym2.lift_mk, hf b a, two_nsmul]

/-- **B183 as a sum over the undirected edge finset.**  On each edge the
shown summand equals the card's displayed local expression by
`norm_mul_add_mul_eq_of_mem_unitaryGroup`. -/
theorem b183_oppositeEnergy_eq_sum_edgeFinset [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) ^ 2 - (diagonal D + A)ᴴ ^ 2‖ ^ 2 / 8 =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun i j => ‖D i * A i j + A i j * D j‖ ^ 2,
        fun i j => by simp only [hA.norm_mul_add_mul_comm hD]⟩ e := by
  rw [norm_sq_square_sub_starSquare D hD A hA.conjTranspose_eq_neg]
  have h : ∀ i j, ‖D i * A i j + A i j * D j‖ ^ 2 =
      if G.Adj i j then ‖D i * A i j + A i j * D j‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rfl
    · rw [hA.eq_zero_of_not_adj i j hij, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j,
    sum_sum_ite_adj_eq_two_mul_sum_edgeFinset _ fun i j => by
      simp only [hA.norm_mul_add_mul_comm hD], nsmul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- The edge sum vanishes exactly on the anti-parallel sections. -/
theorem oppositeEnergy_eq_zero_iff [DecidableRel G.Adj]
    (A : Matrix ι ι (Matrix m m ℂ)) (D : ι → Matrix m m ℂ) :
    oppositeEnergy G A D = 0 ↔ IsAntiParallel G A D := by
  have hnn : ∀ i j, 0 ≤ if G.Adj i j then
      ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j
    split_ifs <;> positivity
  rw [oppositeEnergy, div_eq_zero_iff, or_iff_left two_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  split_ifs with hij
  · simp [hij, pow_eq_zero_iff]
  · simp [hij]

/-- Hermiticity of `H²` is precisely equality with `(Hᴴ)²`. -/
theorem isHermitian_sq_iff {R : Type*} [Ring R] [StarRing R]
    (H : Matrix ι ι R) : (H ^ 2).IsHermitian ↔ H ^ 2 = Hᴴ ^ 2 := by
  simp only [Matrix.IsHermitian, conjTranspose_pow]
  exact eq_comm

/-- **B183's zero condition, with both directions.**  No connectedness,
nonempty-graph, or nondegeneracy assumption is needed. -/
theorem b183_zero_iff_isHermitian_sq [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    oppositeEnergy G A D = 0 ↔ ((diagonal D + A) ^ 2).IsHermitian := by
  let H : Matrix ι ι (Matrix m m ℂ) := diagonal D + A
  have hmain : ‖H ^ 2 - Hᴴ ^ 2‖ ^ 2 / 8 = oppositeEnergy G A D :=
    b183_oppositeEnergy hA hD
  constructor
  · intro he
    rw [← hmain] at he
    have hs : ‖H ^ 2 - Hᴴ ^ 2‖ ^ 2 = 0 := by linarith
    have hn : ‖H ^ 2 - Hᴴ ^ 2‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 hs
    have hm : H ^ 2 - Hᴴ ^ 2 = 0 := norm_eq_zero.1 hn
    exact (isHermitian_sq_iff H).2 (sub_eq_zero.1 hm)
  · intro hh
    have hm : H ^ 2 - Hᴴ ^ 2 = 0 := sub_eq_zero.2 ((isHermitian_sq_iff H).1 hh)
    rw [← hmain, hm, norm_zero]
    norm_num


section B184

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian half, with the real factor `1/2` used in B184. -/
noncomputable def hermPart (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℝ)⁻¹ • (X + Xᴴ)

/-- Skew-Hermitian half, with the real factor `1/2` used in B184. -/
noncomputable def skewPart (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℝ)⁻¹ • (X - Xᴴ)

/-- The two B184 books. -/
noncomputable def Eminus (X : Matrix n n ℂ) : ℝ := 2 * ‖hermPart X‖ ^ 2
noncomputable def Eplus (X : Matrix n n ℂ) : ℝ := 2 * ‖skewPart X‖ ^ 2

/-- Frobenius expansion of a sum, including its real cross term. -/
theorem norm_sq_add (X Y : Matrix n n ℂ) :
    ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 + 2 * (Xᴴ * Y).trace.re := by
  rw [norm_sq_eq_re_trace, norm_sq_eq_re_trace, norm_sq_eq_re_trace]
  have hc : (Yᴴ * X).trace = star ((Xᴴ * Y).trace) := by
    calc
      (Yᴴ * X).trace = ((Xᴴ * Y)ᴴ).trace := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
      _ = star ((Xᴴ * Y).trace) := trace_conjTranspose _
  have hre : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, trace_add,
    RCLike.re_to_complex, Complex.add_re]
  rw [hre]
  ring

/-- Frobenius expansion of a difference. -/
theorem norm_sq_sub (X Y : Matrix n n ℂ) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 - 2 * (Xᴴ * Y).trace.re := by
  have h := norm_sq_add X (-Y)
  simpa [sub_eq_add_neg, Matrix.mul_neg, trace_neg] using h

theorem Eminus_eq_half_norm_add (X : Matrix n n ℂ) :
    Eminus X = ‖X + Xᴴ‖ ^ 2 / 2 := by
  rw [Eminus, hermPart, norm_sq_real_smul]
  have h : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
  rw [h]
  ring

theorem Eplus_eq_half_norm_sub (X : Matrix n n ℂ) :
    Eplus X = ‖X - Xᴴ‖ ^ 2 / 2 := by
  rw [Eplus, skewPart, norm_sq_real_smul]
  have h : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
  rw [h]
  ring

/-- **B184 fixed budget.**  Twice the squared norms of the Hermitian and
skew halves add to twice the squared norm of the product. -/
theorem b184_budget (X : Matrix n n ℂ) :
    Eminus X + Eplus X = 2 * ‖X‖ ^ 2 := by
  rw [Eminus_eq_half_norm_add, Eplus_eq_half_norm_sub,
    norm_sq_add, norm_sq_sub, frobenius_norm_conjTranspose]
  ring

/-- **B184 signed trace form.**  The same two books differ by
`2 Re Tr X²`, with the displayed sign (`Eminus - Eplus`). -/
theorem b184_difference (X : Matrix n n ℂ) :
    Eminus X - Eplus X = 2 * (X ^ 2).trace.re := by
  have hc : (Xᴴ * Xᴴ).trace = star ((X * X).trace) := by
    calc
      (Xᴴ * Xᴴ).trace = ((X * X)ᴴ).trace := by rw [conjTranspose_mul]
      _ = star ((X * X).trace) := trace_conjTranspose _
  have hre : (Xᴴ * Xᴴ).trace.re = (X * X).trace.re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  rw [Eminus_eq_half_norm_add, Eplus_eq_half_norm_sub,
    norm_sq_add, norm_sq_sub]
  rw [hre]
  simp only [pow_two]
  ring

end B184



section GraphProduct

variable {G : SimpleGraph ι}

/-- The adjoint of `diagonal D * A` is `-A * diagonal D`. -/
theorem conjTranspose_diagonal_mul (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) :
    (diagonal D * A)ᴴ = -(A * diagonal D) := by
  have hstar : star D = D := funext (fun i => hD i)
  rw [conjTranspose_mul, hA, diagonal_conjTranspose, hstar, Matrix.neg_mul]

/-- The full trace of a block matrix: the sum of the traces of its diagonal
blocks.  This is definitionally `trace (X i i)` summed over `i`, i.e. the
ordinary trace after flattening the blocks. -/
noncomputable def blockTrace (X : Matrix ι ι (Matrix m m ℂ)) : ℂ :=
  ∑ i, (X i i).trace

@[simp] theorem blockTrace_add (X Y : Matrix ι ι (Matrix m m ℂ)) :
    blockTrace (X + Y) = blockTrace X + blockTrace Y := by
  simp [blockTrace, Matrix.add_apply, trace_add, Finset.sum_add_distrib]

@[simp] theorem blockTrace_neg (X : Matrix ι ι (Matrix m m ℂ)) :
    blockTrace (-X) = -blockTrace X := by
  simp [blockTrace, Matrix.neg_apply, trace_neg, Finset.sum_neg_distrib]

/-- Adjoint turns the full block trace into its conjugate. -/
theorem blockTrace_conjTranspose (X : Matrix ι ι (Matrix m m ℂ)) :
    blockTrace Xᴴ = star (blockTrace X) := by
  simp [blockTrace, conjTranspose_apply, Matrix.star_eq_conjTranspose,
    trace_conjTranspose, star_sum]

/-- The nested Frobenius energy is the real part of the full block Gram trace. -/
theorem block_norm_sq_eq_re_trace (X : Matrix ι ι (Matrix m m ℂ)) :
    ‖X‖ ^ 2 = (blockTrace (Xᴴ * X)).re := by
  rw [norm_sq_eq_sum]
  simp_rw [norm_sq_eq_re_trace]
  simp only [blockTrace, Matrix.mul_apply, conjTranspose_apply,
    RCLike.re_to_complex]
  simp_rw [Matrix.star_eq_conjTranspose, Matrix.trace_sum]
  rw [complex_re_sum]
  simp_rw [complex_re_sum]
  rw [Finset.sum_comm]

/-- Frobenius expansion of a sum of block matrices. -/
theorem block_norm_sq_add (X Y : Matrix ι ι (Matrix m m ℂ)) :
    ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 + 2 * (blockTrace (Xᴴ * Y)).re := by
  rw [block_norm_sq_eq_re_trace, block_norm_sq_eq_re_trace, block_norm_sq_eq_re_trace]
  have hc : blockTrace (Yᴴ * X) = star (blockTrace (Xᴴ * Y)) := by
    calc
      blockTrace (Yᴴ * X) = blockTrace ((Xᴴ * Y)ᴴ) := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
      _ = star (blockTrace (Xᴴ * Y)) := blockTrace_conjTranspose _
  have hre : (blockTrace (Yᴴ * X)).re = (blockTrace (Xᴴ * Y)).re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, blockTrace_add,
    Complex.add_re]
  rw [hre]
  ring

/-- Frobenius expansion of a difference of block matrices. -/
theorem block_norm_sq_sub (X Y : Matrix ι ι (Matrix m m ℂ)) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 - 2 * (blockTrace (Xᴴ * Y)).re := by
  have h := block_norm_sq_add X (-Y)
  simpa [sub_eq_add_neg, Matrix.mul_neg] using h

/-- Hermitian and skew-Hermitian halves of a block matrix. -/
noncomputable def blockHermPart (X : Matrix ι ι (Matrix m m ℂ)) :=
  (2 : ℝ)⁻¹ • (X + Xᴴ)
noncomputable def blockSkewPart (X : Matrix ι ι (Matrix m m ℂ)) :=
  (2 : ℝ)⁻¹ • (X - Xᴴ)

/-- The two B184 books on the full block operator, with exactly the displayed
normalization `2 ‖Herm X‖²` and `2 ‖Skew X‖²`. -/
noncomputable def blockEminus (X : Matrix ι ι (Matrix m m ℂ)) : ℝ :=
  2 * ‖blockHermPart X‖ ^ 2
noncomputable def blockEplus (X : Matrix ι ι (Matrix m m ℂ)) : ℝ :=
  2 * ‖blockSkewPart X‖ ^ 2

theorem blockEminus_eq_half_norm_add (X : Matrix ι ι (Matrix m m ℂ)) :
    blockEminus X = ‖X + Xᴴ‖ ^ 2 / 2 := by
  rw [blockEminus, blockHermPart, norm_sq_real_smul]
  have h : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
  rw [h]
  ring

theorem blockEplus_eq_half_norm_sub (X : Matrix ι ι (Matrix m m ℂ)) :
    blockEplus X = ‖X - Xᴴ‖ ^ 2 / 2 := by
  rw [blockEplus, blockSkewPart, norm_sq_real_smul]
  have h : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
  rw [h]
  ring

/-- B184's fixed budget on block operators. -/
theorem b184_block_budget (X : Matrix ι ι (Matrix m m ℂ)) :
    blockEminus X + blockEplus X = 2 * ‖X‖ ^ 2 := by
  rw [blockEminus_eq_half_norm_add, blockEplus_eq_half_norm_sub,
    block_norm_sq_add, block_norm_sq_sub, frobenius_norm_conjTranspose]
  ring

/-- B184's signed difference on block operators, using the full block trace. -/
theorem b184_block_difference (X : Matrix ι ι (Matrix m m ℂ)) :
    blockEminus X - blockEplus X = 2 * (blockTrace (X ^ 2)).re := by
  have hp : blockTrace (X ^ 2) = blockTrace (X * X) := by rw [pow_two]
  rw [hp]
  have hc : blockTrace (Xᴴ * Xᴴ) = star (blockTrace (X * X)) := by
    calc
      blockTrace (Xᴴ * Xᴴ) = blockTrace ((X * X)ᴴ) := by rw [conjTranspose_mul]
      _ = star (blockTrace (X * X)) := blockTrace_conjTranspose _
  have hre : (blockTrace (Xᴴ * Xᴴ)).re = (blockTrace (X * X)).re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  rw [blockEminus_eq_half_norm_add, blockEplus_eq_half_norm_sub,
    block_norm_sq_add, block_norm_sq_sub]
  rw [hre]
  ring

theorem blockEminus_diagonal_mul (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) :
    blockEminus (diagonal D * A) = ‖diagonal D * A - A * diagonal D‖ ^ 2 / 2 := by
  rw [blockEminus_eq_half_norm_add, conjTranspose_diagonal_mul D hD A hA,
    sub_eq_add_neg]

theorem blockEplus_diagonal_mul (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) :
    blockEplus (diagonal D * A) = ‖diagonal D * A + A * diagonal D‖ ^ 2 / 2 := by
  rw [blockEplus_eq_half_norm_sub, conjTranspose_diagonal_mul D hD A hA,
    sub_neg_eq_add]

/-- The B184 plus book is precisely the B183 opposite energy. -/
theorem blockEplus_diagonal_mul_eq_oppositeEnergy [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    blockEplus (diagonal D * A) = oppositeEnergy G A D := by
  rw [blockEplus_diagonal_mul D hD A hA.conjTranspose_eq_neg,
    ← b183_oppositeEnergy hA hD,
    square_sub_starSquare_diagonal_add D (fun i => hD i) A hA.conjTranspose_eq_neg]
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_sq_real_smul]
  norm_num
  ring

/-- Row sum of an adjacency indicator is the degree. -/
theorem sum_ite_adj (G : SimpleGraph ι) [DecidableRel G.Adj] (i : ι) (x : ℝ) :
    (∑ j, if G.Adj i j then x else 0) = (G.degree i : ℝ) * x := by
  classical
  rw [← Finset.sum_filter]
  simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

/-- The fixed product budget in the graph variables of B184. -/
theorem norm_sq_diagonal_mul_eq_sum_degree [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    (D : ι → Matrix m m ℂ) :
    ‖diagonal D * A‖ ^ 2 = ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  simp only [diagonal_mul]
  have h : ∀ i j, ‖D i * A i j‖ ^ 2 =
      if G.Adj i j then ‖D i‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rw [norm_mul_unitary _ (hA.mem_unitaryGroup i j hij)]
    · simp [hA.eq_zero_of_not_adj i j hij]
  simp_rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_ite_adj G i _

/-- **B184 in its full graph form:** the budget is both `2 ‖DA‖²` and
`2 Σᵢ deg(i) ‖Dᵢ‖²`; the difference is `2 Re Tr (DA)²`. -/
theorem b184_graph_budget_and_difference [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    (blockEminus (diagonal D * A) + blockEplus (diagonal D * A) =
        2 * ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2) ∧
      (blockEminus (diagonal D * A) + blockEplus (diagonal D * A) =
        2 * ‖diagonal D * A‖ ^ 2) ∧
      (blockEminus (diagonal D * A) - blockEplus (diagonal D * A) =
        2 * (blockTrace ((diagonal D * A) ^ 2)).re) := by
  refine ⟨?_, b184_block_budget _, b184_block_difference _⟩
  rw [b184_block_budget, norm_sq_diagonal_mul_eq_sum_degree hA]

end GraphProduct

/-- **B184 corollary.**  On a unitary connection, normality together with
Hermitian `H²` makes every vertex block with an incident edge vanish. -/
theorem b184_normal_hermitian_sq_eq_zero_on_edges
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian)
    (hnorm : IsStarNormal (diagonal D + A))
    (hsq : ((diagonal D + A) ^ 2).IsHermitian) :
    ∀ i j, G.Adj i j → D i = 0 := by
  let H : Matrix ι ι (Matrix m m ℂ) := diagonal D + A
  let X : Matrix ι ι (Matrix m m ℂ) := diagonal D * A
  let Y : Matrix ι ι (Matrix m m ℂ) := A * diagonal D
  have kill2 : ∀ Z : Matrix ι ι (Matrix m m ℂ), (2 : ℕ) • Z = 0 → Z = 0 := by
    intro Z hz
    rw [← Nat.cast_smul_eq_nsmul ℝ] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hstar : star D = D := funext (fun i => hD i)
  have hcomm : H * Hᴴ = Hᴴ * H := ((isStarNormal_iff H).1 hnorm).eq.symm
  have hself : H * Hᴴ - Hᴴ * H = (2 : ℕ) • (Y - X) := by
    dsimp [H, X, Y]
    rw [conjTranspose_add, diagonal_conjTranspose, hstar, hA.conjTranspose_eq_neg]
    noncomm_ring
  have hdiff : Y - X = 0 := by
    apply kill2
    rw [← hself, hcomm, sub_self]
  have hsquare : H ^ 2 - Hᴴ ^ 2 = 0 :=
    sub_eq_zero.2 ((isHermitian_sq_iff H).1 hsq)
  have hplus : X + Y = 0 := by
    apply kill2
    rw [show (2 : ℕ) • (X + Y) = H ^ 2 - Hᴴ ^ 2 by
      dsimp [H, X, Y]
      exact (square_sub_starSquare_diagonal_add D (fun i => hD i) A
        hA.conjTranspose_eq_neg).symm]
    exact hsquare
  have htwoX : (2 : ℝ) • X = 0 := by
    calc
      (2 : ℝ) • X = (X + Y) - (Y - X) := by module
      _ = 0 := by rw [hplus, hdiff, sub_self]
  have hX : X = 0 := (smul_eq_zero.mp htwoX).resolve_left (by norm_num)
  have hentries : ∀ i j, D i * A i j = 0 := by
    intro i j
    have h := congrFun (congrFun hX i) j
    simpa [X, diagonal_mul] using h
  intro i j hij
  calc
    D i = D i * 1 := (Matrix.mul_one _).symm
    _ = D i * (A i j * (A i j)ᴴ) := by
      rw [← star_eq_conjTranspose, (mem_unitaryGroup_iff).1
        (hA.mem_unitaryGroup i j hij)]
    _ = (D i * A i j) * (A i j)ᴴ := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hentries, Matrix.zero_mul]

-- Axiom audits for every theorem in this file.
#print axioms norm_sq_eq_sum
#print axioms complex_re_sum
#print axioms norm_sq_eq_re_trace
#print axioms norm_unitary_mul
#print axioms norm_mul_unitary
#print axioms norm_sq_real_smul
#print axioms square_sub_starSquare_diagonal_add
#print axioms diagonal_mul_add_mul_diagonal_apply
#print axioms norm_sq_square_sub_starSquare
#print axioms IsUnitaryConnection.apply_eq_neg_conjTranspose
#print axioms norm_mul_add_mul_eq_of_mem_unitaryGroup
#print axioms b183_oppositeEnergy
#print axioms IsUnitaryConnection.norm_mul_add_mul_comm
#print axioms sum_sum_ite_adj_eq_two_mul_sum_edgeFinset
#print axioms b183_oppositeEnergy_eq_sum_edgeFinset
#print axioms oppositeEnergy_eq_zero_iff
#print axioms isHermitian_sq_iff
#print axioms b183_zero_iff_isHermitian_sq
#print axioms norm_sq_add
#print axioms norm_sq_sub
#print axioms Eminus_eq_half_norm_add
#print axioms Eplus_eq_half_norm_sub
#print axioms b184_budget
#print axioms b184_difference
#print axioms conjTranspose_diagonal_mul
#print axioms blockTrace_add
#print axioms blockTrace_neg
#print axioms blockTrace_conjTranspose
#print axioms block_norm_sq_eq_re_trace
#print axioms block_norm_sq_add
#print axioms block_norm_sq_sub
#print axioms blockEminus_eq_half_norm_add
#print axioms blockEplus_eq_half_norm_sub
#print axioms b184_block_budget
#print axioms b184_block_difference
#print axioms blockEminus_diagonal_mul
#print axioms blockEplus_diagonal_mul
#print axioms blockEplus_diagonal_mul_eq_oppositeEnergy
#print axioms sum_ite_adj
#print axioms norm_sq_diagonal_mul_eq_sum_degree
#print axioms b184_graph_budget_and_difference
#print axioms b184_normal_hermitian_sq_eq_zero_on_edges

end AtlasB183B184


end

/-! ## B144 — the glued resolvent bound with constant two (proof)

Integrated from `.ultramath/smwtty35w/m10/B144.lean`. The section wrapper keeps each
file's `open`s from leaking into the next one.
-/
section


/-!
# B144: gluing two resolvent bounds

The exact card is archived in `card/B144.html`.  Its proof is the Neumann
argument below, not a Schur-complement argument.
-/

open scoped Ring ComplexConjugate
open Complex

namespace RelationalAtlas.B144

/-- Neumann perturbation of a unit, with an explicit bound on its inverse.
This is the algebraic step in the card's displayed `D - E` factorization. -/
theorem inverse_unit_sub_norm_le {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]
    (u : Rˣ) (e : R) {r q : ℝ}
    (hu : ‖(↑u⁻¹ : R)‖ ≤ r) (he : ‖e‖ ≤ q)
    (hr : 0 ≤ r) (hrq : r * q < 1) :
    ‖Ring.inverse ((u : R) - e)‖ ≤ r / (1 - r * q) := by
  let t : R := (↑u⁻¹ : R) * e
  have ht : ‖t‖ ≤ r * q := by
    calc
      ‖t‖ ≤ ‖(↑u⁻¹ : R)‖ * ‖e‖ := norm_mul_le _ _
      _ ≤ r * q := mul_le_mul hu he (norm_nonneg _) hr
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht hrq
  have hpos : 0 < 1 - r * q := sub_pos.mpr hrq
  have hgeom : ‖Ring.inverse (1 - t)‖ ≤ (1 - r * q)⁻¹ := by
    rw [← geom_series_eq_inverse t ht1]
    calc
      ‖∑' n : ℕ, t ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖t‖)⁻¹ :=
        tsum_geometric_le_of_norm_lt_one t ht1
      _ = (1 - ‖t‖)⁻¹ := by rw [norm_one]; ring
      _ ≤ (1 - r * q)⁻¹ := by
        exact inv_anti₀ hpos (sub_le_sub_left ht 1)
  let U : Rˣ := u * Units.oneSub t ht1
  have hU : (U : R) = (u : R) - e := by
    simp [U, Units.oneSub, t, mul_sub]
  rw [← hU, Ring.inverse_unit]
  change ‖(↑((Units.oneSub t ht1)⁻¹ * u⁻¹) : R)‖ ≤ _
  rw [Units.val_mul]
  calc
    ‖(↑(Units.oneSub t ht1)⁻¹ : R) * (↑u⁻¹ : R)‖
        ≤ ‖(↑(Units.oneSub t ht1)⁻¹ : R)‖ * ‖(↑u⁻¹ : R)‖ := norm_mul_le _ _
    _ = ‖Ring.inverse (1 - t)‖ * ‖(↑u⁻¹ : R)‖ := by
      rw [NormedRing.inverse_one_sub t ht1]
    _ ≤ (1 - r * q)⁻¹ * r := mul_le_mul hgeom hu (norm_nonneg _) (inv_nonneg.mpr hpos.le)
    _ = r / (1 - r * q) := by field_simp

/-! ## The actual four-block operator -/

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A continuous linear map with the four displayed rectangular blocks. -/
def blocks (T₁₁ : E →L[ℂ] E) (T₁₂ : F →L[ℂ] E)
    (T₂₁ : E →L[ℂ] F) (T₂₂ : F →L[ℂ] F) : (E × F) →L[ℂ] (E × F) :=
  (T₁₁.comp (ContinuousLinearMap.fst ℂ E F) +
    T₁₂.comp (ContinuousLinearMap.snd ℂ E F)).prod
  (T₂₁.comp (ContinuousLinearMap.fst ℂ E F) +
    T₂₂.comp (ContinuousLinearMap.snd ℂ E F))

@[simp] theorem blocks_apply (T₁₁ : E →L[ℂ] E) (T₁₂ : F →L[ℂ] E)
    (T₂₁ : E →L[ℂ] F) (T₂₂ : F →L[ℂ] F) (x : E) (y : F) :
    blocks T₁₁ T₁₂ T₂₁ T₂₂ (x, y) = (T₁₁ x + T₁₂ y, T₂₁ x + T₂₂ y) := by
  rfl

/-- `z - H`, with the identity on the underlying Hilbert space made explicit. -/
def resolventArgument (z : ℂ) (H : E →L[ℂ] E) : E →L[ℂ] E :=
  z • ContinuousLinearMap.id ℂ E - H

/-! ## The same blocks on the standard `L²` Hilbert direct sum -/

/-- The four blocks acting on `WithLp 2 (E × F)`, the orthogonal direct sum. -/
def l2Blocks (T₁₁ : E →L[ℂ] E) (T₁₂ : F →L[ℂ] E)
    (T₂₁ : E →L[ℂ] F) (T₂₂ : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
    ((blocks T₁₁ T₁₂ T₂₁ T₂₂).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap)

@[simp] theorem l2Blocks_apply (T₁₁ : E →L[ℂ] E) (T₁₂ : F →L[ℂ] E)
    (T₂₁ : E →L[ℂ] F) (T₂₂ : F →L[ℂ] F) (v : WithLp 2 (E × F)) :
    l2Blocks T₁₁ T₁₂ T₂₁ T₂₂ v = WithLp.toLp 2
      (T₁₁ v.fst + T₁₂ v.snd, T₂₁ v.fst + T₂₂ v.snd) := by
  rfl

/-- The diagonal resolvent on the `L²` direct sum. -/
def l2DiagonalResolvent (z : ℂ) (H_A : E →L[ℂ] E) (H_B : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  l2Blocks (resolventArgument z H_A) 0 0 (resolventArgument z H_B)

/-- The seam on the `L²` direct sum. -/
def l2Seam (C : F →L[ℂ] E) (Cs : E →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  l2Blocks 0 C Cs 0

/-- The card's block operator on the `L²` direct sum. -/
def l2Glued (H_A : E →L[ℂ] E) (C : F →L[ℂ] E) (Cs : E →L[ℂ] F)
    (H_B : F →L[ℂ] F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  l2Blocks H_A C Cs H_B

/-- `z-H = D-E` on the standard Hilbert direct sum. -/
theorem l2_resolvent_glued_eq_diagonal_sub_seam (z : ℂ) (H_A : E →L[ℂ] E)
    (C : F →L[ℂ] E) (Cs : E →L[ℂ] F) (H_B : F →L[ℂ] F) :
    resolventArgument z (l2Glued H_A C Cs H_B) =
      l2DiagonalResolvent z H_A H_B - l2Seam C Cs := by
  apply ContinuousLinearMap.ext
  intro v
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
  apply Prod.ext <;>
    simp [resolventArgument, l2Glued, l2DiagonalResolvent, l2Seam, sub_eq_add_neg] <;> abel

/-- Diagonal-block norm estimate on the `L²` direct sum. -/
theorem l2Blocks_diagonal_norm_le (T_A : E →L[ℂ] E) (T_B : F →L[ℂ] F) {r : ℝ}
    (hr : 0 ≤ r) (hA : ‖T_A‖ ≤ r) (hB : ‖T_B‖ ≤ r) :
    ‖l2Blocks T_A 0 0 T_B‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro v
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp ?_
  have hAx : ‖T_A v.fst‖ ≤ r * ‖v.fst‖ :=
    (T_A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hBy : ‖T_B v.snd‖ ≤ r * ‖v.snd‖ :=
    (T_B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hsAx := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr hAx
  have hsBy := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr hBy
  simp only [l2Blocks_apply, zero_apply, add_zero, zero_add]
  change ‖WithLp.toLp 2 (T_A v.fst, T_B v.snd)‖ ^ 2 ≤ (r * ‖v‖) ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change _ ≤ (r * ‖v‖) ^ 2
  calc
    ‖T_A v.fst‖ ^ 2 + ‖T_B v.snd‖ ^ 2
        ≤ (r * ‖v.fst‖) ^ 2 + (r * ‖v.snd‖) ^ 2 := add_le_add hsAx hsBy
    _ = r ^ 2 * (‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2) := by ring
    _ = r ^ 2 * ‖v‖ ^ 2 := by rw [WithLp.prod_norm_sq_eq_of_L2]
    _ = (r * ‖v‖) ^ 2 := by ring

/-- The seam norm on the `L²` direct sum requires only the two coupling norms. -/
theorem l2Seam_norm_le (C : F →L[ℂ] E) (Cs : E →L[ℂ] F) {q : ℝ}
    (hq : 0 ≤ q) (hC : ‖C‖ ≤ q) (hCs : ‖Cs‖ ≤ q) :
    ‖l2Seam C Cs‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro v
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mp ?_
  have hCy : ‖C v.snd‖ ≤ q * ‖v.snd‖ :=
    (C.le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have hCsx : ‖Cs v.fst‖ ≤ q * ‖v.fst‖ :=
    (Cs.le_opNorm _).trans (mul_le_mul_of_nonneg_right hCs (norm_nonneg _))
  have hsCy := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mpr hCy
  have hsCsx := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mpr hCsx
  simp only [l2Seam, l2Blocks_apply, zero_apply, add_zero, zero_add]
  change ‖WithLp.toLp 2 (C v.snd, Cs v.fst)‖ ^ 2 ≤ (q * ‖v‖) ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change _ ≤ (q * ‖v‖) ^ 2
  calc
    ‖C v.snd‖ ^ 2 + ‖Cs v.fst‖ ^ 2
        ≤ (q * ‖v.snd‖) ^ 2 + (q * ‖v.fst‖) ^ 2 := add_le_add hsCy hsCsx
    _ = q ^ 2 * (‖v.snd‖ ^ 2 + ‖v.fst‖ ^ 2) := by ring
    _ = q ^ 2 * ‖v‖ ^ 2 := by rw [WithLp.prod_norm_sq_eq_of_L2]; ring
    _ = (q * ‖v‖) ^ 2 := by ring

/-- Two units on the diagonal, bundled on the `L²` direct sum. -/
def l2DiagonalUnits (uA : (E →L[ℂ] E)ˣ) (uB : (F →L[ℂ] F)ˣ) :
    (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F))ˣ where
  val := l2Blocks (uA : E →L[ℂ] E) 0 0 (uB : F →L[ℂ] F)
  inv := l2Blocks (↑uA⁻¹ : E →L[ℂ] E) 0 0 (↑uB⁻¹ : F →L[ℂ] F)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro v
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    apply Prod.ext <;>
      simp [l2Blocks, blocks, ← mul_apply_eq_comp]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro v
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    apply Prod.ext <;>
      simp [l2Blocks, blocks, ← mul_apply_eq_comp]

@[simp] theorem l2DiagonalUnits_inv (uA : (E →L[ℂ] E)ˣ) (uB : (F →L[ℂ] F)ˣ) :
    (↑(l2DiagonalUnits uA uB)⁻¹ : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) =
      l2Blocks (↑uA⁻¹ : E →L[ℂ] E) 0 0 (↑uB⁻¹ : F →L[ℂ] F) := rfl

variable [CompleteSpace E] [CompleteSpace F]

/-- One-frequency form of the gluing estimate.  The two units make explicit
what the card's resolvent notation already presupposes: the inverses exist. -/
theorem l2Glued_resolvent_norm_le_of_units (z : ℂ) (H_A : E →L[ℂ] E)
    (C : F →L[ℂ] E) (Cs : E →L[ℂ] F) (H_B : F →L[ℂ] F)
    (uA : (E →L[ℂ] E)ˣ) (uB : (F →L[ℂ] F)ˣ)
    (huA : (uA : E →L[ℂ] E) = resolventArgument z H_A)
    (huB : (uB : F →L[ℂ] F) = resolventArgument z H_B)
    {K δ : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hRA : ‖Ring.inverse (resolventArgument z H_A)‖ ≤ K / δ)
    (hRB : ‖Ring.inverse (resolventArgument z H_B)‖ ≤ K / δ)
    (hC : ‖C‖ ≤ δ / (2 * K)) (hCs : ‖Cs‖ ≤ δ / (2 * K)) :
    ‖Ring.inverse (resolventArgument z (l2Glued H_A C Cs H_B))‖ ≤ 2 * K / δ := by
  by_cases hV : Subsingleton (WithLp 2 (E × F))
  · letI := hV
    have hzero : resolventArgument z (l2Glued H_A C Cs H_B) = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp only [Ring.inverse_zero, norm_zero]
    positivity
  · letI : Nontrivial (WithLp 2 (E × F)) := not_subsingleton_iff_nontrivial.mp hV
    letI : ContinuousSMul ℂ (WithLp 2 (E × F)) := IsBoundedSMul.continuousSMul
    letI : CompleteSpace (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) :=
      ContinuousLinearMap.instCompleteSpace
    let u : (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F))ˣ := l2DiagonalUnits uA uB
    have hu : ‖(↑u⁻¹ : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F))‖ ≤ K / δ := by
      dsimp [u]
      apply l2Blocks_diagonal_norm_le _ _ (by positivity)
      · rw [← Ring.inverse_unit uA, huA]
        exact hRA
      · rw [← Ring.inverse_unit uB, huB]
        exact hRB
    have huval : (u : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) =
        l2DiagonalResolvent z H_A H_B := by
      change l2Blocks (uA : E →L[ℂ] E) 0 0 (uB : F →L[ℂ] F) = _
      simp only [l2DiagonalResolvent, huA, huB]
    have hE : ‖l2Seam C Cs‖ ≤ δ / (2 * K) :=
      l2Seam_norm_le C Cs (by positivity) hC hCs
    have hprod : (K / δ) * (δ / (2 * K)) = 1 / 2 := by
      field_simp
    have hprod_lt : (K / δ) * (δ / (2 * K)) < 1 := by rw [hprod]; norm_num
    have hcore := inverse_unit_sub_norm_le u (l2Seam C Cs) hu hE
      (show 0 ≤ K / δ by positivity) hprod_lt
    rw [huval, ← l2_resolvent_glued_eq_diagonal_sub_seam] at hcore
    exact hcore.trans_eq (by rw [hprod]; ring)

/-- The glued resolvent bound on the card's entire half-plane. -/
theorem l2Glued_resolvent_bound (H_A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (Cs : E →L[ℂ] F) (H_B : F →L[ℂ] F) {K δ : ℝ}
    (hδ : 0 < δ) (hK : 0 < K)
    (hunitA : ∀ z : ℂ, δ ≤ z.re → IsUnit (resolventArgument z H_A))
    (hunitB : ∀ z : ℂ, δ ≤ z.re → IsUnit (resolventArgument z H_B))
    (hRA : ∀ z : ℂ, δ ≤ z.re → ‖Ring.inverse (resolventArgument z H_A)‖ ≤ K / δ)
    (hRB : ∀ z : ℂ, δ ≤ z.re → ‖Ring.inverse (resolventArgument z H_B)‖ ≤ K / δ)
    (hC : ‖C‖ ≤ δ / (2 * K)) (hCs : ‖Cs‖ ≤ δ / (2 * K)) :
    ∀ z : ℂ, δ ≤ z.re →
      ‖Ring.inverse (resolventArgument z (l2Glued H_A C Cs H_B))‖ ≤ 2 * K / δ := by
  intro z hz
  let uA := (hunitA z hz).unit
  let uB := (hunitB z hz).unit
  exact l2Glued_resolvent_norm_le_of_units z H_A C Cs H_B uA uB
    (hunitA z hz).unit_spec (hunitB z hz).unit_spec hδ hK (hRA z hz) (hRB z hz) hC hCs

/-- **B144 exactly as displayed**, on a Hilbert `L²` direct sum.  The lower
left block is the adjoint `C*`, so its norm bound follows from that of `C`. -/
theorem B144_glued_resolvent_bound (H_A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (H_B : F →L[ℂ] F) {K δ : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hunitA : ∀ z : ℂ, δ ≤ z.re → IsUnit (resolventArgument z H_A))
    (hunitB : ∀ z : ℂ, δ ≤ z.re → IsUnit (resolventArgument z H_B))
    (hRA : ∀ z : ℂ, δ ≤ z.re → ‖Ring.inverse (resolventArgument z H_A)‖ ≤ K / δ)
    (hRB : ∀ z : ℂ, δ ≤ z.re → ‖Ring.inverse (resolventArgument z H_B)‖ ≤ K / δ)
    (hC : ‖C‖ ≤ δ / (2 * K)) :
    ∀ z : ℂ, δ ≤ z.re →
      ‖Ring.inverse (resolventArgument z
        (l2Glued H_A C (ContinuousLinearMap.adjoint C) H_B))‖ ≤ 2 * K / δ := by
  apply l2Glued_resolvent_bound H_A C (ContinuousLinearMap.adjoint C) H_B
    hδ hK hunitA hunitB hRA hRB hC
  simpa only [ContinuousLinearMap.adjoint.norm_map] using hC

end RelationalAtlas.B144

#print axioms RelationalAtlas.B144.inverse_unit_sub_norm_le
#print axioms RelationalAtlas.B144.blocks_apply
#print axioms RelationalAtlas.B144.l2Blocks_apply
#print axioms RelationalAtlas.B144.l2_resolvent_glued_eq_diagonal_sub_seam
#print axioms RelationalAtlas.B144.l2Blocks_diagonal_norm_le
#print axioms RelationalAtlas.B144.l2Seam_norm_le
#print axioms RelationalAtlas.B144.l2DiagonalUnits
#print axioms RelationalAtlas.B144.l2DiagonalUnits_inv
#print axioms RelationalAtlas.B144.l2Glued_resolvent_norm_le_of_units
#print axioms RelationalAtlas.B144.l2Glued_resolvent_bound
#print axioms RelationalAtlas.B144.B144_glued_resolvent_bound


end
