/-
Tenth batch: a straw-man side and a breaker side, a role swap, and a referee pass.

The seven cards here were the last still graded `theorem` without a local kernel. Each
card got two or more members with opposite orders of work — one built the weakest reading
a careless reader would call the card and refuted that first, the other attacked the
card's own claim first — and each then swapped roles. The point was to separate a real
counterexample from a real computation against an invented reading, and it worked in both
directions: one member's `REFUTED` was withdrawn when the document it had read turned out
to be the 93-card edition rather than the pinned v7 card, and another member's refutation
survived a referee re-derivation and is recorded as genuine.

Each contribution is reproduced verbatim except its import line and is wrapped in its own
`section ... end`, so that no file-level `open` leaks into the next. Nothing in the earlier
modules is modified.
-/
import Mathlib


/-! ## B9 — gauge dependence of the closed-loop winding, and fixed-loop integrality

Integrated from `.ultramath/smwwdl7d5/m2/B9.lean`.
-/

section
/-!
# B9 — fixed-loop winding, periodic-gauge covariance, and an open-path warning

The strong faithful counterexample uses a constant two-band Hermitian family
`loopH t = diag(1,-1)`. Its upper eigenvalue is `+1`, its lower eigenvalue is
`-1`, and the gap is `2` everywhere on the closed parameter loop. The two
eigenvectors `upper` and `gaugedUpper` represent the same eigenline and differ
by the periodic unit-modulus gauge `exp(2π i t)`. Their nonvanishing first
components have normalized unwrapped-phase changes `0` and `1`, respectively.

This directly contradicts the Closed field's assertion that the value on a
closed loop is not gauge-dependent. It does not refute the positive assertion
that a *fixed* continuous nowhere-zero complex loop has integer winding; that
assertion is proved separately below as `fixed_loop_integer_winding`.

The deliberately weak reading drops the word "closed" and treats every phase
change as an integer winding. `openPhi` is an exact half-turn counterexample
to that invented reading only.
-/

open scoped ComplexConjugate

namespace AtlasB9

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- A normalized unwrapped-phase change. For a closed nowhere-zero loop this
is its winding; on an open path it need not be an integer. -/
def normalizedPhaseChange (θ : ℝ → ℝ) : ℝ :=
  (θ 1 - θ 0) / (2 * Real.pi)

/-- The displayed integral `(1/2π) ∫ dθ`, parameterized on `[0,1]`.
For an unwrapped argument `θ` of `Φ`, this is `(1/2π) ∮ d arg Φ`. -/
def normalizedPhaseIntegral (θ : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..1, deriv θ t

/-- `θ` is an unwrapped argument of `Φ`. -/
def IsPhaseLift (Φ : ℝ → ℂ) (θ : ℝ → ℝ) : Prop :=
  ∀ t, Φ t = ‖Φ t‖ * Complex.exp (θ t * Complex.I)

/-- The constant gapped Hermitian two-band matrix. -/
def D : Mat2 := !![1, 0; 0, -1]

/-- The constant family used in the faithful counterexample. -/
def loopH (_t : ℝ) : Mat2 := D

/-- Upper and lower algebraic eigenvectors of `D`. -/
def upper : Fin 2 → ℂ := ![1, 0]
def lower : Fin 2 → ℂ := ![0, 1]

/-- One full unit-modulus periodic gauge transformation. -/
def phase (t : ℝ) : ℝ := 2 * Real.pi * t
def gauge (t : ℝ) : ℂ := Complex.exp (phase t * Complex.I)

/-- The same upper eigenline, in the gauged frame. -/
def gaugedUpper (t : ℝ) : Fin 2 → ℂ := gauge t • upper

/-- The nonvanishing components whose arguments are being tracked. -/
def basePhi (_t : ℝ) : ℂ := 1
def gaugedPhi (t : ℝ) : ℂ := gauge t

/-- Their explicit unwrapped arguments. -/
def baseTheta (_t : ℝ) : ℝ := 0
def gaugedTheta (t : ℝ) : ℝ := phase t

lemma D_hermitian : D.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, Matrix.conjTranspose_apply]

lemma D_upper : D.mulVec upper = upper := by
  ext i
  fin_cases i <;> simp [D, upper, Matrix.mulVec]

lemma D_lower : D.mulVec lower = -lower := by
  ext i
  fin_cases i <;> simp [D, lower, Matrix.mulVec]

lemma D_trace : D.trace = 0 := by
  simp [D, Matrix.trace_fin_two]

lemma D_det : D.det = -1 := by
  simp [D, Matrix.det_fin_two]

/-- The two displayed eigenvalues are real and separated by `2`. -/
lemma spectral_gap : (1 : ℝ) - (-1) = 2 := by norm_num

lemma loopH_hermitian (t : ℝ) : (loopH t).IsHermitian := D_hermitian
lemma loopH_upper (t : ℝ) : (loopH t).mulVec upper = upper := D_upper
lemma loopH_lower (t : ℝ) : (loopH t).mulVec lower = -lower := D_lower
lemma loopH_continuous : Continuous loopH := continuous_const
lemma loopH_closed : loopH 1 = loopH 0 := rfl

lemma gauge_ne_zero (t : ℝ) : gauge t ≠ 0 := Complex.exp_ne_zero _

@[simp] lemma gauge_norm (t : ℝ) : ‖gauge t‖ = 1 := by
  simp [gauge, phase, Complex.norm_exp]

lemma gauge_zero : gauge 0 = 1 := by
  simp [gauge, phase]

lemma gauge_one : gauge 1 = 1 := by
  simpa [gauge, phase] using Complex.exp_two_pi_mul_I

lemma gauge_closed : gauge 1 = gauge 0 := by
  rw [gauge_one, gauge_zero]

lemma gaugedUpper_eqgauge (t : ℝ) : gaugedUpper t = gauge t • upper := rfl

lemma loopH_gaugedUpper (t : ℝ) :
    (loopH t).mulVec (gaugedUpper t) = gaugedUpper t := by
  rw [gaugedUpper, loopH, Matrix.mulVec_smul, D_upper]

lemma upper_ne_zero : upper ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [upper] at h0

lemma gaugedUpper_ne_zero (t : ℝ) : gaugedUpper t ≠ 0 := by
  exact smul_ne_zero (gauge_ne_zero t) upper_ne_zero

lemma gaugedUpper_closed : gaugedUpper 1 = gaugedUpper 0 := by
  simp [gaugedUpper, gauge_closed]

lemma basePhi_component (t : ℝ) : basePhi t = upper 0 := by
  simp [basePhi, upper]

lemma gaugedPhi_component (t : ℝ) : gaugedPhi t = gaugedUpper t 0 := by
  simp [gaugedPhi, gaugedUpper, upper]

lemma basePhi_ne_zero (t : ℝ) : basePhi t ≠ 0 := by simp [basePhi]
lemma gaugedPhi_ne_zero (t : ℝ) : gaugedPhi t ≠ 0 := gauge_ne_zero t
lemma basePhi_closed : basePhi 1 = basePhi 0 := rfl
lemma gaugedPhi_closed : gaugedPhi 1 = gaugedPhi 0 := gauge_closed

lemma basePhi_continuous : Continuous basePhi := continuous_const
lemma gaugedPhi_continuous : Continuous gaugedPhi := by
  unfold gaugedPhi gauge phase
  fun_prop

lemma base_lift : IsPhaseLift basePhi baseTheta := by
  intro t
  simp [IsPhaseLift, basePhi, baseTheta]

lemma gauged_lift : IsPhaseLift gaugedPhi gaugedTheta := by
  intro t
  simp [IsPhaseLift, gaugedPhi, gaugedTheta, gauge]

lemma base_winding_zero : normalizedPhaseChange baseTheta = 0 := by
  simp [normalizedPhaseChange, baseTheta]

lemma gauged_winding_one : normalizedPhaseChange gaugedTheta = 1 := by
  simp [normalizedPhaseChange, gaugedTheta, phase]

lemma base_winding_integral_zero : normalizedPhaseIntegral baseTheta = 0 := by
  have hd : (fun t => deriv baseTheta t) = fun _t => (0 : ℝ) := by
    funext t
    change deriv (fun _x : ℝ => (0 : ℝ)) t = 0
    simp
  rw [normalizedPhaseIntegral, hd]
  simp

lemma gauged_winding_integral_one : normalizedPhaseIntegral gaugedTheta = 1 := by
  have hd : (fun t => deriv gaugedTheta t) = fun _t => 2 * Real.pi := by
    funext t
    change deriv (fun x : ℝ => (2 * Real.pi) * x) t = 2 * Real.pi
    simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).deriv
  rw [normalizedPhaseIntegral, hd]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  field_simp [Real.pi_ne_zero]

lemma the_two_closed_loop_windings_differ :
    normalizedPhaseIntegral baseTheta ≠ normalizedPhaseIntegral gaugedTheta := by
  rw [base_winding_integral_zero, gauged_winding_integral_one]
  norm_num

/-- **Faithful B9 counterexample.** On one and the same closed gapped
Hermitian two-band family, two eigenline representatives differ by a closed
unit-modulus gauge. Both tracked components are continuous, nowhere-zero and
closed, yet their displayed normalized phase integrals have values `0` and `1`.

The gap is witnessed by `D_lower`, `D_upper` and `spectral_gap`; this theorem
bundles the gauge and winding part of that witness. -/
theorem closed_loop_winding_is_gauge_dependent :
    (∀ t, (loopH t).IsHermitian) ∧
    (∀ t, (loopH t).mulVec upper = upper) ∧
    (∀ t, (loopH t).mulVec (gaugedUpper t) = gaugedUpper t) ∧
    (∀ t, gaugedUpper t = gauge t • upper) ∧
    (∀ t, ‖gauge t‖ = 1) ∧
    gaugedUpper 1 = gaugedUpper 0 ∧
    IsPhaseLift basePhi baseTheta ∧
    IsPhaseLift gaugedPhi gaugedTheta ∧
    basePhi 1 = basePhi 0 ∧ gaugedPhi 1 = gaugedPhi 0 ∧
    normalizedPhaseChange baseTheta = 0 ∧
    normalizedPhaseChange gaugedTheta = 1 ∧
    normalizedPhaseIntegral baseTheta = 0 ∧
    normalizedPhaseIntegral gaugedTheta = 1 := by
  exact ⟨loopH_hermitian, loopH_upper, loopH_gaugedUpper,
    gaugedUpper_eqgauge, gauge_norm, gaugedUpper_closed,
    base_lift, gauged_lift, basePhi_closed, gaugedPhi_closed,
    base_winding_zero, gauged_winding_one,
    base_winding_integral_zero, gauged_winding_integral_one⟩

/-- A nonzero continuous complex loop has a continuous unwrapped argument
whose normalized endpoint change is an integer. This concerns a fixed `Φ`,
not invariance under changing `Φ` by an integer-winding gauge. -/
theorem fixed_loop_integer_winding (Φ : ℝ → ℂ) (hΦ : Continuous Φ)
    (hΦ0 : ∀ t, Φ t ≠ 0) (hloop : Φ 1 = Φ 0) :
    ∃ θ : C(ℝ, ℝ), ∃ n : ℤ,
      IsPhaseLift Φ θ ∧
      normalizedPhaseChange θ = n := by
  let u : ℝ → ℂ := fun t => Φ t / ‖Φ t‖
  have hu : Continuous u := by
    exact hΦ.div (Complex.continuous_ofReal.comp hΦ.norm)
      (fun t => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hΦ0 t)))
  let γ : C(ℝ, Circle) :=
    ⟨fun t => ⟨u t, by
      simp [Submonoid.unitSphere, u, norm_ne_zero_iff.mpr (hΦ0 t)]⟩, by
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
    change Φ 1 / (‖Φ 1‖ : ℂ) = Φ 0 / (‖Φ 0‖ : ℂ)
    rw [hloop]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hcircle
  refine ⟨θ, n, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun z : Circle => (z : ℂ)) (hlift t)
    have ht' : Complex.exp (θ t * Complex.I) = Φ t / ‖Φ t‖ := by
      change Complex.exp (θ t * Complex.I) = Φ t / ‖Φ t‖ at ht
      exact ht
    calc
      Φ t = (‖Φ t‖ : ℂ) * (Φ t / ‖Φ t‖) := by
        field_simp [norm_ne_zero_iff.mpr (hΦ0 t)]
      _ = ‖Φ t‖ * Complex.exp (θ t * Complex.I) := by rw [← ht']
  · rw [normalizedPhaseChange, hn]
    field_simp [Real.pi_ne_zero]
    ring

/-- The weak-reading model: a nonvanishing smooth phase on an open path. -/
def openTheta (t : ℝ) : ℝ := Real.pi * t
def openPhi (t : ℝ) : ℂ := Complex.exp (openTheta t * Complex.I)

lemma openPhi_continuous : Continuous openPhi := by
  unfold openPhi openTheta
  fun_prop

lemma openPhi_ne_zero (t : ℝ) : openPhi t ≠ 0 := Complex.exp_ne_zero _
lemma openPhi_lift : IsPhaseLift openPhi openTheta := by
  intro t
  simp [IsPhaseLift, openPhi, openTheta, Complex.norm_exp]

lemma openPhi_zero : openPhi 0 = 1 := by simp [openPhi, openTheta]
lemma openPhi_one : openPhi 1 = -1 := by
  simpa [openPhi, openTheta] using Complex.exp_pi_mul_I
lemma openPhi_not_closed : openPhi 1 ≠ openPhi 0 := by
  rw [openPhi_one, openPhi_zero]
  norm_num

lemma open_phase_change_one_half :
    normalizedPhaseChange openTheta = (1 / 2 : ℝ) := by
  calc
    normalizedPhaseChange openTheta =
        (Real.pi * 1 - Real.pi * 0) / (2 * Real.pi) := rfl
    _ = Real.pi / (2 * Real.pi) := by ring
    _ = (1 / 2 : ℝ) := by field_simp [Real.pi_ne_zero]

lemma open_phase_integral_one_half :
    normalizedPhaseIntegral openTheta = (1 / 2 : ℝ) := by
  have hd : (fun t => deriv openTheta t) = fun _t => Real.pi := by
    funext t
    change deriv (fun x : ℝ => Real.pi * x) t = Real.pi
    simpa using ((hasDerivAt_id t).const_mul Real.pi).deriv
  rw [normalizedPhaseIntegral, hd]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  field_simp [Real.pi_ne_zero]

/-- The half-turn is not an integer, so dropping closure breaks integrality. -/
lemma open_phase_change_not_integer :
    ¬ ∃ n : ℤ, normalizedPhaseChange openTheta = (n : ℝ) := by
  rintro ⟨n, hn⟩
  rw [open_phase_change_one_half] at hn
  have hreal : (2 : ℝ) * (n : ℝ) = 1 := by linarith
  have hint : 2 * n = 1 := by exact_mod_cast hreal
  omega

end
end AtlasB9

#print axioms AtlasB9.D_hermitian
#print axioms AtlasB9.D_upper
#print axioms AtlasB9.D_lower
#print axioms AtlasB9.D_trace
#print axioms AtlasB9.D_det
#print axioms AtlasB9.spectral_gap
#print axioms AtlasB9.gauge_norm
#print axioms AtlasB9.gauge_closed
#print axioms AtlasB9.loopH_gaugedUpper
#print axioms AtlasB9.gaugedUpper_closed
#print axioms AtlasB9.basePhi_component
#print axioms AtlasB9.gaugedPhi_component
#print axioms AtlasB9.basePhi_continuous
#print axioms AtlasB9.gaugedPhi_continuous
#print axioms AtlasB9.basePhi_ne_zero
#print axioms AtlasB9.gaugedPhi_ne_zero
#print axioms AtlasB9.base_winding_integral_zero
#print axioms AtlasB9.gauged_winding_integral_one
#print axioms AtlasB9.the_two_closed_loop_windings_differ
#print axioms AtlasB9.closed_loop_winding_is_gauge_dependent
#print axioms AtlasB9.fixed_loop_integer_winding
#print axioms AtlasB9.openPhi_lift
#print axioms AtlasB9.openPhi_not_closed
#print axioms AtlasB9.open_phase_change_one_half
#print axioms AtlasB9.open_phase_integral_one_half
#print axioms AtlasB9.open_phase_change_not_integer
end


/-! ## B9 — a non-constant two-band witness, and invariance under zero-winding gauges

Integrated from `.ultramath/smwwdl7d5/m1/B9Comparison.lean`.
-/

section
open scoped Real
open Matrix

namespace AtlasB9Comparison

/-- The winding computed from a continuous angular lift on `[0,2π]`.
This is a real-valued normalization; in the closed nonvanishing examples below
its values are integers. -/
noncomputable def liftWinding (α : ℝ → ℝ) : ℝ :=
  (α (2 * Real.pi) - α 0) / (2 * Real.pi)

/-- The displayed normalization for a differentiable angular lift, parameterized
on the explicit interval `[0,2π]`. -/
noncomputable def normalizedPhaseIntegral (α : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in 0..2 * Real.pi, deriv α θ

/-- The closed unit-circle phase represented by an angular lift. -/
noncomputable def phaseLoop (α : ℝ → ℝ) (θ : ℝ) : ℂ :=
  Complex.exp ((α θ : ℂ) * Complex.I)

/-- The explicit phase `exp(iθ)`. -/
def identityLift : ℝ → ℝ := fun θ => θ

/-- A periodic large gauge whose angular lift is `-θ`. -/
def inverseGaugeLift : ℝ → ℝ := fun θ => -θ

@[simp] theorem phaseLoop_ne_zero (α : ℝ → ℝ) (θ : ℝ) : phaseLoop α θ ≠ 0 := by
  exact Complex.exp_ne_zero _

@[simp] theorem liftWinding_zero : liftWinding (fun _ => 0) = 0 := by
  simp [liftWinding]

theorem liftWinding_add (α β : ℝ → ℝ) :
    liftWinding (fun θ => α θ + β θ) = liftWinding α + liftWinding β := by
  unfold liftWinding
  field_simp [Real.pi_ne_zero]
  ring

@[simp] theorem liftWinding_identity : liftWinding identityLift = 1 := by
  simp [liftWinding, identityLift, Real.pi_ne_zero]

@[simp] theorem liftWinding_inverseGauge : liftWinding inverseGaugeLift = -1 := by
  simp [liftWinding, inverseGaugeLift, Real.pi_ne_zero]

/-- The explicit phase and inverse-gauge loops are differentiable (and hence
admissible for the displayed angular differential, not just endpoint algebra). -/
theorem identityPhase_differentiable : Differentiable ℝ (phaseLoop identityLift) := by
  unfold phaseLoop identityLift
  fun_prop

theorem inverseGauge_differentiable : Differentiable ℝ (phaseLoop inverseGaugeLift) := by
  unfold phaseLoop inverseGaugeLift
  fun_prop

/-- Both the original phase and the inverse gauge close as complex-valued loops. -/
theorem identityLoop_closed :
    phaseLoop identityLift (2 * Real.pi) = phaseLoop identityLift 0 := by
  simp only [phaseLoop, identityLift, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * Real.pi * Complex.I by ring,
    Complex.exp_two_pi_mul_I]

theorem inverseGauge_closed :
    phaseLoop inverseGaugeLift (2 * Real.pi) = phaseLoop inverseGaugeLift 0 := by
  simp only [phaseLoop, inverseGaugeLift, Complex.ofReal_zero, neg_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [show (-((2 : ℂ) * (Real.pi : ℂ))) * Complex.I =
      -(2 * Real.pi * Complex.I) by ring,
    Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- The gauged phase is still the same closed, nonvanishing kind of loop. -/
theorem gaugedLoop_closed :
    (phaseLoop identityLift * phaseLoop inverseGaugeLift) (2 * Real.pi) =
      (phaseLoop identityLift * phaseLoop inverseGaugeLift) 0 := by
  rw [Pi.mul_apply, Pi.mul_apply, identityLoop_closed, inverseGauge_closed]

/-- INVENTED READING ONLY: this refutes the careless assertion that equality of
principal endpoint phases makes the winding zero.  It does not refute the card's
integral of the differential of a continuously unwrapped argument. -/
theorem weak_closed_endpoint_reading_refuted :
    phaseLoop identityLift (2 * Real.pi) = phaseLoop identityLift 0 ∧
      liftWinding identityLift ≠ 0 := by
  exact ⟨identityLoop_closed, by simp⟩

/-- The card's displayed integral evaluates to `1` for the phase `exp(iθ)`. -/
theorem normalizedPhaseIntegral_identity : normalizedPhaseIntegral identityLift = 1 := by
  have hderiv : deriv identityLift = fun _ => 1 := by
    funext θ
    change deriv (fun x : ℝ => x) θ = 1
    simp
  rw [normalizedPhaseIntegral, hderiv]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  field_simp [Real.pi_ne_zero]

/-- The same integral evaluates to `0` after the periodic inverse gauge. -/
theorem normalizedPhaseIntegral_gauged :
    normalizedPhaseIntegral (fun θ => identityLift θ + inverseGaugeLift θ) = 0 := by
  have h : (fun θ => identityLift θ + inverseGaugeLift θ) = (fun _ => 0) := by
    funext θ
    simp [identityLift, inverseGaugeLift]
  rw [h]
  simp [normalizedPhaseIntegral]

/-- Literal displayed-form counterexample to unrestricted gauge invariance. -/
theorem periodic_gauge_changes_displayed_integral :
    normalizedPhaseIntegral identityLift = 1 ∧
      normalizedPhaseIntegral (fun θ => identityLift θ + inverseGaugeLift θ) = 0 :=
  ⟨normalizedPhaseIntegral_identity, normalizedPhaseIntegral_gauged⟩

/-- A literal counterexample to unrestricted gauge invariance of the integer
winding: the original winding is `1`, the gauged winding is `0`. -/
theorem periodic_gauge_changes_winding :
    liftWinding (fun θ => identityLift θ + inverseGaugeLift θ) = 0 ∧
      liftWinding identityLift = 1 := by
  constructor
  · rw [liftWinding_add, liftWinding_identity, liftWinding_inverseGauge]
    norm_num
  exact liftWinding_identity

/-- If `Φ` is instead explicitly defined as the fixed-component ratio `z/1`,
common gauge cancels; the card does not state this alternative definition. -/
theorem common_gauge_preserves_relative_phase (g z : ℂ) (hg : g ≠ 0) :
    (g * z) / (g * 1) = z / 1 := by
  field_simp

/-- Zero-winding gauges are exactly the repaired invariance case used below. -/
theorem liftWinding_gauge_add (α β : ℝ → ℝ) (hβ : liftWinding β = 0) :
    liftWinding (fun θ => α θ + β θ) = liftWinding α := by
  rw [liftWinding_add, hβ, add_zero]

/-- Every exponential phase has unit modulus in the multiplicative form used
for the two-band eigenvectors. -/
theorem phaseLoop_unit (α : ℝ → ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (phaseLoop α θ) * phaseLoop α θ = 1 := by
  simp [phaseLoop, ← Complex.exp_conj, ← Complex.exp_add]

/-- Multiplying phase loops adds their angular lifts. -/
theorem phaseLoop_add (α β : ℝ → ℝ) (θ : ℝ) :
    phaseLoop (fun t => α t + β t) θ = phaseLoop α θ * phaseLoop β θ := by
  simp [phaseLoop, Complex.exp_add, add_mul]

/-- The off-diagonal (chiral) two-band operator. -/
def chiral (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, z; (starRingEnd ℂ) z, 0]

/-- The chiral family is Hermitian, so it is a genuine two-band Hermitian model. -/
theorem chiral_isHermitian (z : ℂ) : (chiral z).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [chiral]

/-- The defect in the two real off-diagonal coordinates is exactly `z=0`. -/
theorem chiral_zero_matrix_iff (z : ℂ) : chiral z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simpa [chiral] using h01
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiral]

/-- A finite determinant identity; at unit modulus it is constantly `-1`. -/
theorem chiral_det (z : ℂ) : (chiral z).det = -((starRingEnd ℂ) z * z) := by
  simp [chiral, Matrix.det_fin_two]
  ring

/-- The positive band is always `+1` when `|z|=1`, with explicit eigenvector. -/
theorem chiral_positive_band (z : ℂ) (hz : (starRingEnd ℂ) z * z = 1) :
    chiral z *ᵥ ![z, 1] = ![z, 1] := by
  ext i
  fin_cases i <;> simp [chiral, Matrix.mulVec, dotProduct, hz]

/-- The negative band is always `-1` when `|z|=1`, with explicit eigenvector. -/
theorem chiral_negative_band (z : ℂ) (hz : (starRingEnd ℂ) z * z = 1) :
    chiral z *ᵥ ![-z, 1] = -![-z, 1] := by
  ext i
  fin_cases i <;> simp [chiral, Matrix.mulVec, dotProduct, hz]

/-- The selected positive-band eigenvector, with second component fixed to `1`. -/
noncomputable def upperBandVec (α : ℝ → ℝ) (θ : ℝ) : Fin 2 → ℂ :=
  ![phaseLoop α θ, 1]

/-- A common unit-modulus gauge applied to the whole eigenvector. -/
noncomputable def gaugedUpperBandVec (α β : ℝ → ℝ) (θ : ℝ) : Fin 2 → ℂ :=
  phaseLoop β θ • upperBandVec α θ

theorem upperBandVec_eigen (α : ℝ → ℝ) (θ : ℝ) :
    chiral (phaseLoop α θ) *ᵥ upperBandVec α θ = upperBandVec α θ :=
  chiral_positive_band _ (phaseLoop_unit α θ)

theorem gaugedUpperBandVec_eigen (α β : ℝ → ℝ) (θ : ℝ) :
    chiral (phaseLoop α θ) *ᵥ gaugedUpperBandVec α β θ = gaugedUpperBandVec α β θ := by
  unfold gaugedUpperBandVec
  rw [Matrix.mulVec_smul, upperBandVec_eigen]

/-- Both representatives are closed on the explicit `2π` loop. -/
theorem upperBandVec_closed :
    upperBandVec identityLift (2 * Real.pi) = upperBandVec identityLift 0 := by
  simp only [upperBandVec, identityLoop_closed]

theorem gaugedUpperBandVec_closed :
    gaugedUpperBandVec identityLift inverseGaugeLift (2 * Real.pi) =
      gaugedUpperBandVec identityLift inverseGaugeLift 0 := by
  unfold gaugedUpperBandVec
  rw [inverseGauge_closed, upperBandVec_closed]

/-- The same selected component has winding `1` in one representative and `0`
in the other, although both are nowhere-zero closed eigenvector phases. -/
theorem upperBandVec_selected_phase (θ : ℝ) :
    upperBandVec identityLift θ 0 = phaseLoop identityLift θ := by
  rfl

theorem gaugedUpperBandVec_selected_phase (θ : ℝ) :
    gaugedUpperBandVec identityLift inverseGaugeLift θ 0 =
      phaseLoop (fun t => identityLift t + inverseGaugeLift t) θ := by
  simp [gaugedUpperBandVec, upperBandVec, phaseLoop_add, mul_comm]

/-- Every eigenvalue of the unit-modulus chiral model is constrained to `±1`.
Thus no eigenvalue can pass through any fixed level strictly between them. -/
theorem chiral_eigenvalue_sq (z μ : ℂ) (hz : (starRingEnd ℂ) z * z = 1)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) (heig : chiral z *ᵥ v = μ • v) : μ ^ 2 = 1 := by
  have hshift : (chiral z - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, heig, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdet : (chiral z - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hshift⟩
  have hformula : (chiral z - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      μ ^ 2 - (starRingEnd ℂ) z * z := by
    simp [chiral, Matrix.det_fin_two]
    ring
  rw [hformula, hz] at hdet
  exact sub_eq_zero.mp hdet

/-- The two possible eigenvalues on the unit-modulus circuit are exactly `±1`. -/
theorem chiral_eigenvalue_eq_pm (z μ : ℂ) (hz : (starRingEnd ℂ) z * z = 1)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) (heig : chiral z *ᵥ v = μ • v) :
    μ = 1 ∨ μ = -1 := by
  have hs := chiral_eigenvalue_sq z μ hz v hv heig
  have hfactor : (μ - 1) * (μ + 1) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

/-- In particular zero is never an eigenvalue, so there is no zero-cut spectral
flow anywhere on this family. -/
theorem chiral_no_zero_mode (z : ℂ) (hz : (starRingEnd ℂ) z * z = 1)
    (v : Fin 2 → ℂ) (hv : chiral z *ᵥ v = 0) : v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero _ hv
  rw [chiral_det, hz]
  norm_num

/-- The concrete loop `H(exp(iα(θ)))` is gapped at zero for every angle. -/
theorem phaseLoop_chiral_no_zero_mode (α : ℝ → ℝ) (θ : ℝ) (v : Fin 2 → ℂ)
    (hv : chiral (phaseLoop α θ) *ᵥ v = 0) : v = 0 :=
  chiral_no_zero_mode _ (phaseLoop_unit α θ) v hv

/-- The decisive comparison kernel: the phase circuit winds once while the
associated two-band family remains gapped at zero and its eigenvalues are
constrained to the two constant levels `±1`. -/
theorem chiral_comparison_kernel :
    (phaseLoop identityLift (2 * Real.pi) = phaseLoop identityLift 0) ∧
      liftWinding identityLift = 1 ∧
      (∀ θ v, chiral (phaseLoop identityLift θ) *ᵥ v = 0 → v = 0) ∧
      (∀ θ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
        chiral (phaseLoop identityLift θ) *ᵥ v = μ • v → μ = 1 ∨ μ = -1) := by
  refine ⟨identityLoop_closed, liftWinding_identity, ?_, ?_⟩
  · intro θ v hv
    exact phaseLoop_chiral_no_zero_mode identityLift θ v hv
  · intro θ μ v hv heig
    exact chiral_eigenvalue_eq_pm (phaseLoop identityLift θ) μ
      (phaseLoop_unit identityLift θ) v hv heig

end AtlasB9Comparison

#print axioms AtlasB9Comparison.liftWinding
#print axioms AtlasB9Comparison.normalizedPhaseIntegral
#print axioms AtlasB9Comparison.phaseLoop
#print axioms AtlasB9Comparison.identityLift
#print axioms AtlasB9Comparison.inverseGaugeLift
#print axioms AtlasB9Comparison.chiral
#print axioms AtlasB9Comparison.upperBandVec
#print axioms AtlasB9Comparison.gaugedUpperBandVec

#print axioms AtlasB9Comparison.phaseLoop_ne_zero
#print axioms AtlasB9Comparison.liftWinding_zero
#print axioms AtlasB9Comparison.liftWinding_add
#print axioms AtlasB9Comparison.liftWinding_identity
#print axioms AtlasB9Comparison.liftWinding_inverseGauge
#print axioms AtlasB9Comparison.identityPhase_differentiable
#print axioms AtlasB9Comparison.inverseGauge_differentiable
#print axioms AtlasB9Comparison.identityLoop_closed
#print axioms AtlasB9Comparison.inverseGauge_closed
#print axioms AtlasB9Comparison.gaugedLoop_closed
#print axioms AtlasB9Comparison.normalizedPhaseIntegral_identity
#print axioms AtlasB9Comparison.normalizedPhaseIntegral_gauged
#print axioms AtlasB9Comparison.periodic_gauge_changes_displayed_integral
#print axioms AtlasB9Comparison.weak_closed_endpoint_reading_refuted
#print axioms AtlasB9Comparison.periodic_gauge_changes_winding
#print axioms AtlasB9Comparison.common_gauge_preserves_relative_phase
#print axioms AtlasB9Comparison.liftWinding_gauge_add
#print axioms AtlasB9Comparison.phaseLoop_add
#print axioms AtlasB9Comparison.phaseLoop_unit
#print axioms AtlasB9Comparison.chiral_isHermitian
#print axioms AtlasB9Comparison.chiral_zero_matrix_iff
#print axioms AtlasB9Comparison.chiral_det
#print axioms AtlasB9Comparison.chiral_positive_band
#print axioms AtlasB9Comparison.chiral_negative_band
#print axioms AtlasB9Comparison.upperBandVec_eigen
#print axioms AtlasB9Comparison.gaugedUpperBandVec_eigen
#print axioms AtlasB9Comparison.upperBandVec_closed
#print axioms AtlasB9Comparison.gaugedUpperBandVec_closed
#print axioms AtlasB9Comparison.upperBandVec_selected_phase
#print axioms AtlasB9Comparison.gaugedUpperBandVec_selected_phase
#print axioms AtlasB9Comparison.chiral_eigenvalue_sq
#print axioms AtlasB9Comparison.chiral_eigenvalue_eq_pm
#print axioms AtlasB9Comparison.phaseLoop_chiral_no_zero_mode
#print axioms AtlasB9Comparison.chiral_no_zero_mode
#print axioms AtlasB9Comparison.chiral_comparison_kernel
end


/-! ## B11 — the figure-eight shapes, the vanishing correction term and the two-tetrahedron sum

Integrated from `.ultramath/smwwdl7d5/m3/B11.lean`.
-/

section
open scoped ComplexConjugate
open Complex

noncomputable section

namespace RelationalAtlas.B11

/-- The displayed Bloch--Wigner expression, with the imaginary part of Li₂
supplied as a parameter (Mathlib has no dilogarithm definition). -/
def blochWigner (imLi₂ : ℂ → ℝ) (z : ℂ) : ℝ :=
  imLi₂ z + Complex.arg (1 - z) * Real.log ‖z‖

/-- The upper-half-plane point used only against the invented, truncated
reading `D(z) = Im Li₂(z)`. -/
def strawZ : ℂ := (1 + Complex.I) / 2

lemma strawZ_im : 0 < strawZ.im := by
  norm_num [strawZ]

lemma one_sub_strawZ_im : (1 - strawZ).im < 0 := by
  norm_num [strawZ]

lemma strawZ_norm_pos : 0 < ‖strawZ‖ := by
  rw [norm_pos_iff]
  norm_num [strawZ]
  intro h
  have := congrArg Complex.re h
  norm_num at this

lemma strawZ_norm_lt_one : ‖strawZ‖ < 1 := by
  have hsq : ‖strawZ‖ ^ 2 = 1 / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [strawZ, Complex.normSq_apply]
  nlinarith [sq_nonneg ‖strawZ‖, strawZ_norm_pos]

/-- The omitted term is strictly positive at `strawZ`. -/
lemma strawman_omitted_term_pos :
    0 < Complex.arg (1 - strawZ) * Real.log ‖strawZ‖ := by
  exact mul_pos_of_neg_of_neg
    (Complex.arg_neg_iff.mpr one_sub_strawZ_im)
    (Real.log_neg strawZ_norm_pos strawZ_norm_lt_one)

/-- STRAWMAN ONLY: no imaginary dilogarithm can make the truncated expression
equal the displayed one at `strawZ`, because the displayed correction is
nonzero. This is not a refutation of B11. -/
theorem strawman_truncation_refuted (imLi₂ : ℂ → ℝ) :
    blochWigner imLi₂ strawZ ≠ imLi₂ strawZ := by
  unfold blochWigner
  have h := strawman_omitted_term_pos
  linarith

/-- The regular upper-half-plane tetrahedron shape `(1 + √3 i)/2`. -/
def regularShape : ℂ := (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

lemma sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

lemma regularShape_im : 0 < regularShape.im := by
  have h : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp [regularShape, h]

lemma regularShape_gluing : regularShape ^ 2 - regularShape + 1 = 0 := by
  have hsqrt := sqrt_three_sq
  apply Complex.ext <;> simp [regularShape, pow_two] at *
  · ring_nf
    norm_num
  · ring_nf

lemma regularShape_norm : ‖regularShape‖ = 1 := by
  have hsq : ‖regularShape‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [regularShape, Complex.normSq_apply]
  nlinarith [norm_nonneg regularShape]

lemma regularShape_ne_zero : regularShape ≠ 0 := by
  rw [← norm_ne_zero_iff, regularShape_norm]
  norm_num

/-- The usual rectangular form is the exponential shape `exp(iπ/3)`. -/
theorem regularShape_eq_exp :
    regularShape = Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [regularShape, Real.cos_pi_div_three, Real.sin_pi_div_three]

/-- The two polynomial gluing equations for the standard two-tetrahedron
figure-eight triangulation, specialised to equal shapes. -/
def figureEightGluing (z w : ℂ) : Prop :=
  z ^ 2 * w ^ 2 * (1 - z⁻¹) * (1 - w⁻¹) = 1 ∧
    z * w * (1 - z⁻¹) = -1

lemma figureEightGluing_of_shape {z : ℂ}
    (hz : z ^ 2 - z + 1 = 0) (hz0 : z ≠ 0) : figureEightGluing z z := by
  have hzz : z * (z - 1) = -1 := by linear_combination hz
  have hinv : 1 - z⁻¹ = (z - 1) / z := by field_simp
  unfold figureEightGluing
  rw [hinv]
  constructor
  · calc
      z ^ 2 * z ^ 2 * ((z - 1) / z) * ((z - 1) / z) =
          (z * (z - 1)) ^ 2 := by field_simp
      _ = 1 := by rw [hzz]; norm_num
  · calc
      z * z * ((z - 1) / z) = z * (z - 1) := by field_simp
      _ = -1 := hzz

/-- Both displayed figure-eight gluing equations hold at the regular shape. -/
theorem regularShape_figureEight_gluing : figureEightGluing regularShape regularShape :=
  figureEightGluing_of_shape regularShape_gluing regularShape_ne_zero

/-- The upper-half-plane solution of the quadratic shape equation is unique. -/
theorem upper_shape_unique {z : ℂ} (hz : z ^ 2 - z + 1 = 0) (him : 0 < z.im) :
    z = regularShape := by
  have hfactor : (z - regularShape) * (z + regularShape - 1) = 0 := by
    linear_combination hz - regularShape_gluing
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hother : z = 1 - regularShape := by
      apply eq_of_sub_eq_zero
      linear_combination h
    have himage : z.im = -regularShape.im := by simp [hother]
    linarith [regularShape_im]

/-- The correction vanishes on a unit-modulus shape. -/
theorem blochWigner_of_norm_one (imLi₂ : ℂ → ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    blochWigner imLi₂ z = imLi₂ z := by
  simp [blochWigner, hz]

/-- Finite two-tetrahedron expression: after the regular-shape reduction it is
exactly twice the imaginary dilogarithm. No numerical value or hyperbolic
volume identity is asserted here. -/
theorem figureEight_finite_sum (imLi₂ : ℂ → ℝ) :
    (∑ _j : Fin 2, blochWigner imLi₂ regularShape) = 2 * imLi₂ regularShape := by
  rw [Fin.sum_univ_two]
  rw [blochWigner_of_norm_one imLi₂ regularShape regularShape_norm]
  ring

#print axioms blochWigner
#print axioms strawZ
#print axioms strawZ_im
#print axioms one_sub_strawZ_im
#print axioms strawZ_norm_pos
#print axioms strawZ_norm_lt_one
#print axioms strawman_omitted_term_pos
#print axioms strawman_truncation_refuted
#print axioms regularShape
#print axioms sqrt_three_sq
#print axioms regularShape_im
#print axioms regularShape_gluing
#print axioms regularShape_norm
#print axioms regularShape_ne_zero
#print axioms regularShape_eq_exp
#print axioms figureEightGluing
#print axioms figureEightGluing_of_shape
#print axioms regularShape_figureEight_gluing
#print axioms upper_shape_unique
#print axioms blochWigner_of_norm_one
#print axioms figureEight_finite_sum

end RelationalAtlas.B11
end
end


/-! ## B29 — the classical coefficients, and the index the displayed power law gives them

Integrated from `.ultramath/smwwdl7d5/m4/B29.lean`.
-/

section
open Real Filter Topology

namespace RelationalAtlas.B29

/-- The two-dimensional leading coefficient, exactly as in the Check field. -/
noncomputable def classicalA0 (Area : ℝ) : ℝ := Area / (4 * π)

/-- The two-dimensional scalar-curvature coefficient, exactly as in the Check field. -/
noncomputable def classicalA1 (integralR : ℝ) : ℝ := (1 / (4 * π)) * (integralR / 6)

theorem classicalA1_eq (integralR : ℝ) :
    classicalA1 integralR = integralR / (24 * π) := by
  unfold classicalA1
  ring

/-- With scalar curvature convention `∫ R = 4πχ`, the Check formula is χ/6. -/
theorem classicalA1_euler (integralR χ : ℝ)
    (hGaussBonnet : integralR = 4 * π * χ) :
    classicalA1 integralR = χ / 6 := by
  rw [classicalA1_eq, hGaussBonnet]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- Unit round S² has area 4π, hence leading coefficient one. -/
theorem unitSphere_A0 : classicalA0 (4 * π) = 1 := by
  unfold classicalA0
  field_simp [Real.pi_ne_zero]

/-- Unit round S² has ∫R = 8π, hence curvature coefficient 1/3. -/
theorem unitSphere_A1 : classicalA1 (8 * π) = 1 / 3 := by
  rw [classicalA1_eq]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The square flat torus of side 2π has leading coefficient π. -/
theorem squareFlatTorus_A0 : classicalA0 ((2 * π) * (2 * π)) = π := by
  unfold classicalA0
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- Zero total scalar curvature gives zero value of the Check's curvature coefficient. -/
theorem flat_A1 : classicalA1 0 = 0 := by
  simp [classicalA1]

/-- The exponent attached by the display to coefficient index k in dimension d. -/
noncomputable def displayedExponent (d k : ℝ) : ℝ := (k - d) / 2

theorem displayedExponent_d2_k0 : displayedExponent 2 0 = -1 := by
  norm_num [displayedExponent]

theorem displayedExponent_d2_k1 : displayedExponent 2 1 = -(1 / 2) := by
  norm_num [displayedExponent]

theorem displayedExponent_d2_k2 : displayedExponent 2 2 = 0 := by
  norm_num [displayedExponent]

/-- The finite indexing discrepancy: a nonzero curvature value cannot simultaneously
be the display's k=1 coefficient and its constant (k=2) coefficient. -/
theorem unitSphere_curvature_index_discrepancy :
    classicalA1 (8 * π) ≠ 0 ∧ displayedExponent 2 1 ≠ displayedExponent 2 2 := by
  constructor
  · rw [unitSphere_A1]
    norm_num
  · rw [displayedExponent_d2_k1, displayedExponent_d2_k2]
    norm_num

/-- The unit sphere contradicts the *mixed* display/Check indexing once the standard
closed-manifold heat theorem supplies the vanishing odd coefficient.  The hypothesis
`hOdd` is precisely that cited analytic input; the contradiction itself is finite. -/
theorem unitSphere_display_check_inconsistent_of_odd_vanishing
    (a : ℕ → ℝ) (hOdd : a 1 = 0)
    (hCheck : a 1 = classicalA1 (8 * π)) : False := by
  rw [hOdd, unitSphere_A1] at hCheck
  norm_num at hCheck

/-- Constant term after multiplying a two-dimensional heat expansion by exp(-q*t).
This is the coefficient recurrence, not a definition of a differential operator. -/
noncomputable def shiftedConstantCoefficient (q a0 a1 : ℝ) : ℝ := a1 - q * a0

@[simp] theorem shiftedConstantCoefficient_zero (a0 a1 : ℝ) :
    shiftedConstantCoefficient 0 a0 a1 = a1 := by
  simp [shiftedConstantCoefficient]

theorem shiftedConstantCoefficient_ne (q a0 a1 : ℝ)
    (hq : q ≠ 0) (ha0 : a0 ≠ 0) :
    shiftedConstantCoefficient q a0 a1 ≠ a1 := by
  unfold shiftedConstantCoefficient
  intro h
  have hzero : q * a0 = 0 := by linarith
  exact hq ((mul_eq_zero.mp hzero).resolve_right ha0)

/-- The deleted baseline limit really does repair the potential-shift counterexample. -/
theorem shiftedConstantCoefficient_tendsto (a0 a1 : ℝ) :
    Tendsto (fun q : ℝ => shiftedConstantCoefficient q a0 a1) (𝓝 0) (𝓝 a1) := by
  have hcont : Continuous (fun q : ℝ => shiftedConstantCoefficient q a0 a1) := by
    unfold shiftedConstantCoefficient
    fun_prop
  have h : Tendsto (fun q : ℝ => shiftedConstantCoefficient q a0 a1) (𝓝 0)
      (𝓝 (shiftedConstantCoefficient 0 a0 a1)) := hcont.continuousAt.tendsto
  simpa using h

/-- In the unit-sphere potential-shift model the new constant term is 1/3-q. -/
theorem unitSphere_shiftedConstantCoefficient (q : ℝ) :
    shiftedConstantCoefficient q 1 (1 / 3) = 1 / 3 - q := by
  simp [shiftedConstantCoefficient]

end RelationalAtlas.B29

#print axioms RelationalAtlas.B29.classicalA0
#print axioms RelationalAtlas.B29.classicalA1
#print axioms RelationalAtlas.B29.displayedExponent
#print axioms RelationalAtlas.B29.shiftedConstantCoefficient
#print axioms RelationalAtlas.B29.classicalA1_eq
#print axioms RelationalAtlas.B29.classicalA1_euler
#print axioms RelationalAtlas.B29.unitSphere_A0
#print axioms RelationalAtlas.B29.unitSphere_A1
#print axioms RelationalAtlas.B29.squareFlatTorus_A0
#print axioms RelationalAtlas.B29.flat_A1
#print axioms RelationalAtlas.B29.displayedExponent_d2_k0
#print axioms RelationalAtlas.B29.displayedExponent_d2_k1
#print axioms RelationalAtlas.B29.displayedExponent_d2_k2
#print axioms RelationalAtlas.B29.unitSphere_curvature_index_discrepancy
#print axioms RelationalAtlas.B29.unitSphere_display_check_inconsistent_of_odd_vanishing
#print axioms RelationalAtlas.B29.shiftedConstantCoefficient_zero
#print axioms RelationalAtlas.B29.shiftedConstantCoefficient_ne
#print axioms RelationalAtlas.B29.shiftedConstantCoefficient_tendsto
#print axioms RelationalAtlas.B29.unitSphere_shiftedConstantCoefficient
end


/-! ## B29 — the round-sphere heat trace, term by term, and the same index defect

Integrated from `.ultramath/smwwdl7d5/m5/B29.lean`.
-/

section
/-!
# B29: finite classical heat-coefficient checks and a labelled weak-reading test

The differential-geometric input for a round sphere is encoded explicitly as data:
area `4πr²`, scalar curvature `2/r²`, and total scalar curvature `8π`.
No theorem below derives those facts from a Riemannian metric, proves the full
Seeley--DeWitt expansion, or proves the external operator-coefficient reduction.
-/

open scoped BigOperators

namespace B29

/-- The two pieces of classical surface data needed by the displayed check. -/
structure ClosedSurfaceData where
  Area : ℝ
  ScalarIntegral : ℝ

/-- The coefficient of `t⁻¹` in dimension two. -/
noncomputable def classicalA0 (M : ClosedSurfaceData) : ℝ :=
  M.Area / (4 * Real.pi)

/-- The constant coefficient in dimension two. -/
noncomputable def classicalA1 (M : ClosedSurfaceData) : ℝ :=
  M.ScalarIntegral / (6 * (4 * Real.pi))

/-- Classical area and total scalar curvature of the round sphere of radius `r`. -/
noncomputable def roundSphereData (r : ℝ) : ClosedSurfaceData where
  Area := 4 * Real.pi * r ^ 2
  ScalarIntegral := 8 * Real.pi

/-- Scalar (not sectional) curvature of the round sphere of radius `r`. -/
noncomputable def roundSphereScalarCurvature (r : ℝ) : ℝ := 2 / r ^ 2

/-- The encoded total scalar curvature is the area times the constant scalar curvature. -/
theorem roundSphere_scalarIntegral_eq_area_mul_scalar {r : ℝ} (hr : r ≠ 0) :
    (roundSphereData r).Area * roundSphereScalarCurvature r =
      (roundSphereData r).ScalarIntegral := by
  dsimp [roundSphereData, roundSphereScalarCurvature]
  field_simp [hr, Real.pi_ne_zero]
  <;> ring

/-- The area coefficient of a round sphere is exactly `r²`. -/
theorem roundSphere_classicalA0 (r : ℝ) :
    classicalA0 (roundSphereData r) = r ^ 2 := by
  dsimp [classicalA0, roundSphereData]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The constant heat coefficient of a round sphere is independent of its radius. -/
theorem roundSphere_classicalA1 (r : ℝ) :
    classicalA1 (roundSphereData r) = 1 / 3 := by
  dsimp [classicalA1, roundSphereData]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The unit-sphere target is `a₀ = 1`. -/
theorem unitRoundSphere_classicalA0 :
    classicalA0 (roundSphereData 1) = 1 := by
  rw [roundSphere_classicalA0]
  norm_num

/-- The unit-sphere target is `a₁ = 1/3`. -/
theorem unitRoundSphere_classicalA1 :
    classicalA1 (roundSphereData 1) = 1 / 3 := by
  exact roundSphere_classicalA1 1

/-- The exponent attached to `a_k` by the literal display in dimension `d`. -/
noncomputable def displayExponent (d k : ℝ) : ℝ := (k - d) / 2

/-- In two dimensions the display puts `a₀` at power `-1`. -/
theorem displayExponent_d2_k0 : displayExponent 2 0 = -1 := by
  norm_num [displayExponent]

/-- In two dimensions the display puts `a₁` at power `-1/2`. -/
theorem displayExponent_d2_k1 : displayExponent 2 1 = -(1 / 2) := by
  norm_num [displayExponent]

/-- In two dimensions the constant curvature term instead has display index `k = 2`. -/
theorem displayExponent_d2_k2 : displayExponent 2 2 = 0 := by
  norm_num [displayExponent]

/-- The finite normalisation/index discrepancy on unit `S²`. -/
theorem unitSphere_curvature_index_discrepancy :
    classicalA1 (roundSphereData 1) ≠ 0 ∧
      displayExponent 2 1 ≠ displayExponent 2 2 := by
  constructor
  · rw [unitRoundSphere_classicalA1]
    norm_num
  · rw [displayExponent_d2_k1, displayExponent_d2_k2]
    norm_num

/-- LITERAL DISPLAY/CHECK CONTRADICTION. On a closed surface the cited classical
heat theorem gives vanishing odd coefficients; unit `S²` hence has `a₁ = 0` in the
display indexing, whereas Check gives the same slot the nonzero value `1/3`.
The analytic odd-vanishing premise is explicit and is not proved in this file. -/
theorem unitSphere_displayCheck_inconsistent_of_odd_vanishing
    (a : ℕ → ℝ) (hOdd : a 1 = 0)
    (hCheck : a 1 = classicalA1 (roundSphereData 1)) : False := by
  rw [hOdd, unitRoundSphere_classicalA1] at hCheck
  norm_num at hCheck

/-- Under the finite Gauss--Bonnet input, the checked `a₁` is `χ/6`. -/
theorem classicalA1_of_gaussBonnet (M : ClosedSurfaceData) (chi : ℝ)
    (hGB : M.ScalarIntegral = 4 * Real.pi * chi) :
    classicalA1 M = chi / 6 := by
  rw [classicalA1, hGB]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The sphere's value `1/3` agrees with Gauss--Bonnet and `χ(S²) = 2`. -/
theorem roundSphere_classicalA1_gaussBonnet (r : ℝ) :
    classicalA1 (roundSphereData r) = (2 : ℝ) / 6 := by
  apply classicalA1_of_gaussBonnet
  dsimp [roundSphereData]
  ring

/-- Eigenvalue level `l` of the nonnegative unit-sphere Laplacian. -/
def sphereEigenvalue (l : ℕ) : ℕ := l * (l + 1)

/-- The summand in the spherical-harmonic heat trace, with multiplicity `2l+1`. -/
noncomputable def sphereHeatTerm (t : ℝ) (l : ℕ) : ℝ :=
  (2 * (l : ℝ) + 1) * Real.exp (-t * (sphereEigenvalue l : ℝ))

/-- The full spectral heat trace. At negative `t` the default value of `tsum` has
no spectral meaning; all uses below are at the positive time `log 2`. -/
noncomputable def sphereHeatTrace (t : ℝ) : ℝ :=
  ∑' l : ℕ, sphereHeatTerm t l

/-- Every spectral heat-term is nonnegative. -/
theorem sphereHeatTerm_nonneg (t : ℝ) (l : ℕ) : 0 ≤ sphereHeatTerm t l := by
  dsimp [sphereHeatTerm]
  positivity

/-- The first `N` levels have total multiplicity `N²` at time zero. -/
theorem roundSphere_partialHeat_zero (N : ℕ) :
    (∑ l ∈ Finset.range N, sphereHeatTerm 0 l) = (N : ℝ) ^ 2 := by
  have hterm (l : ℕ) : sphereHeatTerm 0 l = 2 * (l : ℝ) + 1 := by
    simp [sphereHeatTerm]
  simp_rw [hterm]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exponential values used at the positive test time `log 2`. -/
theorem exp_neg_nat_mul_log_two (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log 2) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [show -(n : ℝ) * Real.log 2 = (n : ℝ) * (-Real.log 2) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact inv_pow (2 : ℝ) n

/-- At `t = log 2`, every heat-term is a rational multiple of an inverse power of two. -/
theorem sphereHeatTerm_log_two (l : ℕ) :
    sphereHeatTerm (Real.log 2) l =
      (2 * (l : ℝ) + 1) * ((2 : ℝ) ^ sphereEigenvalue l)⁻¹ := by
  unfold sphereHeatTerm
  rw [show -Real.log 2 * (sphereEigenvalue l : ℝ) =
      -(sphereEigenvalue l : ℝ) * Real.log 2 by ring]
  rw [exp_neg_nat_mul_log_two]

/-- A geometric majorant for the heat trace at `log 2`. -/
theorem summable_sphereHeatTerm_log_two : Summable (sphereHeatTerm (Real.log 2)) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hlin : Summable (fun l : ℕ => (l : ℝ) * (1 / 2 : ℝ) ^ l) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr)
  have hgeom : Summable (fun l : ℕ => (1 / 2 : ℝ) ^ l) :=
    summable_geometric_of_norm_lt_one hr
  have hmajor : Summable (fun l : ℕ => (2 * (l : ℝ) + 1) * (1 / 2 : ℝ) ^ l) := by
    convert (hlin.mul_left 2).add hgeom using 1 <;> ext l <;> ring
  apply Summable.of_nonneg_of_le (fun l => sphereHeatTerm_nonneg _ l) _ hmajor
  intro l
  rw [sphereHeatTerm_log_two]
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hexp : ((2 : ℝ) ^ sphereEigenvalue l)⁻¹ ≤ (1 / 2 : ℝ) ^ l := by
    rw [← exp_neg_nat_mul_log_two]
    have heq : (1 / 2 : ℝ) ^ l = Real.exp (-(l : ℝ) * Real.log 2) := by
      rw [exp_neg_nat_mul_log_two]
      simp [inv_pow]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hn : (l : ℝ) ≤ (sphereEigenvalue l : ℝ) := by
      dsimp [sphereEigenvalue]
      push_cast
      nlinarith [Nat.zero_le l]
    nlinarith [mul_le_mul_of_nonneg_right hn hlog]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The first three levels give a rigorous lower bound for the whole heat trace. -/
theorem roundSphere_heatTrace_log_two_lower :
    (117 / 64 : ℝ) ≤ sphereHeatTrace (Real.log 2) := by
  have h := summable_sphereHeatTerm_log_two.sum_le_tsum (Finset.range 3)
    (fun l _ => sphereHeatTerm_nonneg (Real.log 2) l)
  dsimp [sphereHeatTrace]
  convert h using 1
  simp [Finset.sum_range_succ, sphereHeatTerm_log_two, sphereEigenvalue]
  norm_num

/-- The two-term expression obtained by truncating the display after `k = 1`. -/
noncomputable def weakTwoTermFormula (t : ℝ) : ℝ :=
  classicalA0 (roundSphereData 1) / t + classicalA1 (roundSphereData 1)

/-- LABELLED WEAK-READING REFUTATION. Exact equality to just the first two
asymptotic terms is false at `t = log 2`; this is not a refutation of `∼`. -/
theorem weak_two_term_exact_reading_false :
    sphereHeatTrace (Real.log 2) ≠ weakTwoTermFormula (Real.log 2) := by
  intro heq
  have hlog : (69 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
  have hinv : 1 / Real.log 2 < (100 / 69 : ℝ) := by
    apply (div_lt_iff₀ hlogpos).2
    nlinarith
  have hlower := roundSphere_heatTrace_log_two_lower
  rw [heq] at hlower
  dsimp [weakTwoTermFormula] at hlower
  rw [unitRoundSphere_classicalA0, unitRoundSphere_classicalA1] at hlower
  have hinv' : (Real.log 2)⁻¹ < (100 / 69 : ℝ) := by
    simpa only [one_div] using hinv
  norm_num at hlower
  linarith

end B29

#print axioms B29.ClosedSurfaceData
#print axioms B29.classicalA0
#print axioms B29.classicalA1
#print axioms B29.roundSphereData
#print axioms B29.roundSphereScalarCurvature
#print axioms B29.displayExponent
#print axioms B29.sphereEigenvalue
#print axioms B29.sphereHeatTerm
#print axioms B29.sphereHeatTrace
#print axioms B29.weakTwoTermFormula
#print axioms B29.roundSphere_scalarIntegral_eq_area_mul_scalar
#print axioms B29.roundSphere_classicalA0
#print axioms B29.roundSphere_classicalA1
#print axioms B29.unitRoundSphere_classicalA0
#print axioms B29.unitRoundSphere_classicalA1
#print axioms B29.displayExponent_d2_k0
#print axioms B29.displayExponent_d2_k1
#print axioms B29.displayExponent_d2_k2
#print axioms B29.unitSphere_curvature_index_discrepancy
#print axioms B29.unitSphere_displayCheck_inconsistent_of_odd_vanishing
#print axioms B29.classicalA1_of_gaussBonnet
#print axioms B29.roundSphere_classicalA1_gaussBonnet
#print axioms B29.sphereHeatTerm_nonneg
#print axioms B29.roundSphere_partialHeat_zero
#print axioms B29.exp_neg_nat_mul_log_two
#print axioms B29.sphereHeatTerm_log_two
#print axioms B29.summable_sphereHeatTerm_log_two
#print axioms B29.roundSphere_heatTrace_log_two_lower
#print axioms B29.weak_two_term_exact_reading_false
end


/-! ## B36 — the wall transport block: repeated eigenvalue, defectiveness, and the scalar boundary

Integrated from `.ultramath/smwwdl7d5/m8/B36.lean`.
-/

section
/-!
# B36 — two readings of the wall claim

The strong witness uses the actual transport
`A(H) = T*H + H*T - 2*tr(T*H)*G` on traceless symmetric matrices.
At `T = 1` it is the scalar map `H ↦ 2*H`.  The rational matrix `Xwall`
makes every Gram, trace and rank hypothesis computable without square roots.

The second witness is deliberately only a straw-man control: it ignores the
joint condition which the Check field attaches to the double point.  It is
kept separate from the strong witness and is not evidence against that field.
-/

namespace B36

noncomputable section

open scoped BigOperators

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The transport in B36's Carry field. -/
def transport (T G H : Mat 3) : Mat 3 :=
  T * H + H * T - (2 * Matrix.trace (T * H)) • G

/-- A rational square root of a regular rank-two wall Gram matrix. -/
def Xwall : Mat 3 := Matrix.diagonal ![3 / 5, 4 / 5, 0]

/-- The wall Gram matrix, literally in the form required by Carry. -/
def Gwall : Mat 3 := Xwall.transpose * Xwall

/-- The first unnormalised diagonal shape direction. -/
def H₁ : Mat 3 := Matrix.diagonal ![1, -1, 0]

/-- The second unnormalised diagonal shape direction. -/
def H₂ : Mat 3 := Matrix.diagonal ![1, 1, -2]

/-- Diagonalisability without choosing a library-specific Jordan normal form. -/
def Diagonalizable (A : Mat 2) : Prop :=
  ∃ P D : Mat 2, P.det ≠ 0 ∧ D.IsDiag ∧ A * P = P * D

/-- A genuine size-two Jordan block is defective, unlike a scalar `2 × 2` block. -/
def Defective (A : Mat 2) : Prop := ¬ Diagonalizable A

/-- The shape block at the strong witness, in the basis `(H₁,H₂)`. -/
def strongShape : Mat 2 := (2 : ℝ) • 1

/-- The displayed Gram matrix evaluates to a positive-rank-two diagonal matrix. -/
theorem Gwall_eq : Gwall = Matrix.diagonal ![9 / 25, 16 / 25, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Gwall, Xwall, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply]

/-- Carry: `Gwall = Xwallᵀ Xwall` by definition. -/
theorem Gwall_is_gram : Gwall = Xwall.transpose * Xwall := rfl

/-- Carry: the Gram trace is one. -/
theorem trace_Gwall : Matrix.trace Gwall = 1 := by
  rw [Gwall_eq]
  norm_num [Matrix.trace, Fin.sum_univ_three]

/-- Check: the displayed wall has `w₃ = 0`, `w₂ > 0`, and the other retained
weight is positive too. -/
theorem regular_wall_weights :
    (0 : ℝ) < 9 / 25 ∧ (0 : ℝ) < 16 / 25 ∧
      (9 / 25 : ℝ) + 16 / 25 = 1 := by
  norm_num

/-- Check: the Gram matrix has rank exactly two, so this is not the excluded
collinear stratum. -/
theorem rank_Gwall : Gwall.rank = 2 := by
  classical
  rw [Gwall_eq, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![9 / 25, 16 / 25, 0] : Fin 3 → ℝ) x ≠ 0)).card = 2
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![9 / 25, 16 / 25, 0] : Fin 3 → ℝ) x ≠ 0)) = {0, 1} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

/-- Carry: the scalar matrix is diagonal. -/
theorem strong_T_diagonal : (1 : Mat 3).IsDiag := Matrix.isDiag_one

/-- Carry: the scalar matrix is positive definite. -/
theorem strong_T_posDef : (1 : Mat 3).PosDef := Matrix.PosDef.one

/-- Check: the strong witness satisfies the exact joint condition, with
`t₁=t₂=t₃=1` and `(w₁,w₂)=(9/25,16/25)`. -/
theorem strong_joint_condition :
    (1 : ℝ) + 1 - 2 * 1 = (1 - 1) * (9 / 25 - 16 / 25) := by
  norm_num

/-- At scalar `T`, the transport is scalar on every traceless tangent. -/
theorem transport_one_of_trace_zero {G H : Mat 3} (hH : Matrix.trace H = 0) :
    transport 1 G H = (2 : ℝ) • H := by
  simp [transport, hH, two_smul]

theorem trace_H₁ : Matrix.trace H₁ = 0 := by
  norm_num [H₁, Matrix.trace, Fin.sum_univ_three]

theorem trace_H₂ : Matrix.trace H₂ = 0 := by
  norm_num [H₂, Matrix.trace, Fin.sum_univ_three]

/-- The first strong shape column is `(2,0)`, with no hidden off-diagonal term. -/
theorem strong_transport_H₁ : transport 1 Gwall H₁ = (2 : ℝ) • H₁ :=
  transport_one_of_trace_zero trace_H₁

/-- The second strong shape column is `(0,2)`, with no hidden off-diagonal term. -/
theorem strong_transport_H₂ : transport 1 Gwall H₂ = (2 : ℝ) • H₂ :=
  transport_one_of_trace_zero trace_H₂

/-- The strong shape block really is the scalar matrix `2I`. -/
theorem strongShape_eq : strongShape = !![2, 0; 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [strongShape, Matrix.one_apply]

/-- A scalar block is diagonalisable, hence not a genuine size-two Jordan block. -/
theorem strongShape_diagonalizable : Diagonalizable strongShape := by
  refine ⟨1, strongShape, ?_, ?_, ?_⟩
  · simp
  · rw [strongShape_eq]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp

theorem strongShape_not_defective : ¬ Defective strongShape := by
  intro h
  exact h strongShape_diagonalizable

/-- All strong-witness assertions in one package.  In particular, every stated
Carry/Check hypothesis coexists with a diagonalisable (therefore non-Jordan)
shape block. -/
theorem strong_faithful_witness :
    Gwall = Xwall.transpose * Xwall ∧ Matrix.trace Gwall = 1 ∧
      Gwall.rank = 2 ∧
      ((0 : ℝ) < 9 / 25 ∧ (0 : ℝ) < 16 / 25 ∧
        (9 / 25 : ℝ) + 16 / 25 = 1) ∧
      (1 : Mat 3).IsDiag ∧ (1 : Mat 3).PosDef ∧
      ((1 : ℝ) + 1 - 2 * 1 = (1 - 1) * (9 / 25 - 16 / 25)) ∧
      transport 1 Gwall H₁ = (2 : ℝ) • H₁ ∧
      transport 1 Gwall H₂ = (2 : ℝ) • H₂ ∧
      Diagonalizable strongShape := by
  exact ⟨Gwall_is_gram, trace_Gwall, rank_Gwall, regular_wall_weights,
    strong_T_diagonal, strong_T_posDef, strong_joint_condition,
    strong_transport_H₁, strong_transport_H₂, strongShape_diagonalizable⟩

/-! ## General finite defectiveness criterion

These lemmas separate the repeated-eigenvalue condition from the independent
nonzero-off-diagonal condition.  They are scope results, not a refutation of
the v7 ledger card (which has no Jordan clause). -/

/-- An upper-triangular real `2 × 2` matrix is diagonalisable precisely when
its diagonal entries differ or its upper-right entry vanishes. -/
theorem diagonalizable_upper_two (a b d : ℝ) :
    Diagonalizable !![a, b; 0, d] ↔ a ≠ d ∨ b = 0 := by
  constructor
  · rintro ⟨P, D, hP, hD, hmul⟩
    by_cases hb : b = 0
    · exact Or.inr hb
    · left
      intro had
      subst d
      have hD01 : D 0 1 = 0 := hD (by decide)
      have hD10 : D 1 0 = 0 := hD (by decide)
      have h00 := congrArg (fun M : Mat 2 => M 0 0) hmul
      have h01 := congrArg (fun M : Mat 2 => M 0 1) hmul
      have h10 := congrArg (fun M : Mat 2 => M 1 0) hmul
      have h11 := congrArg (fun M : Mat 2 => M 1 1) hmul
      simp [Matrix.mul_apply, Fin.sum_univ_two, hD01, hD10] at h00 h01 h10 h11
      by_cases hp10 : P 1 0 = 0
      · have hdet : P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0 := by
          simpa [Matrix.det_fin_two] using hP
        have hp11 : P 1 1 ≠ 0 := by
          intro hp11
          simp [hp10, hp11] at hdet
        have hd1 : D 1 1 = a := by
          apply (mul_right_cancel₀ hp11)
          linarith
        rw [hd1] at h01
        have : b * P 1 1 = 0 := by linarith
        exact hb ((mul_eq_zero.mp this).resolve_right hp11)
      · have hd0 : D 0 0 = a := by
          apply (mul_right_cancel₀ hp10)
          linarith
        rw [hd0] at h00
        have : b * P 1 0 = 0 := by linarith
        exact hb ((mul_eq_zero.mp this).resolve_right hp10)
  · intro h
    rcases h with had | hb
    · refine ⟨!![1, b; 0, d - a], Matrix.diagonal ![a, d], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two]
        norm_num
        exact sub_ne_zero.mpr (Ne.symm had)
      · exact Matrix.isDiag_diagonal _
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring
    · subst b
      refine ⟨1, !![a, 0; 0, d], by simp, ?_, by simp⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all

/-- Consequently a genuine defect is exactly a repeated diagonal entry together
with a nonzero upper-right entry. -/
theorem defective_upper_two (a b d : ℝ) :
    Defective !![a, b; 0, d] ↔ a = d ∧ b ≠ 0 := by
  simp [Defective, diagonalizable_upper_two]

/-! ## The actual wall block and its exact scope

Here `w₂ = 1 - w₁`, so `wallG w₁` has trace one.  The basis remains the
unnormalised `(H₁,H₂)` used for the explicit witnesses above. -/

/-- A general diagonal transport matrix. -/
def wallT (t₁ t₂ t₃ : ℝ) : Mat 3 := Matrix.diagonal ![t₁, t₂, t₃]

/-- A general diagonal wall Gram matrix with trace one. -/
def wallG (w₁ : ℝ) : Mat 3 := Matrix.diagonal ![w₁, 1 - w₁, 0]

/-- The first diagonal entry of the wall shape block. -/
def wallLambda1 (t₁ t₂ w₁ : ℝ) : ℝ :=
  2 * t₁ * (1 - w₁) + 2 * t₂ * w₁

/-- The upper-right entry of the wall shape block in the unnormalised basis. -/
def wallOff (t₁ t₂ t₃ w₁ : ℝ) : ℝ :=
  2 * (t₁ - t₃ - (t₁ + t₂ - 2 * t₃) * w₁)

/-- The complete wall shape block computed from the carried transport. -/
def wallBlock (t₁ t₂ t₃ w₁ : ℝ) : Mat 2 :=
  !![wallLambda1 t₁ t₂ w₁, wallOff t₁ t₂ t₃ w₁; 0, 2 * t₃]

/-- The Check joint condition, with `w₂ = 1 - w₁`. -/
def JointCondition (t₁ t₂ t₃ w₁ : ℝ) : Prop :=
  t₁ + t₂ - 2 * t₃ = (t₁ - t₂) * (w₁ - (1 - w₁))

theorem trace_wallG (w₁ : ℝ) : Matrix.trace (wallG w₁) = 1 := by
  simp [wallG, Matrix.trace, Fin.sum_univ_three]

theorem wallT_posDef {t₁ t₂ t₃ : ℝ}
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃) : (wallT t₁ t₂ t₃).PosDef := by
  rw [wallT, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃

/-- The first column of the general wall block comes directly from transport. -/
theorem wall_transport_H₁ (t₁ t₂ t₃ w₁ : ℝ) :
    transport (wallT t₁ t₂ t₃) (wallG w₁) H₁ =
      (wallLambda1 t₁ t₂ w₁) • H₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, wallT, wallG, wallLambda1, H₁,
      Matrix.trace, Fin.sum_univ_three] <;> ring

/-- The second column of the general wall block comes directly from transport. -/
theorem wall_transport_H₂ (t₁ t₂ t₃ w₁ : ℝ) :
    transport (wallT t₁ t₂ t₃) (wallG w₁) H₂ =
      (wallOff t₁ t₂ t₃ w₁) • H₁ + (2 * t₃) • H₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, wallT, wallG, wallOff, H₁, H₂,
      Matrix.trace, Fin.sum_univ_three] <;> ring

/-- JC is exactly the repeated-eigenvalue equation, not by itself defectiveness. -/
theorem joint_iff_repeated (t₁ t₂ t₃ w₁ : ℝ) :
    JointCondition t₁ t₂ t₃ w₁ ↔ wallLambda1 t₁ t₂ w₁ = 2 * t₃ := by
  unfold JointCondition wallLambda1
  constructor <;> intro h <;> linear_combination h

/-- Exact defectiveness of the computed wall block. -/
theorem wall_defective_iff (t₁ t₂ t₃ w₁ : ℝ) :
    Defective (wallBlock t₁ t₂ t₃ w₁) ↔
      wallLambda1 t₁ t₂ w₁ = 2 * t₃ ∧ wallOff t₁ t₂ t₃ w₁ ≠ 0 := by
  exact defective_upper_two _ _ _

/-- In particular, the full criterion is JC together with nonzero off-diagonal. -/
theorem wall_defective_iff_joint_and_off (t₁ t₂ t₃ w₁ : ℝ) :
    Defective (wallBlock t₁ t₂ t₃ w₁) ↔
      JointCondition t₁ t₂ t₃ w₁ ∧ wallOff t₁ t₂ t₃ w₁ ≠ 0 := by
  rw [wall_defective_iff, ← joint_iff_repeated]

/-- The explicit off-diagonal vanishing locus. -/
theorem wallOff_eq_zero_iff (t₁ t₂ t₃ w₁ : ℝ) :
    wallOff t₁ t₂ t₃ w₁ = 0 ↔
      t₁ - t₃ = (t₁ + t₂ - 2 * t₃) * w₁ := by
  unfold wallOff
  constructor <;> intro h <;> linarith

/-- Every scalar `T`, not just `T = I`, lies in that vanishing locus. -/
theorem wallOff_scalar (s w₁ : ℝ) : wallOff s s s w₁ = 0 := by
  unfold wallOff
  ring

/-- At scalar `T` the whole shape block is scalar at every wall point. -/
theorem wallBlock_scalar (s w₁ : ℝ) : wallBlock s s s w₁ = (2 * s) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wallBlock, wallLambda1, wallOff, Matrix.one_apply] <;> ring_nf <;> simp_all

theorem wallBlock_scalar_diagonalizable (s w₁ : ℝ) :
    Diagonalizable (wallBlock s s s w₁) := by
  rw [wallBlock_scalar]
  refine ⟨1, (2 * s) • 1, by simp, Matrix.IsDiag.smul _ Matrix.isDiag_one, by simp⟩

/-- At `w₁=w₂=1/2`, the block has the particularly simple entries stated in
the reconciliation: `[[t₁+t₂,t₁-t₂],[0,2t₃]]`. -/
theorem wallBlock_half (t₁ t₂ t₃ : ℝ) :
    wallBlock t₁ t₂ t₃ (1 / 2) = !![t₁ + t₂, t₁ - t₂; 0, 2 * t₃] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wallBlock, wallLambda1, wallOff] <;> ring

theorem joint_half_iff (t₁ t₂ t₃ : ℝ) :
    JointCondition t₁ t₂ t₃ (1 / 2) ↔ t₁ + t₂ - 2 * t₃ = 0 := by
  norm_num [JointCondition]

/-- Sharp equal-weight criterion: JC and `t₁≠t₂` are exactly defectiveness. -/
theorem wall_defective_half_iff (t₁ t₂ t₃ : ℝ) :
    Defective (wallBlock t₁ t₂ t₃ (1 / 2)) ↔
      JointCondition t₁ t₂ t₃ (1 / 2) ∧ t₁ ≠ t₂ := by
  rw [wallBlock_half, defective_upper_two]
  constructor
  · rintro ⟨hrep, hoff⟩
    exact ⟨(joint_half_iff _ _ _).2 (by linarith), sub_ne_zero.mp hoff⟩
  · rintro ⟨hjoint, hne⟩
    exact ⟨by have h := (joint_half_iff _ _ _).1 hjoint; linarith,
      sub_ne_zero.mpr hne⟩

/-- A rational, non-diagonal square root of the equal-weight wall Gram matrix. -/
def Xhalf : Mat 3 := !![1 / 2, 1 / 2, 0; 1 / 2, -1 / 2, 0; 0, 0, 0]

/-- The equal-weight Gram matrix in the exact Carry form. -/
def Ghalf : Mat 3 := Xhalf.transpose * Xhalf

theorem Ghalf_eq_wallG : Ghalf = wallG (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ghalf, Xhalf, wallG, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply]

theorem Ghalf_is_gram : Ghalf = Xhalf.transpose * Xhalf := rfl

theorem trace_Ghalf : Matrix.trace Ghalf = 1 := by
  rw [Ghalf_eq_wallG]
  exact trace_wallG _

/-- Rank two at the equal-weight wall, proved from the explicit diagonal form. -/
theorem rank_Ghalf : Ghalf.rank = 2 := by
  classical
  have hG : Ghalf = Matrix.diagonal ![1 / 2, 1 / 2, 0] := by
    rw [Ghalf_eq_wallG]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [wallG, Matrix.diagonal_apply]
  rw [hG, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) x ≠ 0)).card = 2
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) x ≠ 0)) = {0, 1} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

theorem half_joint_condition : JointCondition 1 1 1 (1 / 2) := by
  norm_num [JointCondition]

/-- The scalar equal-weight case is precisely the diagonalisable boundary case. -/
theorem half_block_eq_strongShape : wallBlock 1 1 1 (1 / 2) = strongShape := by
  rw [wallBlock_scalar]
  norm_num [strongShape]

theorem half_block_diagonalizable : Diagonalizable (wallBlock 1 1 1 (1 / 2)) := by
  rw [half_block_eq_strongShape]
  exact strongShape_diagonalizable

/-- All Carry/Check facts and the equal-weight diagonalisable boundary in one
package; this is a scope boundary, not a refutation of the v7 card. -/
theorem half_faithful_boundary_witness :
    Ghalf = Xhalf.transpose * Xhalf ∧ Matrix.trace Ghalf = 1 ∧
      Ghalf.rank = 2 ∧ (1 : Mat 3).IsDiag ∧ (1 : Mat 3).PosDef ∧
      JointCondition 1 1 1 (1 / 2) ∧
      Diagonalizable (wallBlock 1 1 1 (1 / 2)) := by
  exact ⟨Ghalf_is_gram, trace_Ghalf, rank_Ghalf, strong_T_diagonal,
    strong_T_posDef, half_joint_condition, half_block_diagonalizable⟩

/-- The positive side of the equal-weight criterion: a positive non-scalar `T`
on the JC locus really does give a defective size-two block. -/
theorem half_nonscalar_defective :
    Defective (wallBlock 1 2 (3 / 2) (1 / 2)) := by
  rw [wall_defective_half_iff]
  constructor
  · norm_num [JointCondition]
  · norm_num

/-! ## Phase 2: the deliberately weak reading (a labelled straw man)

A careless reader could delete "For the double point, the joint condition ..."
and assert that *every* positive diagonal `T` at the regular wall gives a
Jordan block.  The following witness refutes only that invented reading. -/

/-- A non-scalar positive diagonal transport for the weak-reading control. -/
def weakT : Mat 3 := Matrix.diagonal ![1, 2, 4]

/-- The computed shape block at the weak-reading witness. -/
def weakShape : Mat 2 := !![68 / 25, -12 / 5; 0, 8]

theorem weakT_diagonal : weakT.IsDiag := by
  intro i j hij
  simp [weakT, hij]

theorem weakT_entries_positive : (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ (0 : ℝ) < 4 := by
  norm_num

theorem weakT_posDef : weakT.PosDef := by
  rw [weakT, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

/-- The weak witness fails the joint condition: its left side is `-5`, whereas
its right side is `7/25`.  It therefore cannot refute B36's actual Check field. -/
theorem weak_joint_condition_fails :
    (1 : ℝ) + 2 - 2 * 4 ≠ (1 - 2) * (9 / 25 - 16 / 25) := by
  norm_num

/-- The first weak shape column is `(68/25,0)`. -/
theorem weak_transport_H₁ : transport weakT Gwall H₁ = (68 / 25 : ℝ) • H₁ := by
  rw [Gwall_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transport, weakT, H₁, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_three, Matrix.diagonal_apply]

/-- The second weak shape column is `(-12/5,8)`. -/
theorem weak_transport_H₂ :
    transport weakT Gwall H₂ = (-12 / 5 : ℝ) • H₁ + (8 : ℝ) • H₂ := by
  rw [Gwall_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transport, weakT, H₁, H₂, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_three, Matrix.diagonal_apply]

/-- Distinct diagonal entries make the weak witness diagonalisable. -/
theorem weakShape_diagonalizable : Diagonalizable weakShape := by
  refine ⟨!![1, -12 / 5; 0, 132 / 25], !![68 / 25, 0; 0, 8], ?_, ?_, ?_⟩
  · norm_num [Matrix.det_fin_two]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [weakShape, Matrix.mul_apply, Fin.sum_univ_two]

/-- This package is explicitly *not* a counterexample to the faithful card:
its final conjunct records failure of the required joint condition. -/
theorem strawman_only_witness :
    weakT.IsDiag ∧ weakT.PosDef ∧
      ((0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ (0 : ℝ) < 4) ∧
      transport weakT Gwall H₁ = (68 / 25 : ℝ) • H₁ ∧
      transport weakT Gwall H₂ = (-12 / 5 : ℝ) • H₁ + (8 : ℝ) • H₂ ∧
      Diagonalizable weakShape ∧
      ((1 : ℝ) + 2 - 2 * 4 ≠ (1 - 2) * (9 / 25 - 16 / 25)) := by
  exact ⟨weakT_diagonal, weakT_posDef, weakT_entries_positive, weak_transport_H₁,
    weak_transport_H₂, weakShape_diagonalizable, weak_joint_condition_fails⟩

#print axioms diagonalizable_upper_two
#print axioms defective_upper_two
#print axioms trace_wallG
#print axioms wallT_posDef
#print axioms wall_transport_H₁
#print axioms wall_transport_H₂
#print axioms joint_iff_repeated
#print axioms wall_defective_iff
#print axioms wall_defective_iff_joint_and_off
#print axioms wallOff_eq_zero_iff
#print axioms wallOff_scalar
#print axioms wallBlock_scalar
#print axioms wallBlock_scalar_diagonalizable
#print axioms wallBlock_half
#print axioms joint_half_iff
#print axioms wall_defective_half_iff
#print axioms Ghalf_eq_wallG
#print axioms Ghalf_is_gram
#print axioms trace_Ghalf
#print axioms rank_Ghalf
#print axioms half_joint_condition
#print axioms half_block_eq_strongShape
#print axioms half_block_diagonalizable
#print axioms half_faithful_boundary_witness
#print axioms half_nonscalar_defective
#print axioms Gwall_eq
#print axioms Gwall_is_gram
#print axioms trace_Gwall
#print axioms regular_wall_weights
#print axioms rank_Gwall
#print axioms strong_T_diagonal
#print axioms strong_T_posDef
#print axioms strong_joint_condition
#print axioms transport_one_of_trace_zero
#print axioms trace_H₁
#print axioms trace_H₂
#print axioms strong_transport_H₁
#print axioms strong_transport_H₂
#print axioms strongShape_eq
#print axioms strongShape_diagonalizable
#print axioms strongShape_not_defective
#print axioms strong_faithful_witness
#print axioms weakT_diagonal
#print axioms weakT_entries_positive
#print axioms weakT_posDef
#print axioms weak_joint_condition_fails
#print axioms weak_transport_H₁
#print axioms weak_transport_H₂
#print axioms weakShape_diagonalizable
#print axioms strawman_only_witness

end
end B36
end


/-! ## B36 — the lift B = J^-1 A J and B(0) = lambda I on the joint condition

Integrated from `.ultramath/smwwdl7d5/m7/B36.lean`.
-/

section
/-!
# B36: transport, the signed-amplitude lift, and two reading controls

The official v7 display says `B(0) = λ * I`; it does not say that the raw
wall block is defective. The finite lift below is computed from the actual
transport on the two diagonal traceless directions. The other local HTML
edition instead says “Jordan block of size two”. A separate witness shows
why that shorter display needs a nonzero-off-diagonal hypothesis.

No curvature or quotient-manifold statement is asserted here.
-/

namespace B36m7

noncomputable section

open scoped BigOperators

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The transport carried by B36. -/
def transport (T G H : Mat 3) : Mat 3 :=
  T * H + H * T - (2 * Matrix.trace (T * H)) • G

/-- Unnormalised diagonal traceless directions. -/
def H₁ : Mat 3 := Matrix.diagonal ![1, -1, 0]
def H₂ : Mat 3 := Matrix.diagonal ![1, 1, -2]

/-- Diagonal transport weights and a trace-one diagonal Gram matrix. -/
def diagT (t₁ t₂ t₃ : ℝ) : Mat 3 := Matrix.diagonal ![t₁, t₂, t₃]
def interiorG (w₁ s : ℝ) : Mat 3 :=
  Matrix.diagonal ![w₁, 1 - w₁ - s ^ 2, s ^ 2]

/-- The first wall entry of the raw shape block. -/
def wallLambda1 (t₁ t₂ w₁ : ℝ) : ℝ :=
  2 * t₁ * (1 - w₁) + 2 * t₂ * w₁

/-- The upper-right wall entry in the unnormalised `(H₁,H₂)` frame. -/
def wallOff (t₁ t₂ t₃ w₁ : ℝ) : ℝ :=
  2 * (t₁ - t₃ - (t₁ + t₂ - 2 * t₃) * w₁)

/-- The raw shape block with `w₃ = s²`. -/
def rawShape (t₁ t₂ t₃ w₁ s : ℝ) : Mat 2 :=
  !![wallLambda1 t₁ t₂ w₁ + (t₂ - t₁) * s ^ 2,
      wallOff t₁ t₂ t₃ w₁ - (t₁ + t₂ - 2 * t₃) * s ^ 2;
    (t₁ - t₂) * s ^ 2,
      2 * t₃ + (t₁ + t₂ - 2 * t₃) * s ^ 2]

/-- Its analytic lift in the signed amplitude `s = σ₃`. -/
def liftedShape (t₁ t₂ t₃ w₁ s : ℝ) : Mat 2 :=
  !![wallLambda1 t₁ t₂ w₁ + (t₂ - t₁) * s ^ 2,
      s * (wallOff t₁ t₂ t₃ w₁ - (t₁ + t₂ - 2 * t₃) * s ^ 2);
    s * (t₁ - t₂),
      2 * t₃ + (t₁ + t₂ - 2 * t₃) * s ^ 2]

/-- The singular frame `J = diag(1,σ₃)`. -/
def frame (s : ℝ) : Mat 2 := !![1, 0; 0, s]
def frameInv (s : ℝ) : Mat 2 := !![1, 0; 0, s⁻¹]

/-- The Check joint condition at the wall, where `w₂ = 1-w₁`. -/
def JointCondition (t₁ t₂ t₃ w₁ : ℝ) : Prop :=
  t₁ + t₂ - 2 * t₃ = (t₁ - t₂) * (w₁ - (1 - w₁))

lemma trace_H₁ : Matrix.trace H₁ = 0 := by
  norm_num [H₁, Matrix.trace, Fin.sum_univ_three]

lemma trace_H₂ : Matrix.trace H₂ = 0 := by
  norm_num [H₂, Matrix.trace, Fin.sum_univ_three]

lemma trace_interiorG (w₁ s : ℝ) : Matrix.trace (interiorG w₁ s) = 1 := by
  simp [interiorG, Matrix.trace, Fin.sum_univ_three]
  ring

lemma diagT_posDef {t₁ t₂ t₃ : ℝ}
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃) :
    (diagT t₁ t₂ t₃).PosDef := by
  rw [diagT, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> assumption

/-- First raw column, computed from the carried transport. -/
lemma raw_transport_H₁ (t₁ t₂ t₃ w₁ s : ℝ) :
    transport (diagT t₁ t₂ t₃) (interiorG w₁ s) H₁ =
      (wallLambda1 t₁ t₂ w₁ + (t₂ - t₁) * s ^ 2) • H₁ +
      ((t₁ - t₂) * s ^ 2) • H₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, diagT, interiorG, wallLambda1, H₁, H₂,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_three,
      Matrix.diagonal_apply] <;> ring

/-- Second raw column, computed from the carried transport. -/
lemma raw_transport_H₂ (t₁ t₂ t₃ w₁ s : ℝ) :
    transport (diagT t₁ t₂ t₃) (interiorG w₁ s) H₂ =
      (wallOff t₁ t₂ t₃ w₁ - (t₁ + t₂ - 2 * t₃) * s ^ 2) • H₁ +
      (2 * t₃ + (t₁ + t₂ - 2 * t₃) * s ^ 2) • H₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transport, diagT, interiorG, wallOff, H₁, H₂,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_three,
      Matrix.diagonal_apply] <;> ring

/-- Integrated conjugation identity, with no division and hence valid at zero. -/
lemma frame_mul_lifted (t₁ t₂ t₃ w₁ s : ℝ) :
    frame s * liftedShape t₁ t₂ t₃ w₁ s = rawShape t₁ t₂ t₃ w₁ s * frame s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, liftedShape, rawShape, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma frameInv_mul_frame {s : ℝ} (hs : s ≠ 0) : frameInv s * frame s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameInv, frame, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, hs]

lemma frame_mul_frameInv {s : ℝ} (hs : s ≠ 0) : frame s * frameInv s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameInv, frame, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, hs]

/-- Away from the wall the lift really is `J⁻¹ A J`, not merely its Taylor truncation. -/
lemma lifted_eq_inv_raw_mul_frame {s : ℝ} (hs : s ≠ 0)
    (t₁ t₂ t₃ w₁ : ℝ) :
    liftedShape t₁ t₂ t₃ w₁ s =
      frameInv s * rawShape t₁ t₂ t₃ w₁ s * frame s := by
  calc
    liftedShape t₁ t₂ t₃ w₁ s = 1 * liftedShape t₁ t₂ t₃ w₁ s := by simp
    _ = (frameInv s * frame s) * liftedShape t₁ t₂ t₃ w₁ s := by
      rw [frameInv_mul_frame hs]
    _ = frameInv s * (frame s * liftedShape t₁ t₂ t₃ w₁ s) := by
      rw [Matrix.mul_assoc]
    _ = frameInv s * (rawShape t₁ t₂ t₃ w₁ s * frame s) := by
      rw [frame_mul_lifted]
    _ = frameInv s * rawShape t₁ t₂ t₃ w₁ s * frame s := by
      rw [Matrix.mul_assoc]

/-- The joint condition is exactly equality of the two wall eigenvalues. -/
lemma joint_iff_lambda_eq (t₁ t₂ t₃ w₁ : ℝ) :
    JointCondition t₁ t₂ t₃ w₁ ↔ wallLambda1 t₁ t₂ w₁ = 2 * t₃ := by
  unfold JointCondition wallLambda1
  constructor <;> intro h <;> linear_combination h

/-- The official v7 finite lift claim: on the joint condition, `B(0)` is scalar. -/
theorem lifted_zero_eq_scalar_of_joint {t₁ t₂ t₃ w₁ : ℝ}
    (hjoint : JointCondition t₁ t₂ t₃ w₁) :
    liftedShape t₁ t₂ t₃ w₁ 0 = (2 * t₃) • (1 : Mat 2) := by
  have hlam : wallLambda1 t₁ t₂ w₁ = 2 * t₃ :=
    (joint_iff_lambda_eq t₁ t₂ t₃ w₁).mp hjoint
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftedShape, hlam, Matrix.one_apply]

/-- Without the joint condition, the wall lift is still diagonal; the two entries
are simply not identified. -/
lemma lifted_zero (t₁ t₂ t₃ w₁ : ℝ) :
    liftedShape t₁ t₂ t₃ w₁ 0 =
      !![wallLambda1 t₁ t₂ w₁, 0; 0, 2 * t₃] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftedShape]

/-! ### The other local display: its raw Jordan assertion needs another condition -/

/-- Diagonalisability without selecting a library Jordan normal form. -/
def Diagonalizable (A : Mat 2) : Prop :=
  ∃ P D : Mat 2, P.det ≠ 0 ∧ D.IsDiag ∧ A * P = P * D

/-- A rational Gram square root; all retained weights are strictly positive. -/
def Xwall : Mat 3 := Matrix.diagonal ![5 / 13, 12 / 13, 0]
def Gwall : Mat 3 := Xwall.transpose * Xwall

lemma Gwall_eq : Gwall = Matrix.diagonal ![25 / 169, 144 / 169, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Gwall, Xwall, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply]

lemma trace_Gwall : Matrix.trace Gwall = 1 := by
  rw [Gwall_eq]
  norm_num [Matrix.trace, Fin.sum_univ_three]

lemma rank_Gwall : Gwall.rank = 2 := by
  classical
  rw [Gwall_eq, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fin 3 =>
    (![25 / 169, 144 / 169, 0] : Fin 3 → ℝ) x ≠ 0)).card = 2
  have h : (Finset.univ.filter (fun x : Fin 3 =>
      (![25 / 169, 144 / 169, 0] : Fin 3 → ℝ) x ≠ 0)) = {0, 1} := by
    ext x
    fin_cases x <;> norm_num
  rw [h]
  norm_num

lemma wall_weights : (0 : ℝ) < 25 / 169 ∧ (0 : ℝ) < 144 / 169 := by norm_num

lemma scalar_joint_condition : JointCondition 1 1 1 (25 / 169) := by
  norm_num [JointCondition]

lemma transport_one_of_trace_zero {G H : Mat 3} (hH : Matrix.trace H = 0) :
    transport 1 G H = (2 : ℝ) • H := by
  simp [transport, hH, two_smul]

lemma raw_scalar_wall_shape :
    rawShape 1 1 1 (25 / 169) 0 = (2 : ℝ) • (1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rawShape, wallLambda1, wallOff, Matrix.one_apply]

lemma scalar_wall_shape_diagonalizable :
    Diagonalizable (rawShape 1 1 1 (25 / 169) 0) := by
  rw [raw_scalar_wall_shape]
  refine ⟨1, (2 : ℝ) • (1 : Mat 2), by simp,
    Matrix.IsDiag.smul _ Matrix.isDiag_one, by simp⟩

/-- Every stated Carry/Check field coexists with a diagonalisable raw wall block.
This is a boundary case for the historical raw-Jordan display, and simultaneously
an instance of the scalar lift asserted by v7. -/
theorem local_raw_jordan_boundary_witness :
    Gwall = Xwall.transpose * Xwall ∧ Matrix.trace Gwall = 1 ∧ Gwall.rank = 2 ∧
      ((0 : ℝ) < 25 / 169 ∧ (0 : ℝ) < 144 / 169) ∧
      (1 : Mat 3).PosDef ∧ JointCondition 1 1 1 (25 / 169) ∧
      transport 1 Gwall H₁ = (2 : ℝ) • H₁ ∧
      transport 1 Gwall H₂ = (2 : ℝ) • H₂ ∧
      Diagonalizable (rawShape 1 1 1 (25 / 169) 0) := by
  exact ⟨rfl, trace_Gwall, rank_Gwall, wall_weights, Matrix.PosDef.one,
    scalar_joint_condition, transport_one_of_trace_zero trace_H₁,
    transport_one_of_trace_zero trace_H₂, scalar_wall_shape_diagonalizable⟩

/-! ### Straw-man-only nonreal-spectrum control -/

/-- Positive diagonal `T`, but an indefinite trace-one `G`: the Gram and regular
hypotheses are deliberately violated in this control. -/
def weakT : Mat 3 := Matrix.diagonal ![1, 3, 2]
def weakG : Mat 3 := Matrix.diagonal ![1, 1, -1]
def weakShape : Mat 2 := !![4, -2; 2, 4]

lemma weakT_posDef : weakT.PosDef := by
  rw [weakT, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

lemma trace_weakG : Matrix.trace weakG = 1 := by
  norm_num [weakG, Matrix.trace, Fin.sum_univ_three]

lemma det_weakG : weakG.det = -1 := by
  norm_num [weakG, Matrix.det_diagonal, Fin.prod_univ_three]

/-- The indefinite control cannot be a Gram matrix: a Gram determinant is a square. -/
lemma weakG_not_gram : ¬ ∃ X : Mat 3, weakG = X.transpose * X := by
  rintro ⟨X, hX⟩
  have hd : weakG.det = X.det ^ 2 := by
    rw [hX, Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [det_weakG] at hd
  nlinarith [sq_nonneg X.det]

lemma weak_transport_H₁ :
    transport weakT weakG H₁ = (4 : ℝ) • H₁ + (2 : ℝ) • H₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transport, weakT, weakG, H₁, H₂, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_three, Matrix.diagonal_apply]

lemma weak_transport_H₂ :
    transport weakT weakG H₂ = (-2 : ℝ) • H₁ + (4 : ℝ) • H₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transport, weakT, weakG, H₁, H₂, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_three, Matrix.diagonal_apply]

lemma det_weakShape_sub_smul (μ : ℝ) :
    (weakShape - μ • (1 : Mat 2)).det = (μ - 4) ^ 2 + 4 := by
  rw [Matrix.det_fin_two]
  simp [weakShape, Matrix.one_apply]
  ring

/-- The weak shape block has no real eigenvalue at all. -/
theorem weakShape_no_real_eigenvector :
    ¬ ∃ μ : ℝ, ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ weakShape.mulVec v = μ • v := by
  rintro ⟨μ, v, hv, heig⟩
  have hdet : (weakShape - μ • (1 : Mat 2)).det ≠ 0 := by
    rw [det_weakShape_sub_smul]
    nlinarith [sq_nonneg (μ - 4)]
  have hzero : (weakShape - μ • (1 : Mat 2)).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, heig, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hdet hzero)

#print axioms raw_transport_H₁
#print axioms raw_transport_H₂
#print axioms frame_mul_lifted
#print axioms lifted_eq_inv_raw_mul_frame
#print axioms joint_iff_lambda_eq
#print axioms lifted_zero_eq_scalar_of_joint
#print axioms local_raw_jordan_boundary_witness
#print axioms weakT_posDef
#print axioms trace_weakG
#print axioms weakG_not_gram
#print axioms weak_transport_H₁
#print axioms weak_transport_H₂
#print axioms weakShape_no_real_eigenvector

end
end B36m7
end


/-! ## B36 — the real split spectrum of the lifted family

Integrated from `.ultramath/smwwdl7d5/m7/B36Spectrum.lean`.
-/

section
/-!
# B36: real spectrum of the regular diagonal eigenvalue block

For positive `t,g`, the block `2 (D_t - g tᵀ)` is conjugate to a real symmetric
matrix by `diag (sqrt (t_i / g_i))`. Consequently its real characteristic
polynomial splits. No simplicity, interlacing, or boundary Jordan assertion is
included.
-/

namespace B36m7
namespace Spectrum

noncomputable section

open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unnormalised eigenvalue block in the display, including its factor two. -/
def ladder (t g : n → ℝ) : Matrix n n ℝ :=
  (2 : ℝ) • (Matrix.diagonal t - Matrix.of fun i j => g i * t j)

/-- Its symmetric rank-one modification. -/
def ladderSym (t g : n → ℝ) : Matrix n n ℝ :=
  (2 : ℝ) • (Matrix.diagonal t - Matrix.of fun i j =>
    Real.sqrt (t i * g i) * Real.sqrt (t j * g j))

/-- The positive diagonal symmetrising frame. -/
def scale (t g : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal fun i => Real.sqrt (t i / g i)

def scaleInv (t g : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal fun i => (Real.sqrt (t i / g i))⁻¹

lemma scale_pos {t g : n → ℝ} (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) (i : n) :
    0 < Real.sqrt (t i / g i) :=
  Real.sqrt_pos.mpr (div_pos (ht i) (hg i))

lemma sqrt_div_mul (t g : ℝ) (ht : 0 < t) (hg : 0 < g) :
    Real.sqrt (t / g) * g = Real.sqrt (t * g) := by
  have hg0 : Real.sqrt g ≠ 0 := (Real.sqrt_ne_zero').mpr hg
  have hgdiv : g / Real.sqrt g = Real.sqrt g :=
    (div_eq_iff hg0).mpr (Real.mul_self_sqrt hg.le).symm
  rw [Real.sqrt_div ht.le, Real.sqrt_mul ht.le]
  calc
    Real.sqrt t / Real.sqrt g * g = Real.sqrt t * (g / Real.sqrt g) := by ring
    _ = Real.sqrt t * Real.sqrt g := by rw [hgdiv]

lemma sqrt_mul_sqrt_div (t g : ℝ) (ht : 0 < t) (hg : 0 < g) :
    Real.sqrt (t * g) * Real.sqrt (t / g) = t := by
  have hg0 : Real.sqrt g ≠ 0 := (Real.sqrt_ne_zero').mpr hg
  rw [Real.sqrt_mul ht.le, Real.sqrt_div ht.le]
  calc
    Real.sqrt t * Real.sqrt g * (Real.sqrt t / Real.sqrt g) =
        (Real.sqrt t * Real.sqrt t) * (Real.sqrt g / Real.sqrt g) := by ring
    _ = t := by rw [Real.mul_self_sqrt ht.le, div_self hg0, mul_one]

/-- Exact integrated similarity identity. -/
lemma scale_mul_ladder {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    scale t g * ladder t g = ladderSym t g * scale t g := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hsq : Real.sqrt (t i * g i) * Real.sqrt (t i * g i) = t i * g i :=
      Real.mul_self_sqrt (mul_nonneg (ht i).le (hg i).le)
    simp [scale, ladder, ladderSym, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply, hsq]
    ring
  · have h₁ := sqrt_div_mul (t i) (g i) (ht i) (hg i)
    have h₂ := sqrt_mul_sqrt_div (t j) (g j) (ht j) (hg j)
    simp [scale, ladder, ladderSym, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply, hij]
    calc
      Real.sqrt (t i / g i) * (2 * (g i * t j)) =
          2 * ((Real.sqrt (t i / g i) * g i) * t j) := by ring
      _ = 2 * (Real.sqrt (t i * g i) * t j) := by rw [h₁]
      _ = 2 * (Real.sqrt (t i * g i) *
          (Real.sqrt (t j * g j) * Real.sqrt (t j / g j))) := by rw [h₂]
      _ = (2 * (Real.sqrt (t i * g i) * Real.sqrt (t j * g j))) *
          Real.sqrt (t j / g j) := by ring

lemma scaleInv_mul_scale {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    scaleInv t g * scale t g = 1 := by
  rw [scaleInv, scale, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, ne_of_gt (scale_pos ht hg i)]
  · simp [Matrix.diagonal_apply, hij]

lemma scale_mul_scaleInv {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    scale t g * scaleInv t g = 1 := by
  rw [scaleInv, scale, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, ne_of_gt (scale_pos ht hg i)]
  · simp [Matrix.diagonal_apply, hij]

lemma ladder_eq_similarity {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    ladder t g = scaleInv t g * ladderSym t g * scale t g := by
  calc
    ladder t g = 1 * ladder t g := by simp
    _ = (scaleInv t g * scale t g) * ladder t g := by
      rw [scaleInv_mul_scale ht hg]
    _ = scaleInv t g * (scale t g * ladder t g) := by rw [Matrix.mul_assoc]
    _ = scaleInv t g * (ladderSym t g * scale t g) := by
      rw [scale_mul_ladder ht hg]
    _ = scaleInv t g * ladderSym t g * scale t g := by rw [Matrix.mul_assoc]

lemma ladderSym_isHermitian (t g : n → ℝ) : (ladderSym t g).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ladderSym, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · simp [ladderSym, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      hij, Ne.symm hij, mul_comm]

lemma ladder_charpoly_eq {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    (ladder t g).charpoly = (ladderSym t g).charpoly := by
  rw [ladder_eq_similarity ht hg, Matrix.mul_assoc,
    Matrix.charpoly_mul_comm, Matrix.mul_assoc,
    scale_mul_scaleInv ht hg, Matrix.mul_one]

/-- Every algebraic eigenvalue of the regular eigenvalue block is real, expressed
as splitting of its real characteristic polynomial. -/
theorem ladder_charpoly_splits {t g : n → ℝ}
    (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    (ladder t g).charpoly.Splits := by
  rw [ladder_charpoly_eq ht hg]
  exact (ladderSym_isHermitian t g).splits_charpoly

/-- The symmetrised matrix is diagonalisable over `ℝ`, with an explicit real
eigenvalue list supplied by the finite spectral theorem. -/
lemma ladderSym_charpoly_eq (t g : n → ℝ) :
    (ladderSym t g).charpoly = ∏ i,
      (Polynomial.X - Polynomial.C ((ladderSym_isHermitian t g).eigenvalues i : ℝ)) := by
  exact (ladderSym_isHermitian t g).charpoly_eq

#print axioms sqrt_div_mul
#print axioms sqrt_mul_sqrt_div
#print axioms scale_mul_ladder
#print axioms ladder_eq_similarity
#print axioms ladderSym_isHermitian
#print axioms ladder_charpoly_eq
#print axioms ladder_charpoly_splits
#print axioms ladderSym_charpoly_eq

end
end Spectrum
end B36m7
end


/-! ## B70 — the diabolical and exceptional gaps, and the geometric fit that recovers them

Integrated from `.ultramath/smwwdl7d5/m6/B70Kernel.lean`.
-/

section
/-!
# B70: finite positive kernels

The fold counterexample in `B70StrongRefutation.lean` concerns the metric half.
This file records what does survive in the two generic spectral normal forms and
in the prescribed geometric-sequence exponent test.  These are finite matrix
and logarithm calculations, not a proof of a general perturbation theorem.
-/

namespace B70Kernel

noncomputable section

/-- A real symmetric two-parameter diabolical normal form. -/
def diabolical (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, -a]

/-- Its characteristic determinant is `l² = a²+b²`. -/
theorem diabolical_charpoly (a b l : ℝ) :
    (diabolical a b - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = l ^ 2 - (a ^ 2 + b ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [diabolical]
  ring

/-- The two eigenvalue branches are `±√(a²+b²)`, hence their gap is radial and linear. -/
theorem diabolical_spectral_root_iff {a b l : ℝ} (hnonneg : 0 ≤ a ^ 2 + b ^ 2) :
    (diabolical a b - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      l = Real.sqrt (a ^ 2 + b ^ 2) ∨ l = -Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [diabolical_charpoly]
  have hs : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hnonneg
  constructor
  · intro h
    have hfac : (l - Real.sqrt (a ^ 2 + b ^ 2)) *
        (l + Real.sqrt (a ^ 2 + b ^ 2)) = 0 := by
      rw [← h]
      nlinarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl)
    · nlinarith
    · nlinarith

/-- The spectral gap of the diabolical normal form is exactly twice radial distance. -/
theorem diabolical_gap (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) - (-Real.sqrt (a ^ 2 + b ^ 2)) =
      2 * Real.sqrt (a ^ 2 + b ^ 2) := by ring

/-- At the diabolical point the matrix itself is zero, so its geometric nullity is two. -/
theorem diabolical_at_zero : diabolical 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diabolical]

/-- The order-two square-root exceptional normal form over real parameter `r ≥ 0`. -/
def exceptional (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; r, 0]

/-- Its characteristic determinant is `l²-r`. -/
theorem exceptional_charpoly (r l : ℝ) :
    (exceptional r - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = l ^ 2 - r := by
  rw [Matrix.det_fin_two]
  simp [exceptional]
  ring

/-- For `r ≥ 0`, the two real spectral roots are exactly `±√r`. -/
theorem exceptional_spectral_root_iff {r l : ℝ} (hr : 0 ≤ r) :
    (exceptional r - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      l = Real.sqrt r ∨ l = -Real.sqrt r := by
  rw [exceptional_charpoly]
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
  constructor
  · intro h
    have hfac : (l - Real.sqrt r) * (l + Real.sqrt r) = 0 := by
      rw [← h]
      nlinarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl)
    · nlinarith
    · nlinarith

/-- The exceptional normal form has gap exactly `2√r`. -/
theorem exceptional_gap (r : ℝ) :
    Real.sqrt r - (-Real.sqrt r) = 2 * Real.sqrt r := by ring

/-- At `r=0` the exceptional matrix is nonzero but squares to zero. -/
theorem exceptional_at_zero_sq : exceptional 0 ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exceptional, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- In particular the coalescence is defective rather than the zero (two-dimensional kernel) matrix. -/
theorem exceptional_at_zero_ne : exceptional 0 ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [exceptional] at hentry

/-- Its kernel is the one-dimensional line `v₁ = 0`, not the whole plane. -/
theorem exceptional_at_zero_kernel_iff (v : Fin 2 → ℝ) :
    Matrix.mulVec (exceptional 0) v = 0 ↔ v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [exceptional, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro hv
    funext i
    fin_cases i <;> simp [exceptional, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv]

/-- A two-sample logarithmic slope on distances `r` and `q*r`. -/
def twoPointExponent (r q gr gqr : ℝ) : ℝ :=
  (Real.log gqr - Real.log gr) / (Real.log (q * r) - Real.log r)

/-- For an exact power law, a geometric two-point fit recovers its exponent exactly. -/
theorem twoPointExponent_power_law {r q c p : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≠ 1) (hc : 0 < c) :
    twoPointExponent r q (c * r ^ p) (c * (q * r) ^ p) = p := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hqr : 0 < q * r := mul_pos hq hr
  have hlog : Real.log q ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq hq1
  have hpr : r ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr p)
  have hpqr : (q * r) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hqr p)
  rw [twoPointExponent, Real.log_mul hc0 hpr, Real.log_mul hc0 hpqr,
    Real.log_rpow hqr, Real.log_rpow hr, Real.log_mul hq0 hr0]
  have hcancel : Real.log q + Real.log r - Real.log r = Real.log q := by ring
  rw [hcancel]
  field_simp [hlog]
  ring

/-- The linear generic diabolical law is recovered as exponent one. -/
theorem geometric_fit_diabolical {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≠ 1) :
    twoPointExponent r q (2 * r) (2 * (q * r)) = 1 := by
  simpa using twoPointExponent_power_law hr hq hq1 (by norm_num : (0 : ℝ) < 2) (p := (1 : ℝ))

/-- The square-root generic exceptional law is recovered as exponent one half. -/
theorem geometric_fit_exceptional {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≠ 1) :
    twoPointExponent r q (2 * Real.sqrt r) (2 * Real.sqrt (q * r)) = 1 / 2 := by
  have h := twoPointExponent_power_law hr hq hq1 (by norm_num : (0 : ℝ) < 2) (p := (1 / 2 : ℝ))
  simpa only [Real.sqrt_eq_rpow] using h

#print axioms diabolical
#print axioms diabolical_charpoly
#print axioms diabolical_spectral_root_iff
#print axioms diabolical_gap
#print axioms diabolical_at_zero
#print axioms exceptional
#print axioms exceptional_charpoly
#print axioms exceptional_spectral_root_iff
#print axioms exceptional_gap
#print axioms exceptional_at_zero_sq
#print axioms exceptional_at_zero_ne
#print axioms exceptional_at_zero_kernel_iff
#print axioms twoPointExponent
#print axioms twoPointExponent_power_law
#print axioms geometric_fit_diabolical
#print axioms geometric_fit_exceptional

end
end B70Kernel
end


/-! ## B70 — an across-kernel fold whose projector does not vary

Integrated from `.ultramath/smwwdl7d5/m6/B70StrongRefutation.lean`.
-/

section
/-!
# B70: a generic fold with across-kernel and constant kernel projector

This is a counterexample to the card's own metric assertion `across : Π varies`.
The map is the ordinary quadratic fold `(x,y) ↦ (x,y²)`.  Its wall is `y = 0`,
its wall kernel is the `y`-axis (across the wall), the image of the wall is the
`x`-axis, and the orthogonal kernel projector is constantly `diag(0,1)` on the
wall.  Nothing here is a higher-order tangency: away from `y = 0` the derivative
is invertible, while on the wall its kernel is one-dimensional.
-/

namespace B70Strong

open scoped Matrix.Norms.Frobenius

noncomputable section

/-- The standard fold, with wall `y = 0`. -/
def fold (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 ^ 2)

/-- Its Fréchet derivative. -/
def foldDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The proposed derivative really is the Fréchet derivative of the fold. -/
theorem hasFDerivAt_fold (p : ℝ × ℝ) :
    HasFDerivAt fold (foldDerivative p) p := by
  have h₁ : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have h₂ : HasFDerivAt (fun q : ℝ × ℝ => q.2 ^ 2)
      ((2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    simpa [two_mul] using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2
  exact h₁.prodMk h₂

@[simp] theorem foldDerivative_apply (p v : ℝ × ℝ) :
    foldDerivative p v = (v.1, 2 * p.2 * v.2) := rfl

/-- The standard Euclidean inner product on the parameter/target plane. -/
def planeDot (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- The pullback metric is `diag(1,(2y)²)`; this is not an arbitrary metric assigned to the fold. -/
theorem fold_pullback_metric (p v w : ℝ × ℝ) :
    planeDot (foldDerivative p v) (foldDerivative p w) =
      v.1 * w.1 + (2 * p.2) ^ 2 * (v.2 * w.2) := by
  simp only [foldDerivative_apply, planeDot]
  ring

/-- The kernel on every point of the wall is exactly the transverse `y`-axis. -/
theorem wall_kernel_iff (x : ℝ) (v : ℝ × ℝ) :
    foldDerivative (x, 0) v = 0 ↔ ∃ c : ℝ, v = (0, c) := by
  constructor
  · intro h
    refine ⟨v.2, ?_⟩
    apply Prod.ext
    · simpa using congrArg Prod.fst h
    · rfl
  · rintro ⟨c, rfl⟩
    apply Prod.ext <;> simp

/-- The wall kernel contains the transverse vector `(0,1)`. -/
theorem transverse_vector_in_wall_kernel (x : ℝ) :
    foldDerivative (x, 0) (0, 1) = 0 := by
  rw [wall_kernel_iff]
  exact ⟨1, rfl⟩

/-- That kernel vector is not tangent to the wall `{(x,0)}`. -/
theorem transverse_vector_not_tangent :
    ¬ ∃ c : ℝ, ((0 : ℝ), (1 : ℝ)) = (c, 0) := by
  rintro ⟨c, h⟩
  have := congrArg Prod.snd h
  norm_num at this

/-- Away from the wall the fold has trivial kernel, hence full rank in dimension two. -/
theorem off_wall_kernel_trivial {p v : ℝ × ℝ} (hp : p.2 ≠ 0)
    (h : foldDerivative p v = 0) : v = 0 := by
  have h₁ : v.1 = 0 := congrArg Prod.fst h
  have h₂ : 2 * p.2 * v.2 = 0 := congrArg Prod.snd h
  have hv₂ : v.2 = 0 := by
    apply (mul_eq_zero.mp h₂).resolve_left
    exact mul_ne_zero (by norm_num) hp
  apply Prod.ext <;> assumption

/-- The orthogonal projector onto the wall kernel at wall parameter `x`. -/
def wallProjectorAt (_x : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem wallProjectorAt_apply (x : ℝ) (v : ℝ × ℝ) :
    wallProjectorAt x v = (0, v.2) := rfl

/-- This projector is idempotent at every wall point. -/
theorem wallProjectorAt_idempotent (x : ℝ) (v : ℝ × ℝ) :
    wallProjectorAt x (wallProjectorAt x v) = wallProjectorAt x v := by
  apply Prod.ext <;> simp

/-- Its fixed-point set is precisely the wall kernel at every wall point. -/
theorem wallProjectorAt_fixed_iff_mem_kernel (x : ℝ) (v : ℝ × ℝ) :
    wallProjectorAt x v = v ↔ foldDerivative (x, 0) v = 0 := by
  rw [wall_kernel_iff]
  constructor
  · intro h
    refine ⟨v.2, ?_⟩
    exact h.symm
  · rintro ⟨c, rfl⟩
    apply Prod.ext <;> simp

/-- The kernel projector does not vary between any two points of the degenerate locus. -/
theorem projector_constant_along_wall (x y : ℝ) :
    wallProjectorAt x = wallProjectorAt y := rfl

/-- The matrix form of the kernel projector at wall parameter `x`. -/
def wallProjectorMatrixAt (_x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- The Frobenius norm of the projector difference between any two wall points vanishes. -/
theorem wall_projector_delta_norm (x y : ℝ) :
    ‖wallProjectorMatrixAt x - wallProjectorMatrixAt y‖ = 0 := by
  simp [wallProjectorMatrixAt]

/-- The wall is not collapsed to one point: its image contains two distinct points. -/
theorem wall_image_nonconstant :
    fold (0, 0) ≠ fold (1, 0) := by
  norm_num [fold]

/-- The two wall points above are distinct and both lie on the wall. -/
theorem wall_image_curve_witness :
    fold (0, 0) = (0, 0) ∧ fold (1, 0) = (1, 0) ∧ (0 : ℝ) ≠ 1 := by
  norm_num [fold]

/-- The nonzero collapsed eigenvalue is exactly quadratic in transverse distance. -/
def collapsedMetricEigenvalue (p : ℝ × ℝ) : ℝ := (2 * p.2) ^ 2

/-- At transverse distance `|y|`, the collapsed eigenvalue is `4|y|²`. -/
theorem collapsedMetricEigenvalue_apply (y : ℝ) :
    collapsedMetricEigenvalue (0, y) = 4 * |y| ^ 2 := by
  simp only [collapsedMetricEigenvalue]
  rw [sq_abs]
  ring

/-- At two distinct wall points the Frobenius projector difference is zero, not a nonzero linear ramp. -/
theorem no_nonconstant_linear_projector_variation :
    ∃ x y : ℝ, x ≠ y ∧ ‖wallProjectorMatrixAt x - wallProjectorMatrixAt y‖ = 0 := by
  exact ⟨0, 1, by norm_num, wall_projector_delta_norm 0 1⟩

/-- No positive constant can be a linear lower envelope for the identically zero projector difference. -/
theorem wall_projector_below_every_positive_linear_bound (c : ℝ) (hc : 0 < c) :
    ∃ x y : ℝ, x ≠ y ∧ ‖wallProjectorMatrixAt x - wallProjectorMatrixAt y‖ < c * |x - y| := by
  refine ⟨0, 1, by norm_num, ?_⟩
  simpa [wallProjectorMatrixAt] using hc

#print axioms fold
#print axioms foldDerivative
#print axioms hasFDerivAt_fold
#print axioms foldDerivative_apply
#print axioms planeDot
#print axioms fold_pullback_metric
#print axioms wall_kernel_iff
#print axioms transverse_vector_in_wall_kernel
#print axioms transverse_vector_not_tangent
#print axioms off_wall_kernel_trivial
#print axioms wallProjectorAt
#print axioms wallProjectorAt_apply
#print axioms wallProjectorAt_idempotent
#print axioms wallProjectorAt_fixed_iff_mem_kernel
#print axioms projector_constant_along_wall
#print axioms wallProjectorMatrixAt
#print axioms wall_projector_delta_norm
#print axioms wall_image_nonconstant
#print axioms wall_image_curve_witness
#print axioms collapsedMetricEigenvalue
#print axioms collapsedMetricEigenvalue_apply
#print axioms no_nonconstant_linear_projector_variation
#print axioms wall_projector_below_every_positive_linear_bound

end
end B70Strong
end


/-! ## B70 — an along-kernel coordinate pole whose projector does vary

Integrated from `.ultramath/smwwdl7d5/m6/B70StrongCurvedPole.lean`.
-/

section
/-!
# B70: an along-kernel coordinate pole whose kernel projector varies

This is a second, independent counterexample to the card's own metric claim,
this time to `along ⇒ Π constant`.  Unlike the fold, its projector variation is
nonzero (and is locally linear near `x=0`), so an objection about fitting the
logarithm of an identically zero observable does not apply.
-/

namespace B70CurvedPole

open scoped Matrix.Norms.Frobenius

noncomputable section

/-- A polynomial coordinate pole: the parabola `y=x²` is collapsed to the origin. -/
def curvedPole (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2 - p.1 ^ 2, p.1 * p.2 - p.1 ^ 3)

/-- Its Fréchet derivative. -/
def curvedPoleDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
      (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (p.2 - 3 * p.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The displayed polynomial derivative is the actual Fréchet derivative. -/
theorem hasFDerivAt_curvedPole (p : ℝ × ℝ) :
    HasFDerivAt curvedPole (curvedPoleDerivative p) p := by
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h₁ : HasFDerivAt (fun q : ℝ × ℝ => q.2 - q.1 ^ 2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ -
        (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    convert hy.sub (hx.pow 2) using 1 <;> simp [two_mul]
  have h₂ : HasFDerivAt (fun q : ℝ × ℝ => q.1 * q.2 - q.1 ^ 3)
      (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
        (p.2 - 3 * p.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    convert (hx.mul hy).sub (hx.pow 3) using 1 <;>
      ext v <;> simp [sub_apply, add_apply] <;> ring
  exact h₁.prodMk h₂

@[simp] theorem curvedPoleDerivative_apply (p v : ℝ × ℝ) :
    curvedPoleDerivative p v =
      (v.2 - 2 * p.1 * v.1, p.1 * v.2 + (p.2 - 3 * p.1 ^ 2) * v.1) := by
  apply Prod.ext <;> simp [curvedPoleDerivative] <;> ring

/-- On the parabolic locus the kernel is exactly its tangent line `v₂=2xv₁`. -/
theorem pole_wall_kernel_iff (x : ℝ) (v : ℝ × ℝ) :
    curvedPoleDerivative (x, x ^ 2) v = 0 ↔ ∃ c : ℝ, v = (c, 2 * x * c) := by
  constructor
  · intro h
    have h₁ : v.2 - 2 * x * v.1 = 0 := by
      simpa using congrArg Prod.fst h
    refine ⟨v.1, Prod.ext rfl ?_⟩
    simp only [Prod.snd]
    linarith
  · rintro ⟨c, rfl⟩
    apply Prod.ext <;> simp [curvedPoleDerivative_apply] <;> ring

/-- The tangent vector to the locus is in the kernel. -/
theorem pole_tangent_in_kernel (x : ℝ) :
    curvedPoleDerivative (x, x ^ 2) (1, 2 * x) = 0 := by
  rw [pole_wall_kernel_iff]
  exact ⟨1, by simp⟩

/-- The whole connected parabolic locus is sent to one point. -/
theorem pole_wall_image_constant (x : ℝ) : curvedPole (x, x ^ 2) = 0 := by
  apply Prod.ext <;> simp [curvedPole] <;> ring

/-- In particular, two different parameters of the locus have the same image. -/
theorem pole_two_wall_points_collapse :
    curvedPole (0, 0) = curvedPole (1, 1) := by
  norm_num [curvedPole]

/-- Away from the parabolic locus the derivative has trivial kernel, hence full rank in dimension two. -/
theorem pole_off_wall_kernel_trivial {p v : ℝ × ℝ} (hp : p.2 - p.1 ^ 2 ≠ 0)
    (h : curvedPoleDerivative p v = 0) : v = 0 := by
  have h₁ : v.2 - 2 * p.1 * v.1 = 0 := by
    simpa using congrArg Prod.fst h
  have h₂ : p.1 * v.2 + (p.2 - 3 * p.1 ^ 2) * v.1 = 0 := by
    simpa using congrArg Prod.snd h
  have hs : (p.2 - p.1 ^ 2) * v.1 = 0 := by
    calc
      (p.2 - p.1 ^ 2) * v.1 =
          p.1 * v.2 + (p.2 - 3 * p.1 ^ 2) * v.1 -
            p.1 * (v.2 - 2 * p.1 * v.1) := by ring
      _ = 0 := by rw [h₂, h₁]; ring
  have hu : v.1 = 0 := (mul_eq_zero.mp hs).resolve_left hp
  have hv : v.2 = 0 := by rw [hu] at h₁; simpa using h₁
  apply Prod.ext <;> assumption

/-- The orthogonal projector onto the tangent kernel at wall parameter `x`. -/
def poleKernelProjector (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (1 + 4 * x ^ 2)) • !![1, 2 * x; 2 * x, 4 * x ^ 2]

/-- This matrix is symmetric. -/
theorem poleKernelProjector_symmetric (x : ℝ) :
    (poleKernelProjector x).transpose = poleKernelProjector x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [poleKernelProjector, Matrix.transpose_apply]

/-- The denominator in the projector is always nonzero. -/
theorem pole_denominator_ne_zero (x : ℝ) : 1 + 4 * x ^ 2 ≠ 0 := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-- The matrix is idempotent, hence a genuine projector. -/
theorem poleKernelProjector_idempotent (x : ℝ) :
    poleKernelProjector x * poleKernelProjector x = poleKernelProjector x := by
  have hd := pole_denominator_ne_zero x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [poleKernelProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hd] <;> ring

/-- It fixes the tangent vector `(1,2x)`. -/
theorem poleKernelProjector_on_tangent (x : ℝ) :
    Matrix.mulVec (poleKernelProjector x) ![1, 2 * x] = ![1, 2 * x] := by
  have hd := pole_denominator_ne_zero x
  funext i
  fin_cases i <;> simp [poleKernelProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [hd] <;> ring

/-- It kills the orthogonal normal `(2x,-1)`. -/
theorem poleKernelProjector_on_normal (x : ℝ) :
    Matrix.mulVec (poleKernelProjector x) ![2 * x, -1] = 0 := by
  have hd := pole_denominator_ne_zero x
  funext i
  fin_cases i <;> simp [poleKernelProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp [hd] <;> ring

/-- The off-diagonal projector entry has nonzero first-order variation near `x=0`. -/
theorem poleKernelProjector_off_diagonal (x : ℝ) :
    poleKernelProjector x 0 1 - poleKernelProjector 0 0 1 = 2 * x / (1 + 4 * x ^ 2) := by
  simp [poleKernelProjector, div_eq_mul_inv, mul_comm]

/-- The along-kernel projector is not constant on the collapsed locus. -/
theorem poleKernelProjector_not_constant : poleKernelProjector 0 ≠ poleKernelProjector 1 := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [poleKernelProjector] at he

/-- Consequently its Frobenius difference between wall parameters zero and one is nonzero. -/
theorem poleKernelProjector_delta_nonzero :
    ‖poleKernelProjector 0 - poleKernelProjector 1‖ ≠ 0 := by
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr poleKernelProjector_not_constant)

#print axioms curvedPole
#print axioms curvedPoleDerivative
#print axioms hasFDerivAt_curvedPole
#print axioms curvedPoleDerivative_apply
#print axioms pole_wall_kernel_iff
#print axioms pole_tangent_in_kernel
#print axioms pole_wall_image_constant
#print axioms pole_two_wall_points_collapse
#print axioms pole_off_wall_kernel_trivial
#print axioms poleKernelProjector
#print axioms poleKernelProjector_symmetric
#print axioms pole_denominator_ne_zero
#print axioms poleKernelProjector_idempotent
#print axioms poleKernelProjector_on_tangent
#print axioms poleKernelProjector_on_normal
#print axioms poleKernelProjector_off_diagonal
#print axioms poleKernelProjector_not_constant
#print axioms poleKernelProjector_delta_nonzero

end
end B70CurvedPole
end


/-! ## B70 — the higher-order tangency, excluded by the card itself

Integrated from `.ultramath/smwwdl7d5/m6/B70WeakReadingRefutation.lean`.
-/

section
/-!
# B70: a refutation of an INVENTED, unqualified spectral reading

This file is deliberately labelled `WeakReading`.  It refutes only the assertion
that *every* exceptional point has square-root gap exponent.  The actual card's
Closed field says: “Higher-order tangencies give other exponents (B90); the two
shown are the generic ones.”  The quadratic parameter substitution below is
exactly such a higher-order example, so this is NOT a refutation of the card.
-/

namespace B70WeakReading

noncomputable section

/-- An order-two exceptional matrix whose parameter is already quadratic in `r`. -/
def higherOrderExceptional (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; r ^ 2, 0]

/-- Its characteristic determinant is `l²-r²`, with roots `±r`, not `±√r`. -/
theorem higherOrder_charpoly (r l : ℝ) :
    (higherOrderExceptional r - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = l ^ 2 - r ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [higherOrderExceptional]
  ring

/-- The two real spectral roots are exactly `r` and `-r`. -/
theorem higherOrder_spectral_root_iff (r l : ℝ) :
    (higherOrderExceptional r - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      l = r ∨ l = -r := by
  rw [higherOrder_charpoly]
  constructor
  · intro h
    have hfac : (l - r) * (l + r) = 0 := by
      rw [← h]
      ring
    rcases mul_eq_zero.mp hfac with h' | h'
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> ring

/-- For nonnegative `r`, the gap is `2r`. -/
theorem higherOrder_gap (r : ℝ) : r - (-r) = 2 * r := by ring

/-- At zero this is a nonzero two-step nilpotent matrix, hence genuinely exceptional. -/
theorem higherOrder_at_zero_sq : higherOrderExceptional 0 ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higherOrderExceptional, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- It is not the zero matrix, so the kernel has not retained dimension two. -/
theorem higherOrder_at_zero_ne : higherOrderExceptional 0 ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [higherOrderExceptional] at hentry

/-- The kernel at zero is exactly the one-dimensional line `v₁ = 0`. -/
theorem higherOrder_at_zero_kernel_iff (v : Fin 2 → ℝ) :
    Matrix.mulVec (higherOrderExceptional 0) v = 0 ↔ v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [higherOrderExceptional, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro hv
    funext i
    fin_cases i <;>
      simp [higherOrderExceptional, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv]

/-- The exponent returned by two samples at distances `r` and `q*r` for this family. -/
def weakFittedExponent (r q : ℝ) : ℝ :=
  (Real.log (2 * (q * r)) - Real.log (2 * r)) /
    (Real.log (q * r) - Real.log r)

/-- On every positive geometric two-sample test, this family reports exponent one. -/
theorem higherOrder_fitted_exponent {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≠ 1) : weakFittedExponent r q = 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hlog : Real.log q ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq hq1
  have hcomm : 2 * (q * r) = q * (2 * r) := by ring
  rw [weakFittedExponent, hcomm, Real.log_mul hq0 hr0,
    Real.log_mul hq0 (mul_ne_zero (by norm_num) hr0)]
  have hn : Real.log q + Real.log (2 * r) - Real.log (2 * r) = Real.log q := by ring
  have hd : Real.log q + Real.log r - Real.log r = Real.log q := by ring
  rw [hn, hd]
  exact div_self hlog

/-- In particular, the fitted exponent is not the displayed generic exponent `1/2`. -/
theorem higherOrder_exponent_not_one_half {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≠ 1) : weakFittedExponent r q ≠ 1 / 2 := by
  rw [higherOrder_fitted_exponent hr hq hq1]
  norm_num

/-- A concrete replay on the geometric pair `r=1`, `q=1/4`. -/
theorem concrete_geometric_replay :
    weakFittedExponent 1 (1 / 4) = 1 ∧ weakFittedExponent 1 (1 / 4) ≠ 1 / 2 := by
  have hr : (0 : ℝ) < 1 := by norm_num
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hq1 : (1 / 4 : ℝ) ≠ 1 := by norm_num
  exact ⟨higherOrder_fitted_exponent hr hq hq1, higherOrder_exponent_not_one_half hr hq hq1⟩

#print axioms higherOrderExceptional
#print axioms higherOrder_charpoly
#print axioms higherOrder_spectral_root_iff
#print axioms higherOrder_gap
#print axioms higherOrder_at_zero_sq
#print axioms higherOrder_at_zero_ne
#print axioms higherOrder_at_zero_kernel_iff
#print axioms weakFittedExponent
#print axioms higherOrder_fitted_exponent
#print axioms higherOrder_exponent_not_one_half
#print axioms concrete_geometric_replay

end
end B70WeakReading
end


/-! ## B70 — the same across-fold, independently, with the operator gap

Integrated from `.ultramath/smwwdl7d5/m12/B70FoldCounterexample.lean`.
-/

section
/-!
# B70: the ordinary fold is a counterexample to `across : Π varies`

The display's prose says that when the kernel points across the locus,
“the projector varies along it”; its figure says “across : Π varies”.
For `F(x,y) = (x,y²)`, the wall is `y = 0`, the kernel is the transverse
`y`-axis, and that kernel and its orthogonal projector are constant in
the wall coordinate `x`. The wall image `(x,0)` is not one point.
-/

namespace B70Fold

/-- The ordinary fold, whose stable wall singularity is quadratic. -/
def fold (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 ^ 2)

/-- The derivative of the fold at any point with second coordinate `y`. -/
def foldD (y : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((2 * y) • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem foldD_apply (y : ℝ) (v : ℝ × ℝ) :
    foldD y v = (v.1, 2 * y * v.2) := rfl

/-- The displayed linear map really is the derivative, not an invented
metric kernel. -/
theorem hasFDerivAt_fold (p : ℝ × ℝ) :
    HasFDerivAt fold (foldD p.2) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have h := hf.prodMk (hs.pow 2)
  change HasFDerivAt (fun q : ℝ × ℝ => (q.1, q.2 ^ 2)) (foldD p.2) p
  convert h using 1
  ext <;> simp [foldD, two_smul, two_mul]

/-- The wall kernel is exactly the transverse `y`-axis. -/
theorem wall_kernel_iff (v : ℝ × ℝ) : foldD 0 v = 0 ↔ v.1 = 0 := by
  constructor
  · intro h
    have hv := congrArg Prod.fst h
    simpa [foldD] using hv
  · intro hv
    apply Prod.ext
    · simpa [foldD] using hv
    · simp [foldD]

/-- The tangent to the wall is not in the kernel. -/
theorem wall_tangent_not_in_kernel : foldD 0 (1, 0) ≠ 0 := by
  intro h
  have hv := congrArg Prod.fst h
  norm_num [foldD] at hv

/-- The transverse direction is in the wall kernel. -/
theorem transverse_in_wall_kernel : foldD 0 (0, 1) = 0 := by
  apply Prod.ext <;> norm_num [foldD]

/-- Off the wall, the fold differential has trivial kernel. -/
theorem off_wall_kernel_trivial {y : ℝ} (hy : y ≠ 0) (v : ℝ × ℝ) :
    foldD y v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hv0 : v.1 = 0 := by
      have hh := congrArg Prod.fst h
      simpa [foldD] using hh
    have hprod : 2 * y * v.2 = 0 := by
      have hh := congrArg Prod.snd h
      simpa [foldD] using hh
    have hv1 : v.2 = 0 := by
      rcases mul_eq_zero.mp hprod with h2y | hv1
      · exact False.elim ((mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hy) h2y)
      · exact hv1
    exact Prod.ext hv0 hv1
  · rintro rfl
    exact map_zero (foldD y)

/-- The coordinate projector onto the wall kernel. The unused argument
is the coordinate along the wall, making constancy explicit. -/
def wallProjector (_x : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem wallProjector_apply (x : ℝ) (v : ℝ × ℝ) :
    wallProjector x v = (0, v.2) := rfl

theorem wallProjector_idempotent (x : ℝ) :
    (wallProjector x).comp (wallProjector x) = wallProjector x := by
  ext <;> rfl

/-- The range of the constant projector is exactly the wall kernel. -/
theorem wallProjector_range (x : ℝ) (v : ℝ × ℝ) :
    wallProjector x v = v ↔ foldD 0 v = 0 := by
  rw [wall_kernel_iff]
  constructor
  · intro h
    have hv : (0 : ℝ) = v.1 := by
      simpa [wallProjector] using congrArg Prod.fst h
    exact hv.symm
  · intro hv
    apply Prod.ext <;> simp [wallProjector, hv]

/-- This is the literal negation of the display's “across : Π varies”:
all projectors along the wall are definitionally equal. -/
theorem projector_constant_along_wall (x z : ℝ) :
    wallProjector x = wallProjector z := rfl

/-- In norm form, the wall-projector difference is exactly zero. -/
theorem projector_delta_norm (x z : ℝ) :
    ‖wallProjector x - wallProjector z‖ = 0 := by
  rw [projector_constant_along_wall x z, sub_self, norm_zero]

/-- The wall is not collapsed to one point in the target. -/
theorem wall_image_nonconstant : fold (0, 0) ≠ fold (1, 0) := by
  norm_num [fold]

/-- The smaller pullback-metric eigenvalue: the squared second component
of the differential. It is exactly quadratic, not a higher tangency. -/
def collapsedMetricEigenvalue (y : ℝ) : ℝ := 4 * y ^ 2

/-- The Euclidean pullback quadratic form `Jv · Jw`. -/
def pullbackMetric (y : ℝ) (v w : ℝ × ℝ) : ℝ :=
  (foldD y v).1 * (foldD y w).1 + (foldD y v).2 * (foldD y w).2

theorem pullbackMetric_formula (y : ℝ) (v w : ℝ × ℝ) :
    pullbackMetric y v w =
      v.1 * w.1 + collapsedMetricEigenvalue y * v.2 * w.2 := by
  simp only [pullbackMetric, foldD_apply, collapsedMetricEigenvalue]
  ring

theorem pullbackMetric_nonneg (y : ℝ) (v : ℝ × ℝ) :
    0 ≤ pullbackMetric y v v := by
  simp only [pullbackMetric, foldD_apply]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem collapsedMetricEigenvalue_eq_norm_sq (y : ℝ) :
    collapsedMetricEigenvalue y = ‖(foldD y) (0, 1)‖ ^ 2 := by
  simp [collapsedMetricEigenvalue, foldD, Real.norm_eq_abs]
  nlinarith [sq_abs y]



/-- A concrete Hermitian diagonal operator family supplies the operator
side of Carry. Its two eigenvalues are `y` and `-y`. -/
def diagonalOperator (y : ℝ) (v : ℝ × ℝ) : ℝ × ℝ := (y * v.1, -y * v.2)

/-- Real symmetry, written directly in the coordinate inner product. -/
theorem diagonalOperator_symmetric (y : ℝ) (u v : ℝ × ℝ) :
    (diagonalOperator y u).1 * v.1 + (diagonalOperator y u).2 * v.2 =
      u.1 * (diagonalOperator y v).1 + u.2 * (diagonalOperator y v).2 := by
  simp only [diagonalOperator]
  ring

theorem diagonalOperator_wall (v : ℝ × ℝ) : diagonalOperator 0 v = 0 := by
  apply Prod.ext <;> simp [diagonalOperator]

theorem diagonalOperator_eigenvector_zero (y : ℝ) :
    diagonalOperator y (1, 0) = y • ((1, 0) : ℝ × ℝ) := by
  apply Prod.ext <;> simp [diagonalOperator]

theorem diagonalOperator_eigenvector_one (y : ℝ) :
    diagonalOperator y (0, 1) = (-y) • ((0, 1) : ℝ × ℝ) := by
  apply Prod.ext <;> simp [diagonalOperator]

/-- At positive distance `r`, the spectral gap is exact amplitude two
times the first power. -/
def operatorGap (r : ℝ) : ℝ := 2 * |r|

theorem operatorGap_linear {r : ℝ} (hr : 0 < r) :
    operatorGap r = 2 * r ^ 1 := by
  simp [operatorGap, abs_of_pos hr]

/-- Packaging of the faithful metric refutation: transverse kernel,
constant wall projector, nonconstant wall image and quadratic collapse. -/
theorem across_kernel_with_constant_projector :
    foldD 0 (0, 1) = 0 ∧
      foldD 0 (1, 0) ≠ 0 ∧
      (∀ x z : ℝ, wallProjector x = wallProjector z) ∧
      fold (0, 0) ≠ fold (1, 0) ∧
      ∀ y : ℝ, collapsedMetricEigenvalue y = 4 * y ^ 2 := by
  exact ⟨transverse_in_wall_kernel, wall_tangent_not_in_kernel,
    projector_constant_along_wall, wall_image_nonconstant,
    fun _ => rfl⟩

#print axioms B70Fold.foldD_apply
#print axioms B70Fold.hasFDerivAt_fold
#print axioms B70Fold.wall_kernel_iff
#print axioms B70Fold.wall_tangent_not_in_kernel
#print axioms B70Fold.transverse_in_wall_kernel
#print axioms B70Fold.off_wall_kernel_trivial
#print axioms B70Fold.wallProjector_idempotent
#print axioms B70Fold.wallProjector_range
#print axioms B70Fold.projector_constant_along_wall
#print axioms B70Fold.projector_delta_norm
#print axioms B70Fold.wall_image_nonconstant
#print axioms B70Fold.pullbackMetric_formula
#print axioms B70Fold.pullbackMetric_nonneg
#print axioms B70Fold.collapsedMetricEigenvalue_eq_norm_sq
#print axioms B70Fold.diagonalOperator_symmetric
#print axioms B70Fold.diagonalOperator_wall
#print axioms B70Fold.diagonalOperator_eigenvector_zero
#print axioms B70Fold.diagonalOperator_eigenvector_one
#print axioms B70Fold.operatorGap_linear
#print axioms B70Fold.across_kernel_with_constant_projector

end B70Fold
end


/-! ## B70 — what a geometric-sequence fit certifies, and what one point does not

Integrated from `.ultramath/smwwdl7d5/m12/B70Sampling.lean`.
-/

section
/-!
# B70: what the sampling Check does and does not assert

`powerLaw p C r = C * r^p`. At `r = 1` every such law with the same `C`
has the same value, which formalises only the failure of the careless
one-point reading. The positive log formulae establish the card's actual
consecutive-geometric-sample diagnostic.
-/

namespace B70Sampling

noncomputable section

/-- A positive-amplitude pure power law, with natural exponent. -/
def powerLaw (p : ℕ) (C r : ℝ) : ℝ := C * r ^ p

/-- Radii `r, r*q, r*q^2, ...`, written with `q = exp h`. -/
def geoRadius (r h : ℝ) (n : ℕ) : ℝ := r * Real.exp (n * h)

/-- PHASE 1, invented weak reading: equality at one sampled point would
identify a power-law exponent. All unit-amplitude powers agree at one. -/
theorem all_unit_powerLaws_agree_at_one (p q : ℕ) :
    powerLaw p 1 1 = powerLaw q 1 1 := by
  simp [powerLaw]

/-- The concrete one-point witness: distinct exponents one and two give
exactly the same nonzero observation at radius one. -/
theorem one_point_counterexample :
    powerLaw 1 1 1 = powerLaw 2 1 1 ∧
      powerLaw 1 1 1 ≠ 0 ∧ (1 : ℕ) ≠ 2 := by
  norm_num [powerLaw]

/-- Positivity of the explicit pure-power models. -/
theorem powerLaw_pos {p : ℕ} {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    0 < powerLaw p C r := by
  exact mul_pos hC (pow_pos hr p)

@[simp] theorem geoRadius_pos {r h : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < geoRadius r h n := by
  exact mul_pos hr (Real.exp_pos _)

theorem log_geoRadius {r h : ℝ} (hr : 0 < r) (n : ℕ) :
    Real.log (geoRadius r h n) = Real.log r + n * h := by
  rw [geoRadius, Real.log_mul (ne_of_gt hr) (Real.exp_ne_zero _), Real.log_exp]

/-- Pure-power observations are affine in log-log coordinates. -/
theorem log_powerLaw {p : ℕ} {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    Real.log (powerLaw p C r) = Real.log C + p * Real.log r := by
  rw [powerLaw, Real.log_mul (ne_of_gt hC) (pow_ne_zero _ (ne_of_gt hr)),
    Real.log_pow]

/-- Exact two-point affine regression in log-log coordinates. -/
def affineExponentFit (x0 x1 z0 z1 : ℝ) : ℝ := (z1 - z0) / (x1 - x0)

theorem affineExponentFit_affine (a p x0 x1 : ℝ) (hx : x1 - x0 ≠ 0) :
    affineExponentFit x0 x1 (a + p * x0) (a + p * x1) = p := by
  unfold affineExponentFit
  field_simp [hx]
  ring

/-- FAITHFUL CHECK KERNEL: consecutive radii in any nonconstant
geometric sequence recover `p`, independently of the amplitude `C`.
The hypothesis `h ≠ 0` says precisely that the ratio `exp h` is not one. -/
theorem geometric_log_ratio {p : ℕ} {C r h : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hh : h ≠ 0) (n : ℕ) :
    affineExponentFit
      (Real.log (geoRadius r h n))
      (Real.log (geoRadius r h (n + 1)))
      (Real.log (powerLaw p C (geoRadius r h n)))
      (Real.log (powerLaw p C (geoRadius r h (n + 1)))) = p := by
  rw [log_geoRadius hr, log_geoRadius hr,
    log_powerLaw hC (geoRadius_pos hr n),
    log_powerLaw hC (geoRadius_pos hr (n + 1)),
    log_geoRadius hr n, log_geoRadius hr (n + 1)]
  apply affineExponentFit_affine
  push_cast
  intro hz
  apply hh
  linarith

/-- The same power law with a real exponent, including the exceptional
square-root exponent `1/2`. -/
def realPowerLaw (p C r : ℝ) : ℝ := C * Real.rpow r p

theorem realPowerLaw_pos {p C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    0 < realPowerLaw p C r := by
  exact mul_pos hC (Real.rpow_pos_of_pos hr p)

theorem log_realPowerLaw {p C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    Real.log (realPowerLaw p C r) = Real.log C + p * Real.log r := by
  calc
    Real.log (realPowerLaw p C r) = Real.log C + Real.log (Real.rpow r p) := by
      exact Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hr p))
    _ = Real.log C + p * Real.log r := by
      have hl : Real.log (Real.rpow r p) = p * Real.log r := Real.log_rpow hr p
      rw [hl]

/-- Real-exponent version of the exact geometric-sequence fit. -/
theorem geometric_log_ratio_real {p C r h : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hh : h ≠ 0) (n : ℕ) :
    affineExponentFit
      (Real.log (geoRadius r h n))
      (Real.log (geoRadius r h (n + 1)))
      (Real.log (realPowerLaw p C (geoRadius r h n)))
      (Real.log (realPowerLaw p C (geoRadius r h (n + 1)))) = p := by
  rw [log_geoRadius hr, log_geoRadius hr,
    log_realPowerLaw hC (geoRadius_pos hr n),
    log_realPowerLaw hC (geoRadius_pos hr (n + 1)),
    log_geoRadius hr n, log_geoRadius hr (n + 1)]
  apply affineExponentFit_affine
  push_cast
  intro hz
  apply hh
  linarith

/-- The card's exceptional generic law `C*sqrt(r)` has fitted exponent
exactly `1/2`, not an exponent inferred from one sample. -/
theorem exceptional_sqrt_exponent_fit {C r h : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hh : h ≠ 0) (n : ℕ) :
    affineExponentFit
      (Real.log (geoRadius r h n))
      (Real.log (geoRadius r h (n + 1)))
      (Real.log (realPowerLaw (1 / 2) C (geoRadius r h n)))
      (Real.log (realPowerLaw (1 / 2) C (geoRadius r h (n + 1)))) = 1 / 2 := by
  exact geometric_log_ratio_real hC hr hh n

#print axioms B70Sampling.all_unit_powerLaws_agree_at_one
#print axioms B70Sampling.one_point_counterexample
#print axioms B70Sampling.powerLaw_pos
#print axioms B70Sampling.geoRadius_pos
#print axioms B70Sampling.log_geoRadius
#print axioms B70Sampling.log_powerLaw
#print axioms B70Sampling.affineExponentFit_affine
#print axioms B70Sampling.geometric_log_ratio
#print axioms B70Sampling.realPowerLaw_pos
#print axioms B70Sampling.log_realPowerLaw
#print axioms B70Sampling.geometric_log_ratio_real
#print axioms B70Sampling.exceptional_sqrt_exponent_fit

end
end B70Sampling
end


/-! ## B140 — the circular-contour bound with the perturbed inverse constructed

Integrated from `.ultramath/smwwdl7d5/m10/B140.lean`.
-/

section
/-!
B140: the displayed Riesz-projector estimate, and the omitted-Check straw man.

The circular-contour theorem below is in a general normed ring with summable
geometric series; continuous linear maps on a complex Banach space are an
instance. Integrability of the two resolvents is made explicit.
-/

namespace B140

open Real

set_option autoImplicit false

/-- The exact right-hand side on the B140 display. -/
noncomputable def displayedBound (ell C δ ε : ℝ) : ℝ :=
  ell * C ^ 2 * ε / (2 * Real.pi * δ * (δ - ε * C))

/-- Scalar witness for the weak reading that deletes `ε C < δ`: on the unit
circle for `A = 0`, one has `δ = C = 1`, `ℓ = 2π`, and `P = 1`. Taking `E = 2`
gives `A' = 2`, still with a resolvent on the unit circle, but `P' = 0`.
The displayed right-hand side is then `-2`. -/
theorem omitted_check_witness_rhs :
    displayedBound (2 * Real.pi) 1 1 2 = -2 := by
  unfold displayedBound
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- A Lean refutation of the weak, invented reading only: without the Check,
the literal scalar values above make the asserted inequality false. -/
theorem omitted_check_reading_is_false :
    ¬ ‖(0 : ℝ) - 1‖ ≤ displayedBound (2 * Real.pi) 1 1 2 := by
  rw [omitted_check_witness_rhs]
  norm_num

section Resolvent

variable {B : Type*} [NormedRing B] [HasSummableGeomSeries B]

/-- The left Neumann factor in the inverse of `q - e`, followed by `r`.
It is used only when `r` is a two-sided inverse of `q`. -/
noncomputable def neumannResolvent (r e : B) (h : ‖r * e‖ < 1) : B :=
  (∑' n : ℕ, (r * e) ^ n) * r

lemma neumannResolvent_right_inverse {q r e : B} (h : ‖r * e‖ < 1)
    (hqr : q * r = 1) : (q - e) * neumannResolvent r e h = 1 := by
  have hfactor : q - e = q * (1 - r * e) := by
    rw [mul_sub, mul_one, ← mul_assoc, hqr, one_mul]
  rw [neumannResolvent, hfactor]
  calc
    q * (1 - r * e) * ((∑' n : ℕ, (r * e) ^ n) * r) =
        q * ((1 - r * e) * (∑' n : ℕ, (r * e) ^ n)) * r := by
          noncomm_ring
    _ = q * r := by rw [mul_neg_geom_series _ h]; simp
    _ = 1 := hqr

lemma neumannResolvent_left_inverse {q r e : B} (h : ‖r * e‖ < 1)
    (hqr : q * r = 1) (hrq : r * q = 1) : neumannResolvent r e h * (q - e) = 1 := by
  have hfactor : q - e = q * (1 - r * e) := by
    rw [mul_sub, mul_one, ← mul_assoc, hqr, one_mul]
  rw [neumannResolvent, hfactor]
  calc
    (∑' n : ℕ, (r * e) ^ n) * r * (q * (1 - r * e)) =
        (∑' n : ℕ, (r * e) ^ n) * (r * q) * (1 - r * e) := by
          noncomm_ring
    _ = (∑' n : ℕ, (r * e) ^ n) * (1 - r * e) := by rw [hrq, mul_one]
    _ = 1 := geom_series_mul_neg _ h

lemma norm_neumannResolvent_le_actual {r e : B} (h : ‖r * e‖ < 1)
    (hone : ‖(1 : B)‖ = 1) :
    ‖neumannResolvent r e h‖ ≤ ‖r‖ * (1 - ‖r * e‖)⁻¹ := by
  have hs : ‖∑' n : ℕ, (r * e) ^ n‖ ≤ (1 - ‖r * e‖)⁻¹ := by
    simpa [hone] using tsum_geometric_le_of_norm_lt_one (r * e) h
  calc
    ‖neumannResolvent r e h‖ ≤ ‖∑' n : ℕ, (r * e) ^ n‖ * ‖r‖ :=
      norm_mul_le _ _
    _ ≤ (1 - ‖r * e‖)⁻¹ * ‖r‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖r‖ * (1 - ‖r * e‖)⁻¹ := mul_comm _ _

lemma norm_re_mul_le {r e : B} {ε ρ : ℝ} (hε : 0 ≤ ε)
    (hr : ‖r‖ ≤ ρ) (he : ‖e‖ ≤ ε) : ‖r * e‖ ≤ ε * ρ := by
  calc
    ‖r * e‖ ≤ ‖r‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ ‖r‖ * ε := mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ ≤ ρ * ε := mul_le_mul_of_nonneg_right hr hε
    _ = ε * ρ := mul_comm _ _

/-- Quantitative Neumann estimate with a uniform resolvent bound `ρ`.
This proves both existence (through the preceding inverse identities) and the
norm estimate, rather than postulating the perturbed resolvent bound. -/
lemma norm_neumannResolvent_le {r e : B} {ε ρ : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hερ : ε * ρ < 1)
    (hr : ‖r‖ ≤ ρ) (he : ‖e‖ ≤ ε) (hone : ‖(1 : B)‖ = 1) :
    ∃ (h : ‖r * e‖ < 1),
      ‖neumannResolvent r e h‖ ≤ ρ / (1 - ε * ρ) := by
  have hre : ‖r * e‖ ≤ ε * ρ := norm_re_mul_le hε hr he
  have h : ‖r * e‖ < 1 := hre.trans_lt hερ
  refine ⟨h, ?_⟩
  have hden : 0 < 1 - ‖r * e‖ := sub_pos.mpr h
  have hinv : (1 - ‖r * e‖)⁻¹ ≤ (1 - ε * ρ)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr hερ) (sub_le_sub_left hre 1)
  have hmain := norm_neumannResolvent_le_actual h hone
  calc
    ‖neumannResolvent r e h‖ ≤ ‖r‖ * (1 - ‖r * e‖)⁻¹ := hmain
    _ ≤ ρ * (1 - ε * ρ)⁻¹ := by
      exact mul_le_mul hr hinv (inv_nonneg.mpr hden.le) hρ
    _ = ρ / (1 - ε * ρ) := by rw [div_eq_mul_inv]

lemma resolvent_difference_identity {q r rp e : B}
    (hqr : q * r = 1) (hrp : rp * (q - e) = 1) :
    rp - r = rp * e * r := by
  calc
    rp - r = rp * (q * r) - (rp * (q - e)) * r := by rw [hqr, hrp]; simp
    _ = rp * e * r := by noncomm_ring

end Resolvent

#print axioms B140.omitted_check_witness_rhs
#print axioms B140.omitted_check_reading_is_false
#print axioms B140.neumannResolvent_right_inverse
#print axioms B140.neumannResolvent_left_inverse
#print axioms B140.norm_neumannResolvent_le_actual
#print axioms B140.norm_re_mul_le
#print axioms B140.norm_neumannResolvent_le
#print axioms B140.resolvent_difference_identity

end B140

namespace B140

section Circle

variable {B : Type*} [NormedRing B] [NormedSpace ℂ B] [HasSummableGeomSeries B]

/-- The contour part of B140 for one positively oriented circle.  The unary
`q z` is `z • 1 - A` in the operator application, and `r`, `rp` are the two
resolvents.  The perturbed-resolvent estimate needed here is proved separately
by `norm_neumannResolvent_le`; it is not part of the contour calculus. -/
theorem circular_projector_bound_aux
    {q r rp : ℂ → B} {e p pp : B} {c : ℂ} {a ε ρ : ℝ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hερ : ε * ρ < 1)
    (he : ‖e‖ ≤ ε)
    (hr : ∀ z ∈ Metric.sphere c a, ‖r z‖ ≤ ρ)
    (hrp : ∀ z ∈ Metric.sphere c a, ‖rp z‖ ≤ ρ / (1 - ε * ρ))
    (hqr : ∀ z ∈ Metric.sphere c a, q z * r z = 1)
    (hrpq : ∀ z ∈ Metric.sphere c a, rp z * (q z - e) = 1)
    (hrint : CircleIntegrable r c a) (hrpint : CircleIntegrable rp c a)
    (hp : p = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), r z)
    (hpp : pp = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), rp z) :
    ‖pp - p‖ ≤ a * (ε * ρ * (ρ / (1 - ε * ρ))) := by
  have hden : 0 < 1 - ε * ρ := sub_pos.mpr hερ
  have hpoint : ∀ z ∈ Metric.sphere c a,
      ‖rp z * e * r z‖ ≤ ε * ρ * (ρ / (1 - ε * ρ)) := by
    intro z hz
    have hρp : 0 ≤ ρ / (1 - ε * ρ) := div_nonneg hρ hden.le
    calc
      ‖rp z * e * r z‖ ≤ ‖rp z * e‖ * ‖r z‖ := norm_mul_le _ _
      _ ≤ (‖rp z‖ * ‖e‖) * ‖r z‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (ρ / (1 - ε * ρ)) * ε * ρ := by
        exact mul_le_mul
          (mul_le_mul (hrp z hz) he (norm_nonneg _) hρp)
          (hr z hz) (norm_nonneg _) (mul_nonneg hρp hε)
      _ = ε * ρ * (ρ / (1 - ε * ρ)) := by ring
  have hdiff : pp - p =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), (rp z * e * r z) := by
    rw [hpp, hp, ← smul_sub, ← circleIntegral.integral_sub hrpint hrint]
    congr 1
    apply circleIntegral.integral_congr ha
    intro z hz
    exact resolvent_difference_identity (hqr z hz) (hrpq z hz)
  rw [hdiff]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const ha hpoint

/-- Algebra converting the `ρ = sup ‖R‖` form to the card's `C = δρ` form. -/
lemma circular_displayed_rhs (a δ ε ρ : ℝ) (hδ : δ ≠ 0)
    (hsub : δ - ε * (δ * ρ) ≠ 0) :
    a * (ε * ρ * (ρ / (1 - ε * ρ))) =
      displayedBound (2 * Real.pi * a) (δ * ρ) δ ε := by
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsmall : 1 - ε * ρ ≠ 0 := by
    intro h
    apply hsub
    have hδ' := congrArg (fun x : ℝ => δ * x) h
    nlinarith
  unfold displayedBound
  field_simp [hδ, hsub, hsmall, hπ]

/-- **B140, faithful circular-contour kernel.**  Here `CΓ = δ * ρ`,
`ε CΓ < δ` is `hmargin`, the circle has length `2πa`, and the unperturbed
resolvent is bounded by `ρ`.  This is exactly the displayed right-hand side,
including its `2π`, `δ`, and `δ - εCΓ` factors. -/
theorem circular_projector_displayed_bound
    {q r rp : ℂ → B} {e p pp : B} {c : ℂ} {a δ ε ρ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hmargin : ε * (δ * ρ) < δ)
    (he : ‖e‖ ≤ ε)
    (hr : ∀ z ∈ Metric.sphere c a, ‖r z‖ ≤ ρ)
    (hrp : ∀ z ∈ Metric.sphere c a, ‖rp z‖ ≤ ρ / (1 - ε * ρ))
    (hqr : ∀ z ∈ Metric.sphere c a, q z * r z = 1)
    (hrpq : ∀ z ∈ Metric.sphere c a, rp z * (q z - e) = 1)
    (hrint : CircleIntegrable r c a) (hrpint : CircleIntegrable rp c a)
    (hp : p = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), r z)
    (hpp : pp = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), rp z) :
    ‖pp - p‖ ≤ displayedBound (2 * Real.pi * a) (δ * ρ) δ ε := by
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have hsub : δ - ε * (δ * ρ) ≠ 0 := ne_of_gt (sub_pos.mpr hmargin)
  have hερ : ε * ρ < 1 := by
    have hmul : δ * (ε * ρ) < δ * 1 := by nlinarith [hmargin]
    nlinarith [hmul, hδ]
  rw [← circular_displayed_rhs a δ ε ρ hδ' hsub]
  exact circular_projector_bound_aux ha hε hρ hερ he hr hrp hqr hrpq
    hrint hrpint hp hpp

end Circle

#print axioms B140.circular_projector_bound_aux
#print axioms B140.circular_displayed_rhs
#print axioms B140.circular_projector_displayed_bound

end B140

namespace B140

section PackagedCircle

variable {B : Type*} [NormedRing B] [NormedSpace ℂ B] [HasSummableGeomSeries B]

/-- Uniqueness of the ring inverse under explicit two-sided inverse equations. -/
lemma ring_inverse_eq_of_two_sided {q r : B}
    (hqr : q * r = 1) (hrq : r * q = 1) : Ring.inverse q = r := by
  have hq : IsUnit q := ⟨⟨q, r, hqr, hrq⟩, rfl⟩
  apply hq.mul_right_inj.mp
  rw [Ring.mul_inverse_cancel _ hq, hqr]

/-- Fully assembled B140 for one circle.  The perturbed resolvent is the actual
`Ring.inverse (q z - e)`, not an arbitrary function assumed to satisfy its
Neumann estimate.  The Check proves its existence and bound point by point. -/
theorem circular_ringInverse_projector_displayed_bound
    {q r : ℂ → B} {e p pp : B} {c : ℂ} {a δ ε ρ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hmargin : ε * (δ * ρ) < δ)
    (he : ‖e‖ ≤ ε) (hone : ‖(1 : B)‖ = 1)
    (hr : ∀ z ∈ Metric.sphere c a, ‖r z‖ ≤ ρ)
    (hqr : ∀ z ∈ Metric.sphere c a, q z * r z = 1)
    (hrq : ∀ z ∈ Metric.sphere c a, r z * q z = 1)
    (hrint : CircleIntegrable r c a)
    (hrpint : CircleIntegrable (fun z => Ring.inverse (q z - e)) c a)
    (hp : p = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, a), r z)
    (hpp : pp = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(c, a), Ring.inverse (q z - e)) :
    ‖pp - p‖ ≤ displayedBound (2 * Real.pi * a) (δ * ρ) δ ε := by
  have hερ : ε * ρ < 1 := by
    have hmul : δ * (ε * ρ) < δ * 1 := by nlinarith [hmargin]
    nlinarith [hmul, hδ]
  have hrp : ∀ z ∈ Metric.sphere c a,
      ‖Ring.inverse (q z - e)‖ ≤ ρ / (1 - ε * ρ) := by
    intro z hz
    obtain ⟨h, hbound⟩ := norm_neumannResolvent_le hε hρ hερ (hr z hz) he hone
    have hi : Ring.inverse (q z - e) = neumannResolvent (r z) e h :=
      ring_inverse_eq_of_two_sided
        (neumannResolvent_right_inverse h (hqr z hz))
        (neumannResolvent_left_inverse h (hqr z hz) (hrq z hz))
    rw [hi]
    exact hbound
  have hrpq : ∀ z ∈ Metric.sphere c a, Ring.inverse (q z - e) * (q z - e) = 1 := by
    intro z hz
    obtain ⟨h, _⟩ := norm_neumannResolvent_le hε hρ hερ (hr z hz) he hone
    have hi : Ring.inverse (q z - e) = neumannResolvent (r z) e h :=
      ring_inverse_eq_of_two_sided
        (neumannResolvent_right_inverse h (hqr z hz))
        (neumannResolvent_left_inverse h (hqr z hz) (hrq z hz))
    rw [hi]
    exact neumannResolvent_left_inverse h (hqr z hz) (hrq z hz)
  exact circular_projector_displayed_bound ha hδ hε hρ hmargin he hr hrp hqr hrpq
    hrint hrpint hp hpp

end PackagedCircle

#print axioms B140.ring_inverse_eq_of_two_sided
#print axioms B140.circular_ringInverse_projector_displayed_bound

end B140

namespace B140

section JordanWitness

open scoped Matrix Matrix.Norms.Elementwise

abbrev RMat := Matrix (Fin 2) (Fin 2) ℝ

/-- The HTML witness `[[b, μ], [d, b]]`; at the numerical witness `b=μ=1`,
`d=s²` is the parameter called `δ` on the card. -/
def jordanPair (b μ d : ℝ) : RMat := !![b, μ; d, b]

/-- The two spectral idempotents when `s² = μd` and `μ,s ≠ 0`. -/
noncomputable def plusProjector (μ s : ℝ) : RMat :=
  !![1 / 2, μ / (2 * s); s / (2 * μ), 1 / 2]

noncomputable def minusProjector (μ s : ℝ) : RMat :=
  !![1 / 2, -μ / (2 * s); -s / (2 * μ), 1 / 2]

/-- The pair (cluster) projector is constant even at the Jordan limit. -/
theorem pair_projector_exactly_one (μ s : ℝ) :
    plusProjector μ s + minusProjector μ s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusProjector, minusProjector] <;> ring

lemma plusProjector_idempotent {μ s : ℝ} (hμ : μ ≠ 0) (hs : s ≠ 0) :
    plusProjector μ s * plusProjector μ s = plusProjector μ s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hμ, hs] <;> ring

lemma minusProjector_idempotent {μ s : ℝ} (hμ : μ ≠ 0) (hs : s ≠ 0) :
    minusProjector μ s * minusProjector μ s = minusProjector μ s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hμ, hs] <;> ring

/-- Right spectral identity for the plus idempotent along the card's family.
No normality or orthogonality is asserted. -/
lemma jordanPair_mul_plusProjector {s : ℝ} (hs : s ≠ 0) :
    jordanPair 1 1 (s ^ 2) * plusProjector 1 s =
      (1 + s) • plusProjector 1 s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPair, plusProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hs] <;> ring

lemma jordanPair_mul_minusProjector {s : ℝ} (hs : s ≠ 0) :
    jordanPair 1 1 (s ^ 2) * minusProjector 1 s =
      (1 - s) • minusProjector 1 s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPair, minusProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hs] <;> ring

lemma plusProjector_commutes {s : ℝ} (hs : s ≠ 0) :
    jordanPair 1 1 (s ^ 2) * plusProjector 1 s =
      plusProjector 1 s * jordanPair 1 1 (s ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanPair, plusProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hs] <;> ring

/-- Exact coefficient divergence on the card's geometric route `s=1/(n+1)`. -/
lemma plusProjector_entry_on_route (n : ℕ) :
    plusProjector 1 (((n : ℝ) + 1)⁻¹) 0 1 = ((n : ℝ) + 1) / 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [plusProjector]
  field_simp [hn]

/-- Hence the operator norm of each individual plus spectral projector is
unbounded, even though the pair projector is exactly the identity.  The norm
here is Mathlib's ordinary entrywise-sup matrix norm. -/
lemma plusProjector_norm_on_route (n : ℕ) :
    ((n : ℝ) + 1) / 2 ≤ ‖plusProjector 1 (((n : ℝ) + 1)⁻¹)‖ := by
  have h := Matrix.norm_entry_le_entrywise_sup_norm
    (plusProjector 1 (((n : ℝ) + 1)⁻¹)) (i := 0) (j := 1)
  rw [plusProjector_entry_on_route] at h
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hn2 : 0 ≤ ((n : ℝ) + 1) / 2 := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hn2] using h

end JordanWitness

#print axioms B140.pair_projector_exactly_one
#print axioms B140.plusProjector_idempotent
#print axioms B140.minusProjector_idempotent
#print axioms B140.jordanPair_mul_plusProjector
#print axioms B140.jordanPair_mul_minusProjector
#print axioms B140.plusProjector_commutes
#print axioms B140.plusProjector_entry_on_route
#print axioms B140.plusProjector_norm_on_route

end B140

namespace B140

section ConcreteWeakWitness

/-- Base scalar Riesz projector for `A=0` on the unit circle. -/
noncomputable def scalarBaseP : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 0)⁻¹

/-- Perturbed scalar Riesz projector for `A'=2` on the same circle. -/
noncomputable def scalarPerturbedP : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, 1), (z - 2)⁻¹

lemma scalar_base_resolvent_norm (z : ℂ) (hz : z ∈ Metric.sphere 0 1) :
    ‖(z - 0)⁻¹‖ = 1 := by
  have hd : dist z 0 = 1 := hz
  have hzn : ‖z‖ = 1 := by simpa [dist_eq_norm] using hd
  simp [norm_inv, hzn]

lemma scalar_perturbed_denominator_ne_zero (z : ℂ)
    (hz : z ∈ Metric.ball 0 1) : z - 2 ≠ 0 := by
  have hd : dist z 0 < 1 := hz
  have hzn : ‖z‖ < 1 := by simpa [dist_eq_norm] using hd
  intro h
  have hz2 : z = 2 := sub_eq_zero.mp h
  rw [hz2] at hzn
  norm_num at hzn

lemma scalar_perturbed_denominator_ne_zero_closed (z : ℂ)
    (hz : z ∈ Metric.closedBall 0 1) : z - 2 ≠ 0 := by
  have hd : dist z 0 ≤ 1 := hz
  have hzn : ‖z‖ ≤ 1 := by simpa [dist_eq_norm] using hd
  intro h
  have hz2 : z = 2 := sub_eq_zero.mp h
  rw [hz2] at hzn
  norm_num at hzn

lemma scalar_perturbed_denominator_ne_zero_on_circle (z : ℂ)
    (hz : z ∈ Metric.sphere 0 1) : z - 2 ≠ 0 := by
  apply scalar_perturbed_denominator_ne_zero_closed z
  have hd : dist z 0 = 1 := hz
  exact le_of_eq hd

/-- Cauchy–Goursat: the perturbed pole is outside the closed unit disk. -/
lemma scalar_perturbed_circle_integral :
    (∮ z in C(0, 1), (z - 2)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (R := 1) (c := 0) (s := ∅) (by norm_num) Set.countable_empty
  · intro z hz
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => (z - 2)⁻¹) z :=
      (differentiableAt_id.sub_const (2 : ℂ)).inv
        (scalar_perturbed_denominator_ne_zero_closed z hz)
    exact hdiff.continuousAt.continuousWithinAt
  · intro z hz
    show DifferentiableAt ℂ (fun z : ℂ => (z - 2)⁻¹) z
    exact (differentiableAt_id.sub_const (2 : ℂ)).inv
      (scalar_perturbed_denominator_ne_zero z hz.1)

lemma scalarBaseP_eq_one : scalarBaseP = 1 := by
  unfold scalarBaseP
  rw [circleIntegral.integral_sub_center_inv 0 (by norm_num : (1 : ℝ) ≠ 0)]
  simp only [smul_eq_mul]
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  exact inv_mul_cancel₀ hc

lemma scalarPerturbedP_eq_zero : scalarPerturbedP = 0 := by
  unfold scalarPerturbedP
  rw [scalar_perturbed_circle_integral]
  simp

/-- Fully concrete version of the weak-reading counterexample: both scalar
Riesz projectors are evaluated from their resolvent integrals in Lean. -/
theorem omitted_check_scalar_projectors_refute_invented_reading :
    ¬ ‖scalarPerturbedP - scalarBaseP‖ ≤
      displayedBound (2 * Real.pi) 1 1 2 := by
  rw [scalarPerturbedP_eq_zero, scalarBaseP_eq_one, omitted_check_witness_rhs]
  norm_num

end ConcreteWeakWitness

#print axioms B140.scalar_base_resolvent_norm
#print axioms B140.scalar_perturbed_denominator_ne_zero
#print axioms B140.scalar_perturbed_denominator_ne_zero_closed
#print axioms B140.scalar_perturbed_denominator_ne_zero_on_circle
#print axioms B140.scalar_perturbed_circle_integral
#print axioms B140.scalarBaseP_eq_one
#print axioms B140.scalarPerturbedP_eq_zero
#print axioms B140.omitted_check_scalar_projectors_refute_invented_reading

end B140

#print axioms B140.displayedBound
#print axioms B140.neumannResolvent
#print axioms B140.jordanPair
#print axioms B140.plusProjector
#print axioms B140.minusProjector
#print axioms B140.scalarBaseP
#print axioms B140.scalarPerturbedP
end


/-! ## B140 — the exact projector norm and the failure of any Lipschitz constant

Integrated from `.ultramath/smwwdl7d5/m11/B140.lean`.
-/

section
open scoped Matrix.Norms.L2Operator BigOperators ComplexConjugate

namespace B140M11

/-! ## Faithful reading: the algebraic part of the resolvent-contour bound -/

/-- Neumann perturbation of a unit with an explicit inverse-norm bound. -/
theorem inverse_unit_sub_norm_le {R : Type*} [NormedRing R] [NormOneClass R]
    [HasSummableGeomSeries R] (u : Rˣ) (e : R) {r q : ℝ}
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
      _ ≤ (1 - r * q)⁻¹ := inv_anti₀ hpos (sub_le_sub_left ht 1)
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
    _ ≤ (1 - r * q)⁻¹ * r :=
      mul_le_mul hgeom hu (norm_nonneg _) (inv_nonneg.mpr hpos.le)
    _ = r / (1 - r * q) := by field_simp

/-- With the same Neumann hypotheses, the perturbed argument is genuinely
invertible; this is the existence content of B140's Check, not merely a bound
on the total function `Ring.inverse`. -/
theorem isUnit_unit_sub_of_norm {R : Type*} [NormedRing R] [NormOneClass R]
    [HasSummableGeomSeries R] (u : Rˣ) (e : R) {r q : ℝ}
    (hu : ‖(↑u⁻¹ : R)‖ ≤ r) (he : ‖e‖ ≤ q)
    (hr : 0 ≤ r) (hrq : r * q < 1) :
    IsUnit ((u : R) - e) := by
  let t : R := (↑u⁻¹ : R) * e
  have ht : ‖t‖ ≤ r * q :=
    (norm_mul_le _ _).trans (mul_le_mul hu he (norm_nonneg _) hr)
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht hrq
  let U : Rˣ := u * Units.oneSub t ht1
  refine ⟨U, ?_⟩
  simp [U, Units.oneSub, t, mul_sub]

/-- Second resolvent identity, in its sign convention `b = a - e`. -/
theorem resolvent_identity {R : Type*} [Ring R] (a b e : R)
    (ha : IsUnit a) (hb : IsUnit b) (hbe : b = a - e) :
    Ring.inverse b - Ring.inverse a =
      Ring.inverse b * e * Ring.inverse a := by
  have he : e = a - b := by rw [hbe]; abel
  rw [he]
  calc
    Ring.inverse b - Ring.inverse a =
        Ring.inverse b * (a * Ring.inverse a) -
          (Ring.inverse b * b) * Ring.inverse a := by
            rw [Ring.mul_inverse_cancel a ha, Ring.inverse_mul_cancel b hb]
            simp
    _ = Ring.inverse b * (a - b) * Ring.inverse a := by noncomm_ring

/-- The perturbed-resolvent estimate in B140's notation.  Here `u` is the
invertible unperturbed resolvent argument at one contour point. -/
theorem perturbed_inverse_norm_le {R : Type*} [NormedRing R] [NormOneClass R]
    [HasSummableGeomSeries R] (u : Rˣ) (e : R) (C δ ε : ℝ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (_hε : 0 ≤ ε)
    (hu : ‖(↑u⁻¹ : R)‖ ≤ C / δ) (he : ‖e‖ ≤ ε) (hmargin : ε * C < δ) :
    ‖Ring.inverse ((u : R) - e)‖ ≤ C / (δ - ε * C) := by
  have hr : 0 ≤ C / δ := div_nonneg hC hδ.le
  have hrq : (C / δ) * ε < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hδ]
    nlinarith
  convert inverse_unit_sub_norm_le u e hu he hr hrq using 1
  have hden : δ - ε * C ≠ 0 := ne_of_gt (sub_pos.mpr hmargin)
  field_simp [ne_of_gt hδ, hden]

/-- Pointwise norm bound for the product in the second resolvent identity.
Integrating this along a finite contour supplies the display's length and
`2π` factors, which are not hidden in this algebraic declaration. -/
theorem resolvent_product_norm_le {R : Type*} [NormedRing R]
    (R' S e : R) (C δ ε : ℝ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (_hε : 0 ≤ ε) (hmargin : ε * C < δ)
    (hR : ‖S‖ ≤ C / δ) (hR' : ‖R'‖ ≤ C / (δ - ε * C))
    (he : ‖e‖ ≤ ε) :
    ‖R' * e * S‖ ≤ ε * C ^ 2 / (δ * (δ - ε * C)) := by
  have hden : 0 < δ - ε * C := sub_pos.mpr hmargin
  calc
    ‖R' * e * S‖ ≤ ‖R'‖ * ‖e‖ * ‖S‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
        (norm_nonneg _))
    _ ≤ (C / (δ - ε * C)) * ε * (C / δ) := by
      gcongr
    _ = ε * C ^ 2 / (δ * (δ - ε * C)) := by
      field_simp [ne_of_gt hδ, ne_of_gt hden]

/-! ## Exact finite display witness, on two-dimensional real Euclidean space -/

abbrev E₂ := EuclideanSpace ℝ (Fin 2)

/-- The normalized rank-one operator determined by a right vector `r` and a
left vector `l`; no orthogonality of `l` and `r` is assumed. -/
noncomputable def rankOneProjector (r l : E₂) : E₂ →L[ℝ] E₂ :=
  (inner ℝ l r)⁻¹ • InnerProductSpace.rankOne ℝ r l

lemma rankOneProjector_comp_self (r l : E₂) (hlr : inner ℝ l r ≠ 0) :
    rankOneProjector r l ∘L rankOneProjector r l = rankOneProjector r l := by
  simp only [rankOneProjector, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, InnerProductSpace.rankOne_comp_rankOne,
    smul_smul]
  rw [show (inner ℝ l r)⁻¹ * ((inner ℝ l r)⁻¹ * inner ℝ l r) =
    (inner ℝ l r)⁻¹ by field_simp]

lemma rankOneProjector_apply (r l x : E₂) :
    rankOneProjector r l x = (inner ℝ l r)⁻¹ • (inner ℝ l x • r) := by
  rfl

lemma rankOneProjector_norm (r l : E₂) :
    ‖rankOneProjector r l‖ = ‖inner ℝ l r‖⁻¹ * (‖r‖ * ‖l‖) := by
  rw [rankOneProjector, norm_smul, InnerProductSpace.norm_rankOne, norm_inv]

noncomputable def rightPlus (η : ℝ) : E₂ := WithLp.toLp 2 ![1, Real.sqrt η]
noncomputable def leftPlus (η : ℝ) : E₂ := WithLp.toLp 2 ![Real.sqrt η, 1]
noncomputable def rightMinus (η : ℝ) : E₂ := WithLp.toLp 2 ![1, -Real.sqrt η]
noncomputable def leftMinus (η : ℝ) : E₂ := WithLp.toLp 2 ![Real.sqrt η, -1]

noncomputable def plus (η : ℝ) : E₂ →L[ℝ] E₂ :=
  rankOneProjector (rightPlus η) (leftPlus η)
noncomputable def minus (η : ℝ) : E₂ →L[ℝ] E₂ :=
  rankOneProjector (rightMinus η) (leftMinus η)

lemma inner_leftPlus_rightPlus (η : ℝ) :
    inner ℝ (leftPlus η) (rightPlus η) = 2 * Real.sqrt η := by
  simp [leftPlus, rightPlus, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]
  ring

lemma inner_leftMinus_rightMinus (η : ℝ) :
    inner ℝ (leftMinus η) (rightMinus η) = 2 * Real.sqrt η := by
  simp [leftMinus, rightMinus, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]
  ring

lemma inner_leftPlus_rightMinus (η : ℝ) :
    inner ℝ (leftPlus η) (rightMinus η) = 0 := by
  simp [leftPlus, rightMinus, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]

lemma inner_leftMinus_rightPlus (η : ℝ) :
    inner ℝ (leftMinus η) (rightPlus η) = 0 := by
  simp [leftMinus, rightPlus, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]

lemma norm_rightPlus {η : ℝ} (hη : 0 ≤ η) :
    ‖rightPlus η‖ = Real.sqrt (1 + η) := by
  simp [rightPlus, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.sq_sqrt hη]

lemma norm_leftPlus {η : ℝ} (hη : 0 ≤ η) :
    ‖leftPlus η‖ = Real.sqrt (1 + η) := by
  simp [leftPlus, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.sq_sqrt hη, add_comm]

lemma norm_rightMinus {η : ℝ} (hη : 0 ≤ η) :
    ‖rightMinus η‖ = Real.sqrt (1 + η) := by
  simp [rightMinus, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.sq_sqrt hη]

lemma norm_leftMinus {η : ℝ} (hη : 0 ≤ η) :
    ‖leftMinus η‖ = Real.sqrt (1 + η) := by
  simp [leftMinus, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.sq_sqrt hη, add_comm]

lemma plus_apply (η : ℝ) (x : E₂) :
    plus η x = (2 * Real.sqrt η)⁻¹ • (inner ℝ (leftPlus η) x • rightPlus η) := by
  rw [plus, rankOneProjector_apply, inner_leftPlus_rightPlus]

lemma minus_apply (η : ℝ) (x : E₂) :
    minus η x = (2 * Real.sqrt η)⁻¹ •
      (inner ℝ (leftMinus η) x • rightMinus η) := by
  rw [minus, rankOneProjector_apply, inner_leftMinus_rightMinus]

/-- Exact Euclidean operator norm, including the non-asymptotic `+√η` term. -/
theorem plus_norm {η : ℝ} (hη : 0 < η) :
    ‖plus η‖ = (1 + η) / (2 * Real.sqrt η) := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  rw [plus, rankOneProjector_norm, inner_leftPlus_rightPlus,
    norm_rightPlus hη.le, norm_leftPlus hη.le]
  simp only [Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hs)]
  rw [Real.mul_self_sqrt (by positivity : 0 ≤ 1 + η)]
  rw [div_eq_mul_inv]
  ring

/-- The other one-dimensional eigenprojector has exactly the same norm. -/
theorem minus_norm {η : ℝ} (hη : 0 < η) :
    ‖minus η‖ = (1 + η) / (2 * Real.sqrt η) := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  rw [minus, rankOneProjector_norm, inner_leftMinus_rightMinus,
    norm_rightMinus hη.le, norm_leftMinus hη.le]
  simp only [Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hs)]
  rw [Real.mul_self_sqrt (by positivity : 0 ≤ 1 + η)]
  rw [div_eq_mul_inv]
  ring

/-- The full two-dimensional cluster projector is the identity, exactly. -/
theorem plus_add_minus {η : ℝ} (hη : 0 < η) :
    plus η + minus η = ContinuousLinearMap.id ℝ E₂ := by
  have hs : Real.sqrt η ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hη)
  ext x i
  fin_cases i <;>
    simp [plus_apply, minus_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two, rightPlus, rightMinus, leftPlus, leftMinus,
      smul_eq_mul] <;>
    field_simp [hs] <;> ring

lemma plus_idempotent {η : ℝ} (hη : 0 < η) :
    plus η ∘L plus η = plus η := by
  apply rankOneProjector_comp_self
  rw [inner_leftPlus_rightPlus]
  exact mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr hη))

lemma minus_idempotent {η : ℝ} (hη : 0 < η) :
    minus η ∘L minus η = minus η := by
  apply rankOneProjector_comp_self
  rw [inner_leftMinus_rightMinus]
  exact mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr hη))

/-- Exact spectral action on the right vectors of `[[1,1],[η,1]]`. -/
def K (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; η, 1]

lemma K_rightPlus {η : ℝ} (hη : 0 ≤ η) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K η) (rightPlus η) =
      (1 + Real.sqrt η) • rightPlus η := by
  rw [rightPlus, Matrix.toEuclideanCLM_toLp]
  ext i
  fin_cases i <;> simp [K, Matrix.mulVec, Fin.sum_univ_two, smul_eq_mul] <;>
    nlinarith [Real.sq_sqrt hη]

lemma K_rightMinus {η : ℝ} (hη : 0 ≤ η) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K η) (rightMinus η) =
      (1 - Real.sqrt η) • rightMinus η := by
  rw [rightMinus, Matrix.toEuclideanCLM_toLp]
  ext i
  fin_cases i <;> simp [K, Matrix.mulVec, Fin.sum_univ_two, smul_eq_mul] <;>
    nlinarith [Real.sq_sqrt hη]

/-- The two eigenprojectors really annihilate the opposite eigenspaces. -/
lemma plus_rightMinus (η : ℝ) : plus η (rightMinus η) = 0 := by
  rw [plus, rankOneProjector_apply, inner_leftPlus_rightMinus]
  simp

lemma minus_rightPlus (η : ℝ) : minus η (rightPlus η) = 0 := by
  rw [minus, rankOneProjector_apply, inner_leftMinus_rightPlus]
  simp

/-! ## Phase-two weak readings, explicitly not the card's own claim -/

/-- The display's right-hand side, with no hidden simplification. -/
noncomputable def displayedBound (ell C δ ε : ℝ) : ℝ :=
  ell * C ^ 2 * ε / (2 * Real.pi * δ * (δ - ε * C))

/-- On the unit circle with scalar `A = 0`, take `δ = C = 1` and `E = 2`.
The resolvent of `A' = 2` still exists on the unit circle, and its interior
Riesz projector is zero whereas `P = 1`; the displayed bound is nevertheless
`-2`.  This refutes only deletion of Check. -/
theorem omitted_margin_display_rhs :
    displayedBound (2 * Real.pi) 1 1 2 = -2 := by
  unfold displayedBound
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

theorem omitted_margin_reading_is_false :
    ¬ ‖(0 : ℝ) - 1‖ ≤ displayedBound (2 * Real.pi) 1 1 2 := by
  rw [omitted_margin_display_rhs]
  norm_num

/-- A scalar witness that dropping `ε*C < δ` can destroy invertibility.
It refutes only the invented reading that Check is unnecessary; B140 states
exactly this Check and therefore is not refuted by this declaration. -/
theorem dropped_margin_witness :
    let ε : ℝ := 1
    let C : ℝ := 1
    let δ : ℝ := 1
    let u : ℝ := 1
    let e : ℝ := 1
    ε * C = δ ∧ ¬ IsUnit (u - e) := by
  norm_num [isUnit_iff_ne_zero]

/-- The rank-one eigenprojectors are unbounded although their sum is always
`I`.  This refutes an invented uniform-bound claim for individual
projectors, not the displayed Riesz-cluster estimate. -/
theorem plus_unbounded (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 16 ∧ M < ‖plus η‖ := by
  let t : ℝ := 8 + 2 * (M + 1 + |M|)
  have habs : 0 ≤ M + |M| := by linarith [neg_le_abs M]
  have ht : 8 ≤ t := by
    dsimp [t]
    linarith
  have htpos : 0 < t := by linarith
  have hη : 0 < (t⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr htpos)
  have hs : Real.sqrt ((t⁻¹) ^ 2) = t⁻¹ := by
    rw [Real.sqrt_sq (inv_nonneg.mpr htpos.le)]
  have hηnorm := plus_norm hη
  rw [hs] at hηnorm
  have hform : (1 + (t⁻¹) ^ 2) / (2 * t⁻¹) = (t + t⁻¹) / 2 := by
    field_simp [ne_of_gt htpos]
  have ht_large : M < t / 2 := by
    have habs : 0 ≤ |M| := abs_nonneg M
    dsimp [t]
    linarith
  refine ⟨(t⁻¹) ^ 2, hη, ?_, ?_⟩
  · have htinv : t⁻¹ < (4 : ℝ)⁻¹ := by
      apply (inv_lt_inv₀ htpos (by norm_num)).mpr
      linarith
    nlinarith [inv_pos.mpr htpos]
  · rw [hηnorm, hform]
    have hinv : 0 < t⁻¹ := inv_pos.mpr htpos
    linarith

/-- No Lipschitz selection of this rank-one eigenprojector exists on the
bounded parameter interval `(0,1/16)`, although the full pair projector is
`I`.  The argument uses no Taylor expansion or asymptotic assertion. -/
theorem plus_not_lipschitz_on_fixed_margin (L : NNReal) :
    ¬ LipschitzWith L (fun η : Set.Ioo (0 : ℝ) (1 / 16) => plus η) := by
  intro hLip
  let η₀ : Set.Ioo (0 : ℝ) (1 / 16) := ⟨1 / 32, by norm_num⟩
  let M : ℝ := ‖plus (η₀ : ℝ)‖ + (L : ℝ)
  obtain ⟨η, hη, hsmall, hlarge⟩ := plus_unbounded M
  let η' : Set.Ioo (0 : ℝ) (1 / 16) := ⟨η, hη, hsmall⟩
  have hdist : dist (plus (η' : ℝ)) (plus (η₀ : ℝ)) ≤ (L : ℝ) := by
    have h := hLip.dist_le_mul η' η₀
    have hd : dist η' η₀ ≤ 1 := by
      change dist (η' : ℝ) (η₀ : ℝ) ≤ 1
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> dsimp [η', η₀] <;> linarith [η'.property.1, η'.property.2]
    exact h.trans ((mul_le_mul_of_nonneg_left hd L.coe_nonneg).trans (by
      rw [mul_one]))
  have hnorm : ‖plus (η' : ℝ)‖ ≤ M := by
    calc
      ‖plus (η' : ℝ)‖ = ‖plus (η₀ : ℝ) +
          (plus (η' : ℝ) - plus (η₀ : ℝ))‖ := by congr 1 <;> abel
      _ ≤ ‖plus (η₀ : ℝ)‖ + ‖plus (η' : ℝ) - plus (η₀ : ℝ)‖ := norm_add_le _ _
      _ ≤ ‖plus (η₀ : ℝ)‖ + (L : ℝ) := by
        exact add_le_add (le_refl _) (by simpa [dist_eq_norm] using hdist)
      _ = M := rfl
  exact (not_lt_of_ge hnorm) hlarge


/-- Quantitative version of the display's eigenprojector witness: even after
restricting to the fixed outer margin `1/2 - √η > 1/4`, no uniform norm bound
on the rank-one eigenprojector is possible. -/
theorem plus_unbounded_with_fixed_margin (M : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 16 ∧ M < ‖plus η‖ ∧
      1 / 4 < 1 / 2 - Real.sqrt η := by
  obtain ⟨η, hη, hsmall, hlarge⟩ := plus_unbounded M
  have hs0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg η
  have hs : Real.sqrt η < 1 / 4 := by
    nlinarith [Real.sq_sqrt hη.le, sq_nonneg (Real.sqrt η - 1 / 4)]
  exact ⟨η, hη, hsmall, hlarge, by linarith⟩

end B140M11

#print axioms B140M11.inverse_unit_sub_norm_le
#print axioms B140M11.isUnit_unit_sub_of_norm
#print axioms B140M11.resolvent_identity
#print axioms B140M11.perturbed_inverse_norm_le
#print axioms B140M11.resolvent_product_norm_le
#print axioms B140M11.rankOneProjector_comp_self
#print axioms B140M11.plus_norm
#print axioms B140M11.minus_norm
#print axioms B140M11.plus_add_minus
#print axioms B140M11.plus_idempotent
#print axioms B140M11.minus_idempotent
#print axioms B140M11.K_rightPlus
#print axioms B140M11.K_rightMinus
#print axioms B140M11.plus_not_lipschitz_on_fixed_margin
#print axioms B140M11.displayedBound
#print axioms B140M11.omitted_margin_display_rhs
#print axioms B140M11.omitted_margin_reading_is_false
#print axioms B140M11.dropped_margin_witness
#print axioms B140M11.plus_unbounded
#print axioms B140M11.plus_unbounded_with_fixed_margin
end


/-! ## B164 — the Pauli-current identity, component by component

Integrated from `.ultramath/smwwdl7d5/m14/B164.lean`.
-/

section
/-!
# B164: the Pauli-current identity

This file isolates the finite-dimensional algebra in the HTML display.  The
three components of a derivative are arbitrary complex two-vectors `d l`;
`spinDerivative l m` is the real number `2 Re ψ†σ_m(d l)`, i.e. the derivative
of `ψ†σ_mψ` in direction `l` when `d l = ∂_l ψ`.  We separately prove that
calculus identity for differentiable one-variable spinor paths.
-/

namespace AtlasB164

open Complex
open scoped ComplexConjugate Matrix

noncomputable section

abbrev Spinor : Type := Fin 2 → ℂ

/-- The two-component sesquilinear form, without conjugate-linearity tricks. -/
def braket (ψ φ : Spinor) : ℂ :=
  conj (ψ 0) * φ 0 + conj (ψ 1) * φ 1

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℂ

def sigmaX : Mat2 := !![0, 1; 1, 0]
def sigmaY : Mat2 := !![0, -Complex.I; Complex.I, 0]
def sigmaZ : Mat2 := !![1, 0; 0, -1]

/-- Kinetic momentum in direction `l`: `d l` stands for `∂_l ψ`. -/
def momentum (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) (l : Fin 3) : Spinor :=
  (-Complex.I) • d l - (A l : ℂ) • ψ

/-- `2 Re ψ†σ_m(d l)`, equal to `∂_l(ψ†σ_mψ)` for differentiable fields. -/
def spinDerivative (d : Fin 3 → Spinor) (ψ : Spinor) (l m : Fin 3) : ℝ :=
  2 * (braket ψ (match m with
    | 0 => sigmaX *ᵥ d l
    | 1 => sigmaY *ᵥ d l
    | 2 => sigmaZ *ᵥ d l
  )).re

/-- The vector `σ·π ψ` before contraction with the displayed `ψ†σ_k`. -/
def sigmaDotMomentum (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) : Spinor :=
  sigmaX *ᵥ momentum A d ψ 0 + sigmaY *ᵥ momentum A d ψ 1 +
    sigmaZ *ᵥ momentum A d ψ 2

/-- The three Pauli contractions with `σ·π ψ`. -/
def currentX (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (braket ψ (sigmaX *ᵥ sigmaDotMomentum A d ψ)).re

def currentY (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (braket ψ (sigmaY *ᵥ sigmaDotMomentum A d ψ)).re

def currentZ (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (braket ψ (sigmaZ *ᵥ sigmaDotMomentum A d ψ)).re

/-- Convective current `Re ψ†π_kψ`. -/
def convective (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) (k : Fin 3) : ℝ :=
  (braket ψ (momentum A d ψ k)).re

/-- Half the x-component of `curl(ψ†σψ)`, expressed via the derivative data. -/
def halfCurlX (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (spinDerivative d ψ 1 2 - spinDerivative d ψ 2 1) / 2

def halfCurlY (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (spinDerivative d ψ 2 0 - spinDerivative d ψ 0 2) / 2

def halfCurlZ (d : Fin 3 → Spinor) (ψ : Spinor) : ℝ :=
  (spinDerivative d ψ 0 1 - spinDerivative d ψ 1 0) / 2

/-- B164, first display component, with exactly the displayed sign and factor. -/
theorem pauli_current_x (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) :
    currentX A d ψ = convective A d ψ 0 + halfCurlX d ψ := by
  simp [currentX, convective, sigmaDotMomentum, momentum, halfCurlX,
    spinDerivative, braket, sigmaX, sigmaY, sigmaZ, Fin.isValue,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- B164, second display component. -/
theorem pauli_current_y (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) :
    currentY A d ψ = convective A d ψ 1 + halfCurlY d ψ := by
  simp [currentY, convective, sigmaDotMomentum, momentum, halfCurlY,
    spinDerivative, braket, sigmaX, sigmaY, sigmaZ, Fin.isValue,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- B164, third display component. -/
theorem pauli_current_z (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) :
    currentZ A d ψ = convective A d ψ 2 + halfCurlZ d ψ := by
  simp [currentZ, convective, sigmaDotMomentum, momentum, halfCurlZ,
    spinDerivative, braket, sigmaX, sigmaY, sigmaZ, Fin.isValue,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring


/-- The displayed zero-mode hypothesis, before taking the real part. -/
def ZeroMode (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor) : Prop :=
  sigmaDotMomentum A d ψ = 0

/-- A zero mode has cancelling convective and spin currents in direction one. -/
theorem zero_mode_cancel_x (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor)
    (h : ZeroMode A d ψ) : convective A d ψ 0 + halfCurlX d ψ = 0 := by
  rw [← pauli_current_x]
  change sigmaDotMomentum A d ψ = 0 at h
  simp [currentX, braket, h]

/-- A zero mode has cancelling convective and spin currents in direction two. -/
theorem zero_mode_cancel_y (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor)
    (h : ZeroMode A d ψ) : convective A d ψ 1 + halfCurlY d ψ = 0 := by
  rw [← pauli_current_y]
  change sigmaDotMomentum A d ψ = 0 at h
  simp [currentY, braket, h]

/-- A zero mode has cancelling convective and spin currents in direction three. -/
theorem zero_mode_cancel_z (A : Fin 3 → ℝ) (d : Fin 3 → Spinor) (ψ : Spinor)
    (h : ZeroMode A d ψ) : convective A d ψ 2 + halfCurlZ d ψ = 0 := by
  rw [← pauli_current_z]
  change sigmaDotMomentum A d ψ = 0 at h
  simp [currentZ, braket, h]


/-! ### Why `spinDerivative` is the actual derivative of spin density -/

lemma hasDerivAt_re_part {u : ℝ → ℂ} {u' : ℂ} {t : ℝ} (h : HasDerivAt u u' t) :
    HasDerivAt (fun s => (u s).re) u'.re t := by
  have H := (Complex.reCLM.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt
  simpa [Function.comp_def] using H

lemma hasDerivAt_im_part {u : ℝ → ℂ} {u' : ℂ} {t : ℝ} (h : HasDerivAt u u' t) :
    HasDerivAt (fun s => (u s).im) u'.im t := by
  have H := (Complex.imCLM.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt
  simpa [Function.comp_def] using H

/-- Along a differentiable spinor path, the derivative of `ψ†σ_xψ` is
`2 Re ψ†σ_xψ'`. -/
theorem hasDerivAt_spin_x {ψ : ℝ → Spinor} {dψ : Spinor} {t : ℝ}
    (h0 : HasDerivAt (fun s => ψ s 0) (dψ 0) t)
    (h1 : HasDerivAt (fun s => ψ s 1) (dψ 1) t) :
    HasDerivAt (fun s => (braket (ψ s) (sigmaX *ᵥ ψ s)).re)
      (2 * (braket (ψ t) (sigmaX *ᵥ dψ)).re) t := by
  have H := HasDerivAt.const_mul (2 : ℝ)
    (((hasDerivAt_re_part h0).mul (hasDerivAt_re_part h1)).add
      ((hasDerivAt_im_part h0).mul (hasDerivAt_im_part h1)))
  convert H using 1 <;>
    (try funext s) <;>
    simp [braket, sigmaX, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring


/-- Along a differentiable spinor path, the derivative of `ψ†σ_yψ` is
`2 Re ψ†σ_yψ'`. -/
theorem hasDerivAt_spin_y {ψ : ℝ → Spinor} {dψ : Spinor} {t : ℝ}
    (h0 : HasDerivAt (fun s => ψ s 0) (dψ 0) t)
    (h1 : HasDerivAt (fun s => ψ s 1) (dψ 1) t) :
    HasDerivAt (fun s => (braket (ψ s) (sigmaY *ᵥ ψ s)).re)
      (2 * (braket (ψ t) (sigmaY *ᵥ dψ)).re) t := by
  have H := HasDerivAt.const_mul (2 : ℝ)
    (((hasDerivAt_re_part h0).mul (hasDerivAt_im_part h1)).sub
      ((hasDerivAt_im_part h0).mul (hasDerivAt_re_part h1)))
  convert H using 1 <;>
    (try funext s) <;>
    simp [braket, sigmaY, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- Along a differentiable spinor path, the derivative of `ψ†σ_zψ` is
`2 Re ψ†σ_zψ'`. -/
theorem hasDerivAt_spin_z {ψ : ℝ → Spinor} {dψ : Spinor} {t : ℝ}
    (h0 : HasDerivAt (fun s => ψ s 0) (dψ 0) t)
    (h1 : HasDerivAt (fun s => ψ s 1) (dψ 1) t) :
    HasDerivAt (fun s => (braket (ψ s) (sigmaZ *ᵥ ψ s)).re)
      (2 * (braket (ψ t) (sigmaZ *ᵥ dψ)).re) t := by
  have H := (((hasDerivAt_re_part h0).mul (hasDerivAt_re_part h0)).add
      ((hasDerivAt_im_part h0).mul (hasDerivAt_im_part h0))).sub
    (((hasDerivAt_re_part h1).mul (hasDerivAt_re_part h1)).add
      ((hasDerivAt_im_part h1).mul (hasDerivAt_im_part h1)))
  convert H using 1 <;>
    (try funext s) <;>
    simp [braket, sigmaZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-! ### The explicitly invented weak reading

Dropping both real parts in the second display line is false.  This witness is
only a refutation of that invented complex-valued identity, not of B164.
-/

def weakPsi : Spinor := ![1, 0]
def weakDeriv : Fin 3 → Spinor := fun _ _ => 0
def weakA : Fin 3 → ℝ := ![0, 1, 0]

/-- The un-real-parted left side at the weak-reading witness is `-i`. -/
theorem weak_complex_lhs :
    braket weakPsi (sigmaX *ᵥ sigmaDotMomentum weakA weakDeriv weakPsi) = -Complex.I := by
  simp [braket, weakPsi, sigmaDotMomentum, momentum, weakA, weakDeriv,
    sigmaX, sigmaY, sigmaZ, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
    dotProduct, Fin.sum_univ_two]

/-- At the same witness the un-real-parted right side is zero. -/
theorem weak_complex_rhs :
    braket weakPsi (momentum weakA weakDeriv weakPsi 0) +
      (halfCurlX weakDeriv weakPsi : ℂ) = 0 := by
  simp [braket, momentum, weakPsi, weakA, weakDeriv, halfCurlX,
    spinDerivative, sigmaY, sigmaZ, Matrix.mulVec, dotProduct]

/-- STRAWMAN ONLY: deleting the displayed `Re` operations gives a false formula. -/
theorem weak_complex_reading_ne :
    braket weakPsi (sigmaX *ᵥ sigmaDotMomentum weakA weakDeriv weakPsi) ≠
      braket weakPsi (momentum weakA weakDeriv weakPsi 0) +
        (halfCurlX weakDeriv weakPsi : ℂ) := by
  rw [weak_complex_lhs, weak_complex_rhs]
  norm_num [Complex.ext_iff]


#print axioms pauli_current_x
#print axioms pauli_current_y
#print axioms pauli_current_z
#print axioms zero_mode_cancel_x
#print axioms zero_mode_cancel_y
#print axioms zero_mode_cancel_z
#print axioms hasDerivAt_re_part
#print axioms hasDerivAt_im_part
#print axioms hasDerivAt_spin_x
#print axioms hasDerivAt_spin_y
#print axioms hasDerivAt_spin_z
#print axioms weak_complex_lhs
#print axioms weak_complex_rhs
#print axioms weak_complex_reading_ne

end
end AtlasB164
end


/-! ## B164 — the identity again, and the Loss-Yau seed that is not self-sourced

Integrated from `.ultramath/smwwdl7d5/m13/B164.lean`.
-/

section
open Complex
open scoped ComplexConjugate

namespace B164

/-- Two-component complex spinors and their three Pauli actions. -/
abbrev Spinor := Fin 2 → ℂ

/-- The Pauli matrices, written as their action on a spinor; indices are 0=x, 1=y, 2=z. -/
def sigma (k : Fin 3) (v : Spinor) : Spinor :=
  (![ ![v 1, v 0],
      ![-Complex.I * v 1, Complex.I * v 0],
      ![v 0, -v 1] ] : (Fin 3 → Spinor)) k

/-- `pair k ψ v` is ψ†σ_k v. -/
def pair (k : Fin 3) (ψ v : Spinor) : ℂ :=
  conj (ψ 0) * sigma k v 0 + conj (ψ 1) * sigma k v 1

/-- Covariant derivative components, with d containing ∂ψ and a real vector potential A. -/
def covariant (ψ : Spinor) (d : Fin 3 → Spinor) (A : Fin 3 → ℝ) (l : Fin 3) : Spinor :=
  fun a => -Complex.I * d l a - (A l : ℂ) * ψ a

/-- The kth component of ψ†σ_k(σ·π)ψ. -/
def pauliCurrentRaw (k : Fin 3) (ψ : Spinor) (π : Fin 3 → Spinor) : ℂ :=
  ∑ l : Fin 3, pair k ψ (sigma l (π l))

/-- The kth convective term ψ†π_kψ. -/
def convectiveRaw (k : Fin 3) (ψ : Spinor) (π : Fin 3 → Spinor) : ℂ :=
  ∑ a : Fin 2, conj (ψ a) * π k a

/-- Half the curl of spin density.  For actual differentiable functions,
  ∂_l(ψ†σ_mψ) = 2 Re(pair m ψ (dψ_l)). -/
def halfCurlSpin (k : Fin 3) (ψ : Spinor) (d : Fin 3 → Spinor) : ℝ :=
  (![ (pair 2 ψ (d 1)).re - (pair 1 ψ (d 2)).re,
      (pair 0 ψ (d 2)).re - (pair 2 ψ (d 0)).re,
      (pair 1 ψ (d 0)).re - (pair 0 ψ (d 1)).re ] : (Fin 3 → ℝ)) k

/-- Exact algebraic Pauli-current identity for arbitrary values ψ, derivatives d
and a real vector potential. This has no zero-mode hypothesis. -/
theorem pauli_current_identity (k : Fin 3) (ψ : Spinor) (d : Fin 3 → Spinor)
    (A : Fin 3 → ℝ) :
    (pauliCurrentRaw k ψ (covariant ψ d A)).re =
      (convectiveRaw k ψ (covariant ψ d A)).re + halfCurlSpin k ψ d := by
  fin_cases k <;>
    simp [pauliCurrentRaw, convectiveRaw, halfCurlSpin, pair, sigma,
      covariant, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re,
      Complex.mul_im] <;>
    ring

lemma pair_zero (k : Fin 3) (ψ : Spinor) : pair k ψ 0 = 0 := by
  fin_cases k <;> simp [pair, sigma]

lemma pair_sum_sigma (k : Fin 3) (ψ : Spinor) (π : Fin 3 → Spinor) :
    pair k ψ (∑ l : Fin 3, sigma l (π l)) = pauliCurrentRaw k ψ π := by
  fin_cases k <;>
    simp [pair, pauliCurrentRaw, sigma, Fin.sum_univ_three] <;>
    ring

/-- Product rule for a Pauli spin density along any differentiable spinor curve. -/
theorem hasDerivAt_pair_self (k : Fin 3) (ψ : ℝ → Spinor) (t : ℝ) (d : Spinor)
    (h0 : HasDerivAt (fun t => ψ t 0) (d 0) t)
    (h1 : HasDerivAt (fun t => ψ t 1) (d 1) t) :
    HasDerivAt (fun t => pair k (ψ t) (ψ t))
      (pair k d (ψ t) + pair k (ψ t) d) t := by
  fin_cases k
  · convert (h0.star.mul h1).add (h1.star.mul h0) using 1
    funext x
    simp [pair, sigma]
    ring
    simp [pair, sigma]
    ring
  · convert (h0.star.mul (h1.const_mul (-Complex.I))).add
      (h1.star.mul (h0.const_mul Complex.I)) using 1
    funext x
    simp [pair, sigma]
    ring
    simp [pair, sigma]
    ring
  · convert (h0.star.mul h0).sub (h1.star.mul h1) using 1
    funext x
    simp [pair, sigma]
    ring
    simp [pair, sigma]
    ring

/-- Hermitian symmetry turns the derivative into twice a real part. -/
theorem pair_derivative_eq_two_re (k : Fin 3) (ψ d : Spinor) :
    pair k d ψ + pair k ψ d = ((2 * (pair k ψ d).re : ℝ) : ℂ) := by
  fin_cases k <;> apply Complex.ext <;>
    simp [pair, sigma, Complex.add_re, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- A zero mode makes all three Pauli currents vanish. -/
theorem zero_mode_pauli_current (k : Fin 3) (ψ : Spinor) (d : Fin 3 → Spinor)
    (A : Fin 3 → ℝ)
    (hzero : ∑ l : Fin 3, sigma l (covariant ψ d A l) = 0) :
    (convectiveRaw k ψ (covariant ψ d A)).re + halfCurlSpin k ψ d = 0 := by
  rw [← pauli_current_identity, ← pair_sum_sigma, hzero, pair_zero]
  rfl

/-- A common spinor value for the finite countermodels. -/
def cePsi : Spinor := ![1, 0]

/-- A zero real vector potential. -/
def ceA : Fin 3 → ℝ := 0

/-- A finite zero-mode jet used only for the careless delete-`Re` reading. -/
def ceDeleteReD : Fin 3 → Spinor := ![![-1, 0], 0, ![0, -1]]

/-- This finite jet is a zero mode at its point. -/
theorem ceDeleteRe_zero_mode :
    ∑ l : Fin 3, sigma l (covariant cePsi ceDeleteReD ceA l) = 0 := by
  funext a
  fin_cases a <;>
    simp [sigma, covariant, cePsi, ceDeleteReD, ceA, Fin.sum_univ_three]

/-- Countermodel to the invented reading that deletes the displayed real part:
the zero-mode left side vanishes, but the complex right side is `I`, not zero.
This is NOT a counterexample to the card's displayed formula. -/
theorem delete_Re_countermodel :
    pauliCurrentRaw 0 cePsi (covariant cePsi ceDeleteReD ceA) = 0 ∧
      convectiveRaw 0 cePsi (covariant cePsi ceDeleteReD ceA) +
        (halfCurlSpin 0 cePsi ceDeleteReD : ℂ) ≠ 0 := by
  constructor
  · rw [← pair_sum_sigma, ceDeleteRe_zero_mode, pair_zero]
  · simp [convectiveRaw, halfCurlSpin, pair, sigma, covariant,
      cePsi, ceDeleteReD, ceA, Fin.sum_univ_two]

/-- A nearby faithful identity does hold on the same finite jet. -/
theorem delete_Re_countermodel_faithful_side :
    (convectiveRaw 0 cePsi (covariant cePsi ceDeleteReD ceA)).re +
      halfCurlSpin 0 cePsi ceDeleteReD = 0 := by
  exact zero_mode_pauli_current 0 cePsi ceDeleteReD ceA ceDeleteRe_zero_mode

/-- A finite non-zero-mode jet for the careless universal-cancellation reading. -/
def ceDeleteModeD : Fin 3 → Spinor := ![![1, 0], 0, 0]

/-- Countermodel to the invented claim that the convective and spin currents
cancel without assuming a zero mode. It is NOT a counterexample to the display. -/
theorem delete_zero_mode_countermodel :
    (∑ l : Fin 3, sigma l (covariant cePsi ceDeleteModeD ceA l)) ≠ 0 ∧
      (convectiveRaw 1 cePsi (covariant cePsi ceDeleteModeD ceA)).re +
        halfCurlSpin 1 cePsi ceDeleteModeD = -1 := by
  constructor
  · intro h
    have h1 := congrFun h 1
    norm_num [sigma, covariant, cePsi, ceDeleteModeD, ceA,
      Fin.sum_univ_three] at h1
  · norm_num [convectiveRaw, halfCurlSpin, pair, sigma, covariant,
      cePsi, ceDeleteModeD, ceA, Fin.sum_univ_two]

end B164

#print axioms B164.Spinor
#print axioms B164.sigma
#print axioms B164.pair
#print axioms B164.covariant
#print axioms B164.pauliCurrentRaw
#print axioms B164.convectiveRaw
#print axioms B164.halfCurlSpin
#print axioms B164.pauli_current_identity
#print axioms B164.pair_zero
#print axioms B164.pair_sum_sigma
#print axioms B164.hasDerivAt_pair_self
#print axioms B164.pair_derivative_eq_two_re
#print axioms B164.zero_mode_pauli_current
#print axioms B164.cePsi
#print axioms B164.ceA
#print axioms B164.ceDeleteReD
#print axioms B164.ceDeleteRe_zero_mode
#print axioms B164.delete_Re_countermodel
#print axioms B164.delete_Re_countermodel_faithful_side
#print axioms B164.ceDeleteModeD
#print axioms B164.delete_zero_mode_countermodel
end
