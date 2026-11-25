/-
Eighth batch: the remaining analytic and geometric cards, plus the referee notes.

Each contribution is reproduced verbatim except for its import line; all are self-contained
(`import Mathlib`) and keep their own scope delimiters. Nothing in the earlier modules is
modified.
-/
import Mathlib


/-! ## B27 — the path inequality, with both equality directions

Integrated from `.ultramath/smwvwr2ce/m13/B27.lean`.
-/

/-!
# B27: energy dominates squared length divided by duration

For a speed in `L²` on a finite measure space, the proof is the exact centred-square
(variance) identity.  The interval corollaries use Lebesgue measure on `Ioc 0 τ`.
Equality is constant speed almost everywhere; pointwise constancy is neither needed
nor implied by equality of the integrals.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace AtlasB27

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrability of the squared deviation from an arbitrary constant. -/
lemma integrable_centered_sq [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (c : ℝ) :
    Integrable (fun x => (f x - c) ^ 2) μ := by
  have hlin : Integrable (fun x => (2 * f x) * c) μ := (hf.const_mul 2).mul_const c
  have h : Integrable (fun x => f x ^ 2 - (2 * f x) * c + c ^ 2) μ :=
    (hf2.sub hlin).add (integrable_const _)
  convert h using 1
  ext x
  ring

/-- The integral of a squared deviation, expanded without nonnegative assumptions. -/
lemma integral_centered_sq [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (c : ℝ) :
    (∫ x, (f x - c) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - 2 * c * (∫ x, f x ∂μ) + μ.real univ * c ^ 2 := by
  have hlin : Integrable (fun x => (2 * f x) * c) μ := (hf.const_mul 2).mul_const c
  have hrewrite : (fun x => (f x - c) ^ 2) =
      (fun x => f x ^ 2 - (2 * f x) * c + c ^ 2) := by
    funext x
    ring
  rw [hrewrite]
  calc
    (∫ x, f x ^ 2 - (2 * f x) * c + c ^ 2 ∂μ) =
        (∫ x, f x ^ 2 - (2 * f x) * c ∂μ) + ∫ _x : α, c ^ 2 ∂μ := by
      apply integral_add
      · exact hf2.sub hlin
      · exact integrable_const _
    _ = (∫ x, f x ^ 2 ∂μ) - 2 * c * (∫ x, f x ∂μ) + μ.real univ * c ^ 2 := by
      rw [integral_sub hf2 hlin]
      simp only [integral_const_mul, integral_mul_const, integral_const, smul_eq_mul]
      ring

/-- Exact variance defect: Cauchy--Schwarz is nonnegativity of this integral. -/
lemma measureReal_mul_integral_centered_sq [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : μ.real univ ≠ 0) :
    μ.real univ * (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) =
      μ.real univ * (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  rw [integral_centered_sq hf hf2]
  field_simp [hm]
  ring

/-- Cauchy--Schwarz in the form `(∫ speed)² ≤ duration * ∫ speed²`. -/
theorem sq_integral_le_measureReal_mul_integral_sq [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : 0 < μ.real univ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * (∫ x, f x ^ 2 ∂μ) := by
  have hdefect := measureReal_mul_integral_centered_sq hf hf2 hm.ne'
  have hnonneg : 0 ≤ ∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [mul_nonneg hm.le hnonneg]

/-- Equality holds exactly for an almost-everywhere constant function. -/
theorem sq_integral_eq_measureReal_mul_integral_sq_iff [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : 0 < μ.real univ) :
    (∫ x, f x ∂μ) ^ 2 = μ.real univ * (∫ x, f x ^ 2 ∂μ) ↔
      ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  constructor
  · intro heq
    refine ⟨(∫ x, f x ∂μ) / μ.real univ, ?_⟩
    have hid := measureReal_mul_integral_centered_sq hf hf2 hm.ne'
    have hmul : μ.real univ *
        (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) = 0 := by
      nlinarith
    have hzero : (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hm.ne'
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (integrable_centered_sq hf hf2 _)).mp hzero
    filter_upwards [hae] with x hx
    change (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 = 0 at hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · rintro ⟨c, hc⟩
    have hint : (∫ x, f x ∂μ) = μ.real univ * c := by
      rw [integral_congr_ae hc, integral_const, smul_eq_mul]
    have hc2 : (fun x => f x ^ 2) =ᵐ[μ] fun _ => c ^ 2 := by
      filter_upwards [hc] with x hx
      rw [hx]
    have hint2 : (∫ x, f x ^ 2 ∂μ) = μ.real univ * c ^ 2 := by
      rw [integral_congr_ae hc2, integral_const, smul_eq_mul]
    rw [hint, hint2]
    ring

/-- The length of a parametrised path, with its speed supplied as a real function. -/
def pathLength (speed : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t in 0..τ, speed t

/-- The metric energy of the same speed record: `∫ speed² dt`. -/
def pathEnergy (speed : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t in 0..τ, speed t ^ 2

lemma volume_restrict_Ioc_real (τ : ℝ) (hτ : 0 ≤ τ) :
    (volume.restrict (Ioc 0 τ)).real univ = τ := by
  simp [measureReal_def, Real.volume_Ioc, hτ]

/-- **B27, undivided form.**  Squared path length is at most duration times energy. -/
theorem pathLength_sq_le (τ : ℝ) (hτ : 0 < τ) (speed : ℝ → ℝ)
    (hs : IntegrableOn speed (Ioc 0 τ))
    (hs2 : IntegrableOn (fun t => speed t ^ 2) (Ioc 0 τ)) :
    pathLength speed τ ^ 2 ≤ τ * pathEnergy speed τ := by
  have hmass : (volume.restrict (Ioc 0 τ)).real univ = τ :=
    volume_restrict_Ioc_real τ hτ.le
  have h := sq_integral_le_measureReal_mul_integral_sq hs hs2 (μ := volume.restrict (Ioc 0 τ))
    (by rw [hmass]; exact hτ)
  simpa only [pathLength, pathEnergy, intervalIntegral.integral_of_le hτ.le, hmass] using h

/-- **B27, card's divided form.**  Energy is at least squared length divided by duration. -/
theorem pathLength_sq_div_le_pathEnergy (τ : ℝ) (hτ : 0 < τ) (speed : ℝ → ℝ)
    (hs : IntegrableOn speed (Ioc 0 τ))
    (hs2 : IntegrableOn (fun t => speed t ^ 2) (Ioc 0 τ)) :
    pathLength speed τ ^ 2 / τ ≤ pathEnergy speed τ := by
  apply (div_le_iff₀ hτ).2
  have h := pathLength_sq_le τ hτ speed hs hs2
  nlinarith

/-- **B27, equality in both directions.**  Constant speed means a.e. on the time interval. -/
theorem pathLength_sq_eq_iff_ae_const (τ : ℝ) (hτ : 0 < τ) (speed : ℝ → ℝ)
    (hs : IntegrableOn speed (Ioc 0 τ))
    (hs2 : IntegrableOn (fun t => speed t ^ 2) (Ioc 0 τ)) :
    pathLength speed τ ^ 2 = τ * pathEnergy speed τ ↔
      ∃ c : ℝ, speed =ᵐ[volume.restrict (Ioc 0 τ)] fun _ => c := by
  have hmass : (volume.restrict (Ioc 0 τ)).real univ = τ :=
    volume_restrict_Ioc_real τ hτ.le
  have h := sq_integral_eq_measureReal_mul_integral_sq_iff hs hs2
    (μ := volume.restrict (Ioc 0 τ)) (by rw [hmass]; exact hτ)
  simpa only [pathLength, pathEnergy, intervalIntegral.integral_of_le hτ.le, hmass] using h

/-- The divided inequality has exactly the same constant-speed equality case. -/
theorem pathLength_sq_div_eq_pathEnergy_iff_ae_const (τ : ℝ) (hτ : 0 < τ)
    (speed : ℝ → ℝ) (hs : IntegrableOn speed (Ioc 0 τ))
    (hs2 : IntegrableOn (fun t => speed t ^ 2) (Ioc 0 τ)) :
    pathLength speed τ ^ 2 / τ = pathEnergy speed τ ↔
      ∃ c : ℝ, speed =ᵐ[volume.restrict (Ioc 0 τ)] fun _ => c := by
  rw [div_eq_iff hτ.ne']
  have h := pathLength_sq_eq_iff_ae_const τ hτ speed hs hs2
  constructor <;> intro heq
  · apply h.mp
    nlinarith
  · apply h.mpr at heq
    nlinarith

#print axioms AtlasB27.integrable_centered_sq
#print axioms AtlasB27.integral_centered_sq
#print axioms AtlasB27.measureReal_mul_integral_centered_sq
#print axioms AtlasB27.sq_integral_le_measureReal_mul_integral_sq
#print axioms AtlasB27.sq_integral_eq_measureReal_mul_integral_sq_iff
#print axioms AtlasB27.volume_restrict_Ioc_real
#print axioms AtlasB27.pathLength_sq_le
#print axioms AtlasB27.pathLength_sq_div_le_pathEnergy
#print axioms AtlasB27.pathLength_sq_eq_iff_ae_const
#print axioms AtlasB27.pathLength_sq_div_eq_pathEnergy_iff_ae_const

end AtlasB27


/-! ## B28 — the SLD tensor is F/4 + C/8, not F/4 - iC/8 (REFUTATION)

Integrated from `.ultramath/smwvwr2ce/m12/B28.lean`.
-/

open scoped ComplexConjugate BigOperators ComplexOrder
open Matrix

namespace B28

/-- The SLD quantum geometric tensor entry used by card B28. -/
noncomputable def sldQGT {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) : ℂ :=
  (1 / 4 : ℂ) * (ρ * A * B).trace

/-- The quantum Fisher/Bures metric, with the standard one-half symmetriser. -/
noncomputable def sldMetric {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) : ℂ :=
  (1 / 2 : ℂ) * (ρ * (A * B + B * A)).trace

/-- The (unscaled) commutator trace appearing in the ledger formula. -/
noncomputable def commutatorTrace {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) : ℂ :=
  (ρ * (A * B - B * A)).trace

/-- The correct complex decomposition: no Hermitian or density hypothesis is needed. -/
theorem sldQGT_eq_metric_add_commutator {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) :
    sldQGT ρ A B =
      (1 / 4 : ℂ) * sldMetric ρ A B + (1 / 8 : ℂ) * commutatorTrace ρ A B := by
  simp only [sldQGT, sldMetric, commutatorTrace, mul_add, mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Matrix.mul_assoc]
  ring

/-- Cyclicity of trace and Hermitianness identify reversal with conjugation. -/
theorem trace_reverse_eq_conj {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ)
    (hρ : ρᴴ = ρ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (ρ * B * A).trace = conj (ρ * A * B).trace := by
  calc
    (ρ * B * A).trace = ((B * A) * ρ).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm ρ (B * A)
    _ = ((ρ * A * B)ᴴ).trace := by
      congr 1
      simp only [Matrix.conjTranspose_mul, hρ, hA, hB, Matrix.mul_assoc]
    _ = conj (ρ * A * B).trace := by
      simpa using Matrix.trace_conjTranspose (ρ * A * B)

/-- The symmetrised trace is twice the real part of the ordered trace. -/
theorem sldMetric_eq_real {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ)
    (hρ : ρᴴ = ρ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    sldMetric ρ A B = (((ρ * A * B).trace.re : ℝ) : ℂ) := by
  simp only [sldMetric, mul_add, Matrix.trace_add, Matrix.mul_assoc]
  have hrev := trace_reverse_eq_conj ρ A B hρ hA hB
  simp only [Matrix.mul_assoc] at hrev
  rw [hrev]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The commutator trace is `2*I` times the imaginary part of the ordered trace. -/
theorem commutatorTrace_eq_two_I_mul_im {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ)
    (hρ : ρᴴ = ρ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    commutatorTrace ρ A B =
      2 * Complex.I * (((ρ * A * B).trace.im : ℝ) : ℂ) := by
  simp only [commutatorTrace, mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  have hrev := trace_reverse_eq_conj ρ A B hρ hA hB
  simp only [Matrix.mul_assoc] at hrev
  rw [hrev]
  apply Complex.ext
  · simp
  · simp
    ring

/-- The real-part law in the card has the advertised factor `1/4`. -/
theorem sldQGT_re_eq_metric_re_div_four {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ)
    (hρ : ρᴴ = ρ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (sldQGT ρ A B).re = (sldMetric ρ A B).re / 4 := by
  rw [sldMetric_eq_real ρ A B hρ hA hB]
  simp [sldQGT]
  ring

/-- The imaginary part, viewed as a real scalar embedded in `ℂ`, is `-i*C/8`. -/
theorem sldQGT_im_eq_neg_I_mul_commutator_div_eight {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ)
    (hρ : ρᴴ = ρ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (((sldQGT ρ A B).im : ℝ) : ℂ) =
      -(Complex.I / 8) * commutatorTrace ρ A B := by
  rw [commutatorTrace_eq_two_I_mul_im ρ A B hρ hA hB]
  apply Complex.ext
  · simp [sldQGT]
    ring
  · simp [sldQGT]

/-- This is the real curvature convention that makes the HTML headline identity hold. -/
noncomputable def uhlmannFromCommutator {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) : ℂ :=
  (Complex.I / 4) * commutatorTrace ρ A B

/-- The HTML headline is correct with `g=F/4` and `Ω=i*C/4`. -/
theorem sldQGT_eq_metric_sub_uhlmann {n : Type*} [Fintype n]
    (ρ A B : Matrix n n ℂ) :
    sldQGT ρ A B =
      (1 / 4 : ℂ) * sldMetric ρ A B -
        (Complex.I / 2) * uhlmannFromCommutator ρ A B := by
  rw [sldQGT_eq_metric_add_commutator]
  unfold uhlmannFromCommutator
  have h : -((Complex.I / 2) * ((Complex.I / 4) * commutatorTrace ρ A B)) =
      (1 / 8 : ℂ) * commutatorTrace ρ A B := by
    calc
      -((Complex.I / 2) * ((Complex.I / 4) * commutatorTrace ρ A B)) =
          -(Complex.I * Complex.I) / 8 * commutatorTrace ρ A B := by ring
      _ = (1 / 8 : ℂ) * commutatorTrace ρ A B := by rw [Complex.I_mul_I]; ring
  rw [sub_eq_add_neg, h]

/-- A full-rank mixed diagonal qubit state. -/
noncomputable def witnessRho : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(3 / 4 : ℂ), 0; 0, (1 / 4 : ℂ)]

/-- Pauli X. -/
def witnessL1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli Y. -/
def witnessL2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- A tangent for which Pauli X is an SLD. -/
noncomputable def witnessD1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (1 / 2 : ℂ); (1 / 2 : ℂ), 0]

/-- A tangent for which Pauli Y is an SLD. -/
noncomputable def witnessD2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I / 2; Complex.I / 2, 0]

/-- The predicate `D = ½(ρL+Lρ)` from the card. -/
def IsSLD {n : Type*} [Fintype n]
    (ρ D L : Matrix n n ℂ) : Prop :=
  D = (1 / 2 : ℂ) • (ρ * L + L * ρ)

 theorem witness_sld1 : IsSLD witnessRho witnessD1 witnessL1 := by
  unfold IsSLD
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessD1, witnessRho, witnessL1, Matrix.mul_apply, Fin.sum_univ_two]

 theorem witness_sld2 : IsSLD witnessRho witnessD2 witnessL2 := by
  unfold IsSLD
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessD2, witnessRho, witnessL2, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I] <;> ring

 theorem witnessRho_trace : witnessRho.trace = 1 := by
  norm_num [witnessRho, Matrix.trace_fin_two]

 theorem witnessRho_hermitian : witnessRhoᴴ = witnessRho := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessRho, Matrix.conjTranspose_apply]

 theorem witnessRho_posDef : witnessRho.PosDef := by
  have hdiag : witnessRho = Matrix.diagonal ![(3 / 4 : ℂ), (1 / 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [witnessRho, Matrix.diagonal]
  rw [hdiag]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

 theorem witnessL1_hermitian : witnessL1ᴴ = witnessL1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessL1, Matrix.conjTranspose_apply]

 theorem witnessL2_hermitian : witnessL2ᴴ = witnessL2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessL2, Matrix.conjTranspose_apply]

 theorem witness_QGT : sldQGT witnessRho witnessL1 witnessL2 = Complex.I / 8 := by
  norm_num [sldQGT, witnessRho, witnessL1, witnessL2, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  ring

 theorem witness_metric : sldMetric witnessRho witnessL1 witnessL2 = 0 := by
  norm_num [sldMetric, witnessRho, witnessL1, witnessL2, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

 theorem witness_commutatorTrace :
    commutatorTrace witnessRho witnessL1 witnessL2 = Complex.I := by
  norm_num [commutatorTrace, witnessRho, witnessL1, witnessL2, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  ring

/-- The displayed complex identity in the ledger is false for this genuine mixed-state SLD example. -/
theorem witness_violates_displayed_card_formula :
    sldQGT witnessRho witnessL1 witnessL2 ≠
      (1 / 4 : ℂ) * sldMetric witnessRho witnessL1 witnessL2 -
        (Complex.I / 8) * commutatorTrace witnessRho witnessL1 witnessL2 := by
  rw [witness_QGT, witness_metric, witness_commutatorTrace]
  norm_num [Complex.ext_iff, Complex.I_mul_I]

#print axioms B28.sldQGT_eq_metric_add_commutator
#print axioms B28.trace_reverse_eq_conj
#print axioms B28.sldMetric_eq_real
#print axioms B28.commutatorTrace_eq_two_I_mul_im
#print axioms B28.sldQGT_re_eq_metric_re_div_four
#print axioms B28.sldQGT_eq_metric_sub_uhlmann
#print axioms B28.sldQGT_im_eq_neg_I_mul_commutator_div_eight
#print axioms B28.witness_sld1
#print axioms B28.witness_sld2
#print axioms B28.witnessRho_trace
#print axioms B28.witnessRho_hermitian
#print axioms B28.witnessRho_posDef
#print axioms B28.witnessL1_hermitian
#print axioms B28.witnessL2_hermitian
#print axioms B28.witness_QGT
#print axioms B28.witness_metric
#print axioms B28.witness_commutatorTrace
#print axioms B28.witness_violates_displayed_card_formula

end B28


/-! ## B73 — the gap exponents, and what antisymmetry removes

Integrated from `.ultramath/smwvwr2ce/m1/B73.lean`.
-/

open scoped Topology
open Filter
open Asymptotics

namespace RelationalAtlas.B73

noncomputable section

/-- The positive-gap side of a square-root collision. -/
abbrev collision : Filter ℝ := 𝓝[>] (0 : ℝ)

/-- Real finite core of the Petermann factor.  A real biorthogonal overlap is
used after fixing phases; its square is the squared modulus in this model. -/
def petermann (overlap : ℝ → ℝ) (g : ℝ) : ℝ := (overlap g)⁻¹ ^ 2

/-- The factorisation displayed in HTML B73: `F = c · gap⁻² √K`. -/
def displayedCurvature (c : ℝ) (overlap : ℝ → ℝ) (g : ℝ) : ℝ :=
  c * g⁻¹ ^ 2 * Real.sqrt (petermann overlap g)

/-- The Petermann factor has exactly the inverse-square asymptotic class when
its overlap is asymptotic to the gap. -/
theorem petermann_isEquivalent {overlap : ℝ → ℝ}
    (h : overlap ~[collision] fun g => g) :
    petermann overlap ~[collision] fun g => g ^ (-2 : ℤ) := by
  have hpow : petermann overlap ~[collision] (fun g : ℝ => g⁻¹ ^ 2) := by
    change (fun g : ℝ => (overlap g)⁻¹ ^ 2) ~[collision] (fun g => g⁻¹ ^ 2)
    exact h.inv.pow 2
  apply hpow.congr_right
  filter_upwards [] with g
  simp [_root_.zpow_neg, inv_pow]

/-- Square-rooting the Petermann asymptotic gives an inverse gap, not an
inverse square gap. -/
theorem sqrt_petermann_isEquivalent {overlap : ℝ → ℝ}
    (h : overlap ~[collision] fun g => g) :
    (fun g => Real.sqrt (petermann overlap g)) ~[collision] fun g => g⁻¹ := by
  have hK : petermann overlap ~[collision] (fun g : ℝ => g⁻¹ ^ 2) := by
    change (fun g : ℝ => (overlap g)⁻¹ ^ 2) ~[collision] (fun g => g⁻¹ ^ 2)
    exact h.inv.pow 2
  have hpow : (fun g : ℝ => petermann overlap g ^ (1 / 2 : ℝ)) ~[collision]
      (fun g => (g⁻¹ ^ 2) ^ (1 / 2 : ℝ)) := by
    exact hK.rpow (fun g : ℝ => sq_nonneg g⁻¹)
  have hright : (fun g : ℝ => (g⁻¹ ^ 2) ^ (1 / 2 : ℝ)) =ᶠ[collision]
      (fun g => g⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hg)]
  apply (hpow.congr_right hright).congr_left
  filter_upwards [] with g
  exact (Real.sqrt_eq_rpow _).symm

/-- The displayed B73 factorisation yields exponent `-3`.  No antisymmetry
hypothesis is needed for this particular algebraic implication. -/
theorem displayedCurvature_isEquivalent {c : ℝ} {overlap : ℝ → ℝ}
    (h : overlap ~[collision] fun g => g) :
    displayedCurvature c overlap ~[collision] fun g => c * g ^ (-3 : ℤ) := by
  have hprod : (fun g : ℝ => c * g⁻¹ ^ 2 * Real.sqrt (petermann overlap g)) ~[collision]
      (fun g => c * g⁻¹ ^ 2 * g⁻¹) := by
    exact (IsEquivalent.refl (l := collision)
      (u := fun g : ℝ => c * g⁻¹ ^ 2)).mul (sqrt_petermann_isEquivalent h)
  apply hprod.congr_right
  filter_upwards [] with g
  simp [_root_.zpow_neg, pow_succ, mul_assoc]

/-- With the curvature prefactor normalised to one, this is the ledger's
literal `F ∼ gap⁻³` in Mathlib's ratio-to-one sense. -/
theorem displayedCurvature_one_isEquivalent {overlap : ℝ → ℝ}
    (h : overlap ~[collision] fun g => g) :
    displayedCurvature 1 overlap ~[collision] fun g => g ^ (-3 : ℤ) := by
  simpa only [one_mul] using displayedCurvature_isEquivalent (c := 1) h

variable {ι : Type*} [Fintype ι]

/-- Sum of a finite real antisymmetric matrix vanishes. -/
theorem sum_matrix_eq_zero_of_antisymm (a : ι → ι → ℝ)
    (ha : ∀ i j, a i j = -a j i) : (∑ i, ∑ j, a i j) = 0 := by
  have hneg : (∑ i, ∑ j, a i j) = -(∑ i, ∑ j, a i j) := by
    calc
      (∑ i, ∑ j, a i j) = ∑ i, ∑ j, a j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -a i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [ha j i]
      _ = -(∑ i, ∑ j, a i j) := by simp
  linarith

/-- First-order numerator in a finite sum-over-states model.  The matrix `a`
is the value at the collision and `b` is the first-order coefficient. -/
def collisionNumerator (a b : ι → ι → ℝ) (g : ℝ) : ℝ :=
  ∑ i, ∑ j, (a i j + g * b i j)

/-- A denominator with the naively counted four gap powers. -/
def rationalCurvature (a b : ι → ι → ℝ) (g : ℝ) : ℝ :=
  collisionNumerator a b g / g ^ 4

/-- Expansion of the finite numerator into its zeroth and first orders. -/
theorem collisionNumerator_expand (a b : ι → ι → ℝ) (g : ℝ) :
    collisionNumerator a b g = (∑ i, ∑ j, a i j) + g * (∑ i, ∑ j, b i j) := by
  simp [collisionNumerator, Finset.sum_add_distrib, Finset.mul_sum]

/-- Antisymmetry makes the zeroth-order numerator vanish and therefore
factors out exactly one power of the gap. -/
theorem collisionNumerator_of_antisymm (a b : ι → ι → ℝ)
    (ha : ∀ i j, a i j = -a j i) (g : ℝ) :
    collisionNumerator a b g = g * (∑ i, ∑ j, b i j) := by
  rw [collisionNumerator_expand, sum_matrix_eq_zero_of_antisymm a ha, zero_add]

/-- Away from the collision, antisymmetry reduces the naive `gap⁻⁴`
rational function to `gap⁻³`. -/
theorem rationalCurvature_of_antisymm (a b : ι → ι → ℝ)
    (ha : ∀ i j, a i j = -a j i) {g : ℝ} (hg : g ≠ 0) :
    rationalCurvature a b g = (∑ i, ∑ j, b i j) * g ^ (-3 : ℤ) := by
  rw [rationalCurvature, collisionNumerator_of_antisymm a b ha]
  field_simp

/-- The reduced curvature is asymptotic to the displayed inverse cube,
including the exact first-order sum-rule coefficient. -/
theorem rationalCurvature_isEquivalent (a b : ι → ι → ℝ)
    (ha : ∀ i j, a i j = -a j i) :
    rationalCurvature a b ~[collision]
      fun g => (∑ i, ∑ j, b i j) * g ^ (-3 : ℤ) := by
  apply IsEquivalent.congr_left IsEquivalent.refl
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact (rationalCurvature_of_antisymm a b ha (show 0 < g from hg).ne').symm

/-- Without the antisymmetry cancellation, the same finite model can retain
all four inverse powers.  This one-state example has numerator identically 1. -/
theorem rationalCurvature_naive_four :
    (fun g : ℝ => rationalCurvature (fun _ _ : Unit => (1 : ℝ))
      (fun _ _ => 0) g) ~[collision] fun g => g ^ (-4 : ℤ) := by
  apply IsEquivalent.congr_left IsEquivalent.refl
  filter_upwards [self_mem_nhdsWithin] with g hg
  simp [rationalCurvature, collisionNumerator, _root_.zpow_neg]

end

end RelationalAtlas.B73

#print axioms RelationalAtlas.B73.petermann_isEquivalent
#print axioms RelationalAtlas.B73.sqrt_petermann_isEquivalent
#print axioms RelationalAtlas.B73.displayedCurvature_isEquivalent
#print axioms RelationalAtlas.B73.displayedCurvature_one_isEquivalent
#print axioms RelationalAtlas.B73.sum_matrix_eq_zero_of_antisymm
#print axioms RelationalAtlas.B73.collisionNumerator_expand
#print axioms RelationalAtlas.B73.collisionNumerator_of_antisymm
#print axioms RelationalAtlas.B73.rationalCurvature_of_antisymm
#print axioms RelationalAtlas.B73.rationalCurvature_isEquivalent
#print axioms RelationalAtlas.B73.rationalCurvature_naive_four


/-! ## B7 — signature steps at unit-circle roots, both directions

Integrated from `.ultramath/smwvwr2ce/m6/B7.lean`.
-/

/-!
# B7 — Unit-circle roots are where the integer may step

This file isolates the finite-dimensional algebraic core of the card.  The
ambient knot theory (construction of a Seifert matrix and identification of the
square knot) is deliberately not asserted as a formal definition.
-/

namespace RelationalAtlas.B7

open scoped ComplexConjugate
open Matrix

abbrev R2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Complexification of a real matrix. -/
def complexify (V : R2) : C2 := V.map (fun x : ℝ ↦ (x : ℂ))

/-- The Levine–Tristram Hermitian form displayed on card B7. -/
def ltForm (V : R2) (ω : ℂ) : C2 :=
  (1 - ω) • complexify V + (1 - conj ω) • complexify V.transpose

/-- The unnormalised Alexander matrix `V - t Vᵀ`, over `ℂ`. -/
def alexanderMatrix (V : R2) (t : ℂ) : C2 :=
  complexify V - t • complexify V.transpose

/-- The determinant representative of the Alexander polynomial. -/
def alexanderDet (V : R2) (t : ℂ) : ℂ := (alexanderMatrix V t).det

/-- The form on the card is Hermitian for every real Seifert matrix and every
complex parameter; no unit-modulus hypothesis is needed for this identity. -/
theorem ltForm_isHermitian (V : R2) (ω : ℂ) : (ltForm V ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ltForm, complexify] <;> ring

/-- On the unit circle the B7 form is a nonzero scalar multiple of the
Alexander matrix, with the exact scalar `(1 - ω)`. -/
theorem ltForm_eq_smul_alexanderMatrix (V : R2) {ω : ℂ} (hω : ‖ω‖ = 1) :
    ltForm V ω = (1 - ω) • alexanderMatrix V ω⁻¹ := by
  have h_conj : conj ω = ω⁻¹ := (Complex.inv_eq_conj hω).symm
  have hω0 : ω ≠ 0 := by
    intro h
    simp [h] at hω
  unfold ltForm
  rw [h_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alexanderMatrix, complexify] <;>
    field_simp <;> ring

/-- The exact determinant normalisation.  In particular, when `ω ≠ 1`, the
form is singular precisely at a root of the determinant representative. -/
theorem ltForm_det (V : R2) {ω : ℂ} (hω : ‖ω‖ = 1) :
    (ltForm V ω).det = (1 - ω) ^ 2 * alexanderDet V ω⁻¹ := by
  rw [ltForm_eq_smul_alexanderMatrix V hω, alexanderDet, Matrix.det_smul]
  simp

theorem ltForm_det_eq_zero_iff (V : R2) {ω : ℂ}
    (hω : ‖ω‖ = 1) (hω1 : ω ≠ 1) :
    (ltForm V ω).det = 0 ↔ alexanderDet V ω⁻¹ = 0 := by
  rw [ltForm_det V hω]
  have hfac : (1 - ω) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hω1.symm)
  exact mul_eq_zero_iff_left hfac

/-- The real trace of a complex `2 × 2` matrix. -/
def realTrace2 (A : C2) : ℝ := (A 0 0 + A 1 1).re

/-- The nonnegative discriminant of a Hermitian `2 × 2` matrix. -/
def discr2 (A : C2) : ℝ :=
  (A 0 0 - A 1 1).re ^ 2 + 4 * ((A 0 1).re ^ 2 + (A 0 1).im ^ 2)

/-- The two explicit eigenvalues of a Hermitian `2 × 2` matrix. -/
noncomputable def eigLow (A : C2) : ℝ := (realTrace2 A - Real.sqrt (discr2 A)) / 2
noncomputable def eigHigh (A : C2) : ℝ := (realTrace2 A + Real.sqrt (discr2 A)) / 2

/-- Integer-valued sign on the real line. -/
noncomputable def zsign (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

/-- Sum of the signs of the two real eigenvalues. -/
noncomputable def signature2 (A : C2) : ℤ := zsign (eigLow A) + zsign (eigHigh A)

/-- Characteristic-polynomial signature.  We use it for Hermitian matrices,
whose characteristic roots are all real and agree with Mathlib's eigenvalues. -/
noncomputable def characteristicSignature {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℤ :=
  (A.charpoly.roots.map (fun z ↦ zsign z.re)).sum

lemma discr2_nonneg (A : C2) : 0 ≤ discr2 A := by
  unfold discr2
  positivity

lemma isHermitian_det_im (A : C2) (hA : A.IsHermitian) : A.det.im = 0 := by
  have h00 := hA.apply 0 0
  have h11 := hA.apply 1 1
  have h01 := hA.apply 0 1
  have h00im : (A 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp at h
    linarith
  have h11im : (A 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp at h
    linarith
  have h10 : A 1 0 = conj (A 0 1) := by
    rw [← h01]
    simp
  simp [Matrix.det_fin_two, Complex.sub_im, Complex.mul_im, h00im, h11im, h10]
  ring

lemma eigLow_add_eigHigh (A : C2) :
    eigLow A + eigHigh A = realTrace2 A := by
  simp only [eigLow, eigHigh]
  ring

lemma eigLow_mul_eigHigh (A : C2) (hA : A.IsHermitian) :
    eigLow A * eigHigh A = A.det.re := by
  have h00 := hA.apply 0 0
  have h11 := hA.apply 1 1
  have h01 := hA.apply 0 1
  have h00im : (A 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp at h
    linarith
  have h11im : (A 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp at h
    linarith
  have h10 : A 1 0 = conj (A 0 1) := by
    rw [← h01]
    simp
  have hsqrt : Real.sqrt (discr2 A) ^ 2 = discr2 A :=
    Real.sq_sqrt (discr2_nonneg A)
  simp only [discr2, Complex.sub_re] at hsqrt
  simp only [eigLow, eigHigh, realTrace2, discr2, Matrix.det_fin_two,
    Complex.add_re, Complex.sub_re, Complex.mul_re, h00im, h11im, h10,
    Complex.conj_re, Complex.conj_im]
  nlinarith

lemma characteristicSignature_eq_sum_eigenvalues {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    characteristicSignature A = ∑ i, zsign (hA.eigenvalues i) := by
  unfold characteristicSignature
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/-- The characteristic-polynomial signature is exactly the explicit two-root
signature for a Hermitian `2 × 2` matrix. -/
theorem characteristicSignature_two (A : C2) (hA : A.IsHermitian) :
    characteristicSignature A = signature2 A := by
  rw [characteristicSignature_eq_sum_eigenvalues A hA]
  simp only [Fin.sum_univ_two, signature2]
  have ht := congrArg Complex.re (hA.trace_eq_sum_eigenvalues)
  have hd := congrArg Complex.re (hA.det_eq_prod_eigenvalues)
  simp [Matrix.trace, Fin.sum_univ_two] at ht
  simp [Fin.prod_univ_two] at hd
  have hs : hA.eigenvalues 0 + hA.eigenvalues 1 = eigLow A + eigHigh A := by
    calc
      hA.eigenvalues 0 + hA.eigenvalues 1 = realTrace2 A := ht.symm
      _ = eigLow A + eigHigh A := (eigLow_add_eigHigh A).symm
  have hp : hA.eigenvalues 0 * hA.eigenvalues 1 = eigLow A * eigHigh A := by
    calc
      hA.eigenvalues 0 * hA.eigenvalues 1 = A.det.re := hd.symm
      _ = eigLow A * eigHigh A := (eigLow_mul_eigHigh A hA).symm
  have hmul := congrArg (fun r : ℝ ↦ hA.eigenvalues 0 * r) hs
  have hfactor : (hA.eigenvalues 0 - eigLow A) *
      (hA.eigenvalues 0 - eigHigh A) = 0 := by
    nlinarith [hp]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · have hx0 : hA.eigenvalues 0 = eigLow A := sub_eq_zero.mp hx
    have hy0 : hA.eigenvalues 1 = eigHigh A := by
      rw [hx0] at hs
      linarith
    rw [hx0, hy0]
  · have hx0 : hA.eigenvalues 0 = eigHigh A := sub_eq_zero.mp hx
    have hy0 : hA.eigenvalues 1 = eigLow A := by
      rw [hx0] at hs
      linarith
    rw [hx0, hy0]
    ring

/-- Characteristic-polynomial signature is additive on block-diagonal
matrices, including zero eigenvalues with their multiplicities. -/
theorem characteristicSignature_fromBlocks {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (B : Matrix m m ℂ) (D : Matrix n n ℂ) :
    characteristicSignature (Matrix.fromBlocks B 0 0 D) =
      characteristicSignature B + characteristicSignature D := by
  classical
  have hprod : B.charpoly * D.charpoly ≠ 0 :=
    mul_ne_zero B.charpoly_monic.ne_zero D.charpoly_monic.ne_zero
  rw [characteristicSignature, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul hprod]
  simp [characteristicSignature]

lemma continuous_eigLow {X : Type*} [TopologicalSpace X]
    (A : X → C2) (hA : Continuous A) : Continuous (fun x ↦ eigLow (A x)) := by
  have h00 : Continuous (fun x ↦ A x 0 0) := hA.matrix_elem 0 0
  have h01 : Continuous (fun x ↦ A x 0 1) := hA.matrix_elem 0 1
  have h11 : Continuous (fun x ↦ A x 1 1) := hA.matrix_elem 1 1
  have htr : Continuous (fun x ↦ realTrace2 (A x)) := by
    exact Complex.continuous_re.comp (h00.add h11)
  have hd : Continuous (fun x ↦ discr2 (A x)) := by
    unfold discr2
    exact ((Complex.continuous_re.comp (h00.sub h11)).pow 2).add
      (continuous_const.mul (((Complex.continuous_re.comp h01).pow 2).add
        ((Complex.continuous_im.comp h01).pow 2)))
  exact (htr.sub (Real.continuous_sqrt.comp hd)).div_const 2

lemma continuous_eigHigh {X : Type*} [TopologicalSpace X]
    (A : X → C2) (hA : Continuous A) : Continuous (fun x ↦ eigHigh (A x)) := by
  have h00 : Continuous (fun x ↦ A x 0 0) := hA.matrix_elem 0 0
  have h01 : Continuous (fun x ↦ A x 0 1) := hA.matrix_elem 0 1
  have h11 : Continuous (fun x ↦ A x 1 1) := hA.matrix_elem 1 1
  have htr : Continuous (fun x ↦ realTrace2 (A x)) := by
    exact Complex.continuous_re.comp (h00.add h11)
  have hd : Continuous (fun x ↦ discr2 (A x)) := by
    unfold discr2
    exact ((Complex.continuous_re.comp (h00.sub h11)).pow 2).add
      (continuous_const.mul (((Complex.continuous_re.comp h01).pow 2).add
        ((Complex.continuous_im.comp h01).pow 2)))
  exact (htr.add (Real.continuous_sqrt.comp hd)).div_const 2

/-- A continuous real function which is nonzero throughout an unordered
interval has the same integer sign at its endpoints. -/
lemma zsign_eq_on_uIcc {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.uIcc a b))
    (hf0 : ∀ t ∈ Set.uIcc a b, f t ≠ 0) : zsign (f a) = zsign (f b) := by
  have ha0 : f a ≠ 0 := hf0 a Set.left_mem_uIcc
  have hb0 : f b ≠ 0 := hf0 b Set.right_mem_uIcc
  have cross_pos_neg (ha : 0 < f a) (hb : f b < 0) : False := by
    have hzero : (0 : ℝ) ∈ Set.uIcc (f a) (f b) :=
      Set.mem_uIcc_of_ge hb.le ha.le
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf hzero
    exact hf0 t ht hft
  have cross_neg_pos (ha : f a < 0) (hb : 0 < f b) : False := by
    have hzero : (0 : ℝ) ∈ Set.uIcc (f a) (f b) :=
      Set.mem_uIcc_of_le ha.le hb.le
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf hzero
    exact hf0 t ht hft
  rcases lt_trichotomy (f a) 0 with ha | ha | ha <;>
    rcases lt_trichotomy (f b) 0 with hb | hb | hb
  · simp [zsign, ha, hb, ha.not_gt, hb.not_gt]
  · exact (hb0 hb).elim
  · exact (cross_neg_pos ha hb).elim
  · exact (ha0 ha).elim
  · exact (ha0 ha).elim
  · exact (ha0 ha).elim
  · exact (cross_pos_neg ha hb).elim
  · exact (hb0 hb).elim
  · simp [zsign, ha, hb]

/-- Nonsingular continuous Hermitian `2 × 2` paths have constant signature. -/
theorem signature2_eq_on_uIcc {A : ℝ → C2} (hA : Continuous A)
    (hherm : ∀ t, (A t).IsHermitian) {a b : ℝ}
    (hdet : ∀ t ∈ Set.uIcc a b, (A t).det ≠ 0) :
    signature2 (A a) = signature2 (A b) := by
  have hlow0 : ∀ t ∈ Set.uIcc a b, eigLow (A t) ≠ 0 := by
    intro t ht hzero
    have hprod := eigLow_mul_eigHigh (A t) (hherm t)
    rw [hzero, zero_mul] at hprod
    have hre : (A t).det.re = 0 := hprod.symm
    apply hdet t ht
    apply Complex.ext
    · simp [hre]
    · simp [isHermitian_det_im (A t) (hherm t)]
  have hhigh0 : ∀ t ∈ Set.uIcc a b, eigHigh (A t) ≠ 0 := by
    intro t ht hzero
    have hprod := eigLow_mul_eigHigh (A t) (hherm t)
    rw [hzero, mul_zero] at hprod
    have hre : (A t).det.re = 0 := hprod.symm
    apply hdet t ht
    apply Complex.ext
    · simp [hre]
    · simp [isHermitian_det_im (A t) (hherm t)]
  unfold signature2
  rw [zsign_eq_on_uIcc (continuous_eigLow A hA).continuousOn hlow0,
    zsign_eq_on_uIcc (continuous_eigHigh A hA).continuousOn hhigh0]

/-- If the two endpoint signatures differ, an actual singular point occurs
between them. -/
theorem exists_det_eq_zero_of_signature_ne {A : ℝ → C2} (hA : Continuous A)
    (hherm : ∀ t, (A t).IsHermitian) {a b : ℝ}
    (hstep : signature2 (A a) ≠ signature2 (A b)) :
    ∃ t ∈ Set.uIcc a b, (A t).det = 0 := by
  by_contra h
  push Not at h
  exact hstep (signature2_eq_on_uIcc hA hherm h)

lemma continuous_ltForm (V : R2) {X : Type*} [TopologicalSpace X]
    {γ : X → ℂ} (hγ : Continuous γ) : Continuous (fun x ↦ ltForm V (γ x)) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ltForm, complexify] <;> fun_prop

/-- **B7, forward direction (two-dimensional Seifert form).**  A step of the
signature along a continuous unit-circle path away from `1` forces a root of
the determinant representative of the Alexander polynomial at an intermediate
parameter.  The unit-modulus conclusion is retained explicitly. -/
theorem B7_step_implies_unit_circle_root (V : R2) (γ : ℝ → ℂ)
    (hγ : Continuous γ) {a b : ℝ}
    (hcircle : ∀ t ∈ Set.uIcc a b, ‖γ t‖ = 1)
    (hne1 : ∀ t ∈ Set.uIcc a b, γ t ≠ 1)
    (hstep : characteristicSignature (ltForm V (γ a)) ≠
      characteristicSignature (ltForm V (γ b))) :
    ∃ t ∈ Set.uIcc a b, ‖γ t‖ = 1 ∧ alexanderDet V (γ t)⁻¹ = 0 := by
  have hstep2 : signature2 (ltForm V (γ a)) ≠ signature2 (ltForm V (γ b)) := by
    simpa only [characteristicSignature_two _ (ltForm_isHermitian _ _)] using hstep
  obtain ⟨t, ht, hsing⟩ := exists_det_eq_zero_of_signature_ne
    (continuous_ltForm V hγ) (fun t ↦ ltForm_isHermitian V (γ t)) hstep2
  exact ⟨t, ht, hcircle t ht, (ltForm_det_eq_zero_iff V (hcircle t ht) (hne1 t ht)).mp hsing⟩

lemma realTrace2_map_conj (A : C2) :
    realTrace2 (A.map (fun z ↦ conj z)) = realTrace2 A := by
  simp [realTrace2, Complex.add_re]

lemma discr2_map_conj (A : C2) :
    discr2 (A.map (fun z ↦ conj z)) = discr2 A := by
  simp [discr2, Complex.sub_re]

lemma signature2_map_conj (A : C2) :
    signature2 (A.map (fun z ↦ conj z)) = signature2 A := by
  simp only [signature2, eigLow, eigHigh, realTrace2_map_conj, discr2_map_conj]

lemma zsign_neg (x : ℝ) : zsign (-x) = -zsign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hnx : 0 < -x := neg_pos.mpr hx
    simp [zsign, hx, hx.not_gt, hnx]
  · simp [zsign, hx]
  · have hnx : -x < 0 := neg_neg_of_pos hx
    simp [zsign, hx, hnx, hnx.not_gt]

lemma eigLow_neg (A : C2) : eigLow (-A) = -eigHigh A := by
  have htr : realTrace2 (-A) = -realTrace2 A := by
    simp [realTrace2, Complex.add_re]
    ring
  have hd : discr2 (-A) = discr2 A := by
    simp [discr2, Complex.sub_re]
    ring
  simp only [eigLow, eigHigh, htr, hd]
  ring

lemma eigHigh_neg (A : C2) : eigHigh (-A) = -eigLow A := by
  have htr : realTrace2 (-A) = -realTrace2 A := by
    simp [realTrace2, Complex.add_re]
    ring
  have hd : discr2 (-A) = discr2 A := by
    simp [discr2, Complex.sub_re]
    ring
  simp only [eigLow, eigHigh, htr, hd]
  ring

lemma signature2_neg (A : C2) : signature2 (-A) = -signature2 A := by
  simp only [signature2, eigLow_neg, eigHigh_neg, zsign_neg]
  ring

lemma ltForm_conj_eq_map_conj (V : R2) (ω : ℂ) :
    ltForm V (conj ω) = (ltForm V ω).map (fun z ↦ conj z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ltForm, complexify]

/-- The mirror Seifert block has the negative form at the conjugate parameter. -/
lemma ltForm_neg_transpose (V : R2) (ω : ℂ) :
    ltForm (-V.transpose) ω = -ltForm V (conj ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ltForm, complexify]

/-- Signature is additive under direct sums.  This definition records just the
sum of the two explicit `2 × 2` spectral signatures of the diagonal blocks. -/
noncomputable def directSumSignature (V W : R2) (ω : ℂ) : ℤ :=
  signature2 (ltForm V ω) + signature2 (ltForm W ω)

/-- A block and its mirror have identically cancelling direct-sum signatures. -/
theorem directSumSignature_add_mirror (V : R2) (ω : ℂ) :
    directSumSignature V (-V.transpose) ω = 0 := by
  unfold directSumSignature
  rw [ltForm_neg_transpose, signature2_neg, ltForm_conj_eq_map_conj,
    signature2_map_conj]
  ring

/-- The standard `2 × 2` Seifert block with determinant representative
`t² - t + 1` (a trefoil block). -/
def trefoilSeifert : R2 := !![-1, 1; 0, -1]

/-- The four-dimensional block matrix used for the square-knot witness. -/
def squareSeifert : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks trefoilSeifert 0 0 (-trefoilSeifert.transpose)

/-- The Levine–Tristram form in arbitrary finite dimension. -/
def generalLtForm {n : Type*} (V : Matrix n n ℝ) (ω : ℂ) : Matrix n n ℂ :=
  (1 - ω) • (V.map (fun x : ℝ ↦ (x : ℂ))) +
    (1 - conj ω) • (V.transpose.map (fun x : ℝ ↦ (x : ℂ)))

lemma generalLtForm_isHermitian {n : Type*} (V : Matrix n n ℝ) (ω : ℂ) :
    (generalLtForm V ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [generalLtForm]
  ring

lemma generalLtForm_square (ω : ℂ) :
    generalLtForm squareSeifert ω =
      Matrix.fromBlocks (ltForm trefoilSeifert ω) 0 0
        (ltForm (-trefoilSeifert.transpose) ω) := by
  ext (i | i) (j | j) <;>
    simp [generalLtForm, squareSeifert, ltForm, complexify]

/-- Alexander matrix in arbitrary finite dimension, used only to state the
block determinant of the square-knot witness. -/
def generalAlexanderMatrix {n : Type*} (V : Matrix n n ℝ) (t : ℂ) :
    Matrix n n ℂ :=
  (V.map (fun x : ℝ ↦ (x : ℂ))) - t • (V.transpose.map (fun x : ℝ ↦ (x : ℂ)))

noncomputable def generalAlexanderDet {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (t : ℂ) : ℂ := (generalAlexanderMatrix V t).det

lemma generalAlexanderMatrix_square (t : ℂ) :
    generalAlexanderMatrix squareSeifert t =
      Matrix.fromBlocks (alexanderMatrix trefoilSeifert t) 0 0
        (alexanderMatrix (-trefoilSeifert.transpose) t) := by
  ext (i | i) (j | j) <;>
    simp [generalAlexanderMatrix, squareSeifert, alexanderMatrix, complexify]

lemma trefoil_alexanderDet (t : ℂ) :
    alexanderDet trefoilSeifert t = t ^ 2 - t + 1 := by
  simp [alexanderDet, alexanderMatrix, complexify, trefoilSeifert, Matrix.det_fin_two]
  ring

lemma mirror_trefoil_alexanderDet (t : ℂ) :
    alexanderDet (-trefoilSeifert.transpose) t = t ^ 2 - t + 1 := by
  simp [alexanderDet, alexanderMatrix, complexify, trefoilSeifert, Matrix.det_fin_two]
  ring

/-- The square-knot witness has the stated squared Alexander factor. -/
theorem squareSeifert_alexanderDet (t : ℂ) :
    generalAlexanderDet squareSeifert t = (t ^ 2 - t + 1) ^ 2 := by
  unfold generalAlexanderDet
  rw [generalAlexanderMatrix_square, Matrix.det_fromBlocks_zero₂₁]
  change alexanderDet trefoilSeifert t *
    alexanderDet (-trefoilSeifert.transpose) t = _
  rw [trefoil_alexanderDet, mirror_trefoil_alexanderDet]
  ring

/-- A primitive sixth root of unity, one of the two double roots. -/
noncomputable def squareRoot : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (((Real.sqrt 3) / 2 : ℝ) : ℂ) * Complex.I

lemma squareRoot_char : squareRoot ^ 2 - squareRoot + 1 = 0 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [squareRoot, pow_two, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]

lemma squareRoot_norm : ‖squareRoot‖ = 1 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : ‖squareRoot‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [squareRoot, Complex.normSq_apply]
    nlinarith [h3]
  nlinarith [norm_nonneg squareRoot]

lemma squareRoot_ne_one : squareRoot ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp [squareRoot] at him

/-- The canonical characteristic-polynomial signature of the actual
four-dimensional Levine–Tristram form of `squareSeifert`. -/
noncomputable def squareSignature (ω : ℂ) : ℤ :=
  characteristicSignature (generalLtForm squareSeifert ω)

theorem squareSignature_eq_directSum (ω : ℂ) :
    squareSignature ω =
      directSumSignature trefoilSeifert (-trefoilSeifert.transpose) ω := by
  unfold squareSignature directSumSignature
  rw [generalLtForm_square, characteristicSignature_fromBlocks,
    characteristicSignature_two _ (ltForm_isHermitian _ _),
    characteristicSignature_two _ (ltForm_isHermitian _ _)]

theorem squareSignature_zero (ω : ℂ) : squareSignature ω = 0 := by
  rw [squareSignature_eq_directSum]
  exact directSumSignature_add_mirror trefoilSeifert ω

/-- **B7, failure of the converse.**  The exhibited unit-circle parameter is a
root of the squared Alexander factor (and is not `1`), yet every parameter has
zero direct-sum signature.  No endpoint pair can therefore exhibit a step. -/
theorem squareKnot_root_without_step :
    ‖squareRoot‖ = 1 ∧ squareRoot ≠ 1 ∧
      generalAlexanderDet squareSeifert squareRoot = 0 ∧
      ∀ ω : ℂ, squareSignature ω = 0 := by
  refine ⟨squareRoot_norm, squareRoot_ne_one, ?_, squareSignature_zero⟩
  rw [squareSeifert_alexanderDet, squareRoot_char]
  simp

section AxiomAudit

#print axioms ltForm_isHermitian
#print axioms ltForm_eq_smul_alexanderMatrix
#print axioms ltForm_det
#print axioms ltForm_det_eq_zero_iff
#print axioms discr2_nonneg
#print axioms isHermitian_det_im
#print axioms eigLow_add_eigHigh
#print axioms eigLow_mul_eigHigh
#print axioms characteristicSignature_eq_sum_eigenvalues
#print axioms characteristicSignature_two
#print axioms characteristicSignature_fromBlocks
#print axioms continuous_eigLow
#print axioms continuous_eigHigh
#print axioms zsign_eq_on_uIcc
#print axioms signature2_eq_on_uIcc
#print axioms exists_det_eq_zero_of_signature_ne
#print axioms continuous_ltForm
#print axioms B7_step_implies_unit_circle_root
#print axioms realTrace2_map_conj
#print axioms discr2_map_conj
#print axioms signature2_map_conj
#print axioms zsign_neg
#print axioms eigLow_neg
#print axioms eigHigh_neg
#print axioms signature2_neg
#print axioms ltForm_conj_eq_map_conj
#print axioms ltForm_neg_transpose
#print axioms directSumSignature_add_mirror
#print axioms generalLtForm_isHermitian
#print axioms generalLtForm_square
#print axioms generalAlexanderMatrix_square
#print axioms trefoil_alexanderDet
#print axioms mirror_trefoil_alexanderDet
#print axioms squareSeifert_alexanderDet
#print axioms squareRoot_char
#print axioms squareRoot_norm
#print axioms squareRoot_ne_one
#print axioms squareSignature_eq_directSum
#print axioms squareSignature_zero
#print axioms squareKnot_root_without_step

end AxiomAudit

end RelationalAtlas.B7


/-! ## B115 — the shape record is well defined, and the fold is on the sphere

Integrated from `.ultramath/smwvwr2ce/m11/B115.lean`.
-/

/-!
# B115 — the triangle distance record and its orientation fold

The source card is `cards/html/B115.html` in Atlas v7. It displays
`P = ψψ†/‖ψ‖²`, `ψ = (ρ₁,ρ₂)`, and the record
`(w₁,w₂,w₃) ↦ (w₁,w₂)`. Its Why-it-holds clause specifies
`d_ij = (1 + w·u_ij)/3`, with three unit vectors `u_ij` at mutual angles
`120°` in the `(w₁,w₂)`-plane. We use exactly those conventions.

The projection to `(w₁,w₂)` has rank two at every point of ambient `ℝ³`.
The rank drop stated on the card is correct after pullback to the unit shape
sphere: its equator `w₃ = 0` is precisely where the vertical tangent is in
the kernel. We prove that sphere version below.
-/

set_option autoImplicit false
noncomputable section

namespace B115

open Matrix

abbrev CMat := Matrix (Fin 2) (Fin 2) ℂ

/-- Euclidean norm squared of the two complex Jacobi coordinates. -/
def energy (ρ₁ ρ₂ : ℂ) : ℝ := Complex.normSq ρ₁ + Complex.normSq ρ₂

/-- The unnormalized outer product `ψψ†`. -/
def outer (ρ₁ ρ₂ : ℂ) : CMat :=
  !![ρ₁ * (starRingEnd ℂ) ρ₁, ρ₁ * (starRingEnd ℂ) ρ₂;
     ρ₂ * (starRingEnd ℂ) ρ₁, ρ₂ * (starRingEnd ℂ) ρ₂]

/-- The card's rank-one projector, with the denominator coerced from `ℝ` to `ℂ`. -/
def projector (ρ₁ ρ₂ : ℂ) : CMat := (energy ρ₁ ρ₂ : ℂ)⁻¹ • outer ρ₁ ρ₂

/-- Bloch/shape coordinates read directly from a `2 × 2` complex matrix.
For the projector these are `(diag diff, 2 Re offdiag, 2 Im offdiag)`;
thus they descend to projective space without choosing a phase. -/
def bloch (P : CMat) : Fin 3 → ℝ :=
  ![(P 0 0 - P 1 1).re, 2 * (P 0 1).re, 2 * (P 0 1).im]

/-- The three unit coefficient vectors at mutual angles `120°`. -/
noncomputable def u : Fin 3 → ℝ × ℝ :=
  ![(1, 0), (-1 / 2, Real.sqrt 3 / 2), (-1 / 2, -(Real.sqrt 3 / 2))]

/-- The card's three normalized squared mutual distances. -/
def distance (w : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  (1 + (w 0 * (u k).1 + w 1 * (u k).2)) / 3

/-- Forget the oriented-area coordinate. -/
def record (w : Fin 3 → ℝ) : ℝ × ℝ := (w 0, w 1)

/-- Reflection in the `(w₁,w₂)`-plane, i.e. reversal of oriented area. -/
def mirror (w : Fin 3 → ℝ) : Fin 3 → ℝ := ![w 0, w 1, -w 2]

lemma sqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))

/-- The outer product acquires exactly the factor `‖c‖²` under a common
complex scaling; this factor cancels the denominator in `projector`. -/
lemma outer_phase (c ρ₁ ρ₂ : ℂ) :
    outer (c * ρ₁) (c * ρ₂) = (Complex.normSq c : ℂ) • outer ρ₁ ρ₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [outer]
  · calc
      c * ρ₁ * ((starRingEnd ℂ) c * (starRingEnd ℂ) ρ₁) =
          (c * (starRingEnd ℂ) c) * (ρ₁ * (starRingEnd ℂ) ρ₁) := by ring
      _ = (Complex.normSq c : ℂ) * (ρ₁ * (starRingEnd ℂ) ρ₁) := by rw [Complex.mul_conj]
  · calc
      c * ρ₁ * ((starRingEnd ℂ) c * (starRingEnd ℂ) ρ₂) =
          (c * (starRingEnd ℂ) c) * (ρ₁ * (starRingEnd ℂ) ρ₂) := by ring
      _ = (Complex.normSq c : ℂ) * (ρ₁ * (starRingEnd ℂ) ρ₂) := by rw [Complex.mul_conj]
  · calc
      c * ρ₂ * ((starRingEnd ℂ) c * (starRingEnd ℂ) ρ₁) =
          (c * (starRingEnd ℂ) c) * (ρ₂ * (starRingEnd ℂ) ρ₁) := by ring
      _ = (Complex.normSq c : ℂ) * (ρ₂ * (starRingEnd ℂ) ρ₁) := by rw [Complex.mul_conj]
  · calc
      c * ρ₂ * ((starRingEnd ℂ) c * (starRingEnd ℂ) ρ₂) =
          (c * (starRingEnd ℂ) c) * (ρ₂ * (starRingEnd ℂ) ρ₂) := by ring
      _ = (Complex.normSq c : ℂ) * (ρ₂ * (starRingEnd ℂ) ρ₂) := by rw [Complex.mul_conj]

/-- Common nonzero complex scaling leaves the normalized projector unchanged.
In particular this applies to `c = exp (I θ)`, without any extra computation
of its modulus. -/
theorem projector_phase (c ρ₁ ρ₂ : ℂ) (hc : c ≠ 0) (hE : energy ρ₁ ρ₂ ≠ 0) :
    projector (c * ρ₁) (c * ρ₂) = projector ρ₁ ρ₂ := by
  have hcn : (Complex.normSq c : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    intro h
    exact hc (Complex.normSq_eq_zero.mp h)
  have hEn : (energy ρ₁ ρ₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE
  have hEc : energy (c * ρ₁) (c * ρ₂) = Complex.normSq c * energy ρ₁ ρ₂ := by
    simp [energy, Complex.normSq_mul, mul_add]
  rw [projector, projector, hEc, outer_phase]
  simp only [Complex.ofReal_mul, mul_inv, smul_smul]
  congr 1
  field_simp

/-- Away from total collision is precisely the nonzero denominator needed by
`P`; the proof uses the Euclidean norm, not a phase assumption. -/
lemma energy_ne_zero {ρ₁ ρ₂ : ℂ} (h : ρ₁ ≠ 0 ∨ ρ₂ ≠ 0) : energy ρ₁ ρ₂ ≠ 0 := by
  have hn1 : 0 ≤ Complex.normSq ρ₁ := Complex.normSq_nonneg _
  have hn2 : 0 ≤ Complex.normSq ρ₂ := Complex.normSq_nonneg _
  rcases h with h | h
  · have hp : 0 < Complex.normSq ρ₁ := Complex.normSq_pos.mpr h
    unfold energy
    linarith
  · have hp : 0 < Complex.normSq ρ₂ := Complex.normSq_pos.mpr h
    unfold energy
    linarith

/-- `outer * outer` is the norm squared times `outer`. -/
lemma outer_mul_outer (ρ₁ ρ₂ : ℂ) :
    outer ρ₁ ρ₂ * outer ρ₁ ρ₂ = (energy ρ₁ ρ₂ : ℂ) • outer ρ₁ ρ₂ := by
  have h1 : ρ₁ * (starRingEnd ℂ) ρ₁ = (Complex.normSq ρ₁ : ℂ) := Complex.mul_conj ρ₁
  have h2 : ρ₂ * (starRingEnd ℂ) ρ₂ = (Complex.normSq ρ₂ : ℂ) := Complex.mul_conj ρ₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outer, Matrix.mul_apply, Fin.sum_univ_two, energy]
  · linear_combination (ρ₁ * (starRingEnd ℂ) ρ₁) * h1 +
      (ρ₁ * (starRingEnd ℂ) ρ₁) * h2
  · linear_combination (ρ₁ * (starRingEnd ℂ) ρ₂) * h1 +
      (ρ₁ * (starRingEnd ℂ) ρ₂) * h2
  · linear_combination (ρ₂ * (starRingEnd ℂ) ρ₁) * h1 +
      (ρ₂ * (starRingEnd ℂ) ρ₁) * h2
  · linear_combination (ρ₂ * (starRingEnd ℂ) ρ₂) * h1 +
      (ρ₂ * (starRingEnd ℂ) ρ₂) * h2

/-- The displayed matrix really is an orthogonal rank-one projector. -/
theorem projector_idempotent (ρ₁ ρ₂ : ℂ) (hE : energy ρ₁ ρ₂ ≠ 0) :
    projector ρ₁ ρ₂ * projector ρ₁ ρ₂ = projector ρ₁ ρ₂ := by
  have hEn : (energy ρ₁ ρ₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE
  simp only [projector, Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_mul_outer]
  congr 1
  field_simp

/-- Hermitian symmetry, with the usual physics dagger convention. -/
theorem projector_hermitian (ρ₁ ρ₂ : ℂ) : (projector ρ₁ ρ₂)ᴴ = projector ρ₁ ρ₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, outer, Matrix.conjTranspose_apply, mul_comm]

/-- Its trace is exactly one away from total collision. -/
theorem projector_trace (ρ₁ ρ₂ : ℂ) (hE : energy ρ₁ ρ₂ ≠ 0) :
    (projector ρ₁ ρ₂).trace = 1 := by
  have hEn : (energy ρ₁ ρ₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE
  simp [projector, outer, Matrix.trace, Fin.sum_univ_two, Complex.mul_conj]
  rw [← mul_add, ← Complex.ofReal_add]
  change (energy ρ₁ ρ₂ : ℂ)⁻¹ * (energy ρ₁ ρ₂ : ℂ) = 1
  exact inv_mul_cancel₀ hEn

/-- Therefore the entire shape-sphere record, and not just the projector, is
well-defined on a complex projective point. -/
theorem bloch_phase (c ρ₁ ρ₂ : ℂ) (hc : c ≠ 0) (hE : energy ρ₁ ρ₂ ≠ 0) :
    bloch (projector (c * ρ₁) (c * ρ₂)) = bloch (projector ρ₁ ρ₂) := by
  rw [projector_phase c ρ₁ ρ₂ hc hE]

/-- The distance record on a Jacobi projector is phase-independent. -/
theorem projector_distance_phase (c ρ₁ ρ₂ : ℂ) (hc : c ≠ 0)
    (hE : energy ρ₁ ρ₂ ≠ 0) (k : Fin 3) :
    distance (bloch (projector (c * ρ₁) (c * ρ₂))) k =
      distance (bloch (projector ρ₁ ρ₂)) k := by
  rw [bloch_phase c ρ₁ ρ₂ hc hE]

/-- Explicit Hopf/Bloch coordinates of the Jacobi projector. -/
lemma bloch_projector_zero (ρ₁ ρ₂ : ℂ) :
    bloch (projector ρ₁ ρ₂) 0 =
      (Complex.normSq ρ₁ - Complex.normSq ρ₂) / energy ρ₁ ρ₂ := by
  simp [bloch, projector, outer, ← Complex.ofReal_inv]
  simp only [Complex.normSq_apply]
  ring

lemma bloch_projector_one (ρ₁ ρ₂ : ℂ) :
    bloch (projector ρ₁ ρ₂) 1 =
      2 * (ρ₁ * (starRingEnd ℂ) ρ₂).re / energy ρ₁ ρ₂ := by
  simp [bloch, projector, outer, ← Complex.ofReal_inv]
  ring

lemma bloch_projector_two (ρ₁ ρ₂ : ℂ) :
    bloch (projector ρ₁ ρ₂) 2 =
      2 * (ρ₁ * (starRingEnd ℂ) ρ₂).im / energy ρ₁ ρ₂ := by
  simp [bloch, projector, outer, ← Complex.ofReal_inv]
  ring

/-- The Bloch vector of every nonzero Jacobi projector lies on the unit shape
sphere. This is the algebraic identity behind the quotient by size and planar
rotation. -/
theorem bloch_projector_unit (ρ₁ ρ₂ : ℂ) (hE : energy ρ₁ ρ₂ ≠ 0) :
    bloch (projector ρ₁ ρ₂) 0 ^ 2 + bloch (projector ρ₁ ρ₂) 1 ^ 2 +
      bloch (projector ρ₁ ρ₂) 2 ^ 2 = 1 := by
  have hoff : (ρ₁ * (starRingEnd ℂ) ρ₂).re ^ 2 +
      (ρ₁ * (starRingEnd ℂ) ρ₂).im ^ 2 =
        Complex.normSq ρ₁ * Complex.normSq ρ₂ := by
    calc
      _ = Complex.normSq (ρ₁ * (starRingEnd ℂ) ρ₂) := by
        rw [Complex.normSq_apply]
        ring
      _ = Complex.normSq ρ₁ * Complex.normSq ρ₂ := by
        rw [Complex.normSq_mul, Complex.normSq_conj]
  rw [bloch_projector_zero, bloch_projector_one, bloch_projector_two]
  have hE0 : energy ρ₁ ρ₂ ≠ 0 := hE
  have hEdef : energy ρ₁ ρ₂ = Complex.normSq ρ₁ + Complex.normSq ρ₂ := rfl
  field_simp
  rw [hEdef]
  nlinarith [hoff]

/-- Complex conjugation of both Jacobi coordinates is the planar mirror: it
keeps the first two Bloch coordinates and negates exactly the oriented-area
coordinate. -/
theorem bloch_jacobi_mirror (ρ₁ ρ₂ : ℂ) :
    bloch (projector ((starRingEnd ℂ) ρ₁) ((starRingEnd ℂ) ρ₂)) =
      mirror (bloch (projector ρ₁ ρ₂)) := by
  ext i
  fin_cases i <;>
    simp [bloch_projector_zero, bloch_projector_one, bloch_projector_two,
      energy, mirror, Complex.mul_re, Complex.mul_im] <;> ring

/-- Consequently the physical Jacobi mirror has the same three distances. -/
theorem projector_mirror_same_distance (ρ₁ ρ₂ : ℂ) (k : Fin 3) :
    distance (bloch (projector ((starRingEnd ℂ) ρ₁) ((starRingEnd ℂ) ρ₂))) k =
      distance (bloch (projector ρ₁ ρ₂)) k := by
  rw [bloch_jacobi_mirror]
  fin_cases k <;> simp [distance, mirror, u]

/-- The distance coefficient vectors are unit vectors. -/
lemma u_unit (k : Fin 3) : (u k).1 ^ 2 + (u k).2 ^ 2 = 1 := by
  fin_cases k <;> simp [u] <;> nlinarith [sqrt3_sq]

/-- Distinct coefficient vectors have inner product `-1/2`, hence angle `120°`. -/
lemma u_inner {j k : Fin 3} (h : j ≠ k) :
    (u j).1 * (u k).1 + (u j).2 * (u k).2 = -1 / 2 := by
  fin_cases j <;> fin_cases k <;> simp [u] at h ⊢ <;> nlinarith [sqrt3_sq]

/-- The three card-normalized squared distances sum to one. -/
theorem normalized_distances_sum (w : Fin 3 → ℝ) :
    distance w 0 + distance w 1 + distance w 2 = 1 := by
  simp [distance, u]
  ring

/-- Distances are unchanged by reversal of the oriented-area coordinate. -/
theorem mirror_same_distance (w : Fin 3 → ℝ) (k : Fin 3) :
    distance (mirror w) k = distance w k := by
  fin_cases k <;> simp [distance, mirror, u]

/-- In fact the whole retained record is fixed by mirroring. -/
theorem record_mirror (w : Fin 3 → ℝ) : record (mirror w) = record w := rfl

/-- A left inverse from the three distances to the retained record:
`w₁ = 3d₀ - 1` and `w₂ = √3 (d₁-d₂)` in the card's zero-based array notation. -/
def recover (d : Fin 3 → ℝ) : ℝ × ℝ :=
  (3 * d 0 - 1, Real.sqrt 3 * (d 1 - d 2))

theorem recover_distance (w : Fin 3 → ℝ) : recover (distance w) = record w := by
  apply Prod.ext
  · simp [recover, distance, u, record]
    ring
  · simp [recover, distance, u, record]
    calc
      _ = (Real.sqrt 3 ^ 2 / 3) * w 1 := by ring
      _ = w 1 := by rw [sqrt3_sq]; ring

/-- The full normalized distance triple determines `(w₁,w₂)` exactly, with no
noncollinearity hypothesis and no choice of sheet. -/
theorem distances_determine_record {w v : Fin 3 → ℝ}
    (h : ∀ k, distance w k = distance v k) : record w = record v := by
  have hr : recover (distance w) = recover (distance v) := by
    congr 1
    funext k
    exact h k
  simpa only [recover_distance] using hr

/-- Reflection is an involution. -/
theorem mirror_involutive (w : Fin 3 → ℝ) : mirror (mirror w) = w := by
  ext i
  fin_cases i <;> simp [mirror]

/-- Its fixed point set is exactly the collinear circle `w₃ = 0`. -/
theorem mirror_fixed_iff (w : Fin 3 → ℝ) : mirror w = w ↔ w 2 = 0 := by
  constructor
  · intro h
    have h2 := congrFun h 2
    simp [mirror] at h2
    linarith
  · intro h
    ext i
    fin_cases i <;> simp [mirror, h]

/-- The phase asked about on the card, `ψ ↦ exp(iθ)ψ`, is a special case. -/
theorem projector_exp_phase (θ : ℝ) (ρ₁ ρ₂ : ℂ) (hE : energy ρ₁ ρ₂ ≠ 0) :
    projector (Complex.exp (θ * Complex.I) * ρ₁)
      (Complex.exp (θ * Complex.I) * ρ₂) = projector ρ₁ ρ₂ := by
  exact projector_phase _ _ _ (Complex.exp_ne_zero _) hE

/-- A nondegenerate, genuinely scalene point of the shape sphere. -/
noncomputable def witnessPlus : Fin 3 → ℝ :=
  ![(1 : ℝ) / 11, 2 * Real.sqrt 3 / 11, 6 * Real.sqrt 3 / 11]

/-- Its reflected sheet. -/
noncomputable def witnessMinus : Fin 3 → ℝ := mirror witnessPlus

theorem witnessPlus_unit :
    witnessPlus 0 ^ 2 + witnessPlus 1 ^ 2 + witnessPlus 2 ^ 2 = 1 := by
  simp [witnessPlus]
  nlinarith [sqrt3_sq]

theorem witnessMinus_unit :
    witnessMinus 0 ^ 2 + witnessMinus 1 ^ 2 + witnessMinus 2 ^ 2 = 1 := by
  simp [witnessMinus, mirror, witnessPlus]
  nlinarith [sqrt3_sq]

theorem witness_sheets_distinct : witnessMinus ≠ witnessPlus := by
  intro h
  have h2 := congrFun h 2
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp [witnessMinus, witnessPlus, mirror] at h2
  linarith

/-- The two different points have identical distance triples. -/
theorem witness_same_distance (k : Fin 3) :
    distance witnessMinus k = distance witnessPlus k := mirror_same_distance _ _

/-- Exact normalized side-length squares for the witness:
`(4/11, 9/22, 5/22)`. -/
theorem witness_distance_values :
    distance witnessPlus 0 = 4 / 11 ∧
      distance witnessPlus 1 = 9 / 22 ∧ distance witnessPlus 2 = 5 / 22 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [distance, witnessPlus, u] <;> nlinarith [sqrt3_sq]

/-- A concrete labelled planar triangle. -/
def trianglePlus : Fin 3 → ℝ × ℝ := ![((0 : ℝ), 0), (4, 0), (1, 3)]

/-- Its mirror in the `x`-axis. -/
def triangleMinus : Fin 3 → ℝ × ℝ := ![((0 : ℝ), 0), (4, 0), (1, -3)]

/-- Squared Euclidean distance between two labelled particles. -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The cyclic list of edges `(01,12,20)` used by `distance`. -/
def edge : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (2, 0)]

/-- The shape-sphere formula really gives the displayed triangle's three
normalized squared mutual distances (normalizing by `16+18+10 = 44`). -/
theorem witness_triangle_distance (k : Fin 3) :
    distance witnessPlus k =
      sqDist (trianglePlus (edge k).1) (trianglePlus (edge k).2) / 44 := by
  fin_cases k <;>
    simp [distance, witnessPlus, u, edge, trianglePlus, sqDist] <;>
    nlinarith [sqrt3_sq]

/-- Planar reflection preserves every pairwise squared distance, not merely
the three total distances after normalization. -/
theorem triangle_mirror_same_sqDist (i j : Fin 3) :
    sqDist (triangleMinus i) (triangleMinus j) =
      sqDist (trianglePlus i) (trianglePlus j) := by
  simp [triangleMinus, trianglePlus, sqDist]
  fin_cases i <;> fin_cases j <;> norm_num [sqDist]

/-- The witness is scalene: all three side-length squares are different. -/
theorem triangle_scalene :
    sqDist (trianglePlus 0) (trianglePlus 1) ≠
        sqDist (trianglePlus 1) (trianglePlus 2) ∧
      sqDist (trianglePlus 1) (trianglePlus 2) ≠
        sqDist (trianglePlus 2) (trianglePlus 0) ∧
      sqDist (trianglePlus 2) (trianglePlus 0) ≠
        sqDist (trianglePlus 0) (trianglePlus 1) := by
  norm_num [trianglePlus, sqDist]

/-- Twice the signed area of a labelled planar triangle. -/
def twiceArea (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The witness has nonzero area, reversed by its mirror. -/
theorem triangle_opposite_area :
    twiceArea (trianglePlus 0) (trianglePlus 1) (trianglePlus 2) = 12 ∧
      twiceArea (triangleMinus 0) (triangleMinus 1) (triangleMinus 2) = -12 := by
  norm_num [twiceArea, trianglePlus, triangleMinus]

/-- The corresponding shape-sphere area coordinates have opposite nonzero signs. -/
theorem witness_opposite_w3 : 0 < witnessPlus 2 ∧ witnessMinus 2 < 0 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  constructor <;> simp [witnessPlus, witnessMinus, mirror]

/-- A right inverse to the ambient record map. Thus the literal map from
`ℝ³` to `ℝ²` is onto everywhere; the fold must be stated after restriction to
the shape sphere, not as a rank drop of the ambient projection itself. -/
def recordSection (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, p.2, 0]

theorem record_section (p : ℝ × ℝ) : record (recordSection p) = p := rfl

theorem record_surjective : Function.Surjective record := fun p => ⟨recordSection p, record_section p⟩

/-- Standard spherical coordinates on the shape sphere; `w₃ = cos θ` is the
card's oriented-area coordinate. -/
noncomputable def sphere (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

theorem sphere_unit (θ φ : ℝ) :
    sphere θ φ 0 ^ 2 + sphere θ φ 1 ^ 2 + sphere θ φ 2 ^ 2 = 1 := by
  simp [sphere]
  linear_combination Real.sin θ ^ 2 * Real.sin_sq_add_cos_sq φ +
    Real.sin_sq_add_cos_sq θ

/-- Reflection of the sphere across its equator reverses exactly `w₃`. -/
theorem sphere_mirror (θ φ : ℝ) : sphere (Real.pi - θ) φ = mirror (sphere θ φ) := by
  ext i
  fin_cases i <;> simp [sphere, mirror, Real.sin_pi_sub, Real.cos_pi_sub]

/-- The equator is the collinear circle. -/
theorem equator_w3 (φ : ℝ) : sphere (Real.pi / 2) φ 2 = 0 := by
  simp [sphere]

theorem equator_mirror_fixed (φ : ℝ) :
    mirror (sphere (Real.pi / 2) φ) = sphere (Real.pi / 2) φ :=
  (mirror_fixed_iff _).mpr (equator_w3 φ)

/-- The meridian derivative of `sin θ` vanishes at the equator. -/
lemma equatorial_sin_derivative :
    HasDerivAt (fun ε : ℝ => Real.sin (ε + Real.pi / 2)) 0 0 := by
  have hg : HasDerivAt (fun ε : ℝ => ε + Real.pi / 2) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).add_const (Real.pi / 2)
  have h := (Real.hasDerivAt_sin (0 + Real.pi / 2)).comp 0 hg
  convert h using 1 <;> simp [Function.comp_def]

/-- The meridian derivative of the height is `-1`, so the meridian direction is
nonzero and transverse to the collinear circle. -/
lemma equatorial_height_derivative (φ : ℝ) :
    HasDerivAt (fun ε : ℝ => sphere (ε + Real.pi / 2) φ 2) (-1) 0 := by
  have hg : HasDerivAt (fun ε : ℝ => ε + Real.pi / 2) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).add_const (Real.pi / 2)
  have h := (Real.hasDerivAt_cos (0 + Real.pi / 2)).comp 0 hg
  convert h using 1 <;> simp [Function.comp_def, sphere]

/-- **The sphere fold.** At every point of the collinear circle, the derivative
of the retained record along the nonzero meridian direction is zero. Together
with `equatorial_height_derivative`, this is the asserted transverse kernel. -/
theorem equatorial_record_derivative (φ : ℝ) :
    HasDerivAt (fun ε : ℝ => record (sphere (ε + Real.pi / 2) φ)) (0, 0) 0 := by
  have h0 := equatorial_sin_derivative.mul_const (Real.cos φ)
  have h1 := equatorial_sin_derivative.mul_const (Real.sin φ)
  simpa [record, sphere] using h0.prodMk h1

/-- The same statement for each of the card's three normalized distances. -/
theorem equatorial_distance_derivative (φ : ℝ) (k : Fin 3) :
    HasDerivAt (fun ε : ℝ => distance (sphere (ε + Real.pi / 2) φ) k) 0 0 := by
  have h0 := equatorial_sin_derivative.mul_const (Real.cos φ)
  have h1 := equatorial_sin_derivative.mul_const (Real.sin φ)
  fin_cases k
  · simpa [distance, sphere, u] using (h0.const_add 1).div_const 3
  · have h := ((h0.mul_const (-1 / 2)).add
      (h1.mul_const (Real.sqrt 3 / 2))).const_add 1 |>.div_const 3
    simpa [distance, sphere, u] using h
  · have h := ((h0.mul_const (-1 / 2)).add
      (h1.mul_const (-(Real.sqrt 3 / 2)))).const_add 1 |>.div_const 3
    simpa [distance, sphere, u] using h

/-- Across the fold the two sheets are related by `ε ↦ -ε` and have exactly
the same distances. -/
theorem equatorial_distance_even (φ ε : ℝ) (k : Fin 3) :
    distance (sphere (Real.pi / 2 - ε) φ) k =
      distance (sphere (ε + Real.pi / 2) φ) k := by
  have hm := sphere_mirror (ε + Real.pi / 2) φ
  have heq : Real.pi - (ε + Real.pi / 2) = Real.pi / 2 - ε := by ring
  rw [heq] at hm
  calc
    distance (sphere (Real.pi / 2 - ε) φ) k =
        distance (mirror (sphere (ε + Real.pi / 2) φ)) k := by rw [hm]
    _ = distance (sphere (ε + Real.pi / 2) φ) k := mirror_same_distance _ _

#print axioms B115.sqrt3_sq
#print axioms B115.sqrt3_ne_zero
#print axioms B115.outer_phase
#print axioms B115.energy_ne_zero
#print axioms B115.projector_phase
#print axioms B115.outer_mul_outer
#print axioms B115.projector_idempotent
#print axioms B115.projector_hermitian
#print axioms B115.projector_trace
#print axioms B115.bloch_phase
#print axioms B115.projector_distance_phase
#print axioms B115.bloch_projector_zero
#print axioms B115.bloch_projector_one
#print axioms B115.bloch_projector_two
#print axioms B115.bloch_projector_unit
#print axioms B115.bloch_jacobi_mirror
#print axioms B115.projector_mirror_same_distance
#print axioms B115.u_unit
#print axioms B115.u_inner
#print axioms B115.normalized_distances_sum
#print axioms B115.mirror_same_distance
#print axioms B115.record_mirror
#print axioms B115.recover_distance
#print axioms B115.distances_determine_record
#print axioms B115.mirror_involutive
#print axioms B115.mirror_fixed_iff
#print axioms B115.projector_exp_phase
#print axioms B115.witnessPlus_unit
#print axioms B115.witnessMinus_unit
#print axioms B115.witness_sheets_distinct
#print axioms B115.witness_same_distance
#print axioms B115.witness_distance_values
#print axioms B115.witness_triangle_distance
#print axioms B115.triangle_mirror_same_sqDist
#print axioms B115.triangle_scalene
#print axioms B115.triangle_opposite_area
#print axioms B115.witness_opposite_w3
#print axioms B115.record_section
#print axioms B115.record_surjective
#print axioms B115.sphere_unit
#print axioms B115.sphere_mirror
#print axioms B115.equator_w3
#print axioms B115.equator_mirror_fixed
#print axioms B115.equatorial_sin_derivative
#print axioms B115.equatorial_height_derivative
#print axioms B115.equatorial_record_derivative
#print axioms B115.equatorial_distance_derivative
#print axioms B115.equatorial_distance_even

end B115


/-! ## B118 — the Veronese curvature and the Chern number 2j

Integrated from `.ultramath/smwvwr2ce/m7/B118.lean`.
-/

/-!
# B118 — Veronese spherical chart, saturation and flux

This file certifies the coordinate-geometric part of card B118.  The unit-sphere
metric and the spin-coherent Berry connection are explicit inputs; the curvature
is defined as the exterior-derivative component of that connection, not assumed
to be `j sin θ`.  We then prove the metric scaling, determinant saturation and
normalised flux, including the sign convention used for the Chern number.

The spin representation, the construction of the coherent state in `ℂ^(2j+1)`,
and the derivation of the Fubini–Study metric from that Hilbert-space family are
outside this finite coordinate kernel.  No claim about generic multilevel bands
is made here.
-/

set_option autoImplicit false
noncomputable section

namespace B118

open scoped intervalIntegral

/-- The round unit-sphere metric in coordinates `(θ, φ)`. -/
def sphereMetric (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, Real.sin θ ^ 2]

/-- The coordinate metric of the degree-`2j` Veronese sphere.  Its value is the
Fubini–Study metric carried by the card; the theorem `veroneseMetric_eq` checks
the advertised factor `j/2` entry by entry. -/
def veroneseMetric (j θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![j / 2, 0; 0, (j / 2) * Real.sin θ ^ 2]

/-- The north-chart Berry connection component `Aθ = 0`. -/
def veroneseAθ : ℝ := 0

/-- The north-chart spin-coherent Berry connection component
`Aφ = j (1 - cos θ)`.  It is independent of `φ`, as in the source card. -/
def veroneseAφ (j θ : ℝ) : ℝ := j * (1 - Real.cos θ)

/-- The signed `(θ,φ)` component of the curvature 2-form, defined by
`Ωθφ = ∂θ Aφ - ∂φ Aθ`.  Positive orientation is `dθ ∧ dφ`. -/
def veroneseCurvature (j θ φ : ℝ) : ℝ :=
  deriv (fun t : ℝ => veroneseAφ j t) θ -
    deriv (fun _ : ℝ => veroneseAθ) φ

/-- Total signed Berry flux on `0 ≤ θ ≤ π`, `0 ≤ φ ≤ 2π`. -/
def berryFlux (j : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    ∫ φ in (0 : ℝ)..(2 * Real.pi), veroneseCurvature j θ φ

/-- Chern number in the card's `1/(2π)` normalisation. -/
def chernNumber (j : ℝ) : ℝ := berryFlux j / (2 * Real.pi)

/-- The metric has exactly the card's factor `j/2`, not `j` or `2j`. -/
theorem veroneseMetric_eq (j θ : ℝ) :
    veroneseMetric j θ = (j / 2) • sphereMetric θ := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [veroneseMetric, sphereMetric, Matrix.smul_apply]

/-- The derivative of the explicit Berry connection gives `Aφ' = j sin θ`. -/
theorem hasDerivAt_veroneseAφ (j θ : ℝ) :
    HasDerivAt (fun t : ℝ => veroneseAφ j t) (j * Real.sin θ) θ := by
  have h := ((hasDerivAt_const θ (1 : ℝ)).sub (Real.hasDerivAt_cos θ)).const_mul j
  convert h using 1 <;> simp [veroneseAφ]

/-- The signed curvature is genuinely obtained from the connection. -/
theorem veroneseCurvature_eq (j θ φ : ℝ) :
    veroneseCurvature j θ φ = j * Real.sin θ := by
  unfold veroneseCurvature
  rw [(hasDerivAt_veroneseAφ j θ).deriv]
  simp [veroneseAθ]

/-- On the northern-to-southern polar chart, and for nonnegative spin, the
signed curvature agrees with its magnitude. -/
theorem abs_veroneseCurvature (j θ φ : ℝ) (hj : 0 ≤ j)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    |veroneseCurvature j θ φ| = j * Real.sin θ := by
  rw [veroneseCurvature_eq]
  exact abs_of_nonneg (mul_nonneg hj (Real.sin_nonneg_of_mem_Icc hθ))

/-- In particular, at spin `(n : ℕ)/2` the displayed magnitude is
`j sin θ` on the whole standard spherical chart. -/
theorem abs_veroneseCurvature_nat (n : ℕ) (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    |veroneseCurvature ((n : ℝ) / 2) θ φ| = ((n : ℝ) / 2) * Real.sin θ := by
  exact abs_veroneseCurvature _ _ _ (by positivity) hθ

/-- The coordinate determinant, including all powers of `j`. -/
theorem det_veroneseMetric (j θ : ℝ) :
    (veroneseMetric j θ).det = (j ^ 2 / 4) * Real.sin θ ^ 2 := by
  rw [veroneseMetric, Matrix.det_fin_two_of]
  ring

/-- B118 saturation is an identity in `j`, in the chart and orientation above:
`4 det g = Ωθφ²`. -/
theorem veronese_saturation (j θ φ : ℝ) :
    4 * (veroneseMetric j θ).det = (veroneseCurvature j θ φ) ^ 2 := by
  rw [det_veroneseMetric, veroneseCurvature_eq]
  ring

/-- The angular integral of one sine is exactly two. -/
theorem integral_sin_zero_pi : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) = 2 := by
  rw [integral_sin]
  norm_num

/-- The `φ` integral contributes `2π`; this lemma keeps the flux normalisation
explicit rather than hiding it in numerical simplification. -/
theorem innerCurvatureIntegral (j θ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), veroneseCurvature j θ φ) =
      (2 * Real.pi) * (j * Real.sin θ) := by
  simp only [veroneseCurvature_eq, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]

/-- The unnormalised signed Berry flux is `4πj`. -/
theorem berryFlux_eq (j : ℝ) : berryFlux j = 4 * Real.pi * j := by
  unfold berryFlux
  simp_rw [innerCurvatureIntegral]
  calc
    (∫ θ in (0 : ℝ)..Real.pi, (2 * Real.pi) * (j * Real.sin θ)) =
        (2 * Real.pi * j) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ := by
      rw [show (fun θ : ℝ => (2 * Real.pi) * (j * Real.sin θ)) =
        (fun θ => (2 * Real.pi * j) * Real.sin θ) by
          funext θ
          ring]
      rw [intervalIntegral.integral_const_mul]
    _ = 4 * Real.pi * j := by rw [integral_sin_zero_pi]; ring

/-- With the card's positive orientation, `C = 2j` exactly. -/
theorem chernNumber_eq (j : ℝ) : chernNumber j = 2 * j := by
  rw [chernNumber, berryFlux_eq]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-- If `n = 2j` is a positive integer, the Chern number is that integer `n`.
The hypothesis is the card's `Check`; positivity is recorded even though the
flux calculation itself is also algebraically valid at zero. -/
theorem chernNumber_nat (n : ℕ) (_hn : 0 < n) :
    chernNumber ((n : ℝ) / 2) = (n : ℤ) := by
  rw [chernNumber_eq]
  push_cast
  ring

/-- Reversing orientation reverses the signed curvature and hence the Chern
number; the saturation equation is unchanged because it squares curvature. -/
theorem reverseOrientation_chernNumber (j : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      ∫ φ in (0 : ℝ)..(2 * Real.pi), -veroneseCurvature j θ φ) /
        (2 * Real.pi) = -(2 * j) := by
  have hneg : (∫ θ in (0 : ℝ)..Real.pi,
      ∫ φ in (0 : ℝ)..(2 * Real.pi), -veroneseCurvature j θ φ) = -berryFlux j := by
    unfold berryFlux
    simp [intervalIntegral.integral_neg]
  rw [hneg, neg_div]
  change -(chernNumber j) = -(2 * j)
  rw [chernNumber_eq]

/-- The spin-one-half witness independently exposes all three normalisations:
`gθθ = 1/4`, `Ω = (1/2) sin θ`, and `C = 1`. -/
theorem spin_half_witness (θ φ : ℝ) :
    (veroneseMetric (1 / 2) θ 0 0 = 1 / 4) ∧
    veroneseCurvature (1 / 2) θ φ = (1 / 2) * Real.sin θ ∧
    chernNumber (1 / 2) = 1 := by
  refine ⟨?_, veroneseCurvature_eq _ _ _, ?_⟩
  · norm_num [veroneseMetric]
  · norm_num [chernNumber_eq]

/-- A concrete false control: replacing `j/2` by `j` in the metric spoils
saturation.  At `j = 1/2`, `θ = π/2`, the left side is `1` while the squared
curvature is `1/4`. -/
theorem wrong_metric_factor_counterexample :
    4 * (((((1 / 2 : ℝ)) • sphereMetric (Real.pi / 2))).det) ≠
      (veroneseCurvature (1 / 2) (Real.pi / 2) 0) ^ 2 := by
  norm_num [sphereMetric, veroneseCurvature_eq, Matrix.det_fin_two,
    Matrix.smul_apply]

/-- The unqualified absolute-value formula is false outside the standard polar
chart.  At `j = 1`, `θ = -π/2`, its left side is `1` and its right side is `-1`. -/
theorem curvature_magnitude_needs_chart :
    |veroneseCurvature 1 (-Real.pi / 2) 0| ≠
      1 * Real.sin (-Real.pi / 2) := by
  have hs : Real.sin (-Real.pi / 2) = -1 := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.sin_neg,
      Real.sin_pi_div_two]
  rw [veroneseCurvature_eq, hs]
  norm_num

/-! ## Axiom audit -/

#print axioms veroneseMetric_eq
#print axioms hasDerivAt_veroneseAφ
#print axioms veroneseCurvature_eq
#print axioms abs_veroneseCurvature
#print axioms abs_veroneseCurvature_nat
#print axioms det_veroneseMetric
#print axioms veronese_saturation
#print axioms integral_sin_zero_pi
#print axioms innerCurvatureIntegral
#print axioms berryFlux_eq
#print axioms chernNumber_eq
#print axioms chernNumber_nat
#print axioms reverseOrientation_chernNumber
#print axioms spin_half_witness
#print axioms wrong_metric_factor_counterexample
#print axioms curvature_magnitude_needs_chart

end B118


/-! ## B150 — the trace-free equation forces d(R + kappa T) = 0

Integrated from `.ultramath/smwvwr2ce/m8/B150.lean`.
-/

/-!
# B150: the finite tensor calculation behind unimodular gravity

We use an abstract real coordinate type `X` and arbitrary real-linear derivative
operators `D μ` on scalar functions. Thus no analytic assertion is smuggled
into the algebra. The contracted Bianchi identity is an explicit hypothesis.

The metric is the constant Minkowski metric `diag (-1, 1, 1, 1)`. Raising the
derivative index in a divergence therefore multiplies the diagonal term by the
same sign. Only the finite sums, linearity, and the numerical factors are
proved here.
-/

namespace RelationalAtlas.B150

open scoped BigOperators

variable {X : Type*}

/-- A covariant four-tensor field with two indices. -/
abbrev Tensor4 (X : Type*) := Fin 4 → Fin 4 → X → ℝ

/-- The entries of the diagonal Minkowski metric. -/
def eta : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- The constant covariant Minkowski metric. Its inverse has the same entries. -/
def minkowski : Fin 4 → Fin 4 → ℝ :=
  fun μ ν => if μ = ν then eta μ else 0

/-- The metric trace of a covariant two-tensor. -/
def scalarTrace (A : Tensor4 X) : X → ℝ :=
  fun x => ∑ μ, eta μ * A μ μ x

/-- Raise the derivative index and contract the first tensor index. -/
def divergence
    (D : Fin 4 → (X → ℝ) →ₗ[ℝ] (X → ℝ)) (A : Tensor4 X) (ν : Fin 4) : X → ℝ :=
  fun x => ∑ μ, eta μ * (D μ (A μ ν)) x

/-- The combination which the trace-free field equation makes pure trace.
The minus sign is essential even though the final constant uses `R + κT`. -/
def tensorDifference (κ : ℝ) (Ric T : Tensor4 X) : Tensor4 X :=
  fun μ ν => Ric μ ν - κ • T μ ν

@[simp] lemma eta_mul_self (μ : Fin 4) : eta μ * eta μ = 1 := by
  fin_cases μ <;> norm_num [eta]

/-- Metric trace is linear in the combination `Ric - κT`. -/
theorem scalarTrace_tensorDifference (κ : ℝ) (Ric T : Tensor4 X) :
    scalarTrace (tensorDifference κ Ric T) =
      scalarTrace Ric - κ • scalarTrace T := by
  funext x
  simp only [scalarTrace, tensorDifference, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The displayed trace-free equation is precisely
`Ric - κT = (1/4) (R - κT) g`. -/
theorem tensorDifference_eq_trace_part
    (κ : ℝ) (Ric T : Tensor4 X)
    (hfield : ∀ μ ν x,
      Ric μ ν x - (1 / 4 : ℝ) * minkowski μ ν * scalarTrace Ric x =
        κ * (T μ ν x - (1 / 4 : ℝ) * minkowski μ ν * scalarTrace T x)) :
    ∀ μ ν, tensorDifference κ Ric T μ ν =
      ((1 / 4 : ℝ) * minkowski μ ν) • scalarTrace (tensorDifference κ Ric T) := by
  intro μ ν
  funext x
  have h := hfield μ ν x
  rw [scalarTrace_tensorDifference]
  simp only [tensorDifference, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h

/-- Divergence is linear in `Ric - κT`. -/
theorem divergence_tensorDifference
    (D : Fin 4 → (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (κ : ℝ) (Ric T : Tensor4 X) (ν : Fin 4) :
    divergence D (tensorDifference κ Ric T) ν =
      divergence D Ric ν - κ • divergence D T ν := by
  funext x
  simp only [divergence, tensorDifference, map_sub, map_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The divergence of `(S/4)g` is `(1/4)dS`; the metric is constant and
its diagonal entries square to one. -/
theorem divergence_metric_trace_part
    (D : Fin 4 → (X → ℝ) →ₗ[ℝ] (X → ℝ)) (S : X → ℝ) (ν : Fin 4) :
    divergence D (fun μ ν => ((1 / 4 : ℝ) * minkowski μ ν) • S) ν =
      (1 / 4 : ℝ) • D ν S := by
  funext x
  fin_cases ν <;>
    simp [divergence, minkowski, eta, Fin.sum_univ_four, map_smul,
      Pi.smul_apply, smul_eq_mul]

/-- The scalar arithmetic at one point. This also checks the sign: a plus
sign inside the bracket on the right would not prove the claimed conclusion. -/
theorem scalar_constant_arithmetic (κ r t : ℝ)
    (h : (1 / 2 : ℝ) * r = (1 / 4 : ℝ) * (r - κ * t)) :
    r + κ * t = 0 := by
  linarith

/-- **B150 finite core.** Assuming the trace-free field equation, matter
conservation, and the contracted Bianchi identity in divergence form, every
coordinate derivative of `R + κT` vanishes.

The Bianchi hypothesis is the analytic/geometric input; all the remaining
steps are finite tensor algebra and linearity of differentiation. -/
theorem derivative_scalar_add_stress_eq_zero
    (D : Fin 4 → (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (κ : ℝ) (Ric T : Tensor4 X)
    (hfield : ∀ μ ν x,
      Ric μ ν x - (1 / 4 : ℝ) * minkowski μ ν * scalarTrace Ric x =
        κ * (T μ ν x - (1 / 4 : ℝ) * minkowski μ ν * scalarTrace T x))
    (hBianchi : ∀ ν, divergence D Ric ν =
      (1 / 2 : ℝ) • D ν (scalarTrace Ric))
    (hconservation : ∀ ν, divergence D T ν = 0)
    (ν : Fin 4) :
    D ν (scalarTrace Ric + κ • scalarTrace T) = 0 := by
  have hpure := tensorDifference_eq_trace_part κ Ric T hfield
  have hdiv_from_bianchi :
      divergence D (tensorDifference κ Ric T) ν =
        (1 / 2 : ℝ) • D ν (scalarTrace Ric) := by
    rw [divergence_tensorDifference, hBianchi, hconservation]
    simp
  have hdiv_from_field :
      divergence D (tensorDifference κ Ric T) ν =
        (1 / 4 : ℝ) • D ν (scalarTrace (tensorDifference κ Ric T)) := by
    have hA : tensorDifference κ Ric T =
        (fun μ ν => ((1 / 4 : ℝ) * minkowski μ ν) •
          scalarTrace (tensorDifference κ Ric T)) := by
      funext μ ν
      exact hpure μ ν
    calc
      divergence D (tensorDifference κ Ric T) ν =
          divergence D (fun μ ν => ((1 / 4 : ℝ) * minkowski μ ν) •
            scalarTrace (tensorDifference κ Ric T)) ν :=
        congrArg (fun B : Tensor4 X => divergence D B ν) hA
      _ = _ := divergence_metric_trace_part D _ ν
  have hmain : (1 / 2 : ℝ) • D ν (scalarTrace Ric) =
      (1 / 4 : ℝ) • D ν (scalarTrace (tensorDifference κ Ric T)) :=
    hdiv_from_bianchi.symm.trans hdiv_from_field
  rw [scalarTrace_tensorDifference] at hmain
  funext x
  have hx := congrFun hmain x
  simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_smul, Pi.sub_apply] at hx
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  exact scalar_constant_arithmetic κ _ _ hx

/-- In a one-dimensional connected model, the usual derivative turns the
vanishing-derivative conclusion into the card's `4Λ` normalisation.  The mean
value theorem, not tensor algebra, is the input to this separate corollary. -/
theorem exists_cosmological_constant_one_dimensional
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hfzero : ∀ x, deriv f x = 0) :
    ∃ Λ : ℝ, ∀ x, f x = 4 * Λ := by
  refine ⟨f 0 / 4, fun x => ?_⟩
  rw [is_const_of_deriv_eq_zero hf hfzero x 0]
  ring

#print axioms eta_mul_self
#print axioms scalarTrace_tensorDifference
#print axioms tensorDifference_eq_trace_part
#print axioms divergence_tensorDifference
#print axioms divergence_metric_trace_part
#print axioms scalar_constant_arithmetic
#print axioms derivative_scalar_add_stress_eq_zero
#print axioms exists_cosmological_constant_one_dimensional

end RelationalAtlas.B150


/-! ## B157 — the signature, the mirror, and the unit-circle roots

Integrated from `.ultramath/smwvwr2ce/m5/B157.lean`.
-/

open scoped ComplexConjugate
open Polynomial

namespace RelationalAtlas.B157

open Matrix

noncomputable section

/-- The integer sign used to count the spectrum. -/
def signZ (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

@[simp] lemma signZ_zero : signZ 0 = 0 := by simp [signZ]

lemma signZ_neg (x : ℝ) : signZ (-x) = -signZ x := by
  unfold signZ
  split_ifs <;> norm_num at * <;> linarith

/-- A characteristic-polynomial formula for the signature. On a Hermitian matrix
this is proved below to be the number of positive minus negative eigenvalues. -/
def spectralSignature {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℤ :=
  (A.charpoly.roots.map (fun z => signZ z.re)).sum

lemma spectralSignature_eq_sum_eigenvalue_signs {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    spectralSignature A = ∑ i, signZ (hA.eigenvalues i) := by
  rw [spectralSignature, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp [Function.comp_def]

lemma charpoly_neg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    (-A).charpoly = Polynomial.C ((-1 : ℂ) ^ Fintype.card n) * A.charpoly.comp (-X) := by
  apply Polynomial.funext
  intro z
  simp only [Matrix.eval_charpoly, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  have hmatrix : Matrix.scalar n (-z) - A = -(Matrix.scalar n z - (-A)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar, h] <;> ring
  have hpow : ((-1 : ℂ) ^ Fintype.card n) * ((-1 : ℂ) ^ Fintype.card n) = 1 := by
    rw [← mul_pow]
    simp
  calc
    (Matrix.scalar n z - -A).det
        = ((-1 : ℂ) ^ Fintype.card n) *
            ((-1 : ℂ) ^ Fintype.card n) * (Matrix.scalar n z - -A).det := by
              rw [hpow, one_mul]
    _ = (-1 : ℂ) ^ Fintype.card n * (Matrix.scalar n (-z) - A).det := by
          rw [hmatrix, Matrix.det_neg]
          ring

lemma roots_charpoly_neg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    (-A).charpoly.roots = A.charpoly.roots.map (fun z => -z) := by
  rw [charpoly_neg, Polynomial.roots_C_mul]
  · exact Polynomial.roots_comp_neg_X A.charpoly
  · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)

lemma spectralSignature_neg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : spectralSignature (-A) = -spectralSignature A := by
  rw [spectralSignature, spectralSignature, roots_charpoly_neg, Multiset.map_map]
  simp only [Function.comp_def]
  have hfun : (fun z : ℂ => signZ (-z).re) = (fun z => -signZ z.re) := by
    funext z
    simp only [Complex.neg_re]
    exact signZ_neg z.re
  rw [hfun, Multiset.sum_map_neg]

@[simp] lemma spectralSignature_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : spectralSignature A.transpose = spectralSignature A := by
  simp [spectralSignature, Matrix.charpoly_transpose]

lemma spectralSignature_neg_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    spectralSignature (-A.transpose) = -spectralSignature A := by
  rw [← Matrix.transpose_neg, spectralSignature_transpose, spectralSignature_neg]

@[simp] lemma spectralSignature_zero {n : Type*} [Fintype n] [DecidableEq n] :
    spectralSignature (0 : Matrix n n ℂ) = 0 := by
  simp [spectralSignature, Multiset.map_nsmul]
  rw [Multiset.sum_nsmul]
  simp

lemma signZ_pair {x y : ℝ} (hxy : x * y ≠ 0) :
    signZ x + signZ y = if x * y < 0 then 0 else if 0 < x + y then 2 else -2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hp : 0 < x * y := mul_pos_of_neg_of_neg hx hy
      have hs : x + y < 0 := add_neg hx hy
      simp [signZ, hx, hx.not_gt, hy, hy.not_gt, (not_lt_of_ge hp.le), hs.not_gt]
    · simp at hxy
    · have hp : x * y < 0 := mul_neg_of_neg_of_pos hx hy
      simp [signZ, hx, hx.not_gt, hy, (not_lt_of_ge hy.le), hp]
  · simp at hxy
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hp : x * y < 0 := mul_neg_of_pos_of_neg hx hy
      simp [signZ, hx, (not_lt_of_ge hx.le), hy, hy.not_gt, hp]
    · simp at hxy
    · have hp : 0 < x * y := mul_pos hx hy
      have hs : 0 < x + y := add_pos hx hy
      simp [signZ, hx, (not_lt_of_ge hx.le), hy, (not_lt_of_ge hy.le), (not_lt_of_ge hp.le), hs]

lemma isHermitian_ofReal_det_re {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) : (A.det.re : ℂ) = A.det := by
  apply Complex.conj_eq_iff_re.mp
  calc
    (starRingEnd ℂ) A.det = star A.det := starRingEnd_apply _
    _ = A.conjTranspose.det := (Matrix.det_conjTranspose A).symm
    _ = A.det := by rw [hA.eq]

lemma hermitian_det_re {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) :
    A.det.re = hA.eigenvalues 0 * hA.eigenvalues 1 := by
  rw [hA.det_eq_prod_eigenvalues, Fin.prod_univ_two]
  simp

lemma hermitian_trace_re {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) :
    A.trace.re = hA.eigenvalues 0 + hA.eigenvalues 1 := by
  rw [hA.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
  simp

/-- In rank two the signature is read exactly from determinant and trace. The
nonsingularity hypothesis is essential when the determinant is positive. -/
lemma spectralSignature_two {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    spectralSignature A = if A.det.re < 0 then 0 else if 0 < A.trace.re then 2 else -2 := by
  have hdetre : A.det.re ≠ 0 := by
    intro hre
    apply hdet
    rw [← isHermitian_ofReal_det_re hA, hre]
    simp
  have hxy : hA.eigenvalues 0 * hA.eigenvalues 1 ≠ 0 := by
    rw [← hermitian_det_re hA]
    exact hdetre
  rw [spectralSignature_eq_sum_eigenvalue_signs hA, Fin.sum_univ_two,
    signZ_pair hxy, ← hermitian_det_re hA, ← hermitian_trace_re hA]

/-- Real Seifert matrices embedded in the complex matrices. -/
def complexify {m n : Type*} (V : Matrix m n ℝ) : Matrix m n ℂ :=
  V.map Complex.ofReal

/-- The Hermitian Levine–Tristram form on a real Seifert matrix. -/
def seifertForm {n : Type*} (V : Matrix n n ℝ) (ω : ℂ) : Matrix n n ℂ :=
  (1 - ω) • complexify V + (1 - star ω) • (complexify V).transpose

/-- The Alexander presentation whose determinant has the same roots as the
usual Alexander polynomial. No normalization is hidden in this definition. -/
def alexanderDet {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (ω : ℂ) : ℂ :=
  ((complexify V).transpose - ω • complexify V).det

lemma seifertForm_isHermitian {n : Type*} (V : Matrix n n ℝ) (ω : ℂ) :
    (seifertForm V ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [seifertForm, complexify, Matrix.conjTranspose_apply]
  ring

/-- With the standard mirror Seifert matrix `-Vᵀ`, mirroring negates and
transposes the Hermitian form. -/
lemma seifertForm_mirror {n : Type*} (V : Matrix n n ℝ) (ω : ℂ) :
    seifertForm (-V.transpose) ω = -(seifertForm V ω).transpose := by
  ext i j
  simp [seifertForm, complexify]
  ring

lemma seifertForm_at_one {n : Type*} (V : Matrix n n ℝ) :
    seifertForm V 1 = 0 := by
  simp [seifertForm]

lemma seifertForm_eq_smul_alexanderMatrix {n : Type*}
    (V : Matrix n n ℝ) (ω : ℂ) (hω : ω * star ω = 1) :
    seifertForm V ω = (1 - star ω) •
      ((complexify V).transpose - ω • complexify V) := by
  have hscalar : 1 - ω = -ω * (1 - star ω) := by
    calc
      1 - ω = ω * star ω - ω := by rw [hω]
      _ = -ω * (1 - star ω) := by ring
  simp only [Complex.star_def] at hscalar
  ext i j
  simp [seifertForm, complexify]
  rw [hscalar]
  ring

lemma seifertForm_det {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (ω : ℂ) (hω : ω * star ω = 1) :
    (seifertForm V ω).det = (1 - star ω) ^ Fintype.card n * alexanderDet V ω := by
  rw [seifertForm_eq_smul_alexanderMatrix V ω hω, Matrix.det_smul, alexanderDet]

/-- Away from 1, nonsingularity is exactly nonvanishing of the Alexander
presentation. This is a wall criterion, not the false converse claiming every
root forces a signature jump. -/
lemma seifertForm_singular_iff_alexander_zero {n : Type*} [Fintype n]
    [DecidableEq n] (V : Matrix n n ℝ) {ω : ℂ}
    (hω : ω * star ω = 1) (hω1 : ω ≠ 1) :
    (seifertForm V ω).det = 0 ↔ alexanderDet V ω = 0 := by
  have hc : 1 - star ω ≠ 0 := by
    intro hc
    have hs : star ω = 1 := (sub_eq_zero.mp hc).symm
    apply hω1
    have h := congrArg star hs
    simpa using h
  rw [seifertForm_det V ω hω, mul_eq_zero]
  constructor
  · rintro (hp | ha)
    · exact (pow_ne_zero _ hc hp).elim
    · exact ha
  · exact Or.inr

lemma nonsingular_seifertForm_excludes_alexander_root {n : Type*} [Fintype n]
    [DecidableEq n] (V : Matrix n n ℝ) {ω : ℂ}
    (hω : ω * star ω = 1) (hω1 : ω ≠ 1) (hnonsing : (seifertForm V ω).det ≠ 0) :
    alexanderDet V ω ≠ 0 := by
  exact (seifertForm_singular_iff_alexander_zero V hω hω1).not.mp hnonsing

lemma mirror_signature_antisymmetric {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (ω : ℂ) :
    spectralSignature (seifertForm (-V.transpose) ω) =
      -spectralSignature (seifertForm V ω) := by
  rw [seifertForm_mirror, spectralSignature_neg_transpose]

lemma signature_zero_of_self_mirror {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (ω : ℂ)
    (hfixed : spectralSignature (seifertForm (-V.transpose) ω) =
      spectralSignature (seifertForm V ω)) :
    spectralSignature (seifertForm V ω) = 0 := by
  rw [mirror_signature_antisymmetric] at hfixed
  omega

/-- Nonsingular Hermitian rank-two forms. -/
abbrev RegularHermitian2 :=
  {A : Matrix (Fin 2) (Fin 2) ℂ // A.IsHermitian ∧ A.det ≠ 0}

/-- The integer plateau function on nonsingular Hermitian rank-two forms. -/
def regularSignature (A : RegularHermitian2) : ℤ := spectralSignature A.1

lemma continuous_regular_det_re :
    Continuous (fun A : RegularHermitian2 => A.1.det.re) := by
  exact Complex.continuous_re.comp continuous_subtype_val.matrix_det

lemma continuous_regular_trace_re :
    Continuous (fun A : RegularHermitian2 => A.1.trace.re) := by
  exact Complex.continuous_re.comp continuous_subtype_val.matrix_trace

lemma trace_re_ne_zero_of_det_pos {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) (hd : 0 < A.det.re) : A.trace.re ≠ 0 := by
  rw [hermitian_det_re hA] at hd
  rw [hermitian_trace_re hA]
  intro hs
  have heq : hA.eigenvalues 1 = -hA.eigenvalues 0 := by linarith
  rw [heq] at hd
  nlinarith [sq_nonneg (hA.eigenvalues 0)]

/-- The full rank-two plateau theorem: the signature is locally constant on
all nonsingular Hermitian forms. -/
lemma isLocallyConstant_regularSignature : IsLocallyConstant regularSignature := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro A
  have hdetre : A.1.det.re ≠ 0 := by
    intro hre
    apply A.2.2
    rw [← isHermitian_ofReal_det_re A.2.1, hre]
    simp
  by_cases hdneg : A.1.det.re < 0
  · have hopen : IsOpen {B : RegularHermitian2 | B.1.det.re < 0} :=
      isOpen_lt continuous_regular_det_re continuous_const
    filter_upwards [hopen.mem_nhds hdneg] with B hB
    change spectralSignature B.1 = spectralSignature A.1
    rw [spectralSignature_two B.2.1 B.2.2, spectralSignature_two A.2.1 A.2.2,
      if_pos hB, if_pos hdneg]
  · have hdpos : 0 < A.1.det.re :=
      lt_of_le_of_ne (not_lt.mp hdneg) (Ne.symm hdetre)
    have htne : A.1.trace.re ≠ 0 := trace_re_ne_zero_of_det_pos A.2.1 hdpos
    have hopenD : IsOpen {B : RegularHermitian2 | 0 < B.1.det.re} :=
      isOpen_lt continuous_const continuous_regular_det_re
    by_cases htpos : 0 < A.1.trace.re
    · have hopenT : IsOpen {B : RegularHermitian2 | 0 < B.1.trace.re} :=
        isOpen_lt continuous_const continuous_regular_trace_re
      filter_upwards [hopenD.mem_nhds hdpos, hopenT.mem_nhds htpos] with B hBd hBt
      change spectralSignature B.1 = spectralSignature A.1
      rw [spectralSignature_two B.2.1 B.2.2, spectralSignature_two A.2.1 A.2.2,
        if_neg (not_lt_of_ge hBd.le), if_neg (not_lt_of_ge hdpos.le),
        if_pos hBt, if_pos htpos]
    · have htneg : A.1.trace.re < 0 := lt_of_le_of_ne (not_lt.mp htpos) htne
      have hopenT : IsOpen {B : RegularHermitian2 | B.1.trace.re < 0} :=
        isOpen_lt continuous_regular_trace_re continuous_const
      filter_upwards [hopenD.mem_nhds hdpos, hopenT.mem_nhds htneg] with B hBd hBt
      change spectralSignature B.1 = spectralSignature A.1
      rw [spectralSignature_two B.2.1 B.2.2, spectralSignature_two A.2.1 A.2.2,
        if_neg (not_lt_of_ge hBd.le), if_neg (not_lt_of_ge hdpos.le),
        if_neg (not_lt_of_ge hBt.le), if_neg (not_lt_of_ge htneg.le)]

/-- A rank-two chiral witness, with Alexander presentation `ω²-ω+1`. -/
def chiralWitnessV : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

lemma chiralWitness_alexanderDet (ω : ℂ) :
    alexanderDet chiralWitnessV ω = ω ^ 2 - ω + 1 := by
  simp [alexanderDet, complexify, chiralWitnessV, Matrix.det_fin_two]
  ring

lemma chiralWitness_form_at_neg_one :
    seifertForm chiralWitnessV (-1) = !![(4 : ℂ), 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seifertForm, complexify, chiralWitnessV]

lemma chiralWitness_signature_at_neg_one :
    spectralSignature (seifertForm chiralWitnessV (-1)) = 2 := by
  have hA := seifertForm_isHermitian chiralWitnessV (-1)
  have hdet : (seifertForm chiralWitnessV (-1)).det ≠ 0 := by
    rw [chiralWitness_form_at_neg_one]
    norm_num [Matrix.det_fin_two]
  rw [spectralSignature_two hA hdet, chiralWitness_form_at_neg_one]
  norm_num [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]

lemma chiralWitness_mirror_signature_at_neg_one :
    spectralSignature (seifertForm (-chiralWitnessV.transpose) (-1)) = -2 := by
  rw [mirror_signature_antisymmetric, chiralWitness_signature_at_neg_one]

/-- A standard Seifert matrix for the figure-eight knot `4_1`. -/
def figureEightV : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -1, -1]

lemma figureEight_alexanderDet (ω : ℂ) :
    alexanderDet figureEightV ω = -ω ^ 2 + 3 * ω - 1 := by
  simp [alexanderDet, complexify, figureEightV, Matrix.det_fin_two]
  ring

lemma figureEight_form_trace (ω : ℂ) :
    (seifertForm figureEightV ω).trace = 0 := by
  simp [seifertForm, complexify, figureEightV, Matrix.trace, Fin.sum_univ_two]
  ring

lemma circle_coordinates {ω : ℂ} (hω : ω * star ω = 1) :
    ω.re ^ 2 + ω.im ^ 2 = 1 := by
  have hre := congrArg Complex.re hω
  simp [Complex.mul_re, pow_two] at hre
  nlinarith

lemma figureEight_form_det {ω : ℂ} (hω : ω * star ω = 1) :
    (seifertForm figureEightV ω).det =
      ((-4 * ω.re ^ 2 + 10 * ω.re - 6 : ℝ) : ℂ) := by
  have hxy := circle_coordinates hω
  apply Complex.ext
  · simp [seifertForm, complexify, figureEightV, Matrix.det_fin_two,
      Complex.mul_re, pow_two]
    nlinarith
  · simp [seifertForm, complexify, figureEightV, Matrix.det_fin_two,
      Complex.mul_re, Complex.mul_im, pow_two]
    ring

lemma figureEight_form_det_re_neg {ω : ℂ}
    (hω : ω * star ω = 1) (hω1 : ω ≠ 1) :
    (seifertForm figureEightV ω).det.re < 0 := by
  have hxy := circle_coordinates hω
  have hxle : ω.re ≤ 1 := by nlinarith [sq_nonneg ω.im]
  have hxne : ω.re ≠ 1 := by
    intro hx
    apply hω1
    have hy : ω.im = 0 := by nlinarith [sq_nonneg ω.im]
    apply Complex.ext <;> simp [hx, hy]
  have hxlt : ω.re < 1 := lt_of_le_of_ne hxle hxne
  have hsecond : 2 * ω.re - 3 < 0 := by linarith
  have hp : 0 < (ω.re - 1) * (2 * ω.re - 3) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hxlt) hsecond
  rw [figureEight_form_det hω]
  simp only [Complex.ofReal_re]
  nlinarith

lemma figureEight_form_nonsingular {ω : ℂ}
    (hω : ω * star ω = 1) (hω1 : ω ≠ 1) :
    (seifertForm figureEightV ω).det ≠ 0 := by
  rw [figureEight_form_det hω]
  apply Complex.ofReal_ne_zero.mpr
  have hneg := figureEight_form_det_re_neg hω hω1
  rw [figureEight_form_det hω] at hneg
  simp only [Complex.ofReal_re] at hneg
  exact ne_of_lt hneg

/-- Direct computation of the figure-eight zero record, including the separate
zero-form point at `ω = 1`. -/
lemma figureEight_signature_zero {ω : ℂ} (hω : ω * star ω = 1) :
    spectralSignature (seifertForm figureEightV ω) = 0 := by
  by_cases hω1 : ω = 1
  · subst ω
    rw [seifertForm_at_one, spectralSignature_zero]
  · rw [spectralSignature_two (seifertForm_isHermitian figureEightV ω)
      (figureEight_form_nonsingular hω hω1),
      if_pos (figureEight_form_det_re_neg hω hω1)]

lemma figureEight_alexander_ne_zero {ω : ℂ} (hω : ω * star ω = 1) :
    alexanderDet figureEightV ω ≠ 0 := by
  by_cases hω1 : ω = 1
  · subst ω
    rw [figureEight_alexanderDet]
    norm_num
  · exact nonsingular_seifertForm_excludes_alexander_root figureEightV hω hω1
      (figureEight_form_nonsingular hω hω1)

lemma unitCircle_iff_mul_star {ω : ℂ} : ‖ω‖ = 1 ↔ ω * star ω = 1 := by
  constructor
  · intro h
    change ω * (starRingEnd ℂ) ω = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num
  · intro h
    have hc : (Complex.normSq ω : ℂ) = 1 := by
      rw [← Complex.mul_conj]
      exact h
    have hn : Complex.normSq ω = 1 := by exact_mod_cast hc
    have hn2 : ‖ω‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, hn]
    nlinarith [norm_nonneg ω]

lemma continuous_seifertForm {n : Type*} (V : Matrix n n ℝ) :
    Continuous (fun ω : ℂ => seifertForm V ω) := by
  unfold seifertForm
  fun_prop

/-- The unit circle, with the spurious form singularity at 1 removed and every
Alexander root removed. -/
abbrev RegularCircle (V : Matrix (Fin 2) (Fin 2) ℝ) :=
  {ω : ℂ // ω * star ω = 1 ∧ ω ≠ 1 ∧ alexanderDet V ω ≠ 0}

def regularFormOfRegularCircle (V : Matrix (Fin 2) (Fin 2) ℝ)
    (ω : RegularCircle V) : RegularHermitian2 :=
  ⟨seifertForm V ω.1, seifertForm_isHermitian V ω.1,
    fun hd => ω.2.2.2 ((seifertForm_singular_iff_alexander_zero V ω.2.1 ω.2.2.1).mp hd)⟩

lemma continuous_regularFormOfRegularCircle (V : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous (regularFormOfRegularCircle V) := by
  apply Continuous.subtype_mk
  exact (continuous_seifertForm V).comp continuous_subtype_val

/-- Rank-two version of `steps only where`: on the unit circle away from 1 and
the Alexander roots, the integer signature is locally constant. -/
lemma isLocallyConstant_signature_on_regularCircle (V : Matrix (Fin 2) (Fin 2) ℝ) :
    IsLocallyConstant (fun ω : RegularCircle V => spectralSignature (seifertForm V ω.1)) := by
  have h := isLocallyConstant_regularSignature.comp_continuous
    (continuous_regularFormOfRegularCircle V)
  simpa only [Function.comp_def, regularSignature, regularFormOfRegularCircle] using h

end
end RelationalAtlas.B157

#print axioms RelationalAtlas.B157.signZ_neg
#print axioms RelationalAtlas.B157.spectralSignature_eq_sum_eigenvalue_signs
#print axioms RelationalAtlas.B157.charpoly_neg
#print axioms RelationalAtlas.B157.roots_charpoly_neg
#print axioms RelationalAtlas.B157.spectralSignature_neg
#print axioms RelationalAtlas.B157.spectralSignature_transpose
#print axioms RelationalAtlas.B157.spectralSignature_neg_transpose
#print axioms RelationalAtlas.B157.spectralSignature_zero
#print axioms RelationalAtlas.B157.seifertForm_isHermitian
#print axioms RelationalAtlas.B157.seifertForm_mirror
#print axioms RelationalAtlas.B157.seifertForm_at_one
#print axioms RelationalAtlas.B157.seifertForm_eq_smul_alexanderMatrix
#print axioms RelationalAtlas.B157.seifertForm_det
#print axioms RelationalAtlas.B157.seifertForm_singular_iff_alexander_zero
#print axioms RelationalAtlas.B157.nonsingular_seifertForm_excludes_alexander_root
#print axioms RelationalAtlas.B157.mirror_signature_antisymmetric
#print axioms RelationalAtlas.B157.signature_zero_of_self_mirror
#print axioms RelationalAtlas.B157.signZ_pair
#print axioms RelationalAtlas.B157.isHermitian_ofReal_det_re
#print axioms RelationalAtlas.B157.hermitian_det_re
#print axioms RelationalAtlas.B157.hermitian_trace_re
#print axioms RelationalAtlas.B157.spectralSignature_two
#print axioms RelationalAtlas.B157.continuous_regular_det_re
#print axioms RelationalAtlas.B157.continuous_regular_trace_re
#print axioms RelationalAtlas.B157.trace_re_ne_zero_of_det_pos
#print axioms RelationalAtlas.B157.isLocallyConstant_regularSignature
#print axioms RelationalAtlas.B157.unitCircle_iff_mul_star
#print axioms RelationalAtlas.B157.continuous_seifertForm
#print axioms RelationalAtlas.B157.continuous_regularFormOfRegularCircle
#print axioms RelationalAtlas.B157.isLocallyConstant_signature_on_regularCircle
#print axioms RelationalAtlas.B157.figureEight_alexanderDet
#print axioms RelationalAtlas.B157.figureEight_form_trace
#print axioms RelationalAtlas.B157.circle_coordinates
#print axioms RelationalAtlas.B157.figureEight_form_det
#print axioms RelationalAtlas.B157.figureEight_form_det_re_neg
#print axioms RelationalAtlas.B157.figureEight_form_nonsingular
#print axioms RelationalAtlas.B157.figureEight_signature_zero
#print axioms RelationalAtlas.B157.figureEight_alexander_ne_zero
#print axioms RelationalAtlas.B157.signZ_zero
#print axioms RelationalAtlas.B157.chiralWitness_alexanderDet
#print axioms RelationalAtlas.B157.chiralWitness_form_at_neg_one
#print axioms RelationalAtlas.B157.chiralWitness_signature_at_neg_one
#print axioms RelationalAtlas.B157.chiralWitness_mirror_signature_at_neg_one


/-! ## B172 — the half coefficient, and the eigenline that returns negated

Integrated from `.ultramath/smwvwr2ce/m10/B172.lean`.
-/

/-!
# B172 — the half-residue and the two signs

This file isolates the finite complex calculation in B172.  The loop coordinate
is `z(θ) = exp(iθ)`, and the oriented frame is the branch along the path
`v(θ) = exp(iθ/2)`.  Thus `v² = z`, without choosing a global square root.
The coefficient `1/2` in the logarithmic exponent gives `v(2π) = -v(0)` and
`v(4π) = v(0)`.

For the total connection, the regular part is treated as a separate loop
exponent.  Its holonomy must be trivial to deduce the sign of the total
transport from the singular term alone; this hypothesis is explicit below.
-/

noncomputable section

namespace RelationalAtlas.B172

open Complex

/-- Exponential phase of a real angle. -/
def phase (x : ℝ) : ℂ := Complex.exp (x * Complex.I)

lemma phase_add_pi (x : ℝ) : phase (x + Real.pi) = -phase x := by
  unfold phase
  push_cast
  exact Complex.exp_mul_I_antiperiodic x

lemma phase_add_two_pi (x : ℝ) : phase (x + 2 * Real.pi) = phase x := by
  unfold phase
  push_cast
  exact Complex.exp_mul_I_periodic x

/-- A positively oriented complex coordinate loop around the wall. -/
def wallLoop (θ : ℝ) : ℂ := phase θ

/-- The oriented Gram-frame phase along the lifted angle. -/
def gramFrame (θ : ℝ) : ℂ := phase (θ / 2)

/-- The half-angle frame squares to the wall coordinate. -/
theorem gramFrame_sq (θ : ℝ) : gramFrame θ ^ 2 = wallLoop θ := by
  rw [gramFrame, wallLoop, phase, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- Along the real parametrisation, the wall coordinate has derivative `zi`. -/
theorem hasDerivAt_wallLoop (θ : ℝ) :
    HasDerivAt wallLoop (wallLoop θ * Complex.I) θ := by
  change HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
    (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ
  simpa using (((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp)

/-- The half-angle frame has derivative `v(i/2)`. -/
theorem hasDerivAt_gramFrame (θ : ℝ) :
    HasDerivAt gramFrame (gramFrame θ * (Complex.I / 2)) θ := by
  change HasDerivAt (fun x : ℝ => Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I))
    (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (Complex.I / 2)) θ
  convert ((((hasDerivAt_id θ).div_const (2 : ℝ)).ofReal_comp.mul_const
    Complex.I).cexp) using 1 <;>
    simp [id, mul_comm, mul_left_comm]
  ring

lemma deriv_wallLoop (θ : ℝ) : deriv wallLoop θ = wallLoop θ * Complex.I :=
  (hasDerivAt_wallLoop θ).deriv

lemma deriv_gramFrame (θ : ℝ) :
    deriv gramFrame θ = gramFrame θ * (Complex.I / 2) :=
  (hasDerivAt_gramFrame θ).deriv


/-- The frame's logarithmic derivative is the constant `i/2`. -/
lemma deriv_gramFrame_div_self (θ : ℝ) :
    deriv gramFrame θ / gramFrame θ = Complex.I / 2 := by
  rw [deriv_gramFrame]
  have hv : gramFrame θ ≠ 0 := by
    unfold gramFrame phase
    exact Complex.exp_ne_zero _
  field_simp [hv]

/-- One base loop has singular logarithmic exponent `πi`. -/
theorem singularExponent_single_loop :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv gramFrame θ / gramFrame θ) =
      (Real.pi : ℂ) * Complex.I := by
  simp_rw [deriv_gramFrame_div_self]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- The closed cover lift has singular logarithmic exponent `2πi`. -/
theorem singularExponent_cover_loop :
    (∫ θ in (0 : ℝ)..(4 * Real.pi), deriv gramFrame θ / gramFrame θ) =
      2 * (Real.pi : ℂ) * Complex.I := by
  simp_rw [deriv_gramFrame_div_self]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- The finite differential identity behind the displayed singular term:
`d log v = (1/2) d log z` along the lifted loop. -/
theorem logarithmic_derivative_half (θ : ℝ) :
    deriv gramFrame θ / gramFrame θ =
      (1 / 2 : ℂ) * (deriv wallLoop θ / wallLoop θ) := by
  rw [deriv_gramFrame, deriv_wallLoop]
  have hv : gramFrame θ ≠ 0 := by
    unfold gramFrame phase
    exact Complex.exp_ne_zero _
  have hz : wallLoop θ ≠ 0 := by
    unfold wallLoop phase
    exact Complex.exp_ne_zero _
  field_simp [hv, hz]

/-- One additional base loop reverses the oriented frame. -/
theorem gramFrame_add_two_pi (θ : ℝ) : gramFrame (θ + 2 * Real.pi) = -gramFrame θ := by
  unfold gramFrame
  rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring]
  exact phase_add_pi _

/-- Two additional base loops restore the oriented frame on the cover. -/
theorem gramFrame_add_four_pi (θ : ℝ) : gramFrame (θ + 4 * Real.pi) = gramFrame θ := by
  unfold gramFrame
  rw [show (θ + 4 * Real.pi) / 2 = θ / 2 + 2 * Real.pi by ring]
  exact phase_add_two_pi _

/-- The single-loop Gram holonomy is `-1`. -/
theorem gramFrame_single_loop : gramFrame (2 * Real.pi) = -1 := by
  change phase ((2 * Real.pi) / 2) = -1
  rw [show (2 * Real.pi) / 2 = Real.pi by ring]
  exact Complex.exp_pi_mul_I

/-- The closed cover lift has holonomy `+1`. -/
theorem gramFrame_cover_loop : gramFrame (4 * Real.pi) = 1 := by
  change phase ((4 * Real.pi) / 2) = 1
  rw [show (4 * Real.pi) / 2 = 2 * Real.pi by ring]
  unfold phase
  push_cast
  exact Complex.exp_two_pi_mul_I

/-- Transport with coefficient `c` and integer winding `n`.  The exponent is
`c * (2πi) * n`; hence `c` is also the flux per unit winding, in `2πi` units. -/
def transport (c : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (c * (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

/-- Singular transport for the displayed coefficient `1/2`. -/
def gramTransport (n : ℤ) : ℂ := transport (1 / 2 : ℂ) n

/-- The transport on the orientation-keeping cover is the square. -/
def coverTransport (n : ℤ) : ℂ := gramTransport n ^ 2

lemma gramTransport_eq_exp (n : ℤ) :
    gramTransport n = Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  unfold gramTransport transport
  congr 1
  ring

/-- The singular transport is `(-1)^winding`: a simple zero gives half a unit
of flux and the sign `-1`, while a nonencircling loop has winding zero. -/
theorem gramTransport_eq_zpow (n : ℤ) : gramTransport n = (-1 : ℂ) ^ n := by
  rw [gramTransport_eq_exp, Complex.exp_int_mul, Complex.exp_pi_mul_I]

@[simp] theorem gramTransport_nonencircling : gramTransport 0 = 1 := by
  simp [gramTransport_eq_zpow]

@[simp] theorem gramTransport_simple_zero : gramTransport 1 = -1 := by
  simp [gramTransport_eq_zpow]

lemma coverTransport_eq_exp (n : ℤ) :
    coverTransport n = Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
  rw [coverTransport, gramTransport_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The cover sign is `+1` for every integer winding. -/
@[simp] theorem coverTransport_eq_one (n : ℤ) : coverTransport n = 1 := by
  rw [coverTransport_eq_exp, Complex.exp_int_mul_two_pi_mul_I]

/-- Replacing the displayed coefficient by `1` destroys the Gram sign: its
single-loop transport is `+1`, not `-1`. -/
theorem coefficient_one_single_loop : transport 1 1 = 1 := by
  simp [transport]

theorem coefficient_one_not_gram : transport 1 1 ≠ gramTransport 1 := by
  rw [coefficient_one_single_loop, gramTransport_simple_zero]
  norm_num

/-- Loop transport obtained by exponentiating the sum of a regular loop
exponent `r` and the singular exponent. -/
def totalTransport (r c : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (r + c * (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

lemma totalTransport_eq (r c : ℂ) (n : ℤ) :
    totalTransport r c n = Complex.exp r * transport c n := by
  rw [totalTransport, transport, Complex.exp_add]

/-- With the displayed coefficient, the total single-loop transport is the
negative of the regular part's holonomy. -/
theorem totalTransport_simple_loop (r : ℂ) :
    totalTransport r (1 / 2 : ℂ) 1 = -Complex.exp r := by
  rw [totalTransport_eq]
  change Complex.exp r * gramTransport 1 = -Complex.exp r
  rw [gramTransport_simple_zero, mul_neg, mul_one]

/-- If the regular part has trivial holonomy, the total Gram sign is `-1`. -/
theorem totalTransport_simple_loop_of_regular_trivial {r : ℂ}
    (hr : Complex.exp r = 1) : totalTransport r (1 / 2 : ℂ) 1 = -1 := by
  rw [totalTransport_simple_loop, hr]


/-- Total transport on the orientation-keeping cover. -/
def totalCoverTransport (r c : ℂ) (n : ℤ) : ℂ := totalTransport r c n ^ 2

/-- With trivial regular holonomy, the total cover transport is `+1` for every
integer winding, complementing the `-1` single-loop Gram sign. -/
@[simp] theorem totalCoverTransport_eq_one_of_regular_trivial {r : ℂ}
    (hr : Complex.exp r = 1) (n : ℤ) : totalCoverTransport r (1 / 2 : ℂ) n = 1 := by
  rw [totalCoverTransport, totalTransport_eq, mul_pow, hr]
  change 1 ^ 2 * coverTransport n = 1
  simp

/-- The displayed decomposition alone does not let one discard the regular
holonomy: `r = πi` supplies an explicit second sign and makes the total `+1`. -/
theorem nontrivial_regular_can_cancel_sign :
    totalTransport ((Real.pi : ℂ) * Complex.I) (1 / 2 : ℂ) 1 = 1 := by
  rw [totalTransport_simple_loop, Complex.exp_pi_mul_I]
  norm_num

/-- A nonencircling loop with zero regular exponent returns `+1`. -/
theorem totalTransport_nonencircling : totalTransport 0 (1 / 2 : ℂ) 0 = 1 := by
  simp [totalTransport]


/-! ### The real eigenline: projective closure is not oriented closure -/

/-- A real oriented frame turning at half the base-loop angle. -/
def realEigenframe (θ : ℝ) : ℝ × ℝ :=
  (Real.cos (θ / 2), Real.sin (θ / 2))

lemma realEigenframe_ne_zero (θ : ℝ) : realEigenframe θ ≠ 0 := by
  intro h
  have hc : Real.cos (θ / 2) = 0 := by
    simpa [realEigenframe] using congrArg Prod.fst h
  have hs : Real.sin (θ / 2) = 0 := by
    simpa [realEigenframe] using congrArg Prod.snd h
  have hunit := Real.cos_sq_add_sin_sq (θ / 2)
  rw [hc, hs] at hunit
  norm_num at hunit

lemma realEigenframe_unit (θ : ℝ) :
    (realEigenframe θ).1 ^ 2 + (realEigenframe θ).2 ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq (θ / 2)

/-- The oriented real frame is antiperiodic under one base loop. -/
theorem realEigenframe_add_two_pi (θ : ℝ) :
    realEigenframe (θ + 2 * Real.pi) = -realEigenframe θ := by
  unfold realEigenframe
  rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring,
    Real.cos_add_pi, Real.sin_add_pi]
  rfl

/-- It is periodic under two base loops, i.e. on the orientation cover. -/
theorem realEigenframe_add_four_pi (θ : ℝ) :
    realEigenframe (θ + 4 * Real.pi) = realEigenframe θ := by
  unfold realEigenframe
  rw [show (θ + 4 * Real.pi) / 2 = θ / 2 + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem realEigenframe_single_loop :
    realEigenframe (2 * Real.pi) = -realEigenframe 0 := by
  simpa using realEigenframe_add_two_pi 0

theorem realEigenframe_cover_loop :
    realEigenframe (4 * Real.pi) = realEigenframe 0 := by
  simpa using realEigenframe_add_four_pi 0

/-- The unoriented real eigenline represented by the nonzero frame. -/
def realEigenline (θ : ℝ) : Projectivization ℝ (ℝ × ℝ) :=
  Projectivization.mk ℝ (realEigenframe θ) (realEigenframe_ne_zero θ)

/-- After a `2π` base loop the unoriented eigenline has returned, although its
oriented representative has changed sign. -/
theorem realEigenline_single_loop : realEigenline (2 * Real.pi) = realEigenline 0 := by
  unfold realEigenline
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨-1, ?_⟩
  rw [realEigenframe_single_loop]
  simp

/-- The real frame coefficient `1`, rather than `1/2`, is an explicit bad
alternative: its `2π` endpoint is `+1`, not `-1`. -/
def fullAngleFrame (θ : ℝ) : ℝ × ℝ := (Real.cos θ, Real.sin θ)

theorem fullAngleFrame_single_loop : fullAngleFrame (2 * Real.pi) = fullAngleFrame 0 := by
  simp [fullAngleFrame]

theorem fullAngleFrame_not_reversed :
    fullAngleFrame (2 * Real.pi) ≠ -fullAngleFrame 0 := by
  intro h
  have h1 : (1 : ℝ) = -1 := by
    simpa [fullAngleFrame] using congrArg Prod.fst h
  norm_num at h1

end RelationalAtlas.B172

#print axioms RelationalAtlas.B172.gramFrame_sq
#print axioms RelationalAtlas.B172.gramFrame_add_two_pi
#print axioms RelationalAtlas.B172.gramFrame_add_four_pi
#print axioms RelationalAtlas.B172.gramFrame_single_loop
#print axioms RelationalAtlas.B172.gramFrame_cover_loop
#print axioms RelationalAtlas.B172.gramTransport_eq_zpow
#print axioms RelationalAtlas.B172.gramTransport_nonencircling
#print axioms RelationalAtlas.B172.gramTransport_simple_zero
#print axioms RelationalAtlas.B172.coverTransport_eq_one
#print axioms RelationalAtlas.B172.coefficient_one_single_loop
#print axioms RelationalAtlas.B172.coefficient_one_not_gram
#print axioms RelationalAtlas.B172.totalTransport_simple_loop
#print axioms RelationalAtlas.B172.totalTransport_simple_loop_of_regular_trivial
#print axioms RelationalAtlas.B172.nontrivial_regular_can_cancel_sign
#print axioms RelationalAtlas.B172.totalTransport_nonencircling
#print axioms RelationalAtlas.B172.realEigenframe_ne_zero
#print axioms RelationalAtlas.B172.realEigenframe_unit
#print axioms RelationalAtlas.B172.realEigenframe_add_two_pi
#print axioms RelationalAtlas.B172.realEigenframe_add_four_pi
#print axioms RelationalAtlas.B172.realEigenframe_single_loop
#print axioms RelationalAtlas.B172.realEigenframe_cover_loop
#print axioms RelationalAtlas.B172.realEigenline_single_loop
#print axioms RelationalAtlas.B172.fullAngleFrame_single_loop
#print axioms RelationalAtlas.B172.fullAngleFrame_not_reversed
#print axioms RelationalAtlas.B172.hasDerivAt_wallLoop
#print axioms RelationalAtlas.B172.hasDerivAt_gramFrame
#print axioms RelationalAtlas.B172.logarithmic_derivative_half
#print axioms RelationalAtlas.B172.deriv_gramFrame_div_self
#print axioms RelationalAtlas.B172.singularExponent_single_loop
#print axioms RelationalAtlas.B172.singularExponent_cover_loop
#print axioms RelationalAtlas.B172.phase_add_pi
#print axioms RelationalAtlas.B172.phase_add_two_pi
#print axioms RelationalAtlas.B172.deriv_wallLoop
#print axioms RelationalAtlas.B172.deriv_gramFrame
#print axioms RelationalAtlas.B172.gramTransport_eq_exp
#print axioms RelationalAtlas.B172.coverTransport_eq_exp
#print axioms RelationalAtlas.B172.totalTransport_eq
#print axioms RelationalAtlas.B172.totalCoverTransport_eq_one_of_regular_trivial


/-! ## B176 — CHSH derived from the state, and the offset with a tan

Integrated from `.ultramath/smwvwr2ce/m2/B176.lean`.
-/

/-!
# B176: thermal reduced records, the Hawking offset, and parity-spin CHSH

The Fock amplitudes and the parity-pseudospin correlator are defined explicitly below.
The parity-flip expectation is a sum over the two off-diagonal terms in each
`(2k,2k+1)` block; it is not the quoted value of CHSH.  The CHSH expression is
then optimised over the planar family used for the displayed value.

The scalar dimensionless inverse-temperature variable is `x`.  Restoring units,
`x = ħω/(k_B T_H)`.  The bosonic angle uses `tanh rb = exp (-x/2)` and the
fermionic angle uses `tan rf = exp (-x/2)`; these are deliberately not conflated.
-/

open scoped BigOperators

namespace RelationalAtlas.B176

noncomputable section

/-- The hyperbolic normalisation identity used by the Fock amplitudes. -/
theorem one_sub_tanh_sq (r : ℝ) :
    1 - Real.tanh r ^ 2 = 1 / Real.cosh r ^ 2 := by
  have hc := (Real.cosh_pos r).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linarith [Real.cosh_sq_sub_sinh_sq r]

/-- The double-argument formula, with the same sign and denominator as the
parity-pseudospin calculation. -/
theorem tanh_two_mul (r : ℝ) :
    Real.tanh (2 * r) = 2 * Real.tanh r / (1 + Real.tanh r ^ 2) := by
  have hc := (Real.cosh_pos r).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul,
    Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- The displayed two-mode squeezed-state Fock amplitude. -/
def fockAmplitude (r : ℝ) (n : ℕ) : ℝ := Real.tanh r ^ n / Real.cosh r

/-- The diagonal reduced-Fock record. -/
def fockOccupation (r : ℝ) (n : ℕ) : ℝ := (fockAmplitude r n) ^ 2

/-- A phase on the amplitude of the `n`-th pair, retained before partial trace. -/
def phasedFockAmplitude (r φ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((n : ℝ) * φ : ℝ) * Complex.I) * (fockAmplitude r n : ℂ)

/-- The diagonal record after tracing out the partner. -/
def phasedFockOccupation (r φ : ℝ) (n : ℕ) : ℝ :=
  Complex.normSq (phasedFockAmplitude r φ n)

/-- Geometric form of the reduced occupation probabilities. -/
theorem fockOccupation_eq_geometric (r : ℝ) (n : ℕ) :
    fockOccupation r n =
      (1 - Real.tanh r ^ 2) * (Real.tanh r ^ 2) ^ n := by
  have hc := (Real.cosh_pos r).ne'
  simp only [fockOccupation, fockAmplitude, div_pow, one_sub_tanh_sq]
  rw [show (Real.tanh r ^ 2) ^ n = (Real.tanh r ^ n) ^ 2 by rw [← pow_mul]; ring_nf]
  field_simp

/-- The phase disappears from every reduced occupation probability. -/
theorem phasedFockOccupation_eq (r φ : ℝ) (n : ℕ) :
    phasedFockOccupation r φ n = fockOccupation r n := by
  have hphase : Complex.normSq (Complex.exp (((n : ℝ) * φ : ℝ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  simp only [phasedFockOccupation, phasedFockAmplitude, Complex.normSq_mul, hphase,
    one_mul, Complex.normSq_ofReal]
  exact (sq (fockAmplitude r n)).symm

/-- The phase-invariance statement is about the whole reduced record, not the
pure-state amplitudes. -/
theorem phasedFockOccupation_independent (r : ℝ) (φ ψ : ℝ) :
    (fun n => phasedFockOccupation r φ n) = (fun n => phasedFockOccupation r ψ n) := by
  funext n
  rw [phasedFockOccupation_eq, phasedFockOccupation_eq]

private theorem tanh_sq_mem (r : ℝ) :
    0 ≤ Real.tanh r ^ 2 ∧ Real.tanh r ^ 2 < 1 := by
  have h := (sq_lt_sq₀ (abs_nonneg (Real.tanh r)) (by norm_num : (0 : ℝ) ≤ 1)).2
    (Real.abs_tanh_lt_one r)
  exact ⟨sq_nonneg _, by simpa [sq_abs] using h⟩

/-- The displayed Fock state is normalised; equivalently its reduced record is
a probability distribution on `ℕ`. -/
theorem tsum_fockOccupation (r : ℝ) : ∑' n, fockOccupation r n = 1 := by
  obtain ⟨hq0, hq1⟩ := tanh_sq_mem r
  have hne : 1 - Real.tanh r ^ 2 ≠ 0 := sub_ne_zero.mpr hq1.ne'
  calc
    ∑' n, fockOccupation r n =
        ∑' n, (1 - Real.tanh r ^ 2) * (Real.tanh r ^ 2) ^ n := by
          apply tsum_congr
          intro n
          exact fockOccupation_eq_geometric r n
    _ = (1 - Real.tanh r ^ 2) * ∑' n : ℕ, (Real.tanh r ^ 2) ^ n := tsum_mul_left
    _ = (1 - Real.tanh r ^ 2) * (1 - Real.tanh r ^ 2)⁻¹ := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = 1 := mul_inv_cancel₀ hne

/-- The two off-diagonal parity-flip contributions from the `(2k,2k+1)` block
of the two-mode state.  This is the state-dependent quantity in the `x-x`
correlator. -/
def parityXX (r : ℝ) : ℝ :=
  ∑' k : ℕ, 2 * fockAmplitude r (2 * k) * fockAmplitude r (2 * k + 1)

private theorem paired_power (q : ℝ) (k : ℕ) :
    q ^ (2 * k) * q ^ (2 * k + 1) = q * (q ^ 4) ^ k := by
  calc
    q ^ (2 * k) * q ^ (2 * k + 1) = (q ^ (2 * k) * q ^ (2 * k)) * q := by
      rw [pow_succ]
      ring
    _ = q ^ (2 * k + 2 * k) * q := by rw [pow_add]
    _ = q * (q ^ 4) ^ k := by
      rw [show 2 * k + 2 * k = 4 * k by ring, pow_mul]
      ring

private theorem parityXX_summand (r : ℝ) (k : ℕ) :
    2 * fockAmplitude r (2 * k) * fockAmplitude r (2 * k + 1) =
      (2 * Real.tanh r / Real.cosh r ^ 2) * (Real.tanh r ^ 4) ^ k := by
  have hc := (Real.cosh_pos r).ne'
  simp only [fockAmplitude]
  field_simp
  rw [paired_power]

/-- **The state calculation.**  The off-diagonal parity-spin expectation is
`tanh (2r)`, obtained by summing the paired Fock amplitudes. -/
theorem parityXX_eq_tanh_two_mul (r : ℝ) : parityXX r = Real.tanh (2 * r) := by
  obtain ⟨hq0, hq1⟩ := tanh_sq_mem r
  have hq4 : Real.tanh r ^ 4 < 1 := by
    have h := (sq_lt_sq₀ (sq_nonneg (Real.tanh r)) (by norm_num : (0 : ℝ) ≤ 1)).2 hq1
    nlinarith [sq_nonneg (Real.tanh r)]
  have hq40 : 0 ≤ Real.tanh r ^ 4 := by positivity
  have hq2ne : 1 - Real.tanh r ^ 2 ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hc := (Real.cosh_pos r).ne'
  rw [tanh_two_mul]
  calc
    parityXX r = ∑' k : ℕ, (2 * Real.tanh r / Real.cosh r ^ 2) *
        (Real.tanh r ^ 4) ^ k := by
      apply tsum_congr
      intro k
      exact parityXX_summand r k
    _ = (2 * Real.tanh r / Real.cosh r ^ 2) * ∑' k : ℕ, (Real.tanh r ^ 4) ^ k :=
      tsum_mul_left
    _ = (2 * Real.tanh r / Real.cosh r ^ 2) * (1 - Real.tanh r ^ 4)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq40 hq4]
    _ = 2 * Real.tanh r / (1 + Real.tanh r ^ 2) := by
      have hcprod : Real.cosh r ^ 2 * (1 - Real.tanh r ^ 2) = 1 := by
        rw [one_sub_tanh_sq]
        field_simp
      have hmain : Real.cosh r ^ 2 * (1 - Real.tanh r ^ 4) =
          1 + Real.tanh r ^ 2 := by
        calc
          Real.cosh r ^ 2 * (1 - Real.tanh r ^ 4) =
              (Real.cosh r ^ 2 * (1 - Real.tanh r ^ 2)) *
                (1 + Real.tanh r ^ 2) := by ring
          _ = 1 + Real.tanh r ^ 2 := by rw [hcprod, one_mul]
      field_simp
      calc
        Real.tanh r * (1 + Real.tanh r ^ 2) =
            Real.tanh r * (Real.cosh r ^ 2 * (1 - Real.tanh r ^ 4)) := by rw [hmain]
        _ = Real.tanh r * Real.cosh r ^ 2 * (1 - Real.tanh r ^ 4) := by ring


/-- A general planar correlation matrix with singular values `1` and `|K|`. -/
def planarCorrelator (K a b : ℝ) : ℝ :=
  Real.cos a * Real.cos b + K * Real.sin a * Real.sin b

/-- The state correlator.  The `z-z` term is the sum of the reduced diagonal
record (the two parity signs cancel), and the `x-x` term is `parityXX`.
Mixed terms vanish by Fock orthogonality and are absent from the definition. -/
def fockCorrelator (r a b : ℝ) : ℝ :=
  Real.cos a * Real.cos b * (∑' n, fockOccupation r n) +
    parityXX r * Real.sin a * Real.sin b

theorem fockCorrelator_eq (r a b : ℝ) :
    fockCorrelator r a b = planarCorrelator (Real.tanh (2 * r)) a b := by
  simp only [fockCorrelator, planarCorrelator, tsum_fockOccupation,
    parityXX_eq_tanh_two_mul, mul_one]

/-- The CHSH combination `E(a,b)+E(a,b')+E(a',b)-E(a',b')`. -/
def CHSH (E : ℝ → ℝ → ℝ) (a a' b b' : ℝ) : ℝ :=
  E a b + E a b' + E a' b - E a' b'

/-- Chen--Pan--Hou--Zhang's planar settings: `a=0`, `a'=π/2`, `b'=-b`.
The remaining angle is left free and is optimised below. -/
def planarCHSHFamily (K b : ℝ) : ℝ :=
  CHSH (planarCorrelator K) 0 (Real.pi / 2) b (-b)

/-- The same family, evaluated directly on the squeezed-state correlator. -/
def fockCHSHFamily (r b : ℝ) : ℝ :=
  CHSH (fockCorrelator r) 0 (Real.pi / 2) b (-b)

theorem planarCHSHFamily_eq (K b : ℝ) :
    planarCHSHFamily K b = 2 * (Real.cos b + K * Real.sin b) := by
  simp only [planarCHSHFamily, CHSH, planarCorrelator, Real.cos_zero,
    Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg,
    Real.sin_neg]
  ring

theorem fockCHSHFamily_eq (r b : ℝ) :
    fockCHSHFamily r b = 2 * (Real.cos b + Real.tanh (2 * r) * Real.sin b) := by
  simp only [fockCHSHFamily, CHSH, fockCorrelator_eq]
  exact planarCHSHFamily_eq (Real.tanh (2 * r)) b

private theorem linear_trig_sq_le (K b : ℝ) :
    (Real.cos b + K * Real.sin b) ^ 2 ≤ 1 + K ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq b, sq_nonneg (K * Real.cos b - Real.sin b)]

/-- The exact maximum over the planar CHSH family, including a maximising
angle.  This proves both the upper bound and attainment. -/
theorem planarCHSHFamily_isGreatest (K : ℝ) :
    IsGreatest (Set.range (planarCHSHFamily K)) (2 * Real.sqrt (1 + K ^ 2)) := by
  let S := Real.sqrt (1 + K ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hSsq : S ^ 2 = 1 + K ^ 2 := Real.sq_sqrt (by positivity)
  constructor
  · refine ⟨Real.arctan K, ?_⟩
    rw [planarCHSHFamily_eq, Real.cos_arctan, Real.sin_arctan]
    change 2 * (1 / S + K * (K / S)) = 2 * S
    field_simp
    nlinarith
  · rintro x ⟨b, rfl⟩
    rw [planarCHSHFamily_eq]
    have hsq : (2 * (Real.cos b + K * Real.sin b)) ^ 2 ≤ (2 * S) ^ 2 := by
      have h := linear_trig_sq_le K b
      nlinarith
    have habs := abs_le_of_sq_le_sq hsq (by positivity : 0 ≤ 2 * S)
    exact (le_abs_self _).trans habs

/-- **B176 CHSH display, computed from the state.** -/
theorem fockCHSHFamily_isGreatest (r : ℝ) :
    IsGreatest (Set.range (fockCHSHFamily r))
      (2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2)) := by
  have hf : fockCHSHFamily r = planarCHSHFamily (Real.tanh (2 * r)) := by
    funext b
    rw [fockCHSHFamily_eq, planarCHSHFamily_eq]
  rw [hf]
  exact planarCHSHFamily_isGreatest (Real.tanh (2 * r))

/-- Positive squeezing gives a strict violation of the classical CHSH bound. -/
theorem two_lt_fockCHSH_max {r : ℝ} (hr : 0 < Real.tanh r) :
    2 < 2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2) := by
  rw [tanh_two_mul]
  have hden : 0 < 1 + Real.tanh r ^ 2 := by positivity
  have ht : 0 < 2 * Real.tanh r / (1 + Real.tanh r ^ 2) := div_pos (by positivity) hden
  have hsqrt : Real.sqrt 1 < Real.sqrt (1 + (2 * Real.tanh r / (1 + Real.tanh r ^ 2)) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [sq_nonneg (2 * Real.tanh r / (1 + Real.tanh r ^ 2))])
  rw [Real.sqrt_one] at hsqrt
  linarith

/-- At zero squeezing the optimum is exactly `2`; strict violation therefore
needs the positive-frequency/nonzero-squeezing hypothesis. -/
theorem fockCHSH_max_zero :
    (2 : ℝ) * Real.sqrt (1 + Real.tanh (2 * 0) ^ 2) = 2 := by
  norm_num

/-- The same strict violation stated directly for positive `r`. -/
theorem two_lt_fockCHSH_max_of_pos {r : ℝ} (hr : 0 < r) :
    2 < 2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2) := by
  apply two_lt_fockCHSH_max
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos r)


/-- The Dirac pair in the basis `(|00⟩, |11⟩)`, including its pair phase. -/
def diracPair (r φ : ℝ) : ℂ × ℂ :=
  ((Real.cos r : ℂ), Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin r : ℂ))

/-- The two diagonal entries of the outside record, empty first and full second. -/
def diracOutsideRecord (ψ : ℂ × ℂ) : ℝ × ℝ :=
  (Complex.normSq ψ.1, Complex.normSq ψ.2)

/-- The card's outside occupation `C = sin²r`. -/
def diracOccupation (r : ℝ) : ℝ := Real.sin r ^ 2

/-- Empty-against-full log-odds. -/
def emptyLogOdds (C : ℝ) : ℝ := Real.log ((1 - C) / C)

/-- Partial tracing removes the Dirac phase exactly. -/
theorem diracOutsideRecord_pair (r φ : ℝ) :
    diracOutsideRecord (diracPair r φ) = (1 - diracOccupation r, diracOccupation r) := by
  have hphase : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
    rw [show (φ : ℂ) = ((φ : ℝ) : ℂ) by rfl, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hsin : Real.sin r ^ 2 + Real.cos r ^ 2 = 1 := Real.sin_sq_add_cos_sq r
  apply Prod.ext
  · simp only [diracOutsideRecord, diracPair, Complex.normSq_ofReal]
    change Real.cos r * Real.cos r = 1 - Real.sin r ^ 2
    nlinarith
  · simp only [diracOutsideRecord, diracPair, Complex.normSq_mul, hphase, one_mul,
      Complex.normSq_ofReal]
    change Real.sin r * Real.sin r = Real.sin r ^ 2
    ring

theorem diracOutsideRecord_phase_independent (r φ ψ : ℝ) :
    diracOutsideRecord (diracPair r φ) = diracOutsideRecord (diracPair r ψ) := by
  rw [diracOutsideRecord_pair, diracOutsideRecord_pair]

/-- The Dirac reduced record is normalised. -/
theorem diracOutsideRecord_normalized (r φ : ℝ) :
    (diracOutsideRecord (diracPair r φ)).1 + (diracOutsideRecord (diracPair r φ)).2 = 1 := by
  rw [diracOutsideRecord_pair]
  exact sub_add_cancel _ _

/-- In the open Dirac window both occupation probabilities are nonzero. -/
theorem diracOccupation_mem_Ioo {r : ℝ} (hr0 : 0 < r) (hr : r < Real.pi / 2) :
    diracOccupation r ∈ Set.Ioo 0 1 := by
  have hrpi : r < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrpi
  have hc : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, hr⟩
  have htrig := Real.sin_sq_add_cos_sq r
  exact ⟨sq_pos_of_pos hs, by dsimp [diracOccupation]; nlinarith [sq_pos_of_pos hc]⟩

/-- The geometric thermal occupation of one fermion mode at dimensionless
`x = ħω/(k_B T_H)`. -/
def thermalFermionOccupation (x : ℝ) : ℝ := Real.exp (-x) / (1 + Real.exp (-x))

theorem thermalFermionOccupation_mem_Ioo (x : ℝ) :
    thermalFermionOccupation x ∈ Set.Ioo 0 1 := by
  have hq : 0 < Real.exp (-x) := Real.exp_pos _
  constructor
  · exact div_pos hq (by positivity)
  · exact (div_lt_one (by positivity)).2 (by linarith)

/-- The fermionic offset is independent of how the occupation was generated. -/
theorem emptyLogOdds_thermalFermionOccupation (x : ℝ) :
    emptyLogOdds (thermalFermionOccupation x) = x := by
  have hq : 0 < Real.exp (-x) := Real.exp_pos _
  have hratio :
      (1 - thermalFermionOccupation x) / thermalFermionOccupation x = Real.exp x := by
    simp only [thermalFermionOccupation]
    calc
      (1 - Real.exp (-x) / (1 + Real.exp (-x))) /
          (Real.exp (-x) / (1 + Real.exp (-x))) = (Real.exp (-x))⁻¹ := by
        field_simp
        ring
      _ = Real.exp x := by rw [Real.exp_neg, inv_inv]
  simp only [emptyLogOdds, hratio, Real.log_exp]

private theorem exp_neg_half_sq (x : ℝ) :
    Real.exp (-x / 2) ^ 2 = Real.exp (-x) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- `tan rf = exp(-x/2)` gives exactly the thermal Dirac occupation. -/
theorem diracOccupation_eq_thermal {r x : ℝ} (hr0 : 0 < r) (hr : r < Real.pi / 2)
    (htan : Real.tan r = Real.exp (-x / 2)) :
    diracOccupation r = thermalFermionOccupation x := by
  have hrpi : r < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrpi
  have hc : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, hr⟩
  have htrig := Real.sin_sq_add_cos_sq r
  have hcos_sq : Real.cos r ^ 2 = 1 - Real.sin r ^ 2 := by nlinarith
  have htan_sq : Real.sin r ^ 2 / (1 - Real.sin r ^ 2) = Real.exp (-x) := by
    rw [← hcos_sq, ← div_pow, ← Real.tan_eq_sin_div_cos, htan, exp_neg_half_sq]
  have hden : 1 - Real.sin r ^ 2 ≠ 0 := by
    rw [← hcos_sq]
    exact (sq_pos_of_pos hc).ne'
  have hsol := (div_eq_iff hden).mp htan_sq
  have hsum : (1 + Real.exp (-x)) ≠ 0 := by positivity
  dsimp [diracOccupation, thermalFermionOccupation]
  apply (eq_div_iff hsum).2
  nlinarith

/-- **B176 fermionic offset, separately from the bosonic CHSH calculation.** -/
theorem dirac_offset_of_thermal_angle {r x : ℝ} (hr0 : 0 < r) (hr : r < Real.pi / 2)
    (htan : Real.tan r = Real.exp (-x / 2)) :
    emptyLogOdds (diracOccupation r) = x := by
  rw [diracOccupation_eq_thermal hr0 hr htan, emptyLogOdds_thermalFermionOccupation]

/-- Restoring the constants in the card's display. -/
theorem dirac_offset_with_units {r ħ ω kB T : ℝ} (hr0 : 0 < r) (hr : r < Real.pi / 2)
    (htan : Real.tan r = Real.exp (-(ħ * ω / (kB * T)) / 2)) :
    emptyLogOdds (diracOccupation r) = ħ * ω / (kB * T) :=
  dirac_offset_of_thermal_angle hr0 hr htan

/-- The bosonic reduced probabilities are the geometric thermal law, not the
fermionic empty/full law. -/
theorem fockOccupation_thermal {r x : ℝ} (hr : Real.tanh r = Real.exp (-x / 2)) (n : ℕ) :
    fockOccupation r n = (1 - Real.exp (-x)) * (Real.exp (-x)) ^ n := by
  rw [fockOccupation_eq_geometric, hr, exp_neg_half_sq]

/-- A finite real squeezing parameter satisfying the thermal relation forces
`x > 0`; this rules out silently extending the strict CHSH claim to `x = 0`. -/
theorem positive_of_tanh_eq_exp_neg_half {r x : ℝ}
    (hr : Real.tanh r = Real.exp (-x / 2)) : 0 < x := by
  have hq : Real.exp (-x / 2) < 1 := by rw [← hr]; exact Real.tanh_lt_one r
  have h := Real.exp_lt_one_iff.mp hq
  linarith

/-- Positive squeezing follows directly from the positive exponential in the
thermal relation. -/
theorem tanh_pos_of_thermal {r x : ℝ} (hr : Real.tanh r = Real.exp (-x / 2)) :
    0 < Real.tanh r := by rw [hr]; exact Real.exp_pos _

/-- Strict CHSH violation for every finite Hawking pair satisfying the displayed
thermal relation. -/
theorem two_lt_fockCHSH_max_of_thermal {r x : ℝ}
    (hr : Real.tanh r = Real.exp (-x / 2)) :
    2 < 2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2) :=
  two_lt_fockCHSH_max (tanh_pos_of_thermal hr)

/-- Unit-restored form of strict CHSH violation. -/
theorem two_lt_fockCHSH_max_with_units {r ħ ω kB T : ℝ}
    (hr : Real.tanh r = Real.exp (-(ħ * ω / (kB * T)) / 2)) :
    2 < 2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2) :=
  two_lt_fockCHSH_max_of_thermal hr


/-- All values obtainable from arbitrary planar Alice/Bob settings. -/
def planarCHSHValues (K : ℝ) : Set ℝ :=
  {v | ∃ a a' b b' : ℝ, v = CHSH (planarCorrelator K) a a' b b'}

private theorem CHSH_sum_difference (K a a' b b' : ℝ) :
    CHSH (planarCorrelator K) a a' b b' =
      2 * ((Real.cos a * Real.cos ((b + b') / 2) +
          K * Real.sin a * Real.sin ((b + b') / 2)) * Real.cos ((b - b') / 2) +
        (-Real.cos a' * Real.sin ((b + b') / 2) +
          K * Real.sin a' * Real.cos ((b + b') / 2)) * Real.sin ((b - b') / 2)) := by
  let x := (b + b') / 2
  let d := (b - b') / 2
  have hb : b = x + d := by dsimp [x, d]; ring
  have hb' : b' = x - d := by dsimp [x, d]; ring
  change CHSH (planarCorrelator K) a a' b b' =
    2 * ((Real.cos a * Real.cos x + K * Real.sin a * Real.sin x) * Real.cos d +
      (-Real.cos a' * Real.sin x + K * Real.sin a' * Real.cos x) * Real.sin d)
  simp only [CHSH, planarCorrelator]
  rw [hb, hb']
  simp only [Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub]
  ring

private theorem correlator_left_sq_le (K a x : ℝ) :
    (Real.cos a * Real.cos x + K * Real.sin a * Real.sin x) ^ 2 ≤
      Real.cos x ^ 2 + K ^ 2 * Real.sin x ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq x,
    sq_nonneg (Real.sin a * Real.cos x - Real.cos a * (K * Real.sin x))]

private theorem correlator_right_sq_le (K a x : ℝ) :
    (-Real.cos a * Real.sin x + K * Real.sin a * Real.cos x) ^ 2 ≤
      Real.sin x ^ 2 + K ^ 2 * Real.cos x ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq x,
    sq_nonneg (Real.sin a * Real.sin x + Real.cos a * (K * Real.cos x))]

private theorem correlator_pair_sq_le (K a a' x : ℝ) :
    (Real.cos a * Real.cos x + K * Real.sin a * Real.sin x) ^ 2 +
      (-Real.cos a' * Real.sin x + K * Real.sin a' * Real.cos x) ^ 2 ≤ 1 + K ^ 2 := by
  have h1 := correlator_left_sq_le K a x
  have h2 := correlator_right_sq_le K a' x
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- The full planar upper bound is the same value attained by the special
one-angle family above. -/
theorem planarCHSH_isGreatest (K : ℝ) :
    IsGreatest (planarCHSHValues K) (2 * Real.sqrt (1 + K ^ 2)) := by
  let S := Real.sqrt (1 + K ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 1 + K ^ 2 := Real.sq_sqrt (by positivity)
  constructor
  · refine ⟨0, Real.pi / 2, Real.arctan K, -Real.arctan K, ?_⟩
    have heq : (2 : ℝ) * (Real.cos (Real.arctan K) + K * Real.sin (Real.arctan K)) =
        2 * S := by
      have hSpos : 0 < S := by dsimp [S]; positivity
      rw [Real.cos_arctan, Real.sin_arctan]
      change 2 * (1 / S + K * (K / S)) = 2 * S
      field_simp
      nlinarith
    change 2 * S = CHSH (planarCorrelator K) 0 (Real.pi / 2)
      (Real.arctan K) (-Real.arctan K)
    rw [← heq]
    exact (planarCHSHFamily_eq K (Real.arctan K)).symm
  · rintro v ⟨a, a', b, b', rfl⟩
    let x := (b + b') / 2
    let d := (b - b') / 2
    let A := Real.cos a * Real.cos x + K * Real.sin a * Real.sin x
    let B := -Real.cos a' * Real.sin x + K * Real.sin a' * Real.cos x
    have heq : CHSH (planarCorrelator K) a a' b b' =
        2 * (A * Real.cos d + B * Real.sin d) := CHSH_sum_difference K a a' b b'
    rw [heq]
    have hdot : (A * Real.cos d + B * Real.sin d) ^ 2 ≤ A ^ 2 + B ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq d,
        sq_nonneg (A * Real.sin d - B * Real.cos d)]
    have hpair : A ^ 2 + B ^ 2 ≤ 1 + K ^ 2 := correlator_pair_sq_le K a a' x
    have hsq : (2 * (A * Real.cos d + B * Real.sin d)) ^ 2 ≤ (2 * S) ^ 2 := by
      nlinarith
    have habs := abs_le_of_sq_le_sq hsq (by positivity : 0 ≤ 2 * S)
    exact (le_abs_self _).trans habs

/-- All planar values obtained directly from the squeezed-state correlator. -/
def fockCHSHValues (r : ℝ) : Set ℝ :=
  {v | ∃ a a' b b' : ℝ, v = CHSH (fockCorrelator r) a a' b b'}

/-- **B176 CHSH maximum over all planar settings**, computed from the Fock
state and its parity-flip sum. -/
theorem fockCHSH_isGreatest (r : ℝ) :
    IsGreatest (fockCHSHValues r)
      (2 * Real.sqrt (1 + Real.tanh (2 * r) ^ 2)) := by
  have h := planarCHSH_isGreatest (Real.tanh (2 * r))
  have hf : fockCorrelator r = planarCorrelator (Real.tanh (2 * r)) := by
    funext a b
    exact fockCorrelator_eq r a b
  have hset : fockCHSHValues r = planarCHSHValues (Real.tanh (2 * r)) := by
    simp only [fockCHSHValues, planarCHSHValues, hf]
  rw [hset]
  exact h

-- Axiom audit for every theorem in this module.
#print axioms CHSH_sum_difference
#print axioms correlator_left_sq_le
#print axioms correlator_right_sq_le
#print axioms correlator_pair_sq_le
#print axioms planarCHSH_isGreatest
#print axioms fockCHSH_isGreatest
#print axioms one_sub_tanh_sq
#print axioms tanh_two_mul
#print axioms fockOccupation_eq_geometric
#print axioms phasedFockOccupation_eq
#print axioms phasedFockOccupation_independent
#print axioms tanh_sq_mem
#print axioms tsum_fockOccupation
#print axioms paired_power
#print axioms parityXX_summand
#print axioms parityXX_eq_tanh_two_mul
#print axioms fockCorrelator_eq
#print axioms planarCHSHFamily_eq
#print axioms fockCHSHFamily_eq
#print axioms linear_trig_sq_le
#print axioms planarCHSHFamily_isGreatest
#print axioms fockCHSHFamily_isGreatest
#print axioms two_lt_fockCHSH_max
#print axioms fockCHSH_max_zero
#print axioms two_lt_fockCHSH_max_of_pos
#print axioms diracOutsideRecord_pair
#print axioms diracOutsideRecord_phase_independent
#print axioms diracOutsideRecord_normalized
#print axioms diracOccupation_mem_Ioo
#print axioms thermalFermionOccupation_mem_Ioo
#print axioms emptyLogOdds_thermalFermionOccupation
#print axioms exp_neg_half_sq
#print axioms diracOccupation_eq_thermal
#print axioms dirac_offset_of_thermal_angle
#print axioms dirac_offset_with_units
#print axioms fockOccupation_thermal
#print axioms positive_of_tanh_eq_exp_neg_half
#print axioms tanh_pos_of_thermal
#print axioms two_lt_fockCHSH_max_of_thermal
#print axioms two_lt_fockCHSH_max_with_units

end
end RelationalAtlas.B176

