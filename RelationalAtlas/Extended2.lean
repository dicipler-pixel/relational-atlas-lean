/-
Second batch of finite kernels for the Operator-First Relational Atlas.

Each section is a self-contained contribution accepted from the second formalisation
run of 23 November 2026 and integrated here with its own `#print axioms` block. Nothing
in `Basic.lean`, `AtlasFormalCore.lean` or `Extended.lean` is modified.
-/
import Mathlib

noncomputable section


/-! ## B128 — the defect and guard budget  δ + g² ≤ 4

Integrated from `.ultramath/smwtkiqjq/m14/B128.lean`.
-/
/-
B128 — the defect and the branch guard share one budget.

This is the finite spectral-algebra kernel. The input is an explicitly given
nonempty finite family of unit complex numbers, playing the role of the
eigenvalues of `U * V * Uᴴ * Vᴴ`. No determinant, winding, principal-argument,
or unitary-diagonalization assertion is made here.
-/

noncomputable section

open scoped BigOperators

namespace AtlasB128

/-- The mean squared distance of a finite spectral family from `1`. -/
def defect {ι : Type*} (s : Finset ι) (z : ι → ℂ) : ℝ :=
  (∑ j ∈ s, ‖z j - 1‖ ^ 2) / s.card

/-- The squared branch guard: the actual minimum, on `s`, of the squared
 distances from the eigenvalues to `-1`. -/
def guardSq {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ) : ℝ :=
  s.inf' hs (fun j => ‖z j + 1‖ ^ 2)

/-- On the unit circle, the two one-point readouts have total budget four. -/
theorem unit_defect_add_guard (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 + ‖z + 1‖ ^ 2 = 4 := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    have hn := Complex.sq_norm z
    rw [hz, Complex.normSq_apply, one_pow] at hn
    linarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im]
  linear_combination 2 * h

#print axioms unit_defect_add_guard

/-- The squared guard really is a lower bound for every squared distance to
`-1`; this is one half of the finite-minimum universal property. -/
theorem guardSq_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (z : ι → ℂ)
    {j : ι} (hj : j ∈ s) : guardSq s hs z ≤ ‖z j + 1‖ ^ 2 := by
  exact Finset.inf'_le _ hj

#print axioms guardSq_le

/-- Every common lower bound for the squared distances is below `guardSq`.
Together with `guardSq_le`, this identifies `guardSq` as the minimum. -/
theorem le_guardSq {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (z : ι → ℂ)
    (g : ℝ) (hg : ∀ j ∈ s, g ≤ ‖z j + 1‖ ^ 2) : g ≤ guardSq s hs z := by
  exact Finset.le_inf' hs _ hg

#print axioms le_guardSq

/-- Exact mean budget identity, before replacing the mean guard by its
minimum. -/
theorem defect_add_mean_guard {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (z : ι → ℂ) (hz : ∀ j ∈ s, ‖z j‖ = 1) :
    defect s z + (∑ j ∈ s, ‖z j + 1‖ ^ 2) / s.card = 4 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : (∑ j ∈ s, ‖z j - 1‖ ^ 2) + (∑ j ∈ s, ‖z j + 1‖ ^ 2) =
      4 * s.card := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun j hj => unit_defect_add_guard (z j) (hz j hj)),
      Finset.sum_const, nsmul_eq_mul]
    ring
  unfold defect
  rw [← add_div, div_eq_iff hc.ne']
  linarith

#print axioms defect_add_mean_guard

/-- **B128 budget.** The mean defect plus the actual minimum squared branch
 guard is at most four. -/
theorem defect_add_guardSq_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (z : ι → ℂ) (hz : ∀ j ∈ s, ‖z j‖ = 1) :
    defect s z + guardSq s hs z ≤ 4 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : (∑ j ∈ s, ‖z j - 1‖ ^ 2) + (∑ j ∈ s, ‖z j + 1‖ ^ 2) =
      4 * s.card := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun j hj => unit_defect_add_guard (z j) (hz j hj)),
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : (s.card : ℝ) * guardSq s hs z ≤ ∑ j ∈ s, ‖z j + 1‖ ^ 2 := by
    have h := Finset.sum_le_sum (fun j hj => guardSq_le hs z hj)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  unfold defect
  rw [div_add' _ _ _ hc.ne', div_le_iff₀ hc]
  linarith

#print axioms defect_add_guardSq_le

/-- The one-point spectrum at the imaginary unit, a nondegenerate concrete
instance for which both squared distances equal two. -/
def quarterTurnSpectrum : Fin 1 → ℂ := fun _ => Complex.I

/-- The concrete family lies on the unit circle. -/
theorem quarterTurnSpectrum_unit (j : Fin 1) : ‖quarterTurnSpectrum j‖ = 1 := by
  simp [quarterTurnSpectrum]

#print axioms quarterTurnSpectrum_unit

/-- Concrete defect calculation: `δ = 2`. -/
theorem quarterTurn_defect : defect Finset.univ quarterTurnSpectrum = 2 := by
  simp [defect, quarterTurnSpectrum, Complex.sq_norm, Complex.normSq_apply]
  norm_num

#print axioms quarterTurn_defect

/-- Concrete minimum-guard calculation: `g² = 2`. -/
theorem quarterTurn_guardSq :
    guardSq Finset.univ Finset.univ_nonempty quarterTurnSpectrum = 2 := by
  simp [guardSq, quarterTurnSpectrum, Complex.sq_norm, Complex.normSq_apply]
  norm_num

#print axioms quarterTurn_guardSq

/-- The concrete instance is sharp: it lies on the boundary `δ + g² = 4`. -/
theorem quarterTurn_budget :
    defect Finset.univ quarterTurnSpectrum +
      guardSq Finset.univ Finset.univ_nonempty quarterTurnSpectrum = 4 := by
  rw [quarterTurn_defect, quarterTurn_guardSq]
  norm_num

#print axioms quarterTurn_budget

end AtlasB128

/-! ## B86 — the diagonal witness of the reciprocity identity

Integrated from `.ultramath/smwtkiqjq/m1/B86.lean`.
-/
/-
B86 — the diagonal reciprocity pairing and its divisor.

Finite algebraic kernel of the card's data `B = diag(t/g)`.  We prove
symmetry, the exact determinant formula, the determinant zero criterion, and
the equivalence with a named Gram divisor under the explicitly displayed
hypothesis `G.det = ∏ i, t i`.  The card does not specify that relation, so we
do not silently assume it.  We also distinguish singularity from divergence:
a positive fixed numerator divided by a positive denominator can exceed every
positive bound as the denominator is chosen small.

The operator norm formula, the physical meaning of reciprocity, Jordan blocks,
and the relation of an arbitrary atlas Gram matrix `G` to `t` are outside this
finite kernel.  No claim about `t/g` is made at a zero denominator.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace AtlasFormal.B86

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The bilinear pairing displayed by B86. -/
def pairing (t g : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => t i / g i)

/-- The numerator polynomial defining the determinant divisor. -/
def divisor (t : n → ℝ) : ℝ := ∏ i, t i

/-- The diagonal pairing is symmetric, including when some entries are zero. -/
theorem pairing_transpose (t g : n → ℝ) :
    (pairing t g)ᵀ = pairing t g := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [pairing]
  · simp [pairing, Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ (Ne.symm h)]

#print axioms pairing_transpose

/-- Exact determinant of the card's diagonal pairing. -/
theorem det_pairing (t g : n → ℝ) :
    (pairing t g).det = divisor t / ∏ i, g i := by
  simp [pairing, divisor, Matrix.det_diagonal, Finset.prod_div_distrib]

#print axioms det_pairing

/-- Away from zero denominators, the pairing degenerates exactly on the
numerator divisor. -/
theorem det_pairing_zero_iff (t g : n → ℝ) (hg : ∀ i, g i ≠ 0) :
    (pairing t g).det = 0 ↔ divisor t = 0 := by
  have hprod : (∏ i, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hg i)
  rw [det_pairing, div_eq_zero_iff]
  simp [hprod]

#print axioms det_pairing_zero_iff

/-- Coordinate form of the divisor: some numerator coordinate vanishes. -/
theorem det_pairing_zero_iff_exists (t g : n → ℝ) (hg : ∀ i, g i ≠ 0) :
    (pairing t g).det = 0 ↔ ∃ i, t i = 0 := by
  rw [det_pairing_zero_iff t g hg, divisor, Finset.prod_eq_zero_iff]
  simp

#print axioms det_pairing_zero_iff_exists

/-- B86's named divisor, with the missing relation between the Gram matrix and
the pairing numerator stated explicitly as an additional hypothesis. -/
theorem det_pairing_zero_iff_gram_divisor (t g : n → ℝ) (G : Matrix n n ℝ)
    (hg : ∀ i, g i ≠ 0) (hG : G.det = divisor t) :
    (pairing t g).det = 0 ↔ G.det = 0 := by
  rw [det_pairing_zero_iff t g hg, ← hG]

#print axioms det_pairing_zero_iff_gram_divisor

/-- The card's identity `AᵀB = BA` says precisely that `BA` is symmetric when
`B` is the diagonal pairing. -/
theorem transport_selfSymmetric_of_pairing (A : Matrix n n ℝ) (t g : n → ℝ)
    (h : Aᵀ * pairing t g = pairing t g * A) :
    (pairing t g * A)ᵀ = pairing t g * A := by
  calc
    (pairing t g * A)ᵀ = Aᵀ * (pairing t g)ᵀ := Matrix.transpose_mul _ _
    _ = Aᵀ * pairing t g := by rw [pairing_transpose]
    _ = pairing t g * A := h

#print axioms transport_selfSymmetric_of_pairing

/-- A small denominator produces arbitrarily large positive pairing entries.
This is the elementary content of the card's divergence statement. -/
theorem pairing_entry_arbitrarily_large (t C : ℝ) (ht : 0 < t) (hC : 0 < C) :
    ∃ g : ℝ, 0 < g ∧ C < t / g := by
  have hCp : 0 < C + 1 := by linarith
  refine ⟨t / (C + 1), div_pos ht hCp, ?_⟩
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hCp0 : C + 1 ≠ 0 := ne_of_gt hCp
  have heq : t / (t / (C + 1)) = C + 1 := by
    field_simp [ht0, hCp0]
  rw [heq]
  linarith

#print axioms pairing_entry_arbitrarily_large

/-- Positive numerator data for a nondegenerate two-state instance. -/
def tRegular : Fin 2 → ℝ := ![2, 4]

/-- Unit denominator data, just for readable concrete matrix calculations. -/
def gUnit : Fin 2 → ℝ := ![1, 1]

/-- The concrete pairing is non-scalar. -/
theorem regular_pairing_matrix :
    pairing tRegular gUnit = !![2, 0; 0, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairing, tRegular, gUnit, Matrix.diagonal_apply]

#print axioms regular_pairing_matrix

/-- A non-symmetric directed transport matrix; its off-diagonal entries are
balanced by the different pairing weights. -/
def witnessA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 4; 2, 3]

/-- The concrete non-symmetric transport satisfies B86's reciprocity pairing. -/
theorem witness_complex_symmetric :
    witnessAᵀ * pairing tRegular gUnit = pairing tRegular gUnit * witnessA := by
  rw [regular_pairing_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms witness_complex_symmetric

/-- The witness is not merely an ordinary symmetric matrix in disguise. -/
theorem witness_not_symmetric : witnessAᵀ ≠ witnessA := by
  intro h
  have h01 : witnessAᵀ 0 1 = witnessA 0 1 := by rw [h]
  norm_num [witnessA] at h01

#print axioms witness_not_symmetric

/-- The regular instance lies off the divisor and has nonzero pairing
determinant. -/
theorem regular_off_divisor :
    (pairing tRegular gUnit).det = 8 ∧ divisor tRegular = 8 := by
  constructor
  · rw [regular_pairing_matrix]
    norm_num [Matrix.det_fin_two]
  · norm_num [divisor, tRegular, Fin.prod_univ_two]

#print axioms regular_off_divisor

/-- Numerator data on the wall. -/
def tWall : Fin 2 → ℝ := ![0, 4]

/-- At the wall both the pairing determinant and the associated diagonal Gram
determinant vanish. -/
theorem wall_on_divisor :
    (pairing tWall gUnit).det = 0 ∧ (Matrix.diagonal tWall).det = 0 := by
  constructor
  · rw [det_pairing]
    norm_num [divisor, tWall, gUnit, Fin.prod_univ_two]
  · simp [Matrix.det_diagonal, tWall, Fin.prod_univ_two]

#print axioms wall_on_divisor

end AtlasFormal.B86

/-! ## B148 — misses compose multiplicatively under a tensor product

Integrated from `.ultramath/smwtkiqjq/m10/B148.lean`.
-/
/-
B148 — Under a tensor product the misses multiply.

This file formalizes the finite rank-one statement behind the card. For
unit vectors, the normalized rank-one Frobenius stress is
`S(u,v) = 1 - (u ⬝ᵥ v)^2`. Tensoring both vectors multiplies the overlaps,
and consequently the *non-stress* parts multiply:

  `1 - S(u ⊗ u', v ⊗ v') = (1 - S(u,v)) * (1 - S(u',v'))`.

The same identity is checked in an explicit product of two finite Bernoulli
distributions. There `q` is a component miss probability, `(1-q)` is its
non-miss probability, and a composite is missed unless both components are
non-missed. Independence gives `q_composite = qA + qB - qA*qB`, not the
product `qA*qB`; a concrete counterexample to the latter reading is included.

Not formalized: condition numbers and additivity of their logarithms,
normality criteria for Kronecker products, limiting selected directions of
transports, and any assertion for arbitrary full-rank commutator stress.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AtlasFormal.B148

/-! ### Rank-one stress and tensor products -/

/-- A real vector on the product index type, with entries `u i * u' j`. -/
def tensorVec {n m : Type*} (u : n → ℝ) (u' : m → ℝ) : n × m → ℝ :=
  fun p => u p.1 * u' p.2

/-- The squared-overlap normalization of rank-one stress. -/
def rankOneStress {n : Type*} [Fintype n] (u v : n → ℝ) : ℝ :=
  1 - (u ⬝ᵥ v) ^ 2

/-- Half the squared Frobenius distance between the two rank-one projectors. -/
def rankOneFrobeniusStress {n : Type*} [Fintype n] (u v : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, (u i * u j - v i * v j) ^ 2

/-- For unit vectors the two normalizations of rank-one stress agree. -/
theorem rankOneFrobeniusStress_eq {n : Type*} [Fintype n] (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    rankOneFrobeniusStress u v = rankOneStress u v := by
  have e : ∑ i, ∑ j, (u i * u j - v i * v j) ^ 2 =
      (u ⬝ᵥ u) * (u ⬝ᵥ u) - 2 * ((u ⬝ᵥ v) * (u ⬝ᵥ v)) +
        (v ⬝ᵥ v) * (v ⬝ᵥ v) := by
    simp only [dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [rankOneFrobeniusStress, rankOneStress, e, hu, hv]
  ring

/-- Overlap is multiplicative on tensor-product vectors. -/
theorem tensor_overlap {n m : Type*} [Fintype n] [Fintype m]
    (u v : n → ℝ) (u' v' : m → ℝ) :
    tensorVec u u' ⬝ᵥ tensorVec v v' = (u ⬝ᵥ v) * (u' ⬝ᵥ v') := by
  rw [dotProduct, Fintype.sum_prod_type, dotProduct, dotProduct,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => by simp only [tensorVec]; ring))

/-- **B148, exact composition law.** The non-stress (squared-overlap) parts
multiply under tensor products. No normalization is needed for this algebraic
identity; unit-vector hypotheses enter when the stress is interpreted as a
probability. -/
theorem b148_stress_composition {n m : Type*} [Fintype n] [Fintype m]
    (u v : n → ℝ) (u' v' : m → ℝ) :
    1 - rankOneStress (tensorVec u u') (tensorVec v v') =
      (1 - rankOneStress u v) * (1 - rankOneStress u' v') := by
  rw [rankOneStress, rankOneStress, rankOneStress, tensor_overlap]
  ring

/-- Unit-vector rank-one stress is nonnegative, since it is half a sum of
squares. -/
theorem rankOneStress_nonneg {n : Type*} [Fintype n] (u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    0 ≤ rankOneStress u v := by
  rw [← rankOneFrobeniusStress_eq u v hu hv]
  unfold rankOneFrobeniusStress
  positivity

/-- Rank-one stress is at most one, without any normalization hypothesis. -/
theorem rankOneStress_le_one {n : Type*} [Fintype n] (u v : n → ℝ) :
    rankOneStress u v ≤ 1 := by
  unfold rankOneStress
  nlinarith [sq_nonneg (u ⬝ᵥ v)]

/-! A nontrivial rational unit-vector instance. -/

def uA : Fin 2 → ℝ := ![1, 0]
def vA : Fin 2 → ℝ := ![3 / 5, 4 / 5]
def uB : Fin 2 → ℝ := ![0, 1]
def vB : Fin 2 → ℝ := ![5 / 13, 12 / 13]

/-- The four vectors in the concrete instance are unit vectors. -/
theorem b148_concrete_unit_vectors :
    uA ⬝ᵥ uA = 1 ∧ vA ⬝ᵥ vA = 1 ∧ uB ⬝ᵥ uB = 1 ∧ vB ⬝ᵥ vB = 1 := by
  norm_num [uA, vA, uB, vB, dotProduct, Fin.sum_univ_two]

/-- The component stresses in the concrete instance are both nonextremal. -/
theorem b148_concrete_component_stress :
    rankOneStress uA vA = 16 / 25 ∧ rankOneStress uB vB = 25 / 169 := by
  norm_num [rankOneStress, uA, vA, uB, vB, dotProduct, Fin.sum_univ_two]

/-- A concrete, non-vacuous evaluation of B148: the tensor overlap squared is
`1296/4225`, so the tensor stress is `2929/4225`. -/
theorem b148_concrete_tensor_stress :
    1 - rankOneStress (tensorVec uA uB) (tensorVec vA vB) = 1296 / 4225 ∧
      rankOneStress (tensorVec uA uB) (tensorVec vA vB) = 2929 / 4225 := by
  norm_num [rankOneStress, tensorVec, uA, vA, uB, vB, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two]

/-! ### An explicit finite independent probability model -/

/-- A distribution on `Fin 2`: outcome `0` is non-miss and outcome `1` is miss.
The parameter `q` is the component miss probability. -/
def bernoulliMiss (q : ℝ) : Fin 2 → ℝ := ![1 - q, q]

/-- The independent product distribution on two-component outcomes. -/
def productDistribution (qA qB : ℝ) (x : Fin 2 × Fin 2) : ℝ :=
  bernoulliMiss qA x.1 * bernoulliMiss qB x.2

/-- The unique outcome in which neither component is missed. -/
def bothNonmiss : Finset (Fin 2 × Fin 2) := {(0, 0)}

/-- A composite is missed exactly when it is not in `bothNonmiss`. -/
def compositeMiss (qA qB : ℝ) : ℝ :=
  1 - ∑ x ∈ bothNonmiss, productDistribution qA qB x

/-- Each Bernoulli law has total mass one, algebraically. -/
theorem bernoulliMiss_sum (q : ℝ) : ∑ i, bernoulliMiss q i = 1 := by
  simp [bernoulliMiss, Fin.sum_univ_two]

/-- With `0 ≤ q ≤ 1`, every Bernoulli mass is nonnegative. -/
theorem bernoulliMiss_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    0 ≤ bernoulliMiss q i := by
  fin_cases i <;> simp [bernoulliMiss] <;> linarith

/-- The independent product law has total mass one. -/
theorem productDistribution_sum (qA qB : ℝ) :
    ∑ x, productDistribution qA qB x = 1 := by
  rw [Fintype.sum_prod_type]
  simp [productDistribution, bernoulliMiss, Fin.sum_univ_two]
  ring

/-- The independent product law is nonnegative for probability parameters. -/
theorem productDistribution_nonneg {qA qB : ℝ}
    (hqA0 : 0 ≤ qA) (hqA1 : qA ≤ 1) (hqB0 : 0 ≤ qB) (hqB1 : qB ≤ 1)
    (x : Fin 2 × Fin 2) : 0 ≤ productDistribution qA qB x := by
  exact mul_nonneg (bernoulliMiss_nonneg hqA0 hqA1 x.1)
    (bernoulliMiss_nonneg hqB0 hqB1 x.2)

/-- Independence computes the probability that neither component is missed. -/
theorem bothNonmiss_probability (qA qB : ℝ) :
    ∑ x ∈ bothNonmiss, productDistribution qA qB x = (1 - qA) * (1 - qB) := by
  simp [bothNonmiss, productDistribution, bernoulliMiss]

/-- **B148 in the explicit probability model.** The composite non-miss
probability is the product of the independent component non-miss probabilities. -/
theorem b148_probability_composition (qA qB : ℝ) :
    1 - compositeMiss qA qB = (1 - qA) * (1 - qB) := by
  rw [compositeMiss, bothNonmiss_probability]
  ring

/-- The actual law for miss probabilities: an inclusion-exclusion sum, not a
product. -/
theorem compositeMiss_expanded (qA qB : ℝ) :
    compositeMiss qA qB = qA + qB - qA * qB := by
  rw [compositeMiss, bothNonmiss_probability]
  ring

/-- Counterexample to the literal slogan if it is read as saying that the
composite miss probability itself is the product of the component miss
probabilities: at two independent misses of probability `1/2`, the composite
miss probability is `3/4`, not `1/4`. -/
theorem b148_miss_product_counterexample :
    compositeMiss (1 / 2) (1 / 2) ≠ (1 / 2 : ℝ) * (1 / 2) := by
  rw [compositeMiss_expanded]
  norm_num

/-- A concrete probability instance: miss probabilities `1/2` and `1/3` give
composite miss probability `2/3`, while the non-miss probability is `1/3`. -/
theorem b148_probability_concrete :
    compositeMiss (1 / 2) (1 / 3) = 2 / 3 ∧
      1 - compositeMiss (1 / 2) (1 / 3) = 1 / 3 := by
  constructor
  · rw [compositeMiss_expanded]
    norm_num
  · rw [b148_probability_composition]
    norm_num

/-- The concrete product distribution has four nonnegative atoms and total
mass one. -/
theorem b148_probability_concrete_valid :
    (∀ x, 0 ≤ productDistribution (1 / 2) (1 / 3) x) ∧
      ∑ x, productDistribution (1 / 2) (1 / 3) x = 1 := by
  constructor
  · intro x
    exact productDistribution_nonneg (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) x
  · exact productDistribution_sum _ _

end AtlasFormal.B148

#print axioms AtlasFormal.B148.rankOneFrobeniusStress_eq
#print axioms AtlasFormal.B148.tensor_overlap
#print axioms AtlasFormal.B148.b148_stress_composition
#print axioms AtlasFormal.B148.rankOneStress_nonneg
#print axioms AtlasFormal.B148.rankOneStress_le_one
#print axioms AtlasFormal.B148.b148_concrete_unit_vectors
#print axioms AtlasFormal.B148.b148_concrete_component_stress
#print axioms AtlasFormal.B148.b148_concrete_tensor_stress
#print axioms AtlasFormal.B148.bernoulliMiss_sum
#print axioms AtlasFormal.B148.bernoulliMiss_nonneg
#print axioms AtlasFormal.B148.productDistribution_sum
#print axioms AtlasFormal.B148.productDistribution_nonneg
#print axioms AtlasFormal.B148.bothNonmiss_probability
#print axioms AtlasFormal.B148.b148_probability_composition
#print axioms AtlasFormal.B148.compositeMiss_expanded
#print axioms AtlasFormal.B148.b148_miss_product_counterexample
#print axioms AtlasFormal.B148.b148_probability_concrete
#print axioms AtlasFormal.B148.b148_probability_concrete_valid

/-! ## B37 — a finite rank makes the trace sum finite

Integrated from `.ultramath/smwtkiqjq/m15/B37.lean`.
-/

noncomputable section

open Matrix
open Module

namespace AtlasFormal.B37

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- B37: the singular-value series of a finite-dimensional map is summable.
The explicit finite support is `T.singularValues.support`; the following theorem
also identifies it by the rank. -/
theorem singularValues_summable (T : E →ₗ[𝕜] F) :
    Summable (fun i => T.singularValues i) := by
  refine summable_of_ne_finset_zero (s := T.singularValues.support) ?_
  intro i hi
  exact Finsupp.notMem_support_iff.mp hi

#print axioms singularValues_summable

/-- The trace-norm series is absolutely summable. -/
theorem singularValues_abs_summable (T : E →ₗ[𝕜] F) :
    Summable (fun i => ‖T.singularValues i‖) := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (T.singularValues_nonneg _)] using
    singularValues_summable T

#print axioms singularValues_abs_summable

/-- The finite index set in B37 is exactly the first `finrank T.range`
natural numbers. -/
theorem traceNorm_tsum_eq_sum_range_rank (T : E →ₗ[𝕜] F) :
    ∑' i, T.singularValues i =
      ∑ i ∈ Finset.range (finrank 𝕜 T.range), T.singularValues i := by
  apply tsum_eq_sum
  intro i hi
  rw [T.singularValues_eq_zero_iff_le_finrank_range]
  simpa only [Finset.mem_range, not_lt] using hi

#print axioms traceNorm_tsum_eq_sum_range_rank

/-- Squared singular values over the finite spectral index set sum to the
real part of the trace of the Gram operator. -/
theorem singularValue_energy_eq_re_trace (T : E →ₗ[𝕜] F) {N : ℕ}
    (hN : finrank 𝕜 E = N) :
    ∑ i : Fin N, T.singularValues i ^ 2 =
      RCLike.re ((LinearMap.trace 𝕜 E) (T.adjoint ∘ₗ T)) := by
  rw [T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hN]
  apply Finset.sum_congr rfl
  intro i _
  exact T.sq_singularValues_fin hN i

#print axioms singularValue_energy_eq_re_trace

/-- The squared-singular-value series is summable, with the same explicit
finite support as the singular values. -/
theorem singularValue_energy_summable (T : E →ₗ[𝕜] F) :
    Summable (fun i => T.singularValues i ^ 2) := by
  refine summable_of_ne_finset_zero (s := T.singularValues.support) ?_
  intro i hi
  simp [Finsupp.notMem_support_iff.mp hi]

#print axioms singularValue_energy_summable

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A matrix as a map between standard Euclidean spaces. -/
def matrixToEuclideanLin (A : Matrix m n 𝕜) :
    EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  Matrix.toLin (EuclideanSpace.basisFun n 𝕜).toBasis
    (EuclideanSpace.basisFun m 𝕜).toBasis A

/-- B37 for a matrix: the finite squared-singular-value sum equals the real
part of the trace of its Gram matrix `Aᴴ A`. -/
theorem matrix_singularValue_energy_eq_gram_trace (A : Matrix m n 𝕜) :
    ∑ i : Fin (Fintype.card n), (matrixToEuclideanLin A).singularValues i ^ 2 =
      RCLike.re (Aᴴ * A).trace := by
  let bn := (EuclideanSpace.basisFun n 𝕜).toBasis
  let bm := (EuclideanSpace.basisFun m 𝕜).toBasis
  have hcomp : (matrixToEuclideanLin A).adjoint ∘ₗ matrixToEuclideanLin A =
      Matrix.toLin bn bn (Aᴴ * A) := by
    unfold matrixToEuclideanLin
    rw [← Matrix.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜)
      (EuclideanSpace.basisFun m 𝕜) A]
    exact (Matrix.toLin_mul bn bm bn Aᴴ A).symm
  calc
    ∑ i : Fin (Fintype.card n), (matrixToEuclideanLin A).singularValues i ^ 2 =
        RCLike.re ((LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n))
          ((matrixToEuclideanLin A).adjoint ∘ₗ matrixToEuclideanLin A)) :=
      singularValue_energy_eq_re_trace _ finrank_euclideanSpace
    _ = RCLike.re ((LinearMap.trace 𝕜 (EuclideanSpace 𝕜 n))
          (Matrix.toLin bn bn (Aᴴ * A))) := by rw [hcomp]
    _ = RCLike.re (Aᴴ * A).trace := by rw [Matrix.trace_toLin_eq]

#print axioms matrix_singularValue_energy_eq_gram_trace

/-- A nonzero two-dimensional witness, with singular values 3 and 4. -/
def witness : Matrix (Fin 2) (Fin 2) ℂ := !![3, 0; 0, 4]

/-- Non-vacuity check: the witness has squared-singular-value energy 25. -/
theorem witness_energy :
    ∑ i : Fin (Fintype.card (Fin 2)),
      (matrixToEuclideanLin witness).singularValues i ^ 2 = 25 := by
  rw [matrix_singularValue_energy_eq_gram_trace]
  norm_num [witness, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms witness_energy

end AtlasFormal.B37

/-! ## B116 — a permutation count is a projector distance

Integrated from `.ultramath/smwtkiqjq/m5/B116.lean`.
-/
/-
# B116 — a permutation count is a projector distance

Finite algebraic kernel: for permutation matrices on a finite type, the squared
Frobenius distance is twice the cardinality of the support of the relative
permutation.  The real trace formula `tr ((P-Q)ᵀ(P-Q))` is used as the squared
Frobenius norm, so no square root or normalization is hidden in the statement.

The graph-projector embedding, principal angles, and the cycle-sensitive length
`L` from the full card are not formalized here.
-/

noncomputable section

open Matrix

namespace AtlasFormal.B116

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard matrix of a permutation: row `σ j`, column `j`, contains one. -/
abbrev permMat (σ : Equiv.Perm ι) : Matrix ι ι ℝ := σ.toPEquiv.toMatrix

/-- The unnormalized squared Frobenius distance between two permutation matrices. -/
def permFrobSq (σ τ : Equiv.Perm ι) : ℝ :=
  ((permMat σ - permMat τ)ᵀ * (permMat σ - permMat τ)).trace

/-- The identity permutation has the identity matrix. -/
theorem permMat_one : permMat (1 : Equiv.Perm ι) = 1 := by
  simp [permMat, ← Matrix.ext_iff, Matrix.one_apply]

#print axioms permMat_one

/-- Transposition inverts a permutation matrix. -/
theorem permMat_transpose (σ : Equiv.Perm ι) :
    (permMat σ)ᵀ = permMat σ⁻¹ := by
  rw [permMat, ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, ← Equiv.Perm.inv_def]

#print axioms permMat_transpose

/-- Matrix multiplication is the opposite-order permutation product. -/
theorem permMat_mul (σ τ : Equiv.Perm ι) :
    permMat (σ * τ) = permMat τ * permMat σ := by
  rw [permMat, Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

#print axioms permMat_mul

/-- Permutation matrices are orthogonal, on the left. -/
theorem permMat_transpose_mul_self (σ : Equiv.Perm ι) :
    (permMat σ)ᵀ * permMat σ = 1 := by
  rw [permMat_transpose, ← permMat_mul]
  simp [permMat_one]

#print axioms permMat_transpose_mul_self

/-- The mixed product is the matrix of the relative permutation `τ * σ⁻¹`. -/
theorem permMat_transpose_mul (σ τ : Equiv.Perm ι) :
    (permMat σ)ᵀ * permMat τ = permMat (τ * σ⁻¹) := by
  rw [permMat_transpose, permMat_mul]

#print axioms permMat_transpose_mul

/-- The trace of a permutation matrix is its number of fixed points. -/
theorem trace_permMat_fixedPoints (ρ : Equiv.Perm ι) :
    (permMat ρ).trace = (Function.fixedPoints ρ).ncard := by
  delta Matrix.trace
  simp [permMat, Equiv.toPEquiv_apply, ← Set.ncard_coe_finset,
    Function.fixedPoints, Function.IsFixedPt]

#print axioms trace_permMat_fixedPoints

/-- The trace of a permutation matrix is its degree minus its number of moved points. -/
theorem trace_permMat_eq_card_sub_support (ρ : Equiv.Perm ι) :
    (permMat ρ).trace = (Fintype.card ι : ℝ) - (ρ.support.card : ℝ) := by
  rw [trace_permMat_fixedPoints]
  have hcompl : (Function.fixedPoints ρ)ᶜ = (ρ.support : Set ι) := by
    ext x
    simp [Function.fixedPoints, Function.IsFixedPt, Equiv.Perm.mem_support]
  have hsum := Set.ncard_add_ncard_compl (Function.fixedPoints ρ)
  rw [hcompl, Set.ncard_coe_finset, Nat.card_eq_fintype_card] at hsum
  have hsumR : ((Function.fixedPoints ρ).ncard : ℝ) + (ρ.support.card : ℝ) =
      (Fintype.card ι : ℝ) := by
    exact_mod_cast hsum
  linarith

#print axioms trace_permMat_eq_card_sub_support

/-- The mixed trace sees precisely the support of `σ⁻¹ * τ`. -/
theorem permMat_mixed_trace (σ τ : Equiv.Perm ι) :
    ((permMat σ)ᵀ * permMat τ).trace =
      (Fintype.card ι : ℝ) - ((σ⁻¹ * τ).support.card : ℝ) := by
  rw [permMat_transpose_mul, trace_permMat_eq_card_sub_support]
  have hρ : τ * σ⁻¹ = σ * (σ⁻¹ * τ) * σ⁻¹ := by group
  rw [hρ, Equiv.Perm.card_support_conj]

#print axioms permMat_mixed_trace

/-- The two mixed traces in the Frobenius expansion agree. -/
theorem permMat_mixed_trace_comm (σ τ : Equiv.Perm ι) :
    ((permMat τ)ᵀ * permMat σ).trace = ((permMat σ)ᵀ * permMat τ).trace := by
  have htrans : ((permMat σ)ᵀ * permMat τ)ᵀ = (permMat τ)ᵀ * permMat σ := by simp
  rw [← htrans, Matrix.trace_transpose]

#print axioms permMat_mixed_trace_comm

/-- **B116.** For permutations `σ, τ` on any finite type,
`‖Pσ - Pτ‖²_F = 2 * moved(σ⁻¹ * τ)`, with `moved` the support cardinality and
without dividing by the degree. -/
theorem b116_perm_frobSq (σ τ : Equiv.Perm ι) :
    permFrobSq σ τ = 2 * ((σ⁻¹ * τ).support.card : ℝ) := by
  unfold permFrobSq
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [permMat_transpose_mul_self σ, permMat_transpose_mul_self τ,
    permMat_mixed_trace σ τ, permMat_mixed_trace_comm σ τ, permMat_mixed_trace σ τ]
  simp only [Matrix.trace_one]
  ring

#print axioms b116_perm_frobSq

/-- In particular, the distance vanishes exactly for equal permutations. -/
theorem b116_perm_frobSq_eq_zero_iff (σ τ : Equiv.Perm ι) :
    permFrobSq σ τ = 0 ↔ σ = τ := by
  rw [b116_perm_frobSq]
  constructor
  · intro h
    have hcardR : (((σ⁻¹ * τ).support.card : ℕ) : ℝ) = 0 := by linarith
    have hcard : (σ⁻¹ * τ).support.card = 0 := by exact_mod_cast hcardR
    have hrel : σ⁻¹ * τ = 1 := Equiv.Perm.card_support_eq_zero.mp hcard
    calc
      σ = σ * 1 := (mul_one σ).symm
      _ = σ * (σ⁻¹ * τ) := by rw [hrel]
      _ = τ := by group
  · intro h
    subst τ
    simp

#print axioms b116_perm_frobSq_eq_zero_iff

/-- A concrete non-vacuous instance: on two points, the identity and the swap
have squared Frobenius distance `4 = 2 * 2`. -/
theorem b116_identity_swap_witness :
    permFrobSq (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1) = 4 := by
  rw [b116_perm_frobSq]
  norm_num [Equiv.Perm.card_support_swap]

#print axioms b116_identity_swap_witness

end AtlasFormal.B116

/-! ## B131 — a divided difference brackets the metric

Integrated from `.ultramath/smwtkiqjq/m16/B131Optical.lean`.
-/
/-
B131 — two optical readings bound the metric from both sides.

The target synopsis supplied with the batch incorrectly described B131 as the
QGT determinant inequality. In `atlas/coverage/coverage.json`, that inequality
is B1/B32 (and is already formalized elsewhere). The actual B131 claim is the
finite-spectrum optical secant bound proved here.

For active gaps `t i ≥ a > 0` and nonnegative oscillator weights `w i`, put
  g = Σ w/t², F = Σ t w, α₀ = Σ 2w/t,
  R(y) = Σ 2tw/(t²-y), B = Σ 2tw/((t²-y₁)(t²-y₂)).
We prove the divided-difference formula for B and, below the gap,
  B/β(a) ≤ g ≤ F^(1/4) (B/2)^(3/4),
where β(a)=2a³/((a²-y₁)(a²-y₂)). The upper bound is finite Hölder with
exponents 4 and 4/3. We also prove the static and one-reading bounds recorded
in the coverage ledger. All powers with real exponents below are `Real.rpow`.

Not formalized: continuum spectra, the optical derivation of this response
model, vector-valued metric directions, and measurement-error propagation.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal.B131

open Finset

variable {ι : Type*}

/-- The scalar field metric `g = Σ w/t²`. -/
def metric (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, w i / t i ^ 2

/-- The oscillator-strength budget `F = Σ t w`. -/
def budget (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, t i * w i

/-- The static response `α₀ = Σ 2w/t`. -/
def static (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, 2 * w i / t i

/-- The third inverse-gap moment `Σ w/t³`. -/
def moment3 (s : Finset ι) (t w : ι → ℝ) : ℝ := ∑ i ∈ s, w i / t i ^ 3

/-- The finite-spectrum subgap response. -/
def response (s : Finset ι) (t w : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, 2 * t i * w i / (t i ^ 2 - y)

/-- The kernel of the divided difference of two subgap responses. -/
def secant (s : Finset ι) (t w : ι → ℝ) (y₁ y₂ : ℝ) : ℝ :=
  ∑ i ∈ s, 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂))

/-- The lower-edge secant kernel `β(a)`. -/
def kernelRatio (y₁ y₂ t : ℝ) : ℝ :=
  2 * t ^ 3 / ((t ^ 2 - y₁) * (t ^ 2 - y₂))

/-- The secant really is the divided difference of the two optical readings.
The two readings need not be ordered; only distinctness and absence of poles
are used. -/
theorem divided_difference_response (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i)
    (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) (hy : y₁ ≠ y₂) :
    (response s t w y₂ - response s t w y₁) / (y₂ - y₁) = secant s t w y₁ y₂ := by
  unfold response secant
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
  have d1 : t i ^ 2 - y₁ ≠ 0 := by linarith
  have d2 : t i ^ 2 - y₂ ≠ 0 := by linarith
  have dy : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  field_simp [d1, d2, dy]
  ring

#print axioms AtlasFormal.B131.divided_difference_response

/-- Static response is bounded below by twice the gap times the metric. -/
theorem static_lower (s : Finset ι) (t w : ι → ℝ) (a : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    2 * a * metric s t w ≤ static s t w := by
  unfold metric static
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have key : 2 * w i / t i =
      2 * a * (w i / t i ^ 2) + 2 * w i * (t i - a) / t i ^ 2 := by
    field_simp <;> ring
  rw [key]
  have hnonneg : 0 ≤ 2 * w i * (t i - a) / t i ^ 2 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (hw i hi)) (sub_nonneg.mpr (hta i hi)))
      (by positivity)
  linarith

#print axioms AtlasFormal.B131.static_lower

/-- Cauchy–Schwarz for the static response and third inverse-gap moment. -/
theorem static_sq_le (s : Finset ι) (t w : ι → ℝ) (a : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    static s t w ^ 2 ≤ 4 * budget s t w * moment3 s t w := by
  have hs : static s t w = 2 * ∑ i ∈ s, w i / t i := by
    unfold static
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hcs : (∑ i ∈ s, w i / t i) ^ 2 ≤ budget s t w * moment3 s t w := by
    unfold budget moment3
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i hi
      exact mul_nonneg (le_trans ha.le (hta i hi)) (hw i hi)
    · intro i hi
      have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
      exact div_nonneg (hw i hi) (by positivity)
    · intro i hi
      have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
      apply le_of_eq
      field_simp <;> ring
  rw [hs]
  nlinarith [hcs]

#print axioms AtlasFormal.B131.static_sq_le

/-- The two-reading secant dominates twice the third inverse-gap moment. -/
theorem moment3_le_secant (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    2 * moment3 s t w ≤ secant s t w y₁ y₂ := by
  unfold moment3 secant
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
  have d1 : 0 < t i ^ 2 - y₁ := by linarith
  have d2 : 0 < t i ^ 2 - y₂ := by linarith
  have hD : (t i ^ 2 - y₁) * (t i ^ 2 - y₂) ≤ t i ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le h₁ hsq)) hy₂,
      mul_nonneg hy₁ (sq_nonneg (t i))]
  have hnum : 0 ≤ 2 * t i * w i := by
    have := hw i hi
    positivity
  calc
    2 * (w i / t i ^ 3) = 2 * t i * w i / t i ^ 4 := by field_simp <;> ring
    _ ≤ 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂)) :=
      div_le_div_of_nonneg_left hnum (mul_pos d1 d2) hD

#print axioms AtlasFormal.B131.moment3_le_secant

/-- The static response is bounded by the budget and the two-reading secant. -/
theorem static_sq_le_budget_secant (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    static s t w ^ 2 ≤ 2 * budget s t w * secant s t w y₁ y₂ := by
  have hF : 0 ≤ budget s t w :=
    sum_nonneg fun i hi => mul_nonneg (le_trans ha.le (hta i hi)) (hw i hi)
  have h1 := static_sq_le s t w a ha hta hw
  have h2 := moment3_le_secant s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂
  nlinarith [mul_le_mul_of_nonneg_left h2 hF]

#print axioms AtlasFormal.B131.static_sq_le_budget_secant

/-- A single subgap reading is bracketed by the static response. -/
theorem response_bracket (s : Finset ι) (t w : ι → ℝ) (a y : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy : 0 ≤ y) (hya : y < a ^ 2) :
    static s t w ≤ response s t w y ∧
      response s t w y ≤ static s t w / (1 - y / a ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hq : 0 < 1 - y / a ^ 2 := by
    rw [sub_pos, div_lt_one ha2]
    exact hya
  constructor
  · unfold static response
    apply sum_le_sum
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
    have d : 0 < t i ^ 2 - y := by linarith
    have hnum : 0 ≤ 2 * t i * w i := by
      have := hw i hi
      positivity
    calc
      2 * w i / t i = 2 * t i * w i / t i ^ 2 := by field_simp <;> ring
      _ ≤ 2 * t i * w i / (t i ^ 2 - y) :=
        div_le_div_of_nonneg_left hnum d (by linarith)
  · unfold static response
    rw [sum_div]
    apply sum_le_sum
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
    have d : 0 < t i ^ 2 - y := by linarith
    have hwi := hw i hi
    have hay : 0 < a ^ 2 - y := by linarith
    have e : 2 * w i / t i / (1 - y / a ^ 2) =
        2 * w i * a ^ 2 / (t i * (a ^ 2 - y)) := by
      field_simp <;> ring
    rw [e, div_le_div_iff₀ d (mul_pos ht hay)]
    nlinarith [mul_nonneg (mul_nonneg hwi hy) (sub_nonneg.mpr hsq)]

#print axioms AtlasFormal.B131.response_bracket

/-- The lower-edge secant kernel decreases as the active gap increases. -/
theorem kernelRatio_antitone (y₁ y₂ a t : ℝ)
    (ha : 0 < a) (hat : a ≤ t) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    kernelRatio y₁ y₂ t ≤ kernelRatio y₁ y₂ a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith
  have form : ∀ x : ℝ, 0 < x → x ^ 2 - y₁ ≠ 0 → x ^ 2 - y₂ ≠ 0 →
      kernelRatio y₁ y₂ x = 2 / ((x - y₁ / x) * (1 - y₂ / x ^ 2)) := by
    intro x hx d1 d2
    unfold kernelRatio
    have hx0 : x ≠ 0 := hx.ne'
    rw [show x - y₁ / x = (x ^ 2 - y₁) / x by field_simp <;> ring,
      show 1 - y₂ / x ^ 2 = (x ^ 2 - y₂) / x ^ 2 by field_simp <;> ring]
    field_simp <;> ring
  have da1 : 0 < a ^ 2 - y₁ := by linarith
  have da2 : 0 < a ^ 2 - y₂ := by linarith
  rw [form t ht (by linarith) (by linarith), form a ha da1.ne' da2.ne']
  have p1 : 0 < a - y₁ / a := by
    rw [show a - y₁ / a = (a ^ 2 - y₁) / a by field_simp <;> ring]
    exact div_pos da1 ha
  have p2 : 0 < 1 - y₂ / a ^ 2 := by
    rw [show 1 - y₂ / a ^ 2 = (a ^ 2 - y₂) / a ^ 2 by field_simp <;> ring]
    exact div_pos da2 (by positivity)
  have q1 : a - y₁ / a ≤ t - y₁ / t := by
    have : y₁ / t ≤ y₁ / a := div_le_div_of_nonneg_left hy₁ ha hat
    linarith
  have q2 : 1 - y₂ / a ^ 2 ≤ 1 - y₂ / t ^ 2 := by
    have : y₂ / t ^ 2 ≤ y₂ / a ^ 2 := div_le_div_of_nonneg_left hy₂ (by positivity) hsq
    linarith
  have hprod : (a - y₁ / a) * (1 - y₂ / a ^ 2) ≤
      (t - y₁ / t) * (1 - y₂ / t ^ 2) :=
    mul_le_mul q1 q2 p2.le (le_trans p1.le q1)
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos p1 p2) hprod

#print axioms AtlasFormal.B131.kernelRatio_antitone

/-- The lower-edge secant kernel is positive below the gap. -/
theorem kernelRatio_pos (y₁ y₂ a : ℝ)
    (ha : 0 < a) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    0 < kernelRatio y₁ y₂ a := by
  unfold kernelRatio
  have d1 : 0 < a ^ 2 - y₁ := by linarith
  have d2 : 0 < a ^ 2 - y₂ := by linarith
  exact div_pos (by positivity) (mul_pos d1 d2)

#print axioms AtlasFormal.B131.kernelRatio_pos

/-- Unnormalized lower metric bound from the two readings. -/
theorem secant_le_kernelRatio_metric (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    secant s t w y₁ y₂ ≤ kernelRatio y₁ y₂ a * metric s t w := by
  unfold secant metric
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
  have hsq : a ^ 2 ≤ t i ^ 2 := by nlinarith [hta i hi]
  have d1 : t i ^ 2 - y₁ ≠ 0 := by
    have : 0 < t i ^ 2 - y₁ := by linarith
    exact this.ne'
  have d2 : t i ^ 2 - y₂ ≠ 0 := by
    have : 0 < t i ^ 2 - y₂ := by linarith
    exact this.ne'
  have split : 2 * t i * w i / ((t i ^ 2 - y₁) * (t i ^ 2 - y₂)) =
      kernelRatio y₁ y₂ (t i) * (w i / t i ^ 2) := by
    unfold kernelRatio
    field_simp <;> ring
  rw [split]
  exact mul_le_mul_of_nonneg_right
    (kernelRatio_antitone y₁ y₂ a (t i) ha (hta i hi) hy₁ hy₂ h₁ h₂)
    (div_nonneg (hw i hi) (by positivity))

#print axioms AtlasFormal.B131.secant_le_kernelRatio_metric

/-- **B131, lower side:** `B/β(a) ≤ g`. -/
theorem secant_div_le_metric (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    secant s t w y₁ y₂ / kernelRatio y₁ y₂ a ≤ metric s t w := by
  rw [div_le_iff₀ (kernelRatio_pos y₁ y₂ a ha h₁ h₂), mul_comm]
  exact secant_le_kernelRatio_metric s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂

#print axioms AtlasFormal.B131.secant_div_le_metric

/-- Finite Hölder with exponents `4` and `4/3`, in the weighted form needed for
B131. The auxiliary functions vanish outside the active finite set, so no
hypotheses outside that set are needed. -/
theorem metric_le_holder (s : Finset ι) (t w : ι → ℝ) (a : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    metric s t w ≤
      moment3 s t w ^ (3 / 4 : ℝ) * budget s t w ^ (1 / 4 : ℝ) := by
  classical
  let W : ι → ℝ := fun i => if i ∈ s then w i / t i ^ 3 else 0
  let T : ι → ℝ := fun i => if i ∈ s then t i else 0
  have hW (i : ι) : 0 ≤ W i := by
    by_cases hi : i ∈ s
    · have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
      simp only [W, if_pos hi]
      exact div_nonneg (hw i hi) (by positivity)
    · simp [W, hi]
  have hT (i : ι) : 0 ≤ T i := by
    by_cases hi : i ∈ s
    · simp only [T, if_pos hi]
      exact le_trans ha.le (hta i hi)
    · simp [T, hi]
  have h := Real.inner_le_weight_mul_Lp_of_nonneg s
    (p := (4 : ℝ)) (by norm_num) W T hW hT
  have hleft : (∑ i ∈ s, W i * T i) = metric s t w := by
    unfold metric
    apply Finset.sum_congr rfl
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    simp only [W, T, if_pos hi]
    field_simp <;> ring
  have hWsum : (∑ i ∈ s, W i) = moment3 s t w := by
    unfold moment3
    apply Finset.sum_congr rfl
    intro i hi
    simp [W, hi]
  have hright : (∑ i ∈ s, W i * T i ^ (4 : ℝ)) = budget s t w := by
    unfold budget
    apply Finset.sum_congr rfl
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    simp only [W, T, if_pos hi]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp <;> ring
  rw [hleft, hWsum, hright] at h
  norm_num at h
  exact h

#print axioms AtlasFormal.B131.metric_le_holder

/-- **B131, upper side:** `g ≤ F^(1/4) (B/2)^(3/4)`. This is the
card's displayed power normalization, using `Real.rpow`. -/
theorem metric_le_budget_secant (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    metric s t w ≤
      budget s t w ^ (1 / 4 : ℝ) * (secant s t w y₁ y₂ / 2) ^ (3 / 4 : ℝ) := by
  have hM : 0 ≤ moment3 s t w := by
    unfold moment3
    apply sum_nonneg
    intro i hi
    have ht : 0 < t i := lt_of_lt_of_le ha (hta i hi)
    exact div_nonneg (hw i hi) (by positivity)
  have h2 := moment3_le_secant s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂
  have hMB : moment3 s t w ≤ secant s t w y₁ y₂ / 2 := by linarith
  have hpow := Real.rpow_le_rpow hM hMB (by norm_num : (0 : ℝ) ≤ 3 / 4)
  calc
    metric s t w ≤ moment3 s t w ^ (3 / 4 : ℝ) * budget s t w ^ (1 / 4 : ℝ) :=
      metric_le_holder s t w a ha hta hw
    _ ≤ (secant s t w y₁ y₂ / 2) ^ (3 / 4 : ℝ) * budget s t w ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by
        unfold budget
        exact sum_nonneg fun i hi => mul_nonneg (le_trans ha.le (hta i hi)) (hw i hi)) _)
    _ = budget s t w ^ (1 / 4 : ℝ) * (secant s t w y₁ y₂ / 2) ^ (3 / 4 : ℝ) := by
      ring

#print axioms AtlasFormal.B131.metric_le_budget_secant

/-- **B131, the full finite two-sided optical metric bracket.** -/
theorem metric_bracket (s : Finset ι) (t w : ι → ℝ) (a y₁ y₂ : ℝ)
    (ha : 0 < a) (hta : ∀ i ∈ s, a ≤ t i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (h₁ : y₁ < a ^ 2) (h₂ : y₂ < a ^ 2) :
    secant s t w y₁ y₂ / kernelRatio y₁ y₂ a ≤ metric s t w ∧
      metric s t w ≤ budget s t w ^ (1 / 4 : ℝ) *
        (secant s t w y₁ y₂ / 2) ^ (3 / 4 : ℝ) := by
  exact ⟨secant_div_le_metric s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂,
    metric_le_budget_secant s t w a y₁ y₂ ha hta hw hy₁ hy₂ h₁ h₂⟩

#print axioms AtlasFormal.B131.metric_bracket

/-! ## A concrete non-vacuous instance

There is one active mode at the lower gap, `a=t=1,w=1`, and the two distinct
readings are `y₁=0`, `y₂=1/2`. Thus `R(0)=2`, `R(1/2)=4`, the secant is `4`,
`β(1)=4`, and the lower bound is the non-vacuous equality `1≤1`. -/

/-- Exact readings and secant data for the one-mode witness. -/
theorem concrete_readings :
    response Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) 0 = 2 ∧
    response Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) = 4 ∧
    secant Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) 0 (1 / 2) = 4 ∧
    kernelRatio 0 (1 / 2) 1 = 4 := by
  norm_num [response, secant, kernelRatio]

#print axioms AtlasFormal.B131.concrete_readings

/-- The divided difference of the two concrete readings is indeed `4`. -/
theorem concrete_divided_difference :
    (response Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) -
      response Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) 0) /
        (1 / 2 - 0) = 4 := by
  norm_num [response]

#print axioms AtlasFormal.B131.concrete_divided_difference

/-- The concrete metric and budget are both one; in particular the witness has
nonzero metric and nonzero oscillator strength. -/
theorem concrete_metric_and_budget :
    metric Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 ∧
    budget Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 := by
  norm_num [metric, budget]

#print axioms AtlasFormal.B131.concrete_metric_and_budget

/-- The general theorem applies to the explicit one-mode, two-reading data. -/
theorem concrete_metric_bracket :
    secant Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) 0 (1 / 2) /
        kernelRatio 0 (1 / 2) 1 ≤
      metric Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) ∧
    metric Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) ≤
      budget Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) ^ (1 / 4 : ℝ) *
        (secant Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) 0 (1 / 2) / 2) ^
          (3 / 4 : ℝ) := by
  apply metric_bracket Finset.univ (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ))
    1 0 (1 / 2) <;> norm_num

#print axioms AtlasFormal.B131.concrete_metric_bracket

end AtlasFormal.B131

/-! ## B142 — the cubic form is the Christoffel data

Integrated from `.ultramath/smwtkiqjq/m6/B142.lean`.
-/
/-
B142: the volume metric's cubic form is its Christoffel data.

Finite matrix calculation. `volumeMetric` is the Hessian metric of `-log det`
on the positive-definite cone, in flat matrix coordinates. `volumeCubic` is
its algebraic first derivative, hence the third derivative of the potential.
No global positive-definiteness, geodesic, or conservation assertion is made.
-/

noncomputable section

open Matrix

namespace AtlasFormal.B142

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hessian metric of `ψ(G) = -log det G`, on symmetric directions `H,K`. -/
def volumeMetric (G H K : Matrix n n ℝ) : ℝ :=
  (G⁻¹ * H * G⁻¹ * K).trace

/-- Third derivative of `-log det`, in the order `D³ψ[G][H,K,L]`. -/
def volumeCubic (G H K L : Matrix n n ℝ) : ℝ :=
  - ((G⁻¹ * H * G⁻¹ * K * G⁻¹ * L).trace +
     (G⁻¹ * K * G⁻¹ * H * G⁻¹ * L).trace)

/-- The Christoffel direction in flat coordinates. -/
def volumeChristoffel (G H K : Matrix n n ℝ) : Matrix n n ℝ :=
  (-(1 / 2 : ℝ)) • (H * G⁻¹ * K + K * G⁻¹ * H)

/-- **B142, Koszul formula.** Pairing the Christoffel direction with a third
constant direction gives exactly one half of the cubic form. -/
theorem volumeMetric_christoffel (G H K L : Matrix n n ℝ) :
    volumeMetric G (volumeChristoffel G H K) L = (1 / 2 : ℝ) * volumeCubic G H K L := by
  simp only [volumeMetric, volumeChristoffel, volumeCubic, mul_add, add_mul,
    Matrix.mul_smul, Matrix.smul_mul, trace_add, trace_smul, Matrix.mul_assoc]
  ring

/-- Reversing a product of symmetric matrices and cyclically permuting its
trace swaps two adjacent symmetric directions in this trace word. -/
theorem trace_symmetric_swap (A H K L : Matrix n n ℝ)
    (hA : Aᵀ = A) (hH : Hᵀ = H) (hK : Kᵀ = K) (hL : Lᵀ = L) :
    (A * H * A * K * A * L).trace = (A * K * A * H * A * L).trace := by
  calc
    (A * H * A * K * A * L).trace = (A * H * A * K * A * L)ᵀ.trace :=
      (trace_transpose _).symm
    _ = (L * A * K * A * H * A).trace := by
      simp only [transpose_mul, hA, hH, hK, hL, Matrix.mul_assoc]
    _ = (A * K * A * H * A * L).trace := by
      simpa only [Matrix.mul_assoc] using trace_mul_comm L (A * K * A * H * A)

/-- **B142, displayed cubic trace.** On the symmetric cone the two trace
words agree, so the cubic form is `-2 tr(G⁻¹HG⁻¹KG⁻¹L)`. -/
theorem volumeCubic_eq_neg_two_trace (G H K L : Matrix n n ℝ)
    (hG : Gᵀ = G) (hH : Hᵀ = H) (hK : Kᵀ = K) (hL : Lᵀ = L) :
    volumeCubic G H K L = -2 * (G⁻¹ * H * G⁻¹ * K * G⁻¹ * L).trace := by
  have hA : G⁻¹ᵀ = G⁻¹ := by rw [transpose_nonsing_inv, hG]
  rw [volumeCubic, trace_symmetric_swap G⁻¹ H K L hA hH hK hL]
  ring

/-- A concrete non-flat two-dimensional direction. -/
def e00 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Concrete instance: the third derivative is nonzero at the identity. -/
theorem concrete_volumeCubic :
    volumeCubic 1 e00 e00 e00 = -2 := by
  norm_num [volumeCubic, e00, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- Concrete instance: the Christoffel pairing is one half, not one times,
the nonzero cubic form. -/
theorem concrete_volumeMetric_christoffel :
    volumeMetric 1 (volumeChristoffel 1 e00 e00) e00 = -1 := by
  norm_num [volumeMetric, volumeChristoffel, e00, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The literal formula `Γ = C` (without the card's factor `1/2`) is false. -/
theorem concrete_christoffel_ne_cubic :
    volumeMetric 1 (volumeChristoffel 1 e00 e00) e00 ≠ volumeCubic 1 e00 e00 e00 := by
  rw [concrete_volumeMetric_christoffel, concrete_volumeCubic]
  norm_num

#print axioms volumeMetric_christoffel
#print axioms trace_symmetric_swap
#print axioms volumeCubic_eq_neg_two_trace
#print axioms concrete_volumeCubic
#print axioms concrete_volumeMetric_christoffel
#print axioms concrete_christoffel_ne_cubic

end AtlasFormal.B142

/-! ## B180 — Fisher information is eight times the shape kinetic energy

Integrated from `.ultramath/smwtkiqjq/m9/B180.lean`.
-/
/-
B180 -- Fisher information and shape kinetic energy.

Finite algebraic kernel for an isospectral curve of real qutrit density
matrices. In the eigenbasis, the fixed eigenvalues are `p 0`, `p 1`, `p 2`
and the infinitesimal rotation has independent entries `a`, `b`, `c`.
The matrix `sld` below is the symmetric logarithmic derivative. The quantum
Fisher information is `tr (rho * L * L)`, while the shape speed is the sum of
the three gap-weighted squared angular velocities. We prove that the SLD
equation holds, that `FQ = 4 * shapeSpeed`, and hence `FQ = 8 * kineticEnergy`
for `kineticEnergy = shapeSpeed / 2`.

The fixed-spectrum (purely angular) hypothesis is additional to the card.
No assertion about varying eigenvalues, fidelity, Bures angles, or the
four-body geometric derivation is made here.
-/

noncomputable section

open Matrix

namespace AtlasB180

/-- A diagonal real qutrit state in its instantaneous eigenbasis. -/
def rho (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal p

/-- The antisymmetric generator of an infinitesimal orthogonal motion. -/
def angular (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, a, b; -a, 0, c; -b, -c, 0]

/-- The tangent to the isospectral density-matrix curve. -/
def tangent (p : Fin 3 → ℝ) (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  angular a b c * rho p - rho p * angular a b c

/-- The symmetric logarithmic derivative, entrywise in the eigenbasis. -/
def sld (p : Fin 3 → ℝ) (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,
      2 * a * (p 1 - p 0) / (p 0 + p 1),
      2 * b * (p 2 - p 0) / (p 0 + p 2);
    2 * a * (p 1 - p 0) / (p 0 + p 1),
      0,
      2 * c * (p 2 - p 1) / (p 1 + p 2);
    2 * b * (p 2 - p 0) / (p 0 + p 2),
      2 * c * (p 2 - p 1) / (p 1 + p 2),
      0]

/-- Quantum Fisher information in the SLD normalization `FQ = tr (ρ L²)`. -/
def fisher (p : Fin 3 → ℝ) (a b c : ℝ) : ℝ :=
  (rho p * sld p a b c * sld p a b c).trace

/-- The three-pair gap metric on purely angular qutrit tangents. -/
def shapeSpeed (p : Fin 3 → ℝ) (a b c : ℝ) : ℝ :=
  a ^ 2 * (p 1 - p 0) ^ 2 / (p 0 + p 1) +
    b ^ 2 * (p 2 - p 0) ^ 2 / (p 0 + p 2) +
      c ^ 2 * (p 2 - p 1) ^ 2 / (p 1 + p 2)

/-- Kinetic energy in the normalization `K = G(dot G, dot G) / 2`. -/
def kineticEnergy (p : Fin 3 → ℝ) (a b c : ℝ) : ℝ :=
  shapeSpeed p a b c / 2

/-- The constructed matrix really is an SLD: `2 dotρ = ρL + Lρ`.
Only positivity of the three eigenvalue sums is needed; the displayed
hypotheses give it for a full-rank state. -/
theorem tangent_eq_half_sld (p : Fin 3 → ℝ) (a b c : ℝ)
    (hp : ∀ i, 0 < p i) :
    (2 : ℝ) • tangent p a b c = rho p * sld p a b c + sld p a b c * rho p := by
  have h01 : p 0 + p 1 ≠ 0 := ne_of_gt (add_pos (hp 0) (hp 1))
  have h02 : p 0 + p 2 ≠ 0 := ne_of_gt (add_pos (hp 0) (hp 2))
  have h12 : p 1 + p 2 ≠ 0 := ne_of_gt (add_pos (hp 1) (hp 2))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tangent, angular, rho, sld, Matrix.mul_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_three] <;>
    field_simp [h01, h02, h12] <;> ring

#print axioms tangent_eq_half_sld

/-- The exact spectral trace computation: `FQ = 4G`. -/
theorem fisher_eq_four_shapeSpeed (p : Fin 3 → ℝ) (a b c : ℝ)
    (hp : ∀ i, 0 < p i) :
    fisher p a b c = 4 * shapeSpeed p a b c := by
  have h01 : p 0 + p 1 ≠ 0 := ne_of_gt (add_pos (hp 0) (hp 1))
  have h02 : p 0 + p 2 ≠ 0 := ne_of_gt (add_pos (hp 0) (hp 2))
  have h12 : p 1 + p 2 ≠ 0 := ne_of_gt (add_pos (hp 1) (hp 2))
  simp [fisher, shapeSpeed, rho, sld, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three]
  field_simp [h01, h02, h12]
  ring

#print axioms fisher_eq_four_shapeSpeed

/-- **B180 (finite isospectral normalization).** The SLD quantum Fisher
information is eight times the kinetic energy when `K = G/2`. -/
theorem fisher_eq_eight_kineticEnergy (p : Fin 3 → ℝ) (a b c : ℝ)
    (hp : ∀ i, 0 < p i) :
    fisher p a b c = 8 * kineticEnergy p a b c := by
  rw [fisher_eq_four_shapeSpeed p a b c hp]
  simp only [kineticEnergy]
  ring

#print axioms fisher_eq_eight_kineticEnergy

/-- A nondegenerate, full-rank, trace-one spectrum with three distinct entries. -/
def exampleP : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

theorem exampleP_pos (i : Fin 3) : 0 < exampleP i := by
  fin_cases i <;> norm_num [exampleP]

#print axioms exampleP_pos

/-- The concrete spectrum satisfies the card's `Tr G = 1` carry hypothesis. -/
theorem exampleP_trace : (rho exampleP).trace = 1 := by
  norm_num [rho, Matrix.trace, Fin.sum_univ_three, exampleP]

#print axioms exampleP_trace

/-- For angular velocity `a = 1`, `b = c = 0`, the speed is nonzero:
`G = (1/2-1/3)^2/(1/2+1/3) = 1/30`. -/
theorem example_shapeSpeed : shapeSpeed exampleP 1 0 0 = 1 / 30 := by
  norm_num [shapeSpeed, exampleP]

#print axioms example_shapeSpeed

/-- The same concrete motion has nonzero Fisher information `2/15`. -/
theorem example_fisher : fisher exampleP 1 0 0 = 2 / 15 := by
  rw [fisher_eq_four_shapeSpeed exampleP 1 0 0 exampleP_pos]
  norm_num [shapeSpeed, exampleP]

#print axioms example_fisher

/-- Numerical non-vacuous instance of the factor eight: both sides are `2/15`. -/
theorem example_factor_eight :
    fisher exampleP 1 0 0 = 8 * kineticEnergy exampleP 1 0 0 ∧
      kineticEnergy exampleP 1 0 0 = 1 / 60 := by
  constructor
  · rw [example_fisher]
    norm_num [kineticEnergy, shapeSpeed, exampleP]
  · norm_num [kineticEnergy, shapeSpeed, exampleP]

#print axioms example_factor_eight

end AtlasB180

/-! ## B89 — reciprocity breaks at first order, quadratically

Integrated from `.ultramath/smwtkiqjq/m11/B89.lean`.
-/
/-
B89 — Reciprocity breaks at first order; conductance sees it at second order.

Finite real algebraic model.  A symmetric matrix `A` is perturbed by an
antisymmetric matrix `B`: `M(b) = A + b • B`.  The two-terminal quadratic
response is the squared Frobenius trace `tr (M(b)ᵀ * M(b))`.  The exact
expansion has zero linear term and second-order coefficient
`tr (Bᵀ * B) = -tr (B * B)`, with no remainder.

This proves the finite trace/modulus-squared kernel.  It does not construct a
scattering matrix from Peierls phases, prove unitarity, or derive the physical
Onsager relation `S(b) = Sᵀ(-b)`; those are inputs to the card, not finite
algebra proved here.  The normalization is the unnormalised trace response;
if a conductance convention divides it by a positive constant, both stated
coefficients divide by that same constant.
-/

set_option autoImplicit false
noncomputable section

namespace AtlasFormal.B89

open Matrix

variable {n : Type*} [Fintype n]

/-- The linear coefficient in the quadratic trace response. -/
def linearTerm (A B : Matrix n n ℝ) : ℝ := (Aᵀ * B + Bᵀ * A).trace

/-- The quadratic coefficient in the quadratic trace response. -/
def quadraticTerm (B : Matrix n n ℝ) : ℝ := (Bᵀ * B).trace

/-- The unnormalised squared-modulus response to the perturbation `A + b • B`. -/
def response (A B : Matrix n n ℝ) (b : ℝ) : ℝ := ((A + b • B)ᵀ * (A + b • B)).trace

/-- The symmetric/antisymmetric trace pairing vanishes. -/
theorem trace_mul_eq_zero_of_symm_of_skew (A B : Matrix n n ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = -B) : (A * B).trace = 0 := by
  have ht : (A * B).trace = -(A * B).trace := by
    calc
      (A * B).trace = ((A * B)ᵀ).trace := (trace_transpose _).symm
      _ = (Bᵀ * Aᵀ).trace := by rw [transpose_mul]
      _ = ((-B) * A).trace := by rw [hA, hB]
      _ = -(B * A).trace := by rw [neg_mul, trace_neg]
      _ = -(A * B).trace := by rw [trace_mul_comm]
  linarith

#print axioms trace_mul_eq_zero_of_symm_of_skew

/-- Consequently the whole linear response coefficient is zero. -/
theorem linearTerm_eq_zero (A B : Matrix n n ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = -B) : linearTerm A B = 0 := by
  have hAB : (A * B).trace = 0 := trace_mul_eq_zero_of_symm_of_skew A B hA hB
  have hBA : (B * A).trace = 0 := by
    calc
      (B * A).trace = (A * B).trace := trace_mul_comm B A
      _ = 0 := hAB
  simp only [linearTerm, hA, hB, neg_mul, trace_add, trace_neg]
  rw [hAB, hBA]
  norm_num

#print axioms linearTerm_eq_zero

/-- Exact expansion, before imposing symmetry: the coefficient names are literal. -/
theorem response_expansion (A B : Matrix n n ℝ) (b : ℝ) :
    response A B b = (Aᵀ * A).trace + b * linearTerm A B +
      b ^ 2 * quadraticTerm B := by
  simp only [response, linearTerm, quadraticTerm, transpose_add, transpose_smul,
    add_mul, mul_add, trace_add, trace_smul, mul_smul_comm, smul_mul_assoc, smul_eq_mul]
  ring

#print axioms response_expansion

/-- The second coefficient is exactly `-tr(B²)` for an antisymmetric `B`. -/
theorem quadraticTerm_eq_neg_trace_sq (B : Matrix n n ℝ) (hB : Bᵀ = -B) :
    quadraticTerm B = -(B * B).trace := by
  simp only [quadraticTerm, hB, neg_mul, trace_neg]

#print axioms quadraticTerm_eq_neg_trace_sq

/-- **B89 exact finite kernel.**  The response has no linear term and no terms
beyond order two; its quadratic term is `-b² tr(B²)`.
-/
theorem response_eq_of_symm_of_skew (A B : Matrix n n ℝ) (b : ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = -B) :
    response A B b = (A * A).trace - b ^ 2 * (B * B).trace := by
  rw [response_expansion, linearTerm_eq_zero A B hA hB,
    quadraticTerm_eq_neg_trace_sq B hB, hA]
  ring

#print axioms response_eq_of_symm_of_skew

/-- Under the symmetry hypotheses the quadratic response is even in the field. -/
theorem response_neg (A B : Matrix n n ℝ) (b : ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = -B) :
    response A B (-b) = response A B b := by
  rw [response_expansion, response_expansion, linearTerm_eq_zero A B hA hB]
  ring

#print axioms response_neg

/-- The response's second coefficient is a sum of entrywise squares. -/
theorem quadraticTerm_eq_sum_sq (B : Matrix n n ℝ) :
    quadraticTerm B = ∑ i, ∑ j, (B i j) ^ 2 := by
  simp only [quadraticTerm, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    transpose_apply, pow_two]
  rw [Finset.sum_comm]

#print axioms quadraticTerm_eq_sum_sq

/-- The second coefficient is nonnegative. -/
theorem quadraticTerm_nonneg (B : Matrix n n ℝ) : 0 ≤ quadraticTerm B := by
  rw [quadraticTerm_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

#print axioms quadraticTerm_nonneg

/-- For a nonzero real perturbation the second coefficient is strictly positive. -/
theorem quadraticTerm_pos_of_ne_zero (B : Matrix n n ℝ) (hB : B ≠ 0) :
    0 < quadraticTerm B := by
  have hnonneg := quadraticTerm_nonneg B
  have hne : quadraticTerm B ≠ 0 := by
    intro hq
    have hs : ∑ i, ∑ j, (B i j) ^ 2 = 0 := by
      rw [← quadraticTerm_eq_sum_sq]
      exact hq
    have hentry : ∀ i j, B i j = 0 := by
      intro i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (B i j))).mp hs i
        (Finset.mem_univ i)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (B i j))).mp hi j (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp hj
    exact hB (Matrix.ext hentry)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

#print axioms quadraticTerm_pos_of_ne_zero

/-- A concrete symmetric unperturbed matrix. -/
def sampleA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

/-- A concrete nonzero antisymmetric perturbation. -/
def sampleB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The sample matrices satisfy the symmetry hypotheses. -/
theorem sampleA_symmetric : sampleAᵀ = sampleA := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sampleA, transpose_apply]

#print axioms sampleA_symmetric

/-- The sample perturbation is antisymmetric. -/
theorem sampleB_antisymmetric : sampleBᵀ = -sampleB := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sampleB, transpose_apply]

#print axioms sampleB_antisymmetric

/-- Non-vacuous numerical instance: response `5 + 2b²`, with zero linear term
and strictly positive second-order term `2 = -tr(sampleB²)`. -/
theorem sample_response (b : ℝ) :
    response sampleA sampleB b = 5 + 2 * b ^ 2 ∧
      linearTerm sampleA sampleB = 0 ∧ quadraticTerm sampleB = 2 := by
  constructor
  · simp [response, sampleA, sampleB, Matrix.trace_fin_two, Matrix.mul_apply,
      transpose_apply, Fin.sum_univ_two]
    ring
  constructor
  · simp [linearTerm, sampleA, sampleB, Matrix.trace_fin_two, Matrix.mul_apply,
      transpose_apply, Fin.sum_univ_two]
  · simp [quadraticTerm, sampleB, Matrix.trace_fin_two, Matrix.mul_apply,
      transpose_apply, Fin.sum_univ_two]
    norm_num

#print axioms sample_response

end AtlasFormal.B89

/-! ## B133 — the off-diagonal block counts the mixed channels

Integrated from `.ultramath/smwtkiqjq/m13/B133.lean`.
-/

noncomputable section

open Matrix

namespace AtlasB133

/-!
# B133: the off-diagonal block counts mixed channels

I work over `ℝ`, an explicit special case of the card's Hermitian setting.
The hypotheses of a diagonal factorization are kept explicit.  We prove the
block-projector defect identity, the identification of the two threshold
censuses, the Frobenius budget, and the rank count for a diagonal
factorization.  No claim about arbitrary Riesz projectors, infinite spaces, or
physical channels is made.
-/

/-- Number of occupation numbers in the transition window. -/
def transitionCount {ι : Type*} [Fintype ι] (ν : ι → ℝ) (ε : ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ ε ≤ ν i ∧ ν i ≤ 1 - ε).card

/-- Number of weights at least `a`. -/
def thresholdCount {ι : Type*} [Fintype ι] (w : ι → ℝ) (a : ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ a ≤ w i).card

/-- The census of squared singular values at the card's threshold. -/
def couplingCount {ι : Type*} [Fintype ι] (b : ι → ℝ) (ε : ℝ) : ℕ :=
  thresholdCount (fun i ↦ (b i) ^ 2) (ε * (1 - ε))

/-- Number of nonzero diagonal singular values. -/
def nonzeroCount {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ b i ≠ 0).card

/-- Squared Frobenius norm, without a choice of matrix norm instance. -/
def frobeniusSq {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (B i j) ^ 2

/-- The `(1,1)` block of idempotence is the exact coupling identity. -/
theorem blockProjector_defect {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (C : Matrix n n ℝ) (B : Matrix n m ℝ) (D : Matrix m m ℝ)
    (hP : Matrix.fromBlocks C B Bᵀ D * Matrix.fromBlocks C B Bᵀ D =
      Matrix.fromBlocks C B Bᵀ D) :
    C - C * C = B * Bᵀ := by
  have h := congrArg Matrix.toBlocks₁₁ hP
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h
  calc
    C - C * C = (C * C + B * Bᵀ) - C * C := by rw [h]
    _ = B * Bᵀ := by abel

#print axioms AtlasB133.blockProjector_defect

/-- Frobenius energy is the trace of the Gram matrix. -/
theorem frobeniusSq_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) :
    frobeniusSq B = (B * Bᵀ).trace := by
  simp [frobeniusSq, Matrix.trace, Matrix.mul_apply, pow_two]

#print axioms AtlasB133.frobeniusSq_eq_trace

/-- Hence the block defect has exactly the off-block Frobenius energy. -/
theorem blockProjector_frobenius_trace {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (C : Matrix n n ℝ) (B : Matrix n m ℝ) (D : Matrix m m ℝ)
    (hP : Matrix.fromBlocks C B Bᵀ D * Matrix.fromBlocks C B Bᵀ D =
      Matrix.fromBlocks C B Bᵀ D) :
    frobeniusSq B = (C - C * C).trace := by
  rw [blockProjector_defect C B D hP]
  exact frobeniusSq_eq_trace B

#print axioms AtlasB133.blockProjector_frobenius_trace

/-- For `ε ≤ 1/2`, the occupation window and coupling threshold agree. -/
theorem transition_window_iff_weight (ε x : ℝ) (hε : ε ≤ 1 / 2) :
    (ε ≤ x ∧ x ≤ 1 - ε) ↔ ε * (1 - ε) ≤ x * (1 - x) := by
  constructor
  · intro hx
    have hp : 0 ≤ (x - ε) * (1 - ε - x) :=
      mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
    nlinarith
  · intro hw
    constructor
    · by_contra h
      have hx : x < ε := lt_of_not_ge h
      have hp : 0 < (ε - x) * (1 - ε - x) :=
        mul_pos (sub_pos.mpr hx) (by linarith)
      nlinarith
    · by_contra h
      have hx : 1 - ε < x := lt_of_not_ge h
      have hp : 0 < (x - ε) * (x - (1 - ε)) :=
        mul_pos (by linarith) (by linarith)
      nlinarith

#print axioms AtlasB133.transition_window_iff_weight

/-- The two finite sets in the card therefore have the same cardinality. -/
theorem transitionCount_eq_census {ι : Type*} [Fintype ι]
    (ν : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2) :
    transitionCount ν ε = thresholdCount (fun i ↦ ν i * (1 - ν i)) (ε * (1 - ε)) := by
  classical
  unfold transitionCount thresholdCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact transition_window_iff_weight ε (ν i) hε

#print axioms AtlasB133.transitionCount_eq_census

/-- Rewrite the census using squared off-block singular values. -/
theorem transitionCount_eq_couplingCount {ι : Type*} [Fintype ι]
    (ν b : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hb : ∀ i, (b i) ^ 2 = ν i * (1 - ν i)) :
    transitionCount ν ε = couplingCount b ε := by
  rw [transitionCount_eq_census ν ε hε]
  unfold thresholdCount couplingCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb i]

#print axioms AtlasB133.transitionCount_eq_couplingCount

/-- A finite threshold census pays its threshold once per selected weight. -/
theorem thresholdCount_mul_le_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a : ℝ) (hw : ∀ i, 0 ≤ w i) :
    (thresholdCount w a : ℝ) * a ≤ ∑ i, w i := by
  classical
  have h : (∑ i, if a ≤ w i then (1 : ℝ) else 0) * a ≤ ∑ i, w i := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hia : a ≤ w i
    · simp [hia]
    · simpa [hia] using hw i
  simpa [thresholdCount] using h

#print axioms AtlasB133.thresholdCount_mul_le_sum

/-- Frobenius energy of a diagonal matrix is its squared-entry sum. -/
theorem frobeniusSq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    frobeniusSq (Matrix.diagonal b) = ∑ i, (b i) ^ 2 := by
  classical
  simp [frobeniusSq, Matrix.diagonal]

#print axioms AtlasB133.frobeniusSq_diagonal

/-- **B133 census budget**, in the card's normalization. -/
theorem diagonal_mixedCensus_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν b : ι → ℝ) (ε : ℝ)
    (hb : ∀ i, (b i) ^ 2 = ν i * (1 - ν i))
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    (transitionCount ν ε : ℝ) ≤
      frobeniusSq (Matrix.diagonal b) / (ε * (1 - ε)) := by
  have hden : 0 < ε * (1 - ε) := mul_pos hε0 (by linarith)
  apply (le_div_iff₀ hden).2
  have hw : ∀ i, 0 ≤ (b i) ^ 2 := fun i ↦ sq_nonneg (b i)
  calc
    (transitionCount ν ε : ℝ) * (ε * (1 - ε)) =
        (couplingCount b ε : ℝ) * (ε * (1 - ε)) := by
      rw [transitionCount_eq_couplingCount ν b ε hε hb]
    _ ≤ ∑ i, (b i) ^ 2 := thresholdCount_mul_le_sum _ _ hw
    _ = frobeniusSq (Matrix.diagonal b) := (frobeniusSq_diagonal b).symm

#print axioms AtlasB133.diagonal_mixedCensus_budget

/-- Rank of a diagonal matrix is its number of nonzero singular values. -/
theorem rank_diagonal_eq_nonzeroCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    (Matrix.diagonal b).rank = nonzeroCount b := by
  classical
  rw [Matrix.rank_diagonal]
  exact Fintype.card_subtype _

#print axioms AtlasB133.rank_diagonal_eq_nonzeroCount

/-- An explicit invertible diagonal factorization preserves that rank count.
Only rank invariance is used here; unitarity is a separate, stronger property. -/
theorem rank_eq_nonzeroCount_of_factorization {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (B U V : Matrix ι ι ℝ) (b : ι → ℝ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hB : B = U * Matrix.diagonal b * V) :
    B.rank = nonzeroCount b := by
  rw [hB, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU]
  exact rank_diagonal_eq_nonzeroCount b

#print axioms AtlasB133.rank_eq_nonzeroCount_of_factorization

/-- A diagonal family of two-by-two projectors, packaged as one block matrix. -/
def diagonalBlockProjector {ι : Type*} [DecidableEq ι]
    (ν b : ι → ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal ν) (Matrix.diagonal b)
    (Matrix.diagonal b)ᵀ (Matrix.diagonal fun i ↦ 1 - ν i)

/-- The diagonal block construction is symmetric. -/
theorem diagonalBlockProjector_transpose {ι : Type*} [DecidableEq ι]
    (ν b : ι → ℝ) :
    (diagonalBlockProjector ν b)ᵀ = diagonalBlockProjector ν b := by
  simp [diagonalBlockProjector, Matrix.fromBlocks_transpose]

#print axioms AtlasB133.diagonalBlockProjector_transpose

/-- The scalar relations `b² = ν(1-ν)` make the diagonal block family idempotent. -/
theorem diagonalBlockProjector_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν b : ι → ℝ) (hb : ∀ i, (b i) ^ 2 = ν i * (1 - ν i)) :
    diagonalBlockProjector ν b * diagonalBlockProjector ν b =
      diagonalBlockProjector ν b := by
  unfold diagonalBlockProjector
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · congr 1
    funext i
    have h := hb i
    nlinarith
  · congr 1
    funext i
    ring
  · congr 1
    funext i
    ring
  · congr 1
    funext i
    have h := hb i
    nlinarith

#print axioms AtlasB133.diagonalBlockProjector_idempotent

/-! ## A concrete two-channel instance, with rational data only. -/

def nuExample : Fin 2 → ℝ := ![1 / 2, 4 / 5]
def bExample : Fin 2 → ℝ := ![1 / 2, 2 / 5]
def CExample : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal nuExample
def BExample : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal bExample
def DExample : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun i ↦ 1 - nuExample i)
def PExample : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  diagonalBlockProjector nuExample bExample

/-- The example's occupations lie in `[0,1]`. -/
theorem nuExample_bounds : ∀ i, 0 ≤ nuExample i ∧ nuExample i ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [nuExample]

#print axioms AtlasB133.nuExample_bounds

/-- The example satisfies the exact projector/coupling scalar relation. -/
theorem bExample_spec : ∀ i, (bExample i) ^ 2 = nuExample i * (1 - nuExample i) := by
  intro i
  fin_cases i <;> norm_num [nuExample, bExample]

#print axioms AtlasB133.bExample_spec

/-- The concrete full matrix is idempotent. -/
theorem PExample_idempotent : PExample * PExample = PExample := by
  exact diagonalBlockProjector_idempotent nuExample bExample bExample_spec

#print axioms AtlasB133.PExample_idempotent

/-- The concrete full matrix is symmetric. -/
theorem PExample_transpose : PExampleᵀ = PExample := by
  exact diagonalBlockProjector_transpose nuExample bExample

#print axioms AtlasB133.PExample_transpose

/-- The concrete block projector realizes `C-C² = BBᵀ`. -/
theorem PExample_defect :
    CExample - CExample * CExample = BExample * BExampleᵀ := by
  apply blockProjector_defect CExample BExample DExample
  exact PExample_idempotent

#print axioms AtlasB133.PExample_defect

/-- Both example occupation numbers are mixed at threshold `ε = 1/5`. -/
theorem transitionCount_example : transitionCount nuExample (1 / 5) = 2 := by
  unfold transitionCount
  have h : (Finset.univ.filter fun i : Fin 2 ↦
      (1 / 5 : ℝ) ≤ nuExample i ∧ nuExample i ≤ 1 - 1 / 5) = Finset.univ := by
    ext i
    fin_cases i <;> norm_num [nuExample]
  rw [h]
  simp

#print axioms AtlasB133.transitionCount_example

/-- Equivalently, both squared singular values cross the card's threshold. -/
theorem couplingCount_example : couplingCount bExample (1 / 5) = 2 := by
  rw [← transitionCount_eq_couplingCount nuExample bExample (1 / 5)
    (by norm_num) bExample_spec]
  exact transitionCount_example

#print axioms AtlasB133.couplingCount_example

/-- Both example singular values are nonzero. -/
theorem nonzeroCount_example : nonzeroCount bExample = 2 := by
  unfold nonzeroCount
  have h : (Finset.univ.filter fun i : Fin 2 ↦ bExample i ≠ 0) = Finset.univ := by
    ext i
    fin_cases i <;> norm_num [bExample]
  rw [h]
  simp

#print axioms AtlasB133.nonzeroCount_example

/-- The off-diagonal block has rank two, witnessed by its diagonal factorization. -/
theorem rank_BExample : BExample.rank = 2 := by
  rw [BExample, rank_diagonal_eq_nonzeroCount, nonzeroCount_example]

#print axioms AtlasB133.rank_BExample

/-- The exact Frobenius energy of the two-channel example. -/
theorem frobeniusSq_BExample : frobeniusSq BExample = 41 / 100 := by
  rw [BExample, frobeniusSq_diagonal]
  norm_num [bExample, Fin.sum_univ_two]

#print axioms AtlasB133.frobeniusSq_BExample

/-- The concrete card inequality at `ε = 1/5`, before numerical simplification. -/
theorem example_mixedCensus_budget :
    (transitionCount nuExample (1 / 5) : ℝ) ≤
      frobeniusSq BExample / ((1 / 5 : ℝ) * (1 - 1 / 5)) := by
  exact diagonal_mixedCensus_budget nuExample bExample (1 / 5)
    bExample_spec (by norm_num) (by norm_num)

#print axioms AtlasB133.example_mixedCensus_budget

/-- The same concrete budget, evaluated: `2 ≤ 41/16`. -/
theorem example_mixedCensus_budget_evaluated :
    (transitionCount nuExample (1 / 5) : ℝ) ≤
      frobeniusSq BExample / ((1 / 5 : ℝ) * (1 - 1 / 5)) ∧
      (frobeniusSq BExample / ((1 / 5 : ℝ) * (1 - 1 / 5))) = 41 / 16 := by
  constructor
  · exact example_mixedCensus_budget
  · rw [frobeniusSq_BExample]
    norm_num

#print axioms AtlasB133.example_mixedCensus_budget_evaluated

end AtlasB133

/-! ## B155 — the shape-sphere Gram spectrum is diag(cos²ϑ, 1)

Integrated from `.ultramath/smwtkiqjq/m12/B155.lean`.
-/
/-
B155: the finite Gram kernel on the shape sphere.

The card's Gram matrix is formed from the two differential vectors
  dΦ(e_θ) = (cos θ cos φ, cos θ sin φ),
  dΦ(e_φ) = (-sin φ, cos φ).
These vectors are orthogonal, of squared lengths cos²θ and 1.  Thus the card's
spectrum {cos²θ, 1}, determinant cos²θ, and gap sin²θ are exact.

The abbreviated prompt also mentions the Gram matrix of two *unit* vectors
whose inner product is cos θ.  That is a different matrix, namely
  [[1, cos θ], [cos θ, 1]],
with spectrum {1 + cos θ, 1 - cos θ} and determinant sin²θ.  We prove this
corrected formula and explicit counterexamples to the abbreviated literal
formula at θ = π/2.  The standard coordinate vectors witness that the
counterexample really arises from two unit vectors.

No three-body equations of motion, global Riesz-projector transport, or
continuity of a projector family are asserted here.
-/

noncomputable section

open Matrix
open Real

namespace AtlasB155

/-- The differential of the declared coordinate map, with the two frame
vectors as columns. -/
def shapeD (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ * cos φ, -sin φ;
     cos θ * sin φ,  cos φ]

/-- The pullback/Gram operator `dΦᵀ dΦ`. -/
def shapeGram (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (shapeD θ φ)ᵀ * shapeD θ φ

/-- The positive difference between the two Gram eigenvalues. -/
def shapeGap (θ : ℝ) : ℝ := 1 - cos θ ^ 2

/-- **B155, Theorem 1 (finite algebraic part).** The Gram operator is exactly
`diag(cos²θ, 1)`; in particular, all azimuthal dependence cancels. -/
theorem shapeGram_eq (θ φ : ℝ) :
    shapeGram θ φ = !![cos θ ^ 2, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shapeGram, shapeD, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination cos θ ^ 2 * sin_sq_add_cos_sq φ
    | linear_combination sin_sq_add_cos_sq φ
    | ring
#print axioms AtlasB155.shapeGram_eq

/-- The determinant is the smaller diagonal entry `cos²θ`. -/
theorem shapeGram_det (θ φ : ℝ) :
    (shapeGram θ φ).det = cos θ ^ 2 := by
  rw [shapeGram_eq]
  simp [Matrix.det_fin_two]
#print axioms AtlasB155.shapeGram_det

/-- The trace is the sum `cos²θ + 1` of the two eigenvalues. -/
theorem shapeGram_trace (θ φ : ℝ) :
    (shapeGram θ φ).trace = cos θ ^ 2 + 1 := by
  rw [shapeGram_eq]
  simp [Matrix.trace, Fin.sum_univ_two]
#print axioms AtlasB155.shapeGram_trace

/-- **B155, exact spectrum.** The characteristic polynomial factors as
`(X - cos²θ)(X - 1)`, with no hypothesis on θ or φ. -/
theorem shapeGram_charpoly (θ φ : ℝ) :
    (shapeGram θ φ).charpoly =
      (Polynomial.X - Polynomial.C (cos θ ^ 2)) * (Polynomial.X - Polynomial.C 1) := by
  rw [Matrix.charpoly_fin_two, shapeGram_trace, shapeGram_det]
  simp only [map_add, map_one]
  ring
#print axioms AtlasB155.shapeGram_charpoly

/-- The coordinate basis vectors are eigenvectors for the two displayed
eigenvalues. -/
theorem shapeGram_coordinate_eigenvectors (θ φ : ℝ) :
    shapeGram θ φ *ᵥ ![1, 0] = (cos θ ^ 2) • ![1, 0] ∧
      shapeGram θ φ *ᵥ ![0, 1] = (1 : ℝ) • ![0, 1] := by
  rw [shapeGram_eq]
  constructor <;> ext i <;> fin_cases i <;>
    simp [Matrix.mulVec]
#print axioms AtlasB155.shapeGram_coordinate_eigenvectors

/-- The spectral gap has the card's exact expression `sin²θ`. -/
theorem shapeGap_eq_sin_sq (θ : ℝ) : shapeGap θ = sin θ ^ 2 := by
  unfold shapeGap
  linear_combination -(sin_sq_add_cos_sq θ)
#print axioms AtlasB155.shapeGap_eq_sin_sq

/-- At syzygy (`θ = π/2`) the spectrum is exactly `{0,1}` and the gap is `1`. -/
theorem syzygy_rank_drop (φ : ℝ) :
    shapeGram (π / 2) φ = !![0, 0; 0, 1] ∧ shapeGap (π / 2) = 1 := by
  constructor
  · rw [shapeGram_eq]
    simp
  · rw [shapeGap_eq_sin_sq]
    simp
#print axioms AtlasB155.syzygy_rank_drop

/-- At the equilateral pole the Gram matrix is the identity and the gap closes. -/
theorem pole_gap_closes_exact (φ : ℝ) :
    shapeGram 0 φ = 1 ∧ shapeGap 0 = 0 := by
  constructor
  · rw [shapeGram_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [shapeGap]
#print axioms AtlasB155.pole_gap_closes_exact

/-- A nondegenerate concrete instance: at `θ = π/3` the determinant is `1/4`
and the gap is `3/4`, independently of φ. -/
theorem concrete_nondegenerate (φ : ℝ) :
    (shapeGram (π / 3) φ).det = (1 : ℝ) / 4 ∧
      0 < (shapeGram (π / 3) φ).det ∧ shapeGap (π / 3) = (3 : ℝ) / 4 := by
  rw [shapeGram_det]
  norm_num [cos_pi_div_three, shapeGap]
#print axioms AtlasB155.concrete_nondegenerate

/-- The Gram matrix occurring in the abbreviated *two unit vectors* reading. -/
def twoUnitGram (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, c; c, 1]

/-- Correction to the abbreviated determinant claim: the determinant is
`1-c²`, not `c²`. -/
theorem twoUnitGram_det (c : ℝ) : (twoUnitGram c).det = 1 - c ^ 2 := by
  simp [twoUnitGram, Matrix.det_fin_two] ; ring
#print axioms AtlasB155.twoUnitGram_det

/-- Correction to the abbreviated spectrum claim: the eigenvalues are `1+c`
and `1-c`. -/
theorem twoUnitGram_charpoly (c : ℝ) :
    (twoUnitGram c).charpoly =
      (Polynomial.X - Polynomial.C (1 + c)) * (Polynomial.X - Polynomial.C (1 - c)) := by
  rw [Matrix.charpoly_fin_two]
  simp [twoUnitGram, Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two] ; ring
#print axioms AtlasB155.twoUnitGram_charpoly

/-- With `c = cos θ`, the corrected determinant is precisely `sin²θ`. -/
theorem twoUnitGram_det_cos (θ : ℝ) :
    (twoUnitGram (cos θ)).det = sin θ ^ 2 := by
  rw [twoUnitGram_det]
  linear_combination -(sin_sq_add_cos_sq θ)
#print axioms AtlasB155.twoUnitGram_det_cos

/-- Literal-formula counterexample at `θ = π/2`: the two-unit-vector Gram
determinant is `1`, whereas the abbreviated formula claims `0`. -/
theorem literal_unitGram_det_counterexample :
    (twoUnitGram (cos (π / 2))).det ≠ cos (π / 2) ^ 2 := by
  rw [twoUnitGram_det_cos]
  norm_num
#print axioms AtlasB155.literal_unitGram_det_counterexample

/-- The same point refutes the abbreviated characteristic-polynomial formula. -/
theorem literal_unitGram_charpoly_counterexample :
    (twoUnitGram (cos (π / 2))).charpoly ≠
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C (cos (π / 2) ^ 2)) := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ℝ)) h
  rw [twoUnitGram_charpoly] at h0
  norm_num at h0
#print axioms AtlasB155.literal_unitGram_charpoly_counterexample

/-- The Gram matrix of an arbitrary pair of real coordinate vectors. -/
def pairGram (u v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u ⬝ᵥ u, u ⬝ᵥ v; v ⬝ᵥ u, v ⬝ᵥ v]

/-- First standard coordinate vector. -/
def e0 : Fin 2 → ℝ := ![1, 0]

/-- Second standard coordinate vector. -/
def e1 : Fin 2 → ℝ := ![0, 1]

/-- A fully concrete unit-vector witness for the counterexample: `e0` and `e1`
are unit, their inner product is `cos(π/2)`, and their actual Gram determinant
is not `cos²(π/2)`. -/
theorem literal_unit_vector_counterexample :
    e0 ⬝ᵥ e0 = 1 ∧ e1 ⬝ᵥ e1 = 1 ∧ e0 ⬝ᵥ e1 = cos (π / 2) ∧
      (pairGram e0 e1).det ≠ cos (π / 2) ^ 2 := by
  have hgram : pairGram e0 e1 = twoUnitGram (cos (π / 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairGram, twoUnitGram, e0, e1, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [e0, dotProduct, Fin.sum_univ_two]
  · norm_num [e1, dotProduct, Fin.sum_univ_two]
  · simp [e0, e1, dotProduct, Fin.sum_univ_two]
  · rw [hgram]
    exact literal_unitGram_det_counterexample
#print axioms AtlasB155.literal_unit_vector_counterexample

end AtlasB155

/-! ## B202 — the books are blind to the orientation, the resolvent is not

Integrated from `.ultramath/smwtkiqjq/m4/B202.lean`.
-/
/-
Finite algebraic kernel for Atlas card B202.

The finite kernel is transpose-invariance of the algebraic symmetric part,
together with the exact resolvents of the card's two oriented 2 by 2 witnesses.
The rounded decimal in the displayed card is replaced by an exact modulus and
also disproved as a literal equality. The double-bracket flow, continuum
operators, and the norms of the card's other self-commutator/opposite books are
outside this kernel.
-/

noncomputable section
set_option autoImplicit false

namespace RelationalAtlas.B202

open Matrix

/-- The symmetric (orientation-blind) part of a square complex matrix. -/
def symmetricPart {n : Type} (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᵀ)

/-- Transposition does not change the symmetric part. -/
theorem symmetricPart_transpose {n : Type} (A : Matrix n n ℂ) :
    symmetricPart Aᵀ = symmetricPart A := by
  simp only [symmetricPart, transpose_transpose]
  rw [add_comm]

/-- Resolvent, using the nonsingular matrix inverse (which is zero outside the
invertible case, as usual in Mathlib). -/
def resolvent {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (z • (1 : Matrix n n ℂ) - A)⁻¹

/-- The resolvent of the transpose is the transpose of the resolvent. -/
theorem resolvent_transpose {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : ℂ) :
    resolvent Aᵀ z = (resolvent A z)ᵀ := by
  unfold resolvent
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp

/-- Exact inverse of a lower-triangular 2 by 2 complex matrix with nonzero
diagonal entries. -/
theorem lowerTriangular₂_inv (a b d : ℂ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (!![a, 0; b, d] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
      !![a⁻¹, 0; -b / (a * d), d⁻¹] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]
  field_simp [ha, hd]; ring

/-- The card's one-way coupling, with `0.3` represented exactly by `3/10`. -/
def oneWayL : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 0; 3 / 10, -2]

/-- The card's resolvent frequency `0.5i`. -/
def probeZ : ℂ := Complex.I / 2

/-- The exact common symmetric part of the card's two orientations. -/
theorem oneWay_symmetricPart :
    symmetricPart oneWayL = !![-1, 3 / 20; 3 / 20, -2] ∧
      symmetricPart oneWayLᵀ = !![-1, 3 / 20; 3 / 20, -2] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [symmetricPart, oneWayL, Matrix.transpose_apply]

/-- Exact resolvent matrix for the forward-oriented witness. -/
theorem oneWay_resolvent :
    resolvent oneWayL probeZ =
      !![(1 + Complex.I / 2)⁻¹, 0;
        (3 / 10) / ((1 + Complex.I / 2) * (2 + Complex.I / 2)),
        (2 + Complex.I / 2)⁻¹] := by
  have ha : (1 + Complex.I / 2 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hd : (2 + Complex.I / 2 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hshift : probeZ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - oneWayL =
      !![1 + Complex.I / 2, 0; -(3 / 10), 2 + Complex.I / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [probeZ, oneWayL] <;> ring
  unfold resolvent
  rw [hshift, lowerTriangular₂_inv _ _ _ ha hd]
  simp

/-- Exact resolvent matrix for the reverse orientation: the nonzero channel
has moved from `(1,0)` to `(0,1)`. -/
theorem oneWay_transpose_resolvent :
    resolvent oneWayLᵀ probeZ =
      !![(1 + Complex.I / 2)⁻¹,
        (3 / 10) / ((1 + Complex.I / 2) * (2 + Complex.I / 2));
        0, (2 + Complex.I / 2)⁻¹] := by
  rw [resolvent_transpose, oneWay_resolvent]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The exact nonzero reverse-channel entry, after clearing the complex
 denominators. -/
def crossEntry : ℂ := (42 : ℂ) / 425 - (36 : ℂ) / 425 * Complex.I

/-- `R₂₁(i/2)` for the forward orientation is exactly `(42-36i)/425`. -/
theorem oneWay_resolvent_lower :
    resolvent oneWayL probeZ 1 0 = crossEntry := by
  rw [oneWay_resolvent]
  norm_num [crossEntry, Complex.ext_iff, Complex.div_re, Complex.div_im,
    Complex.normSq_apply]

/-- Squared modulus of the nonzero channel, with no rounded decimal. -/
theorem crossEntry_normSq :
    Complex.normSq (resolvent oneWayL probeZ 1 0) = (612 : ℝ) / 36125 := by
  rw [oneWay_resolvent_lower]
  norm_num [crossEntry, Complex.normSq_apply]

/-- The corrected exact modulus is `6*sqrt(85)/425`. -/
theorem crossEntry_norm :
    ‖resolvent oneWayL probeZ 1 0‖ = 6 * Real.sqrt 85 / 425 := by
  rw [Complex.norm_def, crossEntry_normSq]
  have h85 : Real.sqrt 85 ^ 2 = (85 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs : (6 * Real.sqrt 85 / 425) ^ 2 = (612 : ℝ) / 36125 := by
    calc
      (6 * Real.sqrt 85 / 425) ^ 2 = 36 * Real.sqrt 85 ^ 2 / 425 ^ 2 := by ring
      _ = (612 : ℝ) / 36125 := by rw [h85]; norm_num
  rw [← hs, Real.sqrt_sq (by positivity)]

/-- The card's displayed decimal is a rounding, not an exact equality:
squaring the claimed decimal contradicts the exact squared modulus. -/
theorem rounded_decimal_not_exact :
    ‖resolvent oneWayL probeZ 1 0‖ ≠ (0.130158 : ℝ) := by
  intro h
  have hs : (612 : ℝ) / 36125 = (0.130158 : ℝ) ^ 2 := by
    calc
      (612 : ℝ) / 36125 = Complex.normSq (resolvent oneWayL probeZ 1 0) :=
        crossEntry_normSq.symm
      _ = ‖resolvent oneWayL probeZ 1 0‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = (0.130158 : ℝ) ^ 2 := by rw [h]
  norm_num at hs

/-- The two orientations really have different resolvent matrices. -/
theorem oneWay_resolvents_differ :
    resolvent oneWayL probeZ ≠ resolvent oneWayLᵀ probeZ := by
  have hq : crossEntry ≠ 0 := by
    intro h
    have hs := crossEntry_normSq
    rw [oneWay_resolvent_lower, h] at hs
    norm_num at hs
  intro h
  have h10 := congrFun (congrFun h 1) 0
  rw [oneWay_resolvent_lower] at h10
  have ht : resolvent oneWayLᵀ probeZ 1 0 = 0 := by
    rw [oneWay_transpose_resolvent]
    rfl
  rw [ht] at h10
  exact hq h10

/-- Non-vacuous concrete B202 kernel: identical symmetric parts, different
resolvents, and a nonzero channel witnessed by its exact squared modulus. -/
theorem B202_concrete_kernel :
    symmetricPart oneWayL = symmetricPart oneWayLᵀ ∧
      resolvent oneWayL probeZ ≠ resolvent oneWayLᵀ probeZ ∧
      resolvent oneWayL probeZ 1 0 ≠ resolvent oneWayL probeZ 0 1 := by
  refine ⟨(symmetricPart_transpose oneWayL).symm, oneWay_resolvents_differ, ?_⟩
  rw [oneWay_resolvent_lower, oneWay_resolvent]
  intro h
  have hr := congrArg Complex.re h
  norm_num [crossEntry] at hr

end RelationalAtlas.B202

#print axioms RelationalAtlas.B202.symmetricPart_transpose
#print axioms RelationalAtlas.B202.resolvent_transpose
#print axioms RelationalAtlas.B202.lowerTriangular₂_inv
#print axioms RelationalAtlas.B202.oneWay_symmetricPart
#print axioms RelationalAtlas.B202.oneWay_resolvent
#print axioms RelationalAtlas.B202.oneWay_transpose_resolvent
#print axioms RelationalAtlas.B202.oneWay_resolvent_lower
#print axioms RelationalAtlas.B202.crossEntry_normSq
#print axioms RelationalAtlas.B202.crossEntry_norm
#print axioms RelationalAtlas.B202.rounded_decimal_not_exact
#print axioms RelationalAtlas.B202.oneWay_resolvents_differ
#print axioms RelationalAtlas.B202.B202_concrete_kernel

/-! ## B78 — the finite spectral calculus behind the contour

Integrated from `.ultramath/smwtkiqjq/m8/B78.lean`.
-/
/-
B78: finite spectral/Lagrange calculus for a diagonalizable matrix.

The labels `ι` index distinct eigenvalues, while `e : n → ι` groups diagonal
coordinates into sectors.  Thus repeated eigenvalues are allowed.  The two
matrices `S`, `T` are assumed to be two-sided inverses.

This file proves the finite algebraic kernel, not the complex contour integral
or the defective/Jordan case of the displayed card.
-/

namespace RelationalAtlas.B78

open Matrix Polynomial
open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Indicator of the coordinates in one eigenvalue sector. -/
def sectorIndicator (e : n → ι) (i : ι) (k : n) : ℂ :=
  if e k = i then 1 else 0

/-- The diagonal projector onto one eigenvalue sector. -/
def sectorProjector (e : n → ι) (i : ι) : Matrix n n ℂ :=
  diagonal (sectorIndicator e i)

/-- The sector projector in the original basis. -/
def spectralProjector (S T : Matrix n n ℂ) (e : n → ι) (i : ι) : Matrix n n ℂ :=
  S * sectorProjector e i * T

@[simp] theorem sectorProjector_mul_self (e : n → ι) (i : ι) :
    sectorProjector e i * sectorProjector e i = sectorProjector e i := by
  rw [sectorProjector, diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : e k = i <;> simp [sectorIndicator, h]

#print axioms RelationalAtlas.B78.sectorProjector_mul_self

theorem sectorProjector_mul_of_ne (e : n → ι) {i j : ι} (hij : i ≠ j) :
    sectorProjector e i * sectorProjector e j = 0 := by
  rw [sectorProjector, sectorProjector, diagonal_mul_diagonal]
  have hzero : (fun k => sectorIndicator e i k * sectorIndicator e j k) = 0 := by
    funext k
    by_cases hki : e k = i
    · by_cases hkj : e k = j
      · exact (hij (hki.symm.trans hkj)).elim
      · simp [sectorIndicator, hki, hkj, hij]
    · simp [sectorIndicator, hki]
  rw [hzero, diagonal_zero']

#print axioms RelationalAtlas.B78.sectorProjector_mul_of_ne

@[simp] theorem spectralProjector_mul_self (S T : Matrix n n ℂ) (hTS : T * S = 1)
    (e : n → ι) (i : ι) :
    spectralProjector S T e i * spectralProjector S T e i = spectralProjector S T e i := by
  simp only [spectralProjector, mul_assoc]
  rw [← mul_assoc T S (sectorProjector e i * T), hTS, one_mul]
  rw [← mul_assoc (sectorProjector e i) (sectorProjector e i) T,
    sectorProjector_mul_self]

#print axioms RelationalAtlas.B78.spectralProjector_mul_self

theorem spectralProjector_mul_of_ne (S T : Matrix n n ℂ) (hTS : T * S = 1)
    (e : n → ι) {i j : ι} (hij : i ≠ j) :
    spectralProjector S T e i * spectralProjector S T e j = 0 := by
  simp only [spectralProjector, mul_assoc]
  rw [← mul_assoc T S (sectorProjector e j * T), hTS, one_mul]
  rw [← mul_assoc (sectorProjector e i) (sectorProjector e j) T,
    sectorProjector_mul_of_ne e hij, zero_mul, mul_zero]

#print axioms RelationalAtlas.B78.spectralProjector_mul_of_ne

@[simp] theorem sum_sectorProjector (e : n → ι) : ∑ i, sectorProjector e i = 1 := by
  ext k l
  by_cases hkl : k = l
  · subst l
    simp [Matrix.sum_apply, sectorProjector, sectorIndicator]
  · simp [Matrix.sum_apply, sectorProjector, diagonal_apply, hkl]

#print axioms RelationalAtlas.B78.sum_sectorProjector

@[simp] theorem sum_spectralProjector (S T : Matrix n n ℂ) (hST : S * T = 1) (e : n → ι) :
    ∑ i, spectralProjector S T e i = 1 := by
  calc
    ∑ i, spectralProjector S T e i = S * (∑ i, sectorProjector e i) * T := by
      simp only [spectralProjector, Finset.mul_sum, Finset.sum_mul]
    _ = 1 := by rw [sum_sectorProjector, mul_one, hST]

#print axioms RelationalAtlas.B78.sum_spectralProjector

/-- Conjugation respects natural powers; both inverse identities are explicit. -/
theorem conjugate_pow (S T D : Matrix n n ℂ) (hST : S * T = 1) (hTS : T * S = 1) (k : ℕ) :
    (S * D * T) ^ k = S * D ^ k * T := by
  induction k with
  | zero => simp [hST]
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc T S (D * T), hTS, one_mul]

#print axioms RelationalAtlas.B78.conjugate_pow

/-- Polynomial evaluation is compatible with the diagonalizing conjugation. -/
theorem aeval_conjugate (S T D : Matrix n n ℂ) (hST : S * T = 1) (hTS : T * S = 1)
    (p : ℂ[X]) : aeval (S * D * T) p = S * aeval D p * T := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, add_mul]
  | monomial k a =>
      rw [aeval_monomial, aeval_monomial, conjugate_pow S T D hST hTS]
      simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, mul_assoc,
        one_mul]

#print axioms RelationalAtlas.B78.aeval_conjugate

/-- Polynomial evaluation of a diagonal matrix is entrywise scalar evaluation. -/
theorem aeval_diagonal (v : n → ℂ) (p : ℂ[X]) :
    aeval (diagonal v) p = diagonal (fun k => p.eval (v k)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext k l
      by_cases hkl : k = l <;> simp [diagonal_apply, hkl]
  | monomial k a =>
      rw [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
      congr 1
      funext j
      simp [Polynomial.eval_monomial]

#print axioms RelationalAtlas.B78.aeval_diagonal

/-- A diagonal matrix is the sum of its sector values times the sector projectors. -/
theorem diagonal_comp_eq_sum_smul_sectorProjector (e : n → ι) (r : ι → ℂ) :
    diagonal (fun k => r (e k)) = ∑ i, r i • sectorProjector e i := by
  ext k l
  by_cases hkl : k = l
  · subst l
    simp [Matrix.sum_apply, sectorProjector, sectorIndicator]
  · simp [Matrix.sum_apply, sectorProjector, diagonal_apply, hkl]

#print axioms RelationalAtlas.B78.diagonal_comp_eq_sum_smul_sectorProjector

/-- **B78 (polynomial spectral decomposition).**  No simplicity of the spectrum is
needed for this identity: `e` can assign many diagonal coordinates to one label. -/
theorem aeval_spectral_decomposition (S T : Matrix n n ℂ) (hST : S * T = 1) (hTS : T * S = 1)
    (lam : ι → ℂ) (e : n → ι) (p : ℂ[X]) :
    aeval (S * diagonal (fun k => lam (e k)) * T) p =
      ∑ i, p.eval (lam i) • spectralProjector S T e i := by
  rw [aeval_conjugate S T _ hST hTS, aeval_diagonal]
  rw [diagonal_comp_eq_sum_smul_sectorProjector (n := n) e (fun i => p.eval (lam i))]
  simp only [spectralProjector, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]

#print axioms RelationalAtlas.B78.aeval_spectral_decomposition

/-- The Lagrange interpolant of an arbitrary function on a finite, distinctly
labelled spectrum.  Nothing holomorphic is needed for this finite algebraic step. -/
def spectralInterpolant (lam : ι → ℂ) (f : ℂ → ℂ) : ℂ[X] :=
  Lagrange.interpolate Finset.univ lam (fun i => f (lam i))

@[simp] theorem eval_spectralInterpolant (lam : ι → ℂ) (hlam : Function.Injective lam)
    (f : ℂ → ℂ) (i : ι) : (spectralInterpolant lam f).eval (lam i) = f (lam i) := by
  apply Lagrange.eval_interpolate_at_node
  · exact hlam.injOn
  · exact Finset.mem_univ i

#print axioms RelationalAtlas.B78.eval_spectralInterpolant

/-- **B78 (any function on the spectrum).**  For every `f : ℂ → ℂ`, an explicit
polynomial agrees with `f` at every spectral value and its matrix evaluation is
the advertised sum over spectral projectors. -/
theorem arbitrary_function_spectral_calculus (S T : Matrix n n ℂ) (hST : S * T = 1)
    (hTS : T * S = 1) (lam : ι → ℂ) (hlam : Function.Injective lam) (e : n → ι) (f : ℂ → ℂ) :
    ∃ p : ℂ[X], (∀ i, p.eval (lam i) = f (lam i)) ∧
      aeval (S * diagonal (fun k => lam (e k)) * T) p =
        ∑ i, f (lam i) • spectralProjector S T e i := by
  refine ⟨spectralInterpolant lam f, eval_spectralInterpolant lam hlam f, ?_⟩
  rw [aeval_spectral_decomposition S T hST hTS]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_spectralInterpolant lam hlam]

#print axioms RelationalAtlas.B78.arbitrary_function_spectral_calculus

/-- **The block-projector case.**  The spectral projector itself is obtained by a
polynomial equal to one on its own sector and zero on every other sector. -/
theorem spectralProjector_is_polynomial (S T : Matrix n n ℂ) (hST : S * T = 1)
    (hTS : T * S = 1) (lam : ι → ℂ) (hlam : Function.Injective lam) (e : n → ι) (j : ι) :
    ∃ p : ℂ[X], (∀ i, p.eval (lam i) = if lam i = lam j then 1 else 0) ∧
      aeval (S * diagonal (fun k => lam (e k)) * T) p = spectralProjector S T e j := by
  obtain ⟨p, hp, hsp⟩ := arbitrary_function_spectral_calculus S T hST hTS lam hlam e
    (fun z => if z = lam j then 1 else 0)
  refine ⟨p, hp, ?_⟩
  rw [hsp]
  have hsum :
      (∑ i, (if lam i = lam j then (1 : ℂ) else 0) • spectralProjector S T e i) =
        ∑ i, (if i = j then (1 : ℂ) else 0) • spectralProjector S T e i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i = j
    · subst i
      simp
    · have hl : lam i ≠ lam j := fun h => hij (hlam h)
      simp [hij, hl]
  rw [hsum]
  simp

#print axioms RelationalAtlas.B78.spectralProjector_is_polynomial

/-- The `f(z) = z` case: the diagonalized operator is its eigenvalue-weighted sum
of spectral projectors. -/
theorem diagonalized_eq_eigenvalue_sum (S T : Matrix n n ℂ) (hST : S * T = 1)
    (hTS : T * S = 1) (lam : ι → ℂ) (e : n → ι) :
    S * diagonal (fun k => lam (e k)) * T = ∑ i, lam i • spectralProjector S T e i := by
  simpa using aeval_spectral_decomposition S T hST hTS lam e X

#print axioms RelationalAtlas.B78.diagonalized_eq_eigenvalue_sum

/-! ## A concrete, non-diagonal two-spectrum instance -/

def exampleS : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
def exampleT : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 0, 1]
def exampleLam : Fin 2 → ℂ := ![1, 2]
def exampleE : Fin 2 → Fin 2 := id
def exampleA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 2]

@[simp] theorem exampleS_mul_exampleT : exampleS * exampleT = 1 := by
  rw [Matrix.one_fin_two]
  norm_num [exampleS, exampleT, Matrix.mul_fin_two]

#print axioms RelationalAtlas.B78.exampleS_mul_exampleT

@[simp] theorem exampleT_mul_exampleS : exampleT * exampleS = 1 := by
  rw [Matrix.one_fin_two]
  norm_num [exampleS, exampleT, Matrix.mul_fin_two]

#print axioms RelationalAtlas.B78.exampleT_mul_exampleS

theorem exampleLam_injective : Function.Injective exampleLam := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleLam]

#print axioms RelationalAtlas.B78.exampleLam_injective

/-- The explicit matrix really has the diagonalization assumed in the general theorem. -/
theorem exampleA_factorization :
    exampleA = exampleS * diagonal (fun k => exampleLam (exampleE k)) * exampleT := by
  norm_num [exampleA, exampleS, exampleT, exampleLam, exampleE,
    Matrix.diagonal_fin_two, Matrix.mul_fin_two]

#print axioms RelationalAtlas.B78.exampleA_factorization

theorem exampleA_offdiagonal_ne_zero : exampleA 0 1 ≠ 0 := by
  norm_num [exampleA]

#print axioms RelationalAtlas.B78.exampleA_offdiagonal_ne_zero

@[simp] theorem example_spectralProjector_zero :
    spectralProjector exampleS exampleT exampleE 0 = !![1, -1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralProjector, sectorProjector, sectorIndicator, exampleS, exampleT, exampleE,
      Matrix.diagonal_fin_two, Matrix.mul_fin_two]

#print axioms RelationalAtlas.B78.example_spectralProjector_zero

@[simp] theorem example_spectralProjector_one :
    spectralProjector exampleS exampleT exampleE 1 = !![0, 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spectralProjector, sectorProjector, sectorIndicator, exampleS, exampleT, exampleE,
      Matrix.diagonal_fin_two, Matrix.mul_fin_two]

#print axioms RelationalAtlas.B78.example_spectralProjector_one

/-- This instance uses the general spectral decomposition, rather than just checking it by hand. -/
theorem example_square_calculus :
    aeval exampleA ((X : ℂ[X]) ^ 2) =
      (1 : ℂ) ^ 2 • spectralProjector exampleS exampleT exampleE 0 +
      (2 : ℂ) ^ 2 • spectralProjector exampleS exampleT exampleE 1 := by
  rw [exampleA_factorization]
  rw [aeval_spectral_decomposition exampleS exampleT exampleS_mul_exampleT exampleT_mul_exampleS]
  simp [Fin.sum_univ_two, exampleLam]

#print axioms RelationalAtlas.B78.example_square_calculus

/-- Numerically, the square is `!![1,3;0,4]`, exactly the weighted sum above. -/
theorem example_square_entries : aeval exampleA ((X : ℂ[X]) ^ 2) = !![1, 3; 0, 4] := by
  rw [map_pow, aeval_X, pow_two, exampleA, Matrix.mul_fin_two]
  norm_num

#print axioms RelationalAtlas.B78.example_square_entries

end
end RelationalAtlas.B78

/-! ## B72 — the projector derivative is the off-block resolvent

Integrated from `.ultramath/smwtkiqjq/m3/B72.lean`.
-/
/-
B72 — The gap is a stiffness.

Finite spectral-basis kernel. A Boolean function labels the inside of the
projector, `eig` is the real diagonal Hermitian operator, and `response` is
its off-block linear response. We prove the differentiated projector and
commutation equations, identify the two real Hermitian directions attached to
every complex off-block entry, and prove the exact reciprocal-gap Frobenius
norm estimate. The last section gives a two-dimensional witness.

No contour integral or global smooth dependence of a spectral projector is
used. The word `response` therefore denotes the algebraic differential in a
fixed eigenbasis; the analytic theorem that the contour-defined projector has
this differential is outside this finite algebraic kernel.
-/

set_option autoImplicit false
noncomputable section

namespace RelationalAtlas.B72

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signed gap `λinside - λoutside`; its value on diagonal blocks is
irrelevant. -/
def signedGap (inside : n → Bool) (eig : n → ℝ) (i j : n) : ℝ :=
  if inside i = true then eig i - eig j else eig j - eig i

/-- The displayed off-block response in the eigenbasis. -/
def response (inside : n → Bool) (eig : n → ℝ) (H : Matrix n n ℂ) :
    Matrix n n ℂ := fun i j =>
  if inside i = inside j then 0 else H i j / (signedGap inside eig i j : ℂ)

/-- The diagonal projector onto the indices labelled `true`. -/
def blockProjector (inside : n → Bool) : Matrix n n ℂ :=
  diagonal (fun i => if inside i = true then 1 else 0)

/-- The diagonal Hermitian operator whose inside/outside gaps are used. -/
def baseOperator (eig : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => (eig i : ℂ))

/-- Every off-block gap is nonzero when all inside/outside eigenvalues differ. -/
theorem signedGap_ne_zero (inside : n → Bool) (eig : n → ℝ)
    (hgap : ∀ i j, inside i ≠ inside j → eig i ≠ eig j)
    {i j : n} (hij : inside i ≠ inside j) :
    signedGap inside eig i j ≠ 0 := by
  cases hi : inside i <;> cases hj : inside j <;>
    simp_all [signedGap, sub_ne_zero]

/-- Reversing an off-block pair does not change the inside-minus-outside sign. -/
theorem signedGap_swap (inside : n → Bool) (eig : n → ℝ) {i j : n}
    (hij : inside i ≠ inside j) :
    signedGap inside eig j i = signedGap inside eig i j := by
  cases hi : inside i <;> cases hj : inside j <;> simp_all [signedGap]

/-- The response is supported exactly on the off-diagonal blocks. -/
theorem response_apply_of_same (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) {i j : n} (hij : inside i = inside j) :
    response inside eig H i j = 0 := by
  simp [response, hij]

/-- The response preserves the Hermitian tangent space. -/
theorem response_isHermitian (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (response inside eig H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : inside i = inside j
  · change star (if inside j = inside i then 0
      else H j i / (signedGap inside eig j i : ℂ)) =
        if inside i = inside j then 0
        else H i j / (signedGap inside eig i j : ℂ)
    rw [if_pos hij.symm, if_pos hij, star_zero]
  · have hji : inside j ≠ inside i := Ne.symm hij
    change star (if inside j = inside i then 0
      else H j i / (signedGap inside eig j i : ℂ)) =
        if inside i = inside j then 0
        else H i j / (signedGap inside eig i j : ℂ)
    rw [if_neg hji, if_neg hij, signedGap_swap inside eig hij]
    rw [show star (H j i / (signedGap inside eig i j : ℂ)) =
      star (H j i) / (signedGap inside eig i j : ℂ) by simp]
    rw [hH.apply]

/-- The real submodule of Hermitian complex matrices. -/
def hermitianSubmodule (n : Type*) [DecidableEq n] :
    Submodule ℝ (Matrix n n ℂ) where
  carrier := {H | H.IsHermitian}
  zero_mem' := by
    change (0 : Matrix n n ℂ).IsHermitian
    exact Matrix.isHermitian_zero
  add_mem' := by
    intro H K hH hK
    change H.IsHermitian at hH
    change K.IsHermitian at hK
    change (H + K).IsHermitian
    exact hH.add hK
  smul_mem' := by
    intro r H hH
    change H.IsHermitian at hH
    change (r • H).IsHermitian
    apply Matrix.IsHermitian.ext
    intro i j
    simp [hH.apply]

/-- The algebraic response as a complex-linear map on matrices. -/
def responseLinearMap (inside : n → Bool) (eig : n → ℝ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := response inside eig
  map_add' := by
    intro H K
    ext i j
    by_cases hij : inside i = inside j <;>
      simp [response, hij, add_div]
  map_smul' := by
    intro z H
    ext i j
    by_cases hij : inside i = inside j <;>
      simp [response, hij, mul_div_assoc]

/-- The response restricted to the real Hermitian tangent space. -/
def hermitianResponse (inside : n → Bool) (eig : n → ℝ) :
    hermitianSubmodule n →ₗ[ℝ] hermitianSubmodule n where
  toFun H := ⟨response inside eig H.1, by
    have hH : H.1.IsHermitian := by
      simpa [hermitianSubmodule] using H.2
    simpa [hermitianSubmodule] using response_isHermitian inside eig H.1 hH⟩
  map_add' := by
    intro H K
    apply Subtype.ext
    exact (responseLinearMap inside eig).map_add H.1 K.1
  map_smul' := by
    intro r H
    apply Subtype.ext
    change response inside eig (r • H.1) = r • response inside eig H.1
    ext i j
    by_cases hij : inside i = inside j <;>
      simp [response, hij, mul_div_assoc]

/-- A Hermitian matrix with one complex off-block parameter `z`; the opposite
entry is `star z`. These are the two real directions for each unordered pair. -/
def pairTangent (a b : n) (z : ℂ) : Matrix n n ℂ :=
  single a b z + single b a (star z)

theorem pairTangent_isHermitian (a b : n) (z : ℂ) :
    (pairTangent a b z).IsHermitian := by
  rw [Matrix.IsHermitian, pairTangent, conjTranspose_add,
    conjTranspose_single, conjTranspose_single, star_star, add_comm]

/-- The real two-dimensional family of Hermitian tangents at `(a,b)`. -/
def pairDirections (a b : n) : ℂ →ₗ[ℝ] hermitianSubmodule n where
  toFun z := ⟨pairTangent a b z, by
    simpa [hermitianSubmodule] using pairTangent_isHermitian a b z⟩
  map_add' := by
    intro z w
    apply Subtype.ext
    simp [pairTangent, single_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro r z
    apply Subtype.ext
    simp [pairTangent, Matrix.smul_apply, smul_add]

/-- Different off-block parameters give different Hermitian tangents. -/
theorem pairDirections_injective {a b : n} (hab : a ≠ b) :
    Function.Injective (pairDirections a b) := by
  intro z w hzw
  have h := congrArg (fun M : hermitianSubmodule n => M.1 a b) hzw
  simpa [pairDirections, pairTangent, Matrix.single_apply, hab, Ne.symm hab] using h

/-- The two real directions are genuinely nonzero when `a ≠ b`. -/
theorem pairDirections_one_ne_zero {a b : n} (hab : a ≠ b) :
    pairDirections a b 1 ≠ 0 := by
  intro h
  have hz : (1 : ℂ) = 0 := by
    apply pairDirections_injective hab
    simpa using h
  exact one_ne_zero hz

/-- Every complex off-block tangent is an eigenvector of the response, with
signed eigenvalue `(λinside - λoutside)⁻¹`. Taking `z = 1` and `z = I`
exhibits its two real dimensions; the singular value is the absolute value. -/
theorem hermitianResponse_pairDirections (inside : n → Bool) (eig : n → ℝ)
    {a b : n} (ha : inside a = true) (hb : inside b = false) (z : ℂ) :
    hermitianResponse inside eig (pairDirections a b z) =
      (signedGap inside eig a b)⁻¹ • pairDirections a b z := by
  apply Subtype.ext
  ext i j
  have hab : a ≠ b := by
    intro h
    subst b
    simp [ha] at hb
  have hcross : inside a ≠ inside b := by simp [ha, hb]
  have hswap : signedGap inside eig b a = signedGap inside eig a b :=
    signedGap_swap inside eig hcross
  by_cases habij : a = i ∧ b = j
  · rcases habij with ⟨hi, hj⟩
    subst i
    subst j
    simp [hermitianResponse, pairDirections, response, pairTangent,
      Matrix.single_apply, ha, hb, hab, Ne.symm hab, signedGap,
      div_eq_mul_inv, mul_comm]
  · by_cases hbaij : b = i ∧ a = j
    · rcases hbaij with ⟨hi, hj⟩
      subst i
      subst j
      simp [hermitianResponse, pairDirections, response, pairTangent,
        Matrix.single_apply, ha, hb, hab, Ne.symm hab, hswap,
        div_eq_mul_inv, mul_comm]
    · simp [hermitianResponse, pairDirections, response, pairTangent,
        Matrix.single_apply, habij, hbaij]

/-- The selected diagonal block is idempotent. -/
theorem blockProjector_idempotent (inside : n → Bool) :
    blockProjector inside * blockProjector inside = blockProjector inside := by
  simp only [blockProjector, diagonal_mul_diagonal]
  congr 1
  funext i
  cases hi : inside i <;> simp [hi]

/-- The selected diagonal block is an orthogonal (Hermitian) projector. -/
theorem blockProjector_isHermitian (inside : n → Bool) :
    (blockProjector inside).IsHermitian := by
  rw [Matrix.IsHermitian, blockProjector, diagonal_conjTranspose]
  congr 1
  funext i
  cases hi : inside i <;> simp [hi]

/-- The real diagonal base operator is Hermitian. -/
theorem baseOperator_isHermitian (eig : n → ℝ) :
    (baseOperator eig).IsHermitian := by
  rw [Matrix.IsHermitian, baseOperator, diagonal_conjTranspose]
  simp

/-- The kernel is exactly the two diagonal blocks: every nonzero singular
value is therefore accounted for by `hermitianResponse_pairDirections`. -/
theorem response_eq_zero_iff (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ)
    (hgap : ∀ i j, inside i ≠ inside j → eig i ≠ eig j) :
    response inside eig H = 0 ↔
      ∀ i j, inside i ≠ inside j → H i j = 0 := by
  constructor
  · intro h i j hij
    have hentry : H i j / (signedGap inside eig i j : ℂ) = 0 := by
      have h' := congrFun (congrFun h i) j
      simpa [response, hij] using h'
    have hd : (signedGap inside eig i j : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (signedGap_ne_zero inside eig hgap hij)
    exact (div_eq_zero_iff.mp hentry).resolve_right hd
  · intro h
    ext i j
    by_cases hij : inside i = inside j
    · simp [response, hij]
    · simp [response, hij, h i j hij]

/-- The response satisfies the differential of `Π² = Π`. -/
theorem projector_tangent_equation (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) :
    blockProjector inside * response inside eig H +
      response inside eig H * blockProjector inside = response inside eig H := by
  ext i j
  cases hi : inside i <;> cases hj : inside j <;>
    simp [blockProjector, response, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]

/-- Differentiating `Π Σ = Σ Π` gives the displayed reciprocal-gap entry.
This is the Sylvester/commutator form of the block formula. -/
theorem response_commutator_equation (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ)
    (hgap : ∀ i j, inside i ≠ inside j → eig i ≠ eig j) :
    response inside eig H * baseOperator eig - baseOperator eig * response inside eig H =
      H * blockProjector inside - blockProjector inside * H := by
  ext i j
  cases hi : inside i <;> cases hj : inside j
  · simp [blockProjector, baseOperator, response,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]
  · have hcross : inside i ≠ inside j := by simp [hi, hj]
    have hd : eig j - eig i ≠ 0 := sub_ne_zero.mpr (hgap j i (by simp [hi, hj]))
    have hdC : ((eig j - eig i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      baseOperator, blockProjector, response, hi, hj, Bool.false_eq_true,
      reduceIte, Matrix.diagonal_apply, Pi.zero_apply, Bool.true_eq_false,
      ↓reduceIte, signedGap]
    field_simp [hdC]
    rw [Complex.ofReal_sub]
    ring
  · have hcross : inside i ≠ inside j := by simp [hi, hj]
    have hd : eig i - eig j ≠ 0 := sub_ne_zero.mpr (hgap i j hcross)
    have hdC : ((eig i - eig j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      baseOperator, blockProjector, response, hi, hj, Bool.false_eq_true,
      reduceIte, Matrix.diagonal_apply, Pi.zero_apply, Bool.true_eq_false,
      ↓reduceIte, signedGap]
    field_simp [hdC]
    rw [Complex.ofReal_sub]
    ring
  · simp [blockProjector, baseOperator, response,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]

/-- Frobenius norm squared, with the finite index sets completely explicit. -/
def frobSq (H : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖H i j‖ ^ 2

/-- The Frobenius norm itself. -/
def frobNorm (H : Matrix n n ℂ) : ℝ := Real.sqrt (frobSq H)

/-- Real scalar multiplication scales squared Frobenius energy by its square. -/
theorem frobSq_real_smul (r : ℝ) (H : Matrix n n ℂ) :
    frobSq (r • H) = r ^ 2 * frobSq H := by
  simp [frobSq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

/-- Real scalar multiplication has the expected Frobenius norm. -/
theorem frobNorm_real_smul (r : ℝ) (H : Matrix n n ℂ) :
    frobNorm (r • H) = |r| * frobNorm H := by
  unfold frobNorm
  rw [frobSq_real_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-- On the whole complex parameter family at one inside/outside pair, the
singular value is exactly `|λinside - λoutside|⁻¹`.  Together with
`pairDirections_injective`, this records the multiplicity two. -/
theorem response_pairDirections_frobNorm (inside : n → Bool) (eig : n → ℝ)
    {a b : n} (ha : inside a = true) (hb : inside b = false) (z : ℂ) :
    frobNorm (response inside eig (pairTangent a b z)) =
      |signedGap inside eig a b|⁻¹ * frobNorm (pairTangent a b z) := by
  have h := congrArg (fun K : hermitianSubmodule n => K.1)
    (hermitianResponse_pairDirections inside eig ha hb z)
  change response inside eig (pairTangent a b z) =
    (signedGap inside eig a b)⁻¹ • pairTangent a b z at h
  rw [h, frobNorm_real_smul, abs_inv]

theorem frobSq_nonneg (H : Matrix n n ℂ) : 0 ≤ frobSq H := by
  unfold frobSq
  positivity

/-- Exact entrywise weights of the response Gram operator. -/
theorem norm_response_apply_sq (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) (i j : n) :
    ‖response inside eig H i j‖ ^ 2 =
      if inside i = inside j then 0
      else ‖H i j‖ ^ 2 / (signedGap inside eig i j) ^ 2 := by
  by_cases hij : inside i = inside j
  · simp [response, hij]
  · simp [response, hij, norm_div, div_pow, sq_abs]

/-- The response has no diagonal-block contribution and has weight
`|λinside - λoutside|⁻²` on every off-block entry. -/
theorem frobSq_response (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) :
    frobSq (response inside eig H) = ∑ i, ∑ j,
      if inside i = inside j then 0
      else ‖H i j‖ ^ 2 / (signedGap inside eig i j) ^ 2 := by
  unfold frobSq
  congr 1
  funext i
  congr 1
  funext j
  exact norm_response_apply_sq inside eig H i j

/-- The exact gap stiffness inequality, squared. -/
theorem frobSq_response_le (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) (gap : ℝ) (hgap : 0 < gap)
    (hwidth : ∀ i j, inside i ≠ inside j → gap ≤ |signedGap inside eig i j|) :
    frobSq (response inside eig H) ≤ frobSq H / gap ^ 2 := by
  rw [frobSq_response]
  calc
    (∑ i, ∑ j, if inside i = inside j then 0
        else ‖H i j‖ ^ 2 / (signedGap inside eig i j) ^ 2)
        ≤ ∑ i, ∑ j, ‖H i j‖ ^ 2 / gap ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : inside i = inside j
      · simp [hij, div_nonneg (sq_nonneg ‖H i j‖) (sq_nonneg gap)]
      · simp only [hij, if_false]
        have hd : 0 < |signedGap inside eig i j| :=
          lt_of_lt_of_le hgap (hwidth i j hij)
        have hsq : gap ^ 2 ≤ |signedGap inside eig i j| ^ 2 := by
          gcongr
          exact hwidth i j hij
        rw [show (signedGap inside eig i j) ^ 2 =
          |signedGap inside eig i j| ^ 2 by exact (sq_abs _).symm]
        gcongr
    _ = frobSq H / gap ^ 2 := by
      simp [frobSq, Finset.sum_div]

/-- In Frobenius norm, the algebraic differential has stiffness at most the
reciprocal of the minimum spectral gap. -/
theorem frobNorm_response_le (inside : n → Bool) (eig : n → ℝ)
    (H : Matrix n n ℂ) (gap : ℝ) (hgap : 0 < gap)
    (hwidth : ∀ i j, inside i ≠ inside j → gap ≤ |signedGap inside eig i j|) :
    frobNorm (response inside eig H) ≤ frobNorm H / gap := by
  unfold frobNorm
  calc
    Real.sqrt (frobSq (response inside eig H))
        ≤ Real.sqrt (frobSq H / gap ^ 2) :=
      Real.sqrt_le_sqrt (frobSq_response_le inside eig H gap hgap hwidth)
    _ = Real.sqrt (frobSq H) / gap := by
      rw [Real.sqrt_div (frobSq_nonneg H), Real.sqrt_sq hgap.le]

/-! ## A non-vacuous two-level witness -/

/-- One eigenvalue is inside and one outside. -/
def witnessInside : Fin 2 → Bool := ![true, false]

/-- The separated eigenvalues `1` and `-1`, with gap `2`. -/
def witnessEig : Fin 2 → ℝ := ![1, -1]

/-- The real Pauli-`x` off-block direction. -/
def witnessReal : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The imaginary Pauli-`y` off-block direction (up to sign convention). -/
def witnessImag : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; -Complex.I, 0]

/-- A diagonal-block perturbation, which lies in the response kernel. -/
def witnessDiagonal : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem witness_inside_zero : witnessInside 0 = true := by rfl
theorem witness_inside_one : witnessInside 1 = false := by rfl

/-- The real direction has signed eigenvalue `1/2`. -/
theorem response_witnessReal :
    response witnessInside witnessEig witnessReal = (2 : ℝ)⁻¹ • witnessReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [response, signedGap, witnessInside, witnessEig, witnessReal]

/-- The imaginary direction has the same signed eigenvalue `1/2`; its singular
value is therefore also `1/|1 - (-1)| = 1/2`. -/
theorem response_witnessImag :
    response witnessInside witnessEig witnessImag = (2 : ℝ)⁻¹ • witnessImag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [response, signedGap, witnessInside, witnessEig, witnessImag] <;> ring

/-- Every diagonal-block direction has singular value zero. -/
theorem response_witnessDiagonal : response witnessInside witnessEig witnessDiagonal = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [response, signedGap, witnessInside, witnessEig, witnessDiagonal]

/-- The concrete perturbation is nonzero. -/
theorem witnessReal_ne_zero : witnessReal ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [witnessReal] at h01

/-- All the example hypotheses of the general kernel are satisfied with gap 2. -/
theorem witness_gap_two {i j : Fin 2} (hij : witnessInside i ≠ witnessInside j) :
    |signedGap witnessInside witnessEig i j| = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [witnessInside, witnessEig, signedGap] <;> norm_num

#print axioms RelationalAtlas.B72.signedGap_ne_zero
#print axioms RelationalAtlas.B72.signedGap_swap
#print axioms RelationalAtlas.B72.response_apply_of_same
#print axioms RelationalAtlas.B72.response_isHermitian
#print axioms RelationalAtlas.B72.pairTangent_isHermitian
#print axioms RelationalAtlas.B72.pairDirections_injective
#print axioms RelationalAtlas.B72.pairDirections_one_ne_zero
#print axioms RelationalAtlas.B72.hermitianResponse_pairDirections
#print axioms RelationalAtlas.B72.blockProjector_idempotent
#print axioms RelationalAtlas.B72.blockProjector_isHermitian
#print axioms RelationalAtlas.B72.baseOperator_isHermitian
#print axioms RelationalAtlas.B72.response_eq_zero_iff
#print axioms RelationalAtlas.B72.projector_tangent_equation
#print axioms RelationalAtlas.B72.response_commutator_equation
#print axioms RelationalAtlas.B72.frobSq_real_smul
#print axioms RelationalAtlas.B72.frobNorm_real_smul
#print axioms RelationalAtlas.B72.response_pairDirections_frobNorm
#print axioms RelationalAtlas.B72.frobSq_nonneg
#print axioms RelationalAtlas.B72.norm_response_apply_sq
#print axioms RelationalAtlas.B72.frobSq_response
#print axioms RelationalAtlas.B72.frobSq_response_le
#print axioms RelationalAtlas.B72.frobNorm_response_le
#print axioms RelationalAtlas.B72.witness_inside_zero
#print axioms RelationalAtlas.B72.witness_inside_one
#print axioms RelationalAtlas.B72.response_witnessReal
#print axioms RelationalAtlas.B72.response_witnessImag
#print axioms RelationalAtlas.B72.response_witnessDiagonal
#print axioms RelationalAtlas.B72.witnessReal_ne_zero
#print axioms RelationalAtlas.B72.witness_gap_two

end RelationalAtlas.B72

/-! ## B186 — the sector flip is a quarter turn

Integrated from `.ultramath/smwtkiqjq/m7/B186.lean`.
-/
/-
B186 — the sector flip is a quarter turn, and it swaps the two halves.

This is a self-contained finite algebraic kernel.  For square complex matrices
we assume exactly the card's grading hypotheses `Γ * Γ = 1`, `Γᴴ = Γ`,
`Γ * A = -(A * Γ)` (crossing), and `Γ * B = B * Γ` (inside).  Here `X = A + B`
in the trace decomposition.

The explicit unitary is `U = q • (1 - iΓ)` with `q = √2/2`.  Under `Γ² = 1`
this is the algebraic evaluation of `exp (-iπΓ/4)`, but this file does NOT prove
that matrix-exponential identity.  Instead, quarter-turn behaviour is proved
independently for the concrete real matrix `J` by its powers and its action on
vectors.  We do not formalize existence of a common grading for a whole family,
nor the card's physical/spectral interpretation.

Definitions do not need axiom audits; every theorem below has `#print axioms`.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace RelationalAtlas.B186
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A grading conjugates a crossing matrix to its negative. -/
theorem crossing_conj (Γ A : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hA : Γ * A = -(A * Γ)) : Γ * A * Γ = -A := by
  calc
    Γ * A * Γ = (-(A * Γ)) * Γ := by rw [hA]
    _ = -(A * (Γ * Γ)) := by rw [neg_mul, mul_assoc]
    _ = -A := by rw [hΓ]; simp

/-- A grading preserves an inside matrix under conjugation. -/
theorem inside_conj (Γ B : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hB : Γ * B = B * Γ) : Γ * B * Γ = B := by
  calc
    Γ * B * Γ = (B * Γ) * Γ := by rw [hB]
    _ = B * (Γ * Γ) := by rw [mul_assoc]
    _ = B := by rw [hΓ, mul_one]

/-- **B186 (quarter turn on crossing squares).** -/
theorem grading_crossing_sq (Γ A : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hA : Γ * A = -(A * Γ)) : (Γ * A) * (Γ * A) = -(A * A) := by
  have hA' : A * Γ = -(Γ * A) := by rw [hA]; simp
  calc
    (Γ * A) * (Γ * A) = Γ * (A * Γ) * A := by simp only [mul_assoc]
    _ = Γ * (-(Γ * A)) * A := by rw [hA']
    _ = -((Γ * Γ) * (A * A)) := by simp only [mul_assoc, neg_mul, mul_neg]
    _ = -(A * A) := by rw [hΓ, one_mul]

/-- Crossing and inside parts are trace-orthogonal; this is proved from the
grading relations, not assumed separately. -/
theorem trace_crossing_inside (Γ A B : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hA : Γ * A = -(A * Γ)) (hB : Γ * B = B * Γ) :
    Matrix.trace (A * B) = 0 := by
  have hconj : Γ * (A * B) * Γ = -(A * B) := by
    calc
      Γ * (A * B) * Γ = (Γ * A) * (B * Γ) := by simp only [mul_assoc]
      _ = (-(A * Γ)) * (Γ * B) := by
        have hB' : B * Γ = Γ * B := hB.symm
        rw [hA, hB']
      _ = -((A * B) * (Γ * Γ)) := by
        rw [hB]
        simp only [mul_assoc, neg_mul]
        rw [← mul_assoc Γ B Γ, hB, mul_assoc]
      _ = -(A * B) := by rw [hΓ]; simp
  have htr : Matrix.trace (Γ * (A * B) * Γ) = Matrix.trace (A * B) := by
    calc
      Matrix.trace (Γ * (A * B) * Γ) = Matrix.trace (Γ * ((A * B) * Γ)) := by rw [mul_assoc]
      _ = Matrix.trace (((A * B) * Γ) * Γ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((A * B) * (Γ * Γ)) := by rw [mul_assoc]
      _ = Matrix.trace (A * B) := by rw [hΓ, mul_one]
  rw [hconj, Matrix.trace_neg] at htr
  exact CharZero.eq_neg_self_iff.mp htr.symm

/-- **B186 (trace defect).** For `X = A + B`, the ordinary and grading-twisted
trace forms differ from twice the inside contribution by exactly zero. -/
theorem trace_sector_decomposition (Γ A B : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hA : Γ * A = -(A * Γ)) (hB : Γ * B = B * Γ) :
    Matrix.trace ((A + B) * (A + B)) +
      Matrix.trace ((Γ * (A + B)) * (Γ * (A + B))) = 2 * Matrix.trace (B * B) := by
  have hAA : (Γ * A) * (Γ * A) = -(A * A) := grading_crossing_sq Γ A hΓ hA
  have hBB : (Γ * B) * (Γ * B) = B * B := by
    calc
      (Γ * B) * (Γ * B) = (Γ * B * Γ) * B := by simp only [mul_assoc]
      _ = B * B := by rw [inside_conj Γ B hΓ hB]
  have hAB : (Γ * A) * (Γ * B) = -(A * B) := by
    calc
      (Γ * A) * (Γ * B) = (Γ * A * Γ) * B := by simp only [mul_assoc]
      _ = -(A * B) := by rw [crossing_conj Γ A hΓ hA]; simp
  have hBA : (Γ * B) * (Γ * A) = B * A := by
    calc
      (Γ * B) * (Γ * A) = (Γ * B * Γ) * A := by simp only [mul_assoc]
      _ = B * A := by rw [inside_conj Γ B hΓ hB]
  have htrAB : Matrix.trace (A * B) = 0 := trace_crossing_inside Γ A B hΓ hA hB
  have htrBA : Matrix.trace (B * A) = 0 := by
    rw [← Matrix.trace_mul_comm A B, htrAB]
  have hX : (A + B) * (A + B) = A * A + A * B + B * A + B * B := by
    simp only [add_mul, mul_add]
    abel
  have hGX : (Γ * (A + B)) * (Γ * (A + B)) =
      -(A * A) + -(A * B) + B * A + B * B := by
    calc
      (Γ * (A + B)) * (Γ * (A + B)) =
          (Γ * A) * (Γ * A) + (Γ * A) * (Γ * B) +
            (Γ * B) * (Γ * A) + (Γ * B) * (Γ * B) := by
        simp only [add_mul, mul_add]
        abel
      _ = -(A * A) + -(A * B) + B * A + B * B := by rw [hAA, hAB, hBA, hBB]
  rw [hX, hGX]
  simp only [Matrix.trace_add, Matrix.trace_neg]
  rw [htrAB, htrBA]
  ring



/-- The real scalar `1/√2`, viewed as a complex number. -/
def quarterScale : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- Its square is one half. -/
theorem quarterScale_sq : quarterScale * quarterScale = 1 / 2 := by
  have hR : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  simpa [quarterScale] using hC

/-- The algebraic evaluation of the quarter-turn frame on a grading:
`q • (1 - iΓ)`, where `q = 1/√2`. -/
def quarterUnitary (Γ : Matrix n n ℂ) : Matrix n n ℂ :=
  quarterScale • (1 - Complex.I • Γ)

omit [Fintype n] in
/-- For a Hermitian grading, the adjoint changes the sign of the phase. -/
theorem quarterUnitary_star (Γ : Matrix n n ℂ) (hΓstar : Γᴴ = Γ) :
    (quarterUnitary Γ)ᴴ = quarterScale • (1 + Complex.I • Γ) := by
  simp [quarterUnitary, hΓstar, quarterScale, sub_eq_add_neg,
    smul_add]


/-- The explicit frame matrix is unitary when `Γ² = I` and `Γ` is Hermitian. -/
theorem quarterUnitary_isUnitary (Γ : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hΓstar : Γᴴ = Γ) :
    quarterUnitary Γ * (quarterUnitary Γ)ᴴ = 1 ∧
      (quarterUnitary Γ)ᴴ * quarterUnitary Γ = 1 := by
  have hforward : (1 - Complex.I • Γ) * (1 + Complex.I • Γ) = (2 : ℂ) • 1 := by
    simp only [sub_mul, one_mul, Matrix.smul_mul, mul_add, mul_one,
      Matrix.mul_smul, smul_smul, Complex.I_mul_I, hΓ]
    module
  have hbackward : (1 + Complex.I • Γ) * (1 - Complex.I • Γ) = (2 : ℂ) • 1 := by
    calc
      (1 + Complex.I • Γ) * (1 - Complex.I • Γ) =
          1 - (Complex.I * Complex.I) • (Γ * Γ) := by
        simp only [mul_sub, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul]
        module
      _ = (2 : ℂ) • 1 := by rw [Complex.I_mul_I, hΓ]; module
  rw [quarterUnitary_star Γ hΓstar]
  constructor
  · simp only [quarterUnitary, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hforward, quarterScale_sq]
    module
  · simp only [quarterUnitary, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hbackward, quarterScale_sq]
    module

omit [DecidableEq n] in
/-- Multiplication by a Hermitian grading turns a Hermitian crossing matrix
into a skew-Hermitian one. -/
theorem grading_mul_skew_of_hermitian (Γ A : Matrix n n ℂ)
    (hΓstar : Γᴴ = Γ) (hA : Γ * A = -(A * Γ)) (hAherm : Aᴴ = A) :
    (Γ * A)ᴴ = -(Γ * A) := by
  rw [Matrix.conjTranspose_mul, hΓstar, hAherm]
  rw [hA]
  simp

omit [DecidableEq n] in
/-- It turns a skew-Hermitian crossing matrix into a Hermitian one. -/
theorem grading_mul_hermitian_of_skew (Γ A : Matrix n n ℂ)
    (hΓstar : Γᴴ = Γ) (hA : Γ * A = -(A * Γ)) (hAskew : Aᴴ = -A) :
    (Γ * A)ᴴ = Γ * A := by
  rw [Matrix.conjTranspose_mul, hΓstar, hAskew, neg_mul]
  exact hA.symm

/-- **B186 (quarter-turn conjugation).**  If `Γ² = I`, `Γ` is Hermitian,
and `A` crosses the sectors, then change of frame by `U` followed by
multiplication by `i` is exactly left multiplication by `Γ`. -/
theorem sector_flip_quarter (Γ A : Matrix n n ℂ) (hΓ : Γ * Γ = 1)
    (hΓstar : Γᴴ = Γ) (hA : Γ * A = -(A * Γ)) :
    Complex.I • (quarterUnitary Γ * A * (quarterUnitary Γ)ᴴ) = Γ * A := by
  have hU : quarterUnitary Γ * A * (quarterUnitary Γ)ᴴ =
      (quarterScale * quarterScale) •
        ((1 - Complex.I • Γ) * A * (1 + Complex.I • Γ)) := by
    rw [quarterUnitary_star Γ hΓstar]
    simp only [quarterUnitary, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hbracket : (1 - Complex.I • Γ) * A * (1 + Complex.I • Γ) =
      (2 * Complex.I) • (A * Γ) := by
    calc
      (1 - Complex.I • Γ) * A * (1 + Complex.I • Γ) =
          A + Complex.I • (A * Γ) - Complex.I • (Γ * A) -
            (Complex.I * Complex.I) • (Γ * A * Γ) := by
        simp only [sub_mul, one_mul, Matrix.smul_mul, mul_add, mul_one,
          Matrix.mul_smul, smul_smul]
        module
      _ = (2 * Complex.I) • (A * Γ) := by
        rw [crossing_conj Γ A hΓ hA, hA, Complex.I_mul_I]
        module
  rw [hU, hbracket]
  simp only [smul_smul, quarterScale_sq]
  rw [show Complex.I * (1 / 2 * (2 * Complex.I)) = Complex.I * Complex.I by ring,
    Complex.I_mul_I]
  simpa using hA.symm

/-- The real quarter-turn on two coordinates. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The projector onto the first diagonal sector. -/
def sectorZero : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The projector onto the second diagonal sector. -/
def sectorOne : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- `J` squares to minus the identity, not to the identity. -/
theorem J_sq : J * J = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Four applications of `J` give the identity. -/
theorem J_pow_four : J ^ 4 = 1 := by
  rw [show 4 = 2 + 2 by norm_num, pow_add, pow_two, J_sq]
  simp

/-- Three applications give the inverse quarter-turn. -/
theorem J_pow_three : J ^ 3 = -J := by
  rw [show 3 = 2 + 1 by norm_num, pow_add, pow_two, pow_one, J_sq]
  simp

/-- Adding four to an exponent does not change the corresponding power. -/
theorem J_pow_add_four (k : ℕ) : J ^ (k + 4) = J ^ k := by
  rw [pow_add, J_pow_four, mul_one]

/-- `J` really is the quarter-turn `(x,y) ↦ (-y,x)`. -/
theorem J_mulVec (x y : ℝ) : J *ᵥ ![x, y] = ![-y, x] := by
  funext i
  fin_cases i <;> norm_num [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A concrete non-vacuous instance: the first coordinate axis is sent to the second. -/
theorem J_basis_vector : J *ᵥ ![1, 0] = ![0, 1] := by
  rw [J_mulVec]
  norm_num

/-- Conjugation by the quarter-turn exchanges the two diagonal sector projectors. -/
theorem J_swaps_sector_projectors :
    J * sectorZero * J.transpose = sectorOne ∧
      J * sectorOne * J.transpose = sectorZero := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [J, sectorZero, sectorOne, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]

#print axioms RelationalAtlas.B186.quarterScale_sq
#print axioms RelationalAtlas.B186.quarterUnitary_star
#print axioms RelationalAtlas.B186.quarterUnitary_isUnitary
#print axioms RelationalAtlas.B186.grading_mul_skew_of_hermitian
#print axioms RelationalAtlas.B186.grading_mul_hermitian_of_skew
#print axioms RelationalAtlas.B186.sector_flip_quarter
#print axioms RelationalAtlas.B186.J_sq
#print axioms RelationalAtlas.B186.J_pow_four
#print axioms RelationalAtlas.B186.J_pow_three
#print axioms RelationalAtlas.B186.J_pow_add_four
#print axioms RelationalAtlas.B186.J_mulVec
#print axioms RelationalAtlas.B186.J_basis_vector
#print axioms RelationalAtlas.B186.J_swaps_sector_projectors
#print axioms RelationalAtlas.B186.crossing_conj
#print axioms RelationalAtlas.B186.inside_conj
#print axioms RelationalAtlas.B186.grading_crossing_sq
#print axioms RelationalAtlas.B186.trace_crossing_inside
#print axioms RelationalAtlas.B186.trace_sector_decomposition

end RelationalAtlas.B186

/-! ## B44 — five sectors and the lift of a defective block

Integrated from `.ultramath/smwtkiqjq/m2/B44.lean`.
-/
/-
B44: the five-dimensional symmetric-traceless sector and the lower bound
transferred from a block on an invariant subspace.

This file proves finite algebra only.  In particular, five is the dimension of
the chosen 2+2+1 profile, not a lower bound for transient growth.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace AtlasB44

/-- Real symmetric matrices of trace zero, as a linear subspace. -/
def symmetricTraceless (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm ∧ A.trace = 0}
  zero_mem' := by simp [Matrix.IsSymm]
  add_mem' := by
    rintro A B ⟨hAs, hAt⟩ ⟨hBs, hBt⟩
    exact ⟨hAs.add hBs, by simp [Matrix.trace_add, hAt, hBt]⟩
  smul_mem' := by
    rintro c A ⟨hAs, hAt⟩
    exact ⟨hAs.smul c, by simp [Matrix.trace_smul, hAt]⟩

/-- The five independent entries of a real symmetric traceless `3 × 3` matrix.
The first two coordinates are the diagonal (shape) modes, the next two are the
first two off-diagonal (shear) modes, and the last is the remaining interface
coordinate. -/
def sectorMatrix (x : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 0, x 2, x 3;
     x 2, x 1, x 4;
     x 3, x 4, -x 0 - x 1]

/-- Coordinates give a linear parametrization of the symmetric traceless sector. -/
def sectorParam : (Fin 5 → ℝ) →ₗ[ℝ] symmetricTraceless 3 where
  toFun x := ⟨sectorMatrix x, by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [sectorMatrix]
    · simp [sectorMatrix, Matrix.trace_fin_three]⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sectorMatrix] <;> ring
  map_smul' c x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sectorMatrix] <;> ring

/-- Read the five free entries back from a symmetric traceless matrix. -/
def sectorCoordinates : symmetricTraceless 3 →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun A := ![A.1 0 0, A.1 1 1, A.1 0 1, A.1 0 2, A.1 1 2]
  map_add' A B := by
    funext i
    fin_cases i <;> simp
  map_smul' c A := by
    funext i
    fin_cases i <;> simp

/-- The parametrization and coordinate read-off are inverse linear maps. -/
def sectorEquiv : (Fin 5 → ℝ) ≃ₗ[ℝ] symmetricTraceless 3 :=
  { sectorParam with
    invFun := sectorCoordinates
    left_inv := by
      intro x
      funext i
      fin_cases i <;> simp [sectorCoordinates, sectorParam, sectorMatrix]
    right_inv := by
      rintro ⟨A, hAs, hAt⟩
      apply Subtype.ext
      ext i j
      have hs01 : A 1 0 = A 0 1 := by
        have := congr_fun (congr_fun hAs 0) 1
        simpa only [Matrix.transpose_apply] using this
      have hs02 : A 2 0 = A 0 2 := by
        have := congr_fun (congr_fun hAs 0) 2
        simpa only [Matrix.transpose_apply] using this
      have hs12 : A 2 1 = A 1 2 := by
        have := congr_fun (congr_fun hAs 1) 2
        simpa only [Matrix.transpose_apply] using this
      have ht : A 2 2 = -A 0 0 - A 1 1 := by
        simp [Matrix.trace_fin_three] at hAt
        linarith
      fin_cases i <;> fin_cases j <;>
        simp [sectorCoordinates, sectorParam, sectorMatrix, hs01, hs02, hs12, ht] }

#print axioms sectorEquiv

/-- **B44, sector count.**  The real symmetric traceless sector in three
ambient dimensions has dimension `2 + 2 + 1 = 5`. -/
theorem finrank_symmetricTraceless_three :
    Module.finrank ℝ (symmetricTraceless 3) = 5 := by
  rw [← sectorEquiv.finrank_eq]
  simp

#print axioms finrank_symmetricTraceless_three

section BlockGrowth

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An isometrically embedded block interlaces with every iterate of the
ambient operator. -/
theorem intertwines_pow (T : E →L[ℝ] E) (S : V →L[ℝ] V) (ι : V →ₗᵢ[ℝ] E)
    (h : ∀ x, T (ι x) = ι (S x)) (n : ℕ) (x : V) :
    (T ^ n) (ι x) = ι ((S ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, mul_apply_eq_comp]
      rw [h, ih]

#print axioms intertwines_pow

/-- **B44, block-to-ambient growth.**  If `ι` is a linear isometry and
`T ∘ ι = ι ∘ S`, every power of the block has operator norm at most that of the
corresponding ambient power.  No finite-dimensionality or nilpotence is needed.
For an invariant subspace, take `ι = V.subtypeₗᵢ` and `S = T.restrict`. -/
theorem opNorm_pow_le_of_intertwining (T : E →L[ℝ] E) (S : V →L[ℝ] V)
    (ι : V →ₗᵢ[ℝ] E) (h : ∀ x, T (ι x) = ι (S x)) (n : ℕ) :
    ‖S ^ n‖ ≤ ‖T ^ n‖ := by
  apply (S ^ n).opNorm_le_bound (norm_nonneg _)
  intro x
  calc
    ‖(S ^ n) x‖ = ‖ι ((S ^ n) x)‖ := (ι.norm_map _).symm
    _ = ‖(T ^ n) (ι x)‖ := by rw [intertwines_pow T S ι h n x]
    _ ≤ ‖T ^ n‖ * ‖ι x‖ := (T ^ n).le_opNorm _
    _ = ‖T ^ n‖ * ‖x‖ := by rw [ι.norm_map]

#print axioms opNorm_pow_le_of_intertwining

variable [CompleteSpace E] [CompleteSpace V]

/-- The same intertwiner transports the convergent exponential series. -/
theorem intertwines_exp (T : E →L[ℝ] E) (S : V →L[ℝ] V) (ι : V →ₗᵢ[ℝ] E)
    (h : ∀ x, T (ι x) = ι (S x)) (x : V) :
    NormedSpace.exp T (ι x) = ι (NormedSpace.exp S x) := by
  have hTx : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (T ^ n) (ι x))
      (NormedSpace.exp T (ι x)) := by
    simpa only [ContinuousLinearMap.apply_apply, _root_.smul_apply] using
      (ContinuousLinearMap.apply ℝ E (ι x)).hasSum
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) T)
  have hSx : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (S ^ n) x)
      (NormedSpace.exp S x) := by
    simpa only [ContinuousLinearMap.apply_apply, _root_.smul_apply] using
      (ContinuousLinearMap.apply ℝ V x).hasSum
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) S)
  have hSi : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • ι ((S ^ n) x))
      (ι (NormedSpace.exp S x)) := by
    simpa only [map_smul, LinearIsometry.coe_toContinuousLinearMap] using
      hSx.mapL ι.toContinuousLinearMap
  simp_rw [intertwines_pow T S ι h] at hTx
  exact hTx.unique hSi

#print axioms intertwines_exp

/-- **B44, exact exponential lower bound.**  On Banach spaces, an invariant
isometric block gives `‖exp(tS)‖ ≤ ‖exp(tT)‖` for every real time.  This is the
ambient-operator content of `max_t ‖e^(tA)‖ ≥ max_t ‖e^(tJ)‖`; the pointwise
inequality is stronger and avoids choosing a time domain. -/
theorem opNorm_exp_smul_le_of_intertwining (T : E →L[ℝ] E) (S : V →L[ℝ] V)
    (ι : V →ₗᵢ[ℝ] E) (h : ∀ x, T (ι x) = ι (S x)) (t : ℝ) :
    ‖NormedSpace.exp (t • S)‖ ≤ ‖NormedSpace.exp (t • T)‖ := by
  have hscaled : ∀ x, (t • T) (ι x) = ι ((t • S) x) := by
    intro x
    simp only [_root_.smul_apply, map_smul, h]
  apply (NormedSpace.exp (t • S)).opNorm_le_bound (norm_nonneg _)
  intro x
  calc
    ‖NormedSpace.exp (t • S) x‖ = ‖ι (NormedSpace.exp (t • S) x)‖ :=
      (ι.norm_map _).symm
    _ = ‖NormedSpace.exp (t • T) (ι x)‖ := by
      rw [intertwines_exp (t • T) (t • S) ι hscaled x]
    _ ≤ ‖NormedSpace.exp (t • T)‖ * ‖ι x‖ :=
      (NormedSpace.exp (t • T)).le_opNorm _
    _ = ‖NormedSpace.exp (t • T)‖ * ‖x‖ := by rw [ι.norm_map]

#print axioms opNorm_exp_smul_le_of_intertwining

end BlockGrowth

/-! ## The defective `2 × 2` block and its exponential -/

/-- A Jordan block with diagonal eigenvalue `a`. -/
def jordanBlock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 1; 0, a]

/-- Its nilpotent, non-scalar part. -/
def nilpotentPart : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The Jordan block really is `aI + N`. -/
theorem jordanBlock_eq (a : ℝ) :
    jordanBlock a = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + nilpotentPart := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jordanBlock, nilpotentPart]

#print axioms jordanBlock_eq

/-- The defect is nonzero but has square zero. -/
theorem nilpotentPart_sq : nilpotentPart * nilpotentPart = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentPart, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms nilpotentPart_sq

/-- In particular, the block is defective rather than diagonalizable. -/
theorem nilpotentPart_ne_zero : nilpotentPart ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [nilpotentPart] at h01

#print axioms nilpotentPart_ne_zero

/-- The exponential of a square-zero matrix truncates after its linear term. -/
theorem exp_smul_of_mul_self_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (hN : N * N = 0) (t : ℝ) :
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

#print axioms exp_smul_of_mul_self_eq_zero

/-- **B44, exact small-block flow.**  For the Jordan block `J = aI + N`,
`e^{tJ} = e^{at}(I + tN)`.  Taking `a < 0` gives a damped eigenvalue while the
factor `t` records the algebraic transient. -/
theorem exp_jordanBlock (a t : ℝ) :
    NormedSpace.exp (t • jordanBlock a) =
      Real.exp (t * a) •
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) + t • nilpotentPart) := by
  have hdecomp : t • jordanBlock a =
      Matrix.diagonal (fun _ : Fin 2 => t * a) + t • nilpotentPart := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanBlock, nilpotentPart, Matrix.diagonal]
  have hcomm : Commute (Matrix.diagonal (fun _ : Fin 2 => t * a))
      (t • nilpotentPart) := by
    show Matrix.diagonal (fun _ : Fin 2 => t * a) * (t • nilpotentPart) =
      (t • nilpotentPart) * Matrix.diagonal (fun _ : Fin 2 => t * a)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, nilpotentPart, Matrix.mul_apply] <;> ring
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, Matrix.exp_diagonal,
    exp_smul_of_mul_self_eq_zero nilpotentPart nilpotentPart_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, nilpotentPart, Real.exp_eq_exp_ℝ, Matrix.mul_apply]

#print axioms exp_jordanBlock

/-- The displayed entrywise form at the damped eigenvalue `-1`. -/
theorem exp_damped_jordanBlock (t : ℝ) :
    NormedSpace.exp (t • jordanBlock (-1)) =
      Real.exp (-t) • !![1, t; 0, 1] := by
  rw [exp_jordanBlock]
  congr 1
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentPart]

#print axioms exp_damped_jordanBlock

/-! ## A concrete four-dimensional invariant lift -/

/-- Two real coordinates with their Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The damped defective block as a continuous operator. -/
def dampedJordanOp : Plane →L[ℝ] Plane :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) (jordanBlock (-1))

/-- A four-real-dimensional operator with two copies of the block.  The first
summand is therefore an invariant defective subspace. -/
def fourDimensionalLift : (Plane × Plane) →L[ℝ] (Plane × Plane) :=
  dampedJordanOp.prodMap dampedJordanOp

/-- **B44, concrete instance.**  The general lower bound is non-vacuous: for
this explicit damped defective block and its four-dimensional lift, every power
of the small block is bounded by the corresponding ambient power. -/
theorem dampedJordanOp_norm_pow_le_fourDimensionalLift (n : ℕ) :
    ‖dampedJordanOp ^ n‖ ≤ ‖fourDimensionalLift ^ n‖ := by
  apply opNorm_pow_le_of_intertwining fourDimensionalLift dampedJordanOp
    (LinearIsometry.inl ℝ Plane Plane)
  intro x
  simp [fourDimensionalLift]

#print axioms dampedJordanOp_norm_pow_le_fourDimensionalLift

/-- **B44, concrete exponential lift.**  The displayed transient-growth floor
holds for the explicit damped defective block and its four-dimensional lift. -/
theorem dampedJordanOp_norm_exp_smul_le_fourDimensionalLift (t : ℝ) :
    ‖NormedSpace.exp (t • dampedJordanOp)‖ ≤
      ‖NormedSpace.exp (t • fourDimensionalLift)‖ := by
  apply opNorm_exp_smul_le_of_intertwining fourDimensionalLift dampedJordanOp
    (LinearIsometry.inl ℝ Plane Plane)
  intro x
  simp [fourDimensionalLift]

#print axioms dampedJordanOp_norm_exp_smul_le_fourDimensionalLift

/-- An explicit vector on which the polynomial transient is visible. -/
theorem exp_damped_jordanBlock_mulVec (t : ℝ) :
    (NormedSpace.exp (t • jordanBlock (-1))) *ᵥ ![0, 1] =
      Real.exp (-t) • ![t, 1] := by
  rw [exp_damped_jordanBlock]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

#print axioms exp_damped_jordanBlock_mulVec

end AtlasB44
