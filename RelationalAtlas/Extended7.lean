/-
Sixth batch: the two-books block, cards B185 to B206.

Each contribution is reproduced verbatim except for its import line. Every file here is
self-contained (`import Mathlib`), which is why they can be concatenated; each keeps its
own scope delimiters, so the concatenation is balanced. Nothing in the earlier modules is
modified.
-/
import Mathlib


/-! ## B185 — the books as a Born sum, and the rank-k overlap

Integrated from `.ultramath/smwvp3cvb/m3/B185.lean`.
-/
/-
B185 — Both books are Born sums over the transport.

The local edge convention is the one inherited from B183/B184: after the two
oriented blocks are combined, one undirected edge contributes
`‖Dᵢ * U - U * Dⱼ‖²` to E⁻ and `‖Dᵢ * U + U * Dⱼ‖²` to E⁺.
There is no additional factor 1/2 in these local books.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators ComplexOrder

namespace AtlasB185

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Born transition weight in fixed eigenbases. -/
def bornWeight (U : Matrix n n ℂ) (a b : n) : ℝ := Complex.normSq (U a b)

/-- The two displayed Born sums. -/
def bornMinus (lambda mu : n → ℝ) (U : Matrix n n ℂ) : ℝ :=
  ∑ a, ∑ b, bornWeight U a b * (lambda a - mu b) ^ 2

def bornPlus (lambda mu : n → ℝ) (U : Matrix n n ℂ) : ℝ :=
  ∑ a, ∑ b, bornWeight U a b * (lambda a + mu b) ^ 2

/-- Local edge books in an arbitrary basis. -/
def edgeMinus (Di Dj U : Matrix n n ℂ) : ℝ := ‖Di * U - U * Dj‖ ^ 2
def edgePlus (Di Dj U : Matrix n n ℂ) : ℝ := ‖Di * U + U * Dj‖ ^ 2

/-- A real diagonal Hermitian block, in its eigenbasis. -/
def realDiagonal (lambda : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun a => (lambda a : ℂ)

/-- Squared Frobenius norm as an entry sum. -/
theorem norm_sq_eq_sum {m o α : Type*} [Fintype m] [Fintype o]
    [SeminormedAddCommGroup α] (X : Matrix m o α) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- **B185, the minus Born sum.** No unitarity is needed for this algebraic
entry identity; double stochasticity is not being used silently here. -/
theorem edgeMinus_realDiagonal (lambda mu : n → ℝ) (U : Matrix n n ℂ) :
    edgeMinus (realDiagonal lambda) (realDiagonal mu) U = bornMinus lambda mu U := by
  rw [edgeMinus, norm_sq_eq_sum, bornMinus]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hentry :
      (realDiagonal lambda * U - U * realDiagonal mu) a b =
        ((lambda a - mu b : ℝ) : ℂ) * U a b := by
    simp only [Matrix.sub_apply, realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    push_cast
    ring
  rw [hentry, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [bornWeight]
  ring

/-- **B185, the plus Born sum.** -/
theorem edgePlus_realDiagonal (lambda mu : n → ℝ) (U : Matrix n n ℂ) :
    edgePlus (realDiagonal lambda) (realDiagonal mu) U = bornPlus lambda mu U := by
  rw [edgePlus, norm_sq_eq_sum, bornPlus]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hentry :
      (realDiagonal lambda * U + U * realDiagonal mu) a b =
        ((lambda a + mu b : ℝ) : ℂ) * U a b := by
    simp only [Matrix.add_apply, realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    push_cast
    ring
  rw [hentry, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [bornWeight]
  ring

lemma bornWeight_nonneg (U : Matrix n n ℂ) (a b : n) : 0 ≤ bornWeight U a b :=
  Complex.normSq_nonneg _

/-- Unitarity gives the row sums of the Born matrix. -/
theorem bornWeight_row_sum {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (a : n) :
    ∑ b, bornWeight U a b = 1 := by
  have h := congrFun (congrFun ((mem_unitaryGroup_iff).1 hU) a) a
  have hre := congrArg Complex.re h
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, bornWeight,
    ← Complex.normSq_eq_conj_mul_self, mul_comm, Complex.normSq_apply] using hre

/-- Unitarity also gives the column sums; together with nonnegativity this
says precisely that `W` is doubly stochastic. -/
theorem bornWeight_col_sum {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (b : n) :
    ∑ a, bornWeight U a b = 1 := by
  have h := congrFun (congrFun ((mem_unitaryGroup_iff').1 hU) b) b
  have hre := congrArg Complex.re h
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, bornWeight,
    ← Complex.normSq_eq_conj_mul_self] using hre

/-- Frobenius energy is the real Gram trace. -/
theorem norm_sq_eq_re_trace {m o 𝕜 : Type*} [Fintype m] [Fintype o] [RCLike 𝕜]
    (X : Matrix m o 𝕜) : ‖X‖ ^ 2 = RCLike.re (trace (Xᴴ * X)) := by
  rw [norm_sq_eq_sum, Finset.sum_comm]
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Left multiplication by a unitary preserves Frobenius norm. -/
theorem norm_unitary_mul {m o : Type*} [Fintype m] [Fintype o] [DecidableEq m]
    {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (X : Matrix m o ℂ) :
    ‖U * X‖ = ‖X‖ := by
  have hsq : ‖U * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [norm_sq_eq_re_trace, norm_sq_eq_re_trace, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Right multiplication by a unitary preserves Frobenius norm. -/
theorem norm_mul_unitary {m o : Type*} [Fintype m] [Fintype o] [DecidableEq o]
    (X : Matrix m o ℂ) {U : Matrix o o ℂ} (hU : U ∈ unitaryGroup o ℂ) :
    ‖X * U‖ = ‖X‖ := by
  rw [← frobenius_norm_conjTranspose (X * U), conjTranspose_mul, ← star_eq_conjTranspose U,
    norm_unitary_mul (Unitary.star_mem hU), frobenius_norm_conjTranspose]

/-- Frobenius expansion of a sum. -/
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

/-- Hermitian orthogonal projector. -/
def IsProjector (P : Matrix n n ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- The normalized transition probability on rank-`k` projector fields.
The real part is only a coercion device: under the projector hypotheses the
trace itself is real (see `transitionTrace_star`). -/
def transitionProbability (P Q U : Matrix n n ℂ) (k : ℝ) : ℝ :=
  (P * U * Q * Uᴴ).trace.re / k

/-- Cyclicity makes the transition trace invariant under adjoint when `P,Q`
are Hermitian. -/
theorem transitionTrace_star {P Q U : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    star (P * U * Q * Uᴴ).trace = (P * U * Q * Uᴴ).trace := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hP.eq, hQ.eq]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (U * Q * Uᴴ) P

lemma transitionTrace_im {P Q U : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (P * U * Q * Uᴴ).trace.im = 0 := by
  have h := transitionTrace_star (U := U) hP hQ
  rw [RCLike.star_def] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

lemma transitionTrace_eq_re {P Q U : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (P * U * Q * Uᴴ).trace = ((P * U * Q * Uᴴ).trace.re : ℂ) := by
  apply Complex.ext <;> simp [transitionTrace_im hP hQ]

/-- For orthogonal projectors the transition trace is nonnegative. This is
trace positivity of `R R*` with `R = P U Q`, plus idempotence and cyclicity. -/
lemma transitionTrace_re_nonneg {P Q U : Matrix n n ℂ}
    (hP : IsProjector P) (hQ : IsProjector Q) :
    0 ≤ (P * U * Q * Uᴴ).trace.re := by
  let R : Matrix n n ℂ := P * U * Q * Q * Uᴴ * P
  have hpsd : R.PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose (P * U * Q)
    rw [conjTranspose_mul, conjTranspose_mul, hP.1.eq, hQ.1.eq] at h
    simpa only [R, Matrix.mul_assoc] using h
  have htr := hpsd.trace_nonneg
  have heq : R.trace = (P * U * Q * Uᴴ).trace := by
    have hcyc := Matrix.trace_mul_comm (P * U * Q * Q * Uᴴ) P
    have hid : P * (P * U * Q * Q * Uᴴ) = P * U * Q * Uᴴ := by
      calc
        P * (P * U * Q * Q * Uᴴ) = (P * P) * (U * Q * Q * Uᴴ) := by noncomm_ring
        _ = P * U * Q * Uᴴ := by
          rw [hP.2, Matrix.mul_assoc U Q Q, hQ.2]
          noncomm_ring
    calc
      R.trace = (P * (P * U * Q * Q * Uᴴ)).trace := by
        simpa only [R, Matrix.mul_assoc] using hcyc
      _ = (P * U * Q * Uᴴ).trace := by rw [hid]
  rw [heq] at htr
  exact (RCLike.nonneg_iff.mp htr).1

/-- **B185's rank-k formulas.** Here `trace P = trace Q = k` is the matrix
form of rank k for Hermitian idempotents. The nonzero `k` hypothesis is only
what is needed to define the displayed normalized `p_e` by division. -/
theorem edge_books_projector {P Q U : Matrix n n ℂ}
    (hP : IsProjector P) (hQ : IsProjector Q) (hU : U ∈ unitaryGroup n ℂ)
    {k : ℝ} (hk : k ≠ 0) (hPk : P.trace = (k : ℂ)) (hQk : Q.trace = (k : ℂ)) :
    edgeMinus P Q U = 2 * k * (1 - transitionProbability P Q U k) ∧
    edgePlus P Q U = 2 * k * (1 + transitionProbability P Q U k) := by
  have hPnorm : ‖P‖ ^ 2 = k := by
    rw [norm_sq_eq_re_trace, hP.1.eq, hP.2, hPk]
    simp
  have hQnorm : ‖Q‖ ^ 2 = k := by
    rw [norm_sq_eq_re_trace, hQ.1.eq, hQ.2, hQk]
    simp
  have hcross :
      ((P * U)ᴴ * (U * Q)).trace = (P * U * Q * Uᴴ).trace := by
    rw [conjTranspose_mul, hP.1.eq]
    rw [show (Uᴴ * P) * (U * Q) = Uᴴ * (P * U * Q) by noncomm_ring]
    exact Matrix.trace_mul_comm Uᴴ (P * U * Q)
  have hminus : edgeMinus P Q U =
      2 * k - 2 * (P * U * Q * Uᴴ).trace.re := by
    rw [edgeMinus, norm_sq_sub, norm_mul_unitary _ hU, norm_unitary_mul hU,
      hPnorm, hQnorm, hcross]
    ring
  have hplus : edgePlus P Q U =
      2 * k + 2 * (P * U * Q * Uᴴ).trace.re := by
    rw [edgePlus, norm_sq_add, norm_mul_unitary _ hU, norm_unitary_mul hU,
      hPnorm, hQnorm, hcross]
    ring
  constructor
  · rw [hminus, transitionProbability]
    field_simp
  · rw [hplus, transitionProbability]
    field_simp

/-- The normalized overlap really is a transition probability, not a signed
cross-moment merely called one on the card. -/
theorem transitionProbability_mem_Icc {P Q U : Matrix n n ℂ}
    (hP : IsProjector P) (hQ : IsProjector Q) (hU : U ∈ unitaryGroup n ℂ)
    {k : ℝ} (hk : k ≠ 0) (hPk : P.trace = (k : ℂ)) (hQk : Q.trace = (k : ℂ)) :
    transitionProbability P Q U k ∈ Set.Icc (0 : ℝ) 1 := by
  have hbooks := edge_books_projector hP hQ hU hk hPk hQk
  have hPnorm : ‖P‖ ^ 2 = k := by
    rw [norm_sq_eq_re_trace, hP.1.eq, hP.2, hPk]
    simp
  have hk0 : 0 ≤ k := by rw [← hPnorm]; positivity
  have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk)
  constructor
  · exact div_nonneg (transitionTrace_re_nonneg hP hQ) hk0
  · have hnonneg : 0 ≤ 2 * k * (1 - transitionProbability P Q U k) := by
      rw [← hbooks.1]
      exact sq_nonneg _
    have hfactor : 0 ≤ 1 - transitionProbability P Q U k :=
      (mul_nonneg_iff_of_pos_left (show 0 < 2 * k by positivity)).mp hnonneg
    linarith

/-- The normalized overlap is the literal complex trace divided by `k`, not
merely an unrelated real-part convention. -/
theorem transitionProbability_eq_trace_div {P Q U : Matrix n n ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) {k : ℝ} :
    ((transitionProbability P Q U k : ℝ) : ℂ) =
      (P * U * Q * Uᴴ).trace / (k : ℂ) := by
  rw [transitionProbability, transitionTrace_eq_re hP hQ]
  simp

/-- The k=1, one-dimensional identity-transport check: the two eigenvalues
coincide, so E⁻=0, E⁺=4 and p=1. -/
theorem rank_one_identity_check :
    edgeMinus (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 = 0 ∧
    edgePlus (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 = 4 ∧
    transitionProbability (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 1 = 1 := by
  constructor
  · rw [edgeMinus, norm_sq_eq_sum]
    norm_num
  constructor
  · rw [edgePlus, norm_sq_eq_sum]
    norm_num [Matrix.one_apply]
  · norm_num [transitionProbability]

#print axioms norm_sq_eq_sum
#print axioms edgeMinus_realDiagonal
#print axioms edgePlus_realDiagonal
#print axioms bornWeight_nonneg
#print axioms bornWeight_row_sum
#print axioms bornWeight_col_sum
#print axioms norm_sq_eq_re_trace
#print axioms norm_unitary_mul
#print axioms norm_mul_unitary
#print axioms norm_sq_add
#print axioms norm_sq_sub
#print axioms transitionTrace_star
#print axioms transitionTrace_im
#print axioms transitionTrace_eq_re
#print axioms transitionTrace_re_nonneg
#print axioms edge_books_projector
#print axioms transitionProbability_mem_Icc
#print axioms transitionProbability_eq_trace_div
#print axioms rank_one_identity_check

end AtlasB185


/-! ## B185 — Born weights are doubly stochastic only one way

Integrated from `.ultramath/smwvp3cvb/m11/B185_BornWeights.lean`.
-/

/-!
# B185: Born weights of a unitary transport

For a unitary matrix `U`, the entrywise squared moduli form a doubly
stochastic matrix.  This is the basis-vector weight assertion in B185.
No nondegeneracy hypothesis on either Hermitian end block is needed.

The only extra formal convention is to write the matrix element
`⟨a|U|b⟩` as `U a b`, and its squared modulus as `Complex.normSq (U a b)`.
-/

open scoped ComplexConjugate

namespace RelationalAtlas.B185

/-- Born transition weights in fixed orthonormal bases, expressed in the
matrix coordinates of the transport. -/
def bornWeights {n : Type*} (U : Matrix n n ℂ) : Matrix n n ℝ :=
  fun a b => Complex.normSq (U a b)

@[simp] theorem bornWeights_nonneg {n : Type*} (U : Matrix n n ℂ) (a b : n) :
    0 ≤ bornWeights U a b :=
  Complex.normSq_nonneg _

/-- A row of Born weights is the corresponding diagonal entry of `U * Uᴴ`. -/
theorem sum_bornWeights_row {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (a : n) :
    ∑ b, bornWeights U a b = 1 := by
  apply Complex.ofReal_injective
  simp only [bornWeights, Complex.ofReal_sum, Complex.ofReal_one,
    Complex.normSq_eq_conj_mul_self]
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) a) a
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, mul_comm] using h

/-- A column of Born weights is the corresponding diagonal entry of `Uᴴ * U`. -/
theorem sum_bornWeights_col {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (b : n) :
    ∑ a, bornWeights U a b = 1 := by
  apply Complex.ofReal_injective
  simp only [bornWeights, Complex.ofReal_sum, Complex.ofReal_one,
    Complex.normSq_eq_conj_mul_self]
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) b) b
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] using h

/-- **B185 Born-weight kernel.**  Squared moduli of a unitary transport are
nonnegative and have unit row and column sums, hence are doubly stochastic. -/
theorem bornWeights_mem_doublyStochastic {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    bornWeights U ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨bornWeights_nonneg U, sum_bornWeights_row hU, sum_bornWeights_col hU⟩

/-- A one-dimensional nonunitary transport used as a boundary check. -/
def nonunitaryTransport : Matrix (Fin 1) (Fin 1) ℂ := !![2]

@[simp] theorem bornWeights_nonunitaryTransport :
    bornWeights nonunitaryTransport = !![(4 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [bornWeights, nonunitaryTransport, Complex.normSq_apply]

/-- The unitary hypothesis cannot simply be omitted: the sole row (and
column) of the squared-modulus weight matrix of `[2]` sums to `4`. -/
theorem nonunitaryTransport_weight_sum_ne_one :
    (∑ b, bornWeights nonunitaryTransport 0 b) ≠ 1 := by
  rw [bornWeights_nonunitaryTransport]
  norm_num [Fin.sum_univ_one]

/-- The boundary transport genuinely fails the unitary hypothesis. -/
theorem nonunitaryTransport_not_unitary :
    nonunitaryTransport ∉ Matrix.unitaryGroup (Fin 1) ℂ := by
  intro h
  exact nonunitaryTransport_weight_sum_ne_one (sum_bornWeights_row h 0)

/-- Consequently the nonunitary witness is not doubly stochastic. -/
theorem nonunitaryTransport_not_doublyStochastic :
    bornWeights nonunitaryTransport ∉ doublyStochastic ℝ (Fin 1) := by
  intro h
  exact nonunitaryTransport_weight_sum_ne_one
    (sum_row_of_mem_doublyStochastic h 0)


/-- Equal-amplitude, equal-phase transport: every entry has modulus squared
`1/2`, but the two columns are identical, so the transport is not unitary. -/
noncomputable def equalPhaseTransport : Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ _ => (1 + Complex.I) / 2

@[simp] theorem bornWeights_equalPhaseTransport :
    bornWeights equalPhaseTransport = fun _ _ => (1 / 2 : ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [bornWeights, equalPhaseTransport, Complex.normSq_apply]

/-- **Boundary correction to B185's closing prose.**  Nonunitarity alone does
not imply that the Born weights fail to be doubly stochastic. -/
theorem equalPhaseTransport_bornWeights_doublyStochastic :
    bornWeights equalPhaseTransport ∈ doublyStochastic ℝ (Fin 2) := by
  refine mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩
  · intro a b
    change 0 ≤ bornWeights equalPhaseTransport a b
    rw [bornWeights_equalPhaseTransport]
    norm_num
  · intro a
    change ∑ b, bornWeights equalPhaseTransport a b = 1
    simp [bornWeights_equalPhaseTransport]
  · intro b
    change ∑ a, bornWeights equalPhaseTransport a b = 1
    simp [bornWeights_equalPhaseTransport]

/-- The equal-phase witness is not unitary: the `(0,1)` entry of
`U * Uᴴ` is nonzero. -/
theorem equalPhaseTransport_not_unitary :
    equalPhaseTransport ∉ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro hU
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) 0) 1
  norm_num [equalPhaseTransport, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.one_apply, Complex.ext_iff] at h

/-- The closing universal implication, read literally, has a counterexample. -/
theorem exists_nonunitary_with_doublyStochastic_bornWeights :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ,
      U ∉ Matrix.unitaryGroup (Fin 2) ℂ ∧
        bornWeights U ∈ doublyStochastic ℝ (Fin 2) :=
  ⟨equalPhaseTransport, equalPhaseTransport_not_unitary,
    equalPhaseTransport_bornWeights_doublyStochastic⟩

/-- Direct negation of the literal closing universal claim. -/
theorem not_nonunitary_implies_weights_not_doublyStochastic :
    ¬ (∀ U : Matrix (Fin 2) (Fin 2) ℂ,
      U ∉ Matrix.unitaryGroup (Fin 2) ℂ →
        bornWeights U ∉ doublyStochastic ℝ (Fin 2)) := by
  intro h
  obtain ⟨U, hU, hW⟩ := exists_nonunitary_with_doublyStochastic_bornWeights
  exact h U hU hW

#print axioms RelationalAtlas.B185.sum_bornWeights_row
#print axioms RelationalAtlas.B185.sum_bornWeights_col
#print axioms RelationalAtlas.B185.bornWeights_mem_doublyStochastic
#print axioms RelationalAtlas.B185.bornWeights_nonunitaryTransport
#print axioms RelationalAtlas.B185.nonunitaryTransport_weight_sum_ne_one
#print axioms RelationalAtlas.B185.nonunitaryTransport_not_unitary
#print axioms RelationalAtlas.B185.nonunitaryTransport_not_doublyStochastic
#print axioms RelationalAtlas.B185.bornWeights_equalPhaseTransport
#print axioms RelationalAtlas.B185.equalPhaseTransport_bornWeights_doublyStochastic
#print axioms RelationalAtlas.B185.equalPhaseTransport_not_unitary
#print axioms RelationalAtlas.B185.exists_nonunitary_with_doublyStochastic_bornWeights
#print axioms RelationalAtlas.B185.not_nonunitary_implies_weights_not_doublyStochastic

end RelationalAtlas.B185


/-! ## B187 — the loop-kernel equivalence and the cover identities

Integrated from `.ultramath/smwvp3cvb/m5/B187.lean`.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace RelationalAtlas.B187

universe u v

variable {ι : Type u} {m : Type v} [Fintype m] [DecidableEq m]

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

/-- Frobenius expansion of a sum. -/
theorem norm_sq_add (X Y : Matrix m m ℂ) :
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
theorem norm_sq_sub (X Y : Matrix m m ℂ) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 - 2 * (Xᴴ * Y).trace.re := by
  have h := norm_sq_add X (-Y)
  simpa [sub_eq_add_neg, Matrix.mul_neg, trace_neg] using h

/-- Parallel transport of an endomorphism across an oriented edge. -/
def transport (U : Matrix m m ℂ) (X : Matrix m m ℂ) : Matrix m m ℂ :=
  U * X * Uᴴ

/-- The two displayed local energies. -/
noncomputable def eminus (U X Y : Matrix m m ℂ) : ℝ := ‖X - transport U Y‖ ^ 2
noncomputable def eplus (U X Y : Matrix m m ℂ) : ℝ := ‖X + transport U Y‖ ^ 2

/-- The two residuals in the double-cover expansion. -/
def parallelResidual (U Si Sj : Matrix m m ℂ) := Si - transport U Sj
def antiResidual (U Ti Tj : Matrix m m ℂ) := Ti + transport U Tj

/-- The exact two-squares computation on one base edge and its two lifts. -/
theorem cover_two_squares (U Si Sj Ti Tj : Matrix m m ℂ) :
    ‖(Si + Ti) - transport U (Sj - Tj)‖ ^ 2 +
      ‖(Si - Ti) - transport U (Sj + Tj)‖ ^ 2 =
    2 * eminus U Si Sj + 2 * eplus U Ti Tj := by
  have hplus : (Si + Ti) - transport U (Sj - Tj) =
      parallelResidual U Si Sj + antiResidual U Ti Tj := by
    simp only [parallelResidual, antiResidual, transport, Matrix.mul_sub,
      Matrix.sub_mul]
    abel
  have hminus : (Si - Ti) - transport U (Sj + Tj) =
      parallelResidual U Si Sj - antiResidual U Ti Tj := by
    simp only [parallelResidual, antiResidual, transport, Matrix.mul_add,
      Matrix.add_mul]
    abel
  rw [hplus, hminus]
  have hp := norm_sq_add (parallelResidual U Si Sj) (antiResidual U Ti Tj)
  have hm := norm_sq_sub (parallelResidual U Si Sj) (antiResidual U Ti Tj)
  simp only [parallelResidual, antiResidual, eminus, eplus] at hp hm ⊢
  nlinarith

/-- The other choice `S - T` on the even sheet has the same two-squares sum. -/
theorem cover_two_squares_swap (U Si Sj Ti Tj : Matrix m m ℂ) :
    ‖(Si - Ti) - transport U (Sj + Tj)‖ ^ 2 +
      ‖(Si + Ti) - transport U (Sj - Tj)‖ ^ 2 =
    2 * eminus U Si Sj + 2 * eplus U Ti Tj := by
  rw [add_comm]
  exact cover_two_squares U Si Sj Ti Tj

/-- Real scalar multiplication commutes with transport. -/
theorem transport_real_smul (U X : Matrix m m ℂ) (r : ℝ) :
    transport U (r • X) = r • transport U X := by
  simp only [transport, Matrix.mul_smul, Matrix.smul_mul, smul_assoc]

/-- Flipping a field on one end of an edge interchanges the two local books. -/
theorem flip_eminus_eq_eplus {εi εj : ℝ} (hε : εi = -εj) (hεi : |εi| = 1)
    (U Di Dj : Matrix m m ℂ) :
    eminus U (εi • Di) (εj • Dj) = eplus U Di Dj := by
  have hε' : εj = -εi := by linarith
  subst εj
  have hfactor : εi • Di - transport U ((-εi) • Dj) =
      εi • (Di + transport U Dj) := by
    rw [transport_real_smul]
    module
  rw [eminus, eplus, hfactor, norm_smul, Real.norm_eq_abs, hεi]
  norm_num

/-- Flipping a field on one end of an edge also sends the opposite book to the
connection book. -/
theorem flip_eplus_eq_eminus {εi εj : ℝ} (hε : εi = -εj) (hεi : |εi| = 1)
    (U Di Dj : Matrix m m ℂ) :
    eplus U (εi • Di) (εj • Dj) = eminus U Di Dj := by
  have hε' : εj = -εi := by linarith
  subst εj
  have hfactor : εi • Di + transport U ((-εi) • Dj) =
      εi • (Di - transport U Dj) := by
    rw [transport_real_smul]
    module
  rw [eminus, eplus, hfactor, norm_smul, Real.norm_eq_abs, hεi]
  norm_num


section GraphEnergies

variable [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- Connection energy: half the sum over ordered adjacent pairs, hence the sum
over undirected edges with the convention of B183. -/
noncomputable def Eminus (U : ι → ι → Matrix m m ℂ)
    (D : ι → Matrix m m ℂ) : ℝ :=
  (∑ i, ∑ j, if G.Adj i j then eminus (U i j) (D i) (D j) else 0) / 2

/-- The opposite book, with exactly the displayed plus sign. -/
noncomputable def Eplus (U : ι → ι → Matrix m m ℂ)
    (D : ι → Matrix m m ℂ) : ℝ :=
  (∑ i, ∑ j, if G.Adj i j then eplus (U i j) (D i) (D j) else 0) / 2

/-- Anti-parallel sections.  This is `D i = -U D_j U*`, written without
subtraction so that it is literally the zero residual of `Eplus`. -/
def IsAntiParallel (U : ι → ι → Matrix m m ℂ)
    (D : ι → Matrix m m ℂ) : Prop :=
  ∀ i j, G.Adj i j → D i + transport (U i j) (D j) = 0

/-- The kernel of the opposite energy is exactly the set of anti-parallel
sections; no connectedness or unitarity is needed for this equivalence. -/
theorem Eplus_eq_zero_iff (U : ι → ι → Matrix m m ℂ)
    (D : ι → Matrix m m ℂ) :
    Eplus G U D = 0 ↔ IsAntiParallel G U D := by
  simp only [Eplus, eplus]
  have hnn : ∀ i j, 0 ≤ if G.Adj i j then
      ‖D i + transport (U i j) (D j)‖ ^ 2 else 0 := by
    intro i j
    split_ifs <;> positivity
  rw [div_eq_zero_iff, or_iff_left (by norm_num : (2 : ℝ) ≠ 0),
    Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  split_ifs with hij
  · simp [hij, pow_eq_zero_iff, IsAntiParallel]
  · simp [hij, IsAntiParallel]

/-- The sign-twisted transport on endomorphism fields: this is `-Ad(U)`, not
`Ad(-U)`. -/
def signTwistedTransport (U X : Matrix m m ℂ) : Matrix m m ℂ :=
  -transport U X

/-- The opposite book is connection energy for the sign-twisted transport. -/
theorem Eplus_eq_signTwistedTransport [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (U : ι → ι → Matrix m m ℂ) (D : ι → Matrix m m ℂ) :
    Eplus G U D = (∑ i, ∑ j, if G.Adj i j then
      ‖D i - signTwistedTransport (U i j) (D j)‖ ^ 2 else 0) / 2 := by
  simp [Eplus, eplus, signTwistedTransport, sub_neg_eq_add]

/-- A bipartition is a sign which changes across every edge. -/
def IsBipartiteSign (ε : ι → ℝ) : Prop :=
  ∀ i j, G.Adj i j → ε i = -ε j

/-- The actual sign-flipped field. -/
noncomputable def flippedField (ε : ι → ℝ) (D : ι → Matrix m m ℂ) :=
  fun i => ε i • D i

theorem Eminus_flippedField (U : ι → ι → Matrix m m ℂ) (D : ι → Matrix m m ℂ) (ε : ι → ℝ)
    (hε : IsBipartiteSign G ε) (hεnorm : ∀ i, |ε i| = 1) :
    Eminus G U (flippedField ε D) = Eplus G U D := by
  unfold Eminus Eplus
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : G.Adj i j
  · simp only [hij, if_true, flippedField]
    exact flip_eminus_eq_eplus (hε i j hij) (hεnorm i) _ _ _
  · simp [hij]

theorem Eplus_flippedField (U : ι → ι → Matrix m m ℂ) (D : ι → Matrix m m ℂ) (ε : ι → ℝ)
    (hε : IsBipartiteSign G ε) (hεnorm : ∀ i, |ε i| = 1) :
    Eplus G U (flippedField ε D) = Eminus G U D := by
  unfold Eminus Eplus
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : G.Adj i j
  · simp only [hij, if_true, flippedField]
    exact flip_eplus_eq_eminus (hε i j hij) (hεnorm i) _ _ _
  · simp [hij]

end GraphEnergies

section DoubleCover

/-- The bipartite double cover: a base edge lifts precisely when the sheet
changes. -/
def bipartiteDoubleCover (G : SimpleGraph ι) : SimpleGraph (ι × Bool) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 ≠ y.2
  symm := ⟨by
    rintro ⟨i, b⟩ ⟨j, c⟩ ⟨h, hbc⟩
    exact ⟨h.symm, hbc.symm⟩⟩
  loopless := ⟨by
    rintro ⟨i, b⟩ ⟨h, -⟩
    exact G.loopless.irrefl i h⟩

noncomputable instance decidableRelBipartiteDoubleCover
    (G : SimpleGraph ι) [DecidableRel G.Adj] :
    DecidableRel (bipartiteDoubleCover G).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Transport on a lifted edge retains its base matrix. -/
def coverTransport (U : ι → ι → Matrix m m ℂ) :
    ι × Bool → ι × Bool → Matrix m m ℂ :=
  fun x y => U x.1 y.1

/-- The even/odd sheet decomposition, using `S + T` on `false` and `S - T` on
`true`. -/
def coverFieldPlus (S T : ι → Matrix m m ℂ) :
    ι × Bool → Matrix m m ℂ :=
  fun x => if x.2 then S x.1 - T x.1 else S x.1 + T x.1

/-- The exchanged sign decomposition, for the displayed `S - T` alternative. -/
def coverFieldMinus (S T : ι → Matrix m m ℂ) :
    ι × Bool → Matrix m m ℂ :=
  fun x => if x.2 then S x.1 + T x.1 else S x.1 - T x.1

variable [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- Sum over the two lifts of an ordered base edge. -/
theorem cover_ordered_summand_plus (U : ι → ι → Matrix m m ℂ)
    (S T : ι → Matrix m m ℂ) (i j : ι) :
    (∑ b : Bool, ∑ c : Bool,
      if (bipartiteDoubleCover G).Adj (i, b) (j, c) then
        eminus (coverTransport U (i, b) (j, c))
          (coverFieldPlus S T (i, b)) (coverFieldPlus S T (j, c)) else 0) =
    if G.Adj i j then
      2 * eminus (U i j) (S i) (S j) + 2 * eplus (U i j) (T i) (T j) else 0 := by
  classical
  by_cases hij : G.Adj i j
  · simp [bipartiteDoubleCover, hij, Fintype.sum_bool, coverTransport,
      coverFieldPlus]
    exact cover_two_squares_swap (U i j) (S i) (S j) (T i) (T j)
  · simp [bipartiteDoubleCover, hij]

/-- Rearranging the four cover indices leaves exactly two lifted terms for each
ordered base pair. -/
theorem cover_inner_summand_plus (U : ι → ι → Matrix m m ℂ)
    (S T : ι → Matrix m m ℂ) (i : ι) :
    (∑ b : Bool, ∑ j : ι, ∑ c : Bool,
      if (bipartiteDoubleCover G).Adj (i, b) (j, c) then
        eminus (coverTransport U (i, b) (j, c))
          (coverFieldPlus S T (i, b)) (coverFieldPlus S T (j, c)) else 0) =
    ∑ j : ι, if G.Adj i j then
      2 * eminus (U i j) (S i) (S j) + 2 * eplus (U i j) (T i) (T j) else 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => cover_ordered_summand_plus G U S T i j

/-- **B187, cover identity.**  Both lifted squares together give twice the
connection book of `S` plus twice the opposite book of `T`.  No additional
unitarity hypothesis is used in this algebraic form. -/
theorem Eminus_cover_plus (U : ι → ι → Matrix m m ℂ)
    (S T : ι → Matrix m m ℂ) :
    Eminus (bipartiteDoubleCover G) (coverTransport U) (coverFieldPlus S T) =
      2 * Eminus G U S + 2 * Eplus G U T := by
  classical
  unfold Eminus Eplus
  simp only [Fintype.sum_prod_type]
  simp_rw [cover_inner_summand_plus G U S T]
  have hterm : ∀ i j, (if G.Adj i j then
      2 * eminus (U i j) (S i) (S j) + 2 * eplus (U i j) (T i) (T j) else 0) =
      2 * (if G.Adj i j then eminus (U i j) (S i) (S j) else 0) +
      2 * (if G.Adj i j then eplus (U i j) (T i) (T j) else 0) := by
    intro i j
    by_cases hij : G.Adj i j <;> simp [hij]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  have hsum2 (f : ι → ι → ℝ) :
      (∑ i, ∑ j, f i j * 2) = (∑ i, ∑ j, f i j) * 2 := by
    simp only [Finset.sum_mul]
  ring_nf
  simp_rw [hsum2]
  ring

end DoubleCover



/-- Negating both vertex values negates the opposite residual, hence leaves
its squared norm unchanged. -/
theorem Eplus_negField [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (U : ι → ι → Matrix m m ℂ) (T : ι → Matrix m m ℂ) :
    Eplus G U (fun i => -T i) = Eplus G U T := by
  unfold Eplus eplus
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : G.Adj i j
  · simp only [hij, if_true]
    have hneg : -T i + transport (U i j) (-T j) =
        -(T i + transport (U i j) (T j)) := by
      simp only [transport, Matrix.mul_neg, Matrix.neg_mul]
      abel
    rw [hneg, norm_neg]
  · simp [hij]

/-- Exchanging which sheet carries `S + T` is the same construction with `T`
replaced by `-T`. -/
theorem coverFieldMinus_eq_plus_neg (S T : ι → Matrix m m ℂ) :
    coverFieldMinus S T = coverFieldPlus S (fun i => -T i) := by
  funext ⟨i, b⟩
  cases b <;> simp [coverFieldMinus, coverFieldPlus, sub_eq_add_neg]

/-- **B187, cover identity for `S - T`.** -/
theorem Eminus_cover_minus [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (U : ι → ι → Matrix m m ℂ)
    (S T : ι → Matrix m m ℂ) :
    Eminus (bipartiteDoubleCover G) (coverTransport U) (coverFieldMinus S T) =
      2 * Eminus G U S + 2 * Eplus G U T := by
  rw [coverFieldMinus_eq_plus_neg, Eminus_cover_plus, Eplus_negField]


section LoopKernel

/-- Transport is additive. -/
theorem transport_add (U X Y : Matrix m m ℂ) :
    transport U (X + Y) = transport U X + transport U Y := by
  simp [transport, Matrix.mul_add, Matrix.add_mul]

/-- Matrix transport is a multiplicative action, so a walk has a holonomy. -/
theorem transport_one (X : Matrix m m ℂ) : transport 1 X = X := by
  simp [transport]

theorem transport_mul (U V X : Matrix m m ℂ) :
    transport (U * V) X = transport U (transport V X) := by
  simp only [transport, conjTranspose_mul]
  noncomm_ring

theorem transport_neg (U X : Matrix m m ℂ) :
    transport U (-X) = -transport U X := by
  simp [transport]

theorem transport_complex_smul (U X : Matrix m m ℂ) (c : ℂ) :
    transport U (c • X) = c • transport U X := by
  simp only [transport, Matrix.mul_smul, Matrix.smul_mul, smul_assoc]

/-- Unitary connection in the B183 convention.  The minus in the reverse
matrix is immaterial to `Ad`, but is retained here because it gives the exact
reverse-holonomy sign needed by the walk computation. -/
structure IsUnitaryTransport (G : SimpleGraph ι) (U : ι → ι → Matrix m m ℂ) : Prop where
  mem_unitary : ∀ i j, G.Adj i j → U i j ∈ unitaryGroup m ℂ
  reverse : ∀ i j, G.Adj i j → U j i = -(U i j)ᴴ

variable {G : SimpleGraph ι} {U : ι → ι → Matrix m m ℂ}

/-- Product of transport matrices along a graph walk. -/
noncomputable def holonomy (U : ι → ι → Matrix m m ℂ) {i j : ι}
    (p : G.Walk i j) : Matrix m m ℂ :=
  p.rec (motive := fun _ _ _ => Matrix m m ℂ)
    (fun {u} => 1) (fun {u v w} h p ih => U u v * ih)

@[simp] theorem holonomy_nil (U : ι → ι → Matrix m m ℂ) (i : ι) :
    holonomy U (SimpleGraph.Walk.nil : G.Walk i i) = 1 := rfl

@[simp] theorem holonomy_cons {i j k : ι} (h : G.Adj i j) (p : G.Walk j k) :
    holonomy U (p.cons h) = U i j * holonomy U p := rfl

/-- The sign attached to a walk in the anti-parallel equation. -/
def walkSign {i j : ι} (p : G.Walk i j) : ℂ := (-1) ^ p.length

/-- Fixed points of all signed based loop holonomies. -/
def LoopFixed (G : SimpleGraph ι) (U : ι → ι → Matrix m m ℂ) (base : ι) (X : Matrix m m ℂ) : Prop :=
  ∀ p : G.Walk base base, walkSign p • transport (holonomy U p) X = X

/-- Anti-parallelity propagates along every walk. -/
theorem antiParallel_eq_signed_transport_walk [DecidableRel G.Adj]
    {D : ι → Matrix m m ℂ} (hD : IsAntiParallel G U D)
    {i j : ι} (p : G.Walk i j) :
    D i = walkSign p • transport (holonomy U p) (D j) := by
  induction p with
  | nil => simp [walkSign, transport_one]
  | @cons u v w huv p ih =>
      have hstep : D u + transport (U u v) (D v) = 0 := hD u v huv
      have hfirst : D u = -transport (U u v) (D v) :=
        eq_neg_of_add_eq_zero_left hstep
      rw [hfirst, ih, transport_complex_smul, ← transport_mul]
      simp only [walkSign, SimpleGraph.Walk.length_cons, holonomy_cons,
        pow_succ, smul_smul]
      module

/-- In particular every anti-parallel section restricts to a fixed point of
all signed based loop holonomies. -/
theorem IsAntiParallel.loopFixed [DecidableRel G.Adj] {base : ι}
    {D : ι → Matrix m m ℂ} (hD : IsAntiParallel G U D) :
    LoopFixed G U base (D base) := by
  intro p
  exact (antiParallel_eq_signed_transport_walk hD p).symm


/-- Holonomy multiplies along concatenation. -/
theorem holonomy_append {i j k : ι} (p : G.Walk i j) (q : G.Walk j k) :
    holonomy U (p.append q) = holonomy U p * holonomy U q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, Matrix.mul_assoc]

/-- Every walk holonomy is unitary. -/
theorem holonomy_mem_unitary (hU : IsUnitaryTransport G U) {i j : ι}
    (p : G.Walk i j) : holonomy U p ∈ unitaryGroup m ℂ := by
  induction p with
  | nil => exact one_mem _
  | cons h p ih => exact mul_mem (hU.mem_unitary _ _ h) ih

/-- The sign attached to a walk has square one. -/
theorem walkSign_mul_self {i j : ι} (p : G.Walk i j) :
    walkSign p * walkSign p = 1 := by
  simp only [walkSign, ← pow_add]
  rw [← two_mul, pow_mul]
  norm_num

@[simp] theorem star_walkSign {i j : ι} (p : G.Walk i j) :
    star (walkSign p) = walkSign p := by
  simp [walkSign]

@[simp] theorem walkSign_nil (i : ι) :
    walkSign (SimpleGraph.Walk.nil : G.Walk i i) = 1 := by
  simp [walkSign]

@[simp] theorem walkSign_append {i j k : ι} (p : G.Walk i j) (q : G.Walk j k) :
    walkSign (p.append q) = walkSign p * walkSign q := by
  simp [walkSign, pow_add]

@[simp] theorem walkSign_reverse {i j : ι} (p : G.Walk i j) :
    walkSign p.reverse = walkSign p := by
  simp [walkSign]

/-- Reversal adjoints holonomy, with precisely the B183 reverse-edge minus. -/
theorem holonomy_reverse (hU : IsUnitaryTransport G U) {i j : ι}
    (p : G.Walk i j) :
    holonomy U p.reverse = walkSign p • (holonomy U p)ᴴ := by
  induction p with
  | nil => simp [walkSign]
  | @cons u v w huv p ih =>
      rw [SimpleGraph.Walk.reverse_cons, holonomy_append, ih]
      simp only [holonomy_cons, holonomy_nil, Matrix.mul_one,
        hU.reverse u v huv, walkSign, SimpleGraph.Walk.length_cons, pow_succ,
        conjTranspose_mul, Matrix.smul_mul, Matrix.mul_neg, smul_neg]
      module

/-- Adjoint transport undoes the sign on a reverse holonomy. -/
theorem transport_holonomy_reverse (hU : IsUnitaryTransport G U) {i j : ι}
    (p : G.Walk i j) (X : Matrix m m ℂ) :
    transport (holonomy U p.reverse) X = transport (holonomy U p)ᴴ X := by
  rw [holonomy_reverse hU]
  simp only [transport, conjTranspose_smul, star_walkSign]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [walkSign_mul_self, one_smul]


/-- Conjugation by a unitary and by its adjoint are inverse operations. -/
theorem transport_conjTranspose_transport {W : Matrix m m ℂ}
    (hW : W ∈ unitaryGroup m ℂ) (X : Matrix m m ℂ) :
    transport Wᴴ (transport W X) = X := by
  rw [← transport_mul, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff').1 hW, transport_one]

theorem transport_transport_conjTranspose {W : Matrix m m ℂ}
    (hW : W ∈ unitaryGroup m ℂ) (X : Matrix m m ℂ) :
    transport W (transport Wᴴ X) = X := by
  rw [← transport_mul, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff).1 hW, transport_one]

/-- A useful inverse form of a transported equation, with its scalar kept
explicit. -/
theorem smul_transport_iff {W X Y : Matrix m m ℂ}
    (hW : W ∈ unitaryGroup m ℂ) (c : ℂ) :
    c • transport W Y = X ↔ c • Y = transport Wᴴ X := by
  constructor
  · intro h
    have hc := congrArg (fun Z => transport Wᴴ Z) h
    rw [transport_complex_smul, transport_conjTranspose_transport hW] at hc
    exact hc
  · intro h
    have hc := congrArg (fun Z => transport W Z) h
    rw [transport_complex_smul, transport_transport_conjTranspose hW] at hc
    exact hc

/-- Candidate value at the endpoint of a based walk. -/
noncomputable def pathValue (U : ι → ι → Matrix m m ℂ) {base i : ι}
    (X : Matrix m m ℂ) (p : G.Walk base i) : Matrix m m ℂ :=
  walkSign p • transport (holonomy U p)ᴴ X

/-- The based loop conditions are exactly what makes the candidate value
independent of the chosen walk. -/
theorem pathValue_independent (hU : IsUnitaryTransport G U) {base i : ι}
    {X : Matrix m m ℂ} (hX : LoopFixed G U base X)
    (p q : G.Walk base i) : pathValue U X p = pathValue U X q := by
  have hloop := hX (p.append q.reverse)
  rw [walkSign_append, holonomy_append, transport_mul,
    transport_holonomy_reverse hU, walkSign_reverse] at hloop
  have heq := (smul_transport_iff (holonomy_mem_unitary hU p)
    (walkSign p * walkSign q) (Y := transport (holonomy U q)ᴴ X)).1 hloop
  have hc := congrArg (fun Z => walkSign p • Z) heq
  simp only [smul_smul] at hc
  have hfactor : walkSign p * (walkSign p * walkSign q) = walkSign q := by
    calc
      walkSign p * (walkSign p * walkSign q) =
          (walkSign p * walkSign p) * walkSign q := by ring
      _ = walkSign q := by rw [walkSign_mul_self, one_mul]
  rw [hfactor] at hc
  exact hc.symm

/-- Transport by a negative matrix is unchanged: precisely `Ad(-U)=Ad(U)`. -/
theorem transport_neg_left (U X : Matrix m m ℂ) :
    transport (-U) X = transport U X := by
  simp [transport]

/-- Appending one edge prepends the inverse transport and one minus sign. -/
theorem pathValue_append_adj (hU : IsUnitaryTransport G U) {base i j : ι}
    (X : Matrix m m ℂ) (p : G.Walk base j) (h : G.Adj j i) :
    pathValue U X (p.append h.toWalk) =
      -transport (U j i)ᴴ (pathValue U X p) := by
  have hs : walkSign h.toWalk = -1 := by simp [walkSign]
  simp only [pathValue, walkSign_append, holonomy_append, holonomy_cons,
    holonomy_nil, Matrix.mul_one, conjTranspose_mul, transport_mul, hs,
    transport_complex_smul, smul_smul]
  module

/-- A chosen walk from the base to every vertex of a connected graph. -/
noncomputable def rootWalk (G : SimpleGraph ι) (base : ι) (hG : G.Connected) (i : ι) :
    G.Walk base i := Classical.choice (hG base i)

/-- The extension of a fixed based matrix along chosen walks. -/
noncomputable def extendedField (G : SimpleGraph ι) (U : ι → ι → Matrix m m ℂ)
    (base : ι) (hG : G.Connected) (X : Matrix m m ℂ) : ι → Matrix m m ℂ :=
  fun i => pathValue U X (rootWalk G base hG i)


/-- A trivial-holonomy odd loop has no nonzero fixed matrix. -/
theorem LoopFixed.eq_zero_of_odd_trivial {base : ι} {X : Matrix m m ℂ}
    (hX : LoopFixed G U base X) (p : G.Walk base base)
    (hp : Odd p.length) (hW : holonomy U p = 1) : X = 0 := by
  have hx := hX p
  simp only [walkSign, hp.neg_one_pow, hW, transport_one, neg_smul, one_smul] at hx
  have hxx : X + X = 0 := by
    have h := congrArg (fun Y => X + Y) hx
    have h' : (0 : Matrix m m ℂ) = X + X := by simpa using h
    exact h'.symm
  have htwo : (2 : ℂ) • X = 0 := by simpa [two_smul] using hxx
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Every anti-parallel field is the extension of its base value along any
chosen based walk. -/
theorem antiParallel_eq_pathValue [DecidableRel G.Adj]
    (hU : IsUnitaryTransport G U) {base i : ι} {D : ι → Matrix m m ℂ}
    (hD : IsAntiParallel G U D) (p : G.Walk base i) :
    D i = pathValue U (D base) p := by
  have hprop := antiParallel_eq_signed_transport_walk hD p
  have heq := (smul_transport_iff (holonomy_mem_unitary hU p)
    (walkSign p) (Y := D i)).1 hprop.symm
  have hc := congrArg (fun Z => walkSign p • Z) heq
  simp only [smul_smul, walkSign_mul_self, one_smul] at hc
  exact hc

/-- Extension returns the based matrix. -/
theorem extendedField_base (hU : IsUnitaryTransport G U) {base : ι}
    (hG : G.Connected) {X : Matrix m m ℂ} (hX : LoopFixed G U base X) :
    extendedField G U base hG X base = X := by
  change pathValue U X (rootWalk G base hG base) = X
  rw [pathValue_independent hU hX (rootWalk G base hG base)
    (SimpleGraph.Walk.nil : G.Walk base base)]
  simp [pathValue, transport_one]

/-- Extension is anti-parallel on every edge. -/
theorem extendedField_isAntiParallel (hU : IsUnitaryTransport G U) {base : ι}
    (hG : G.Connected) {X : Matrix m m ℂ} (hX : LoopFixed G U base X) :
    IsAntiParallel G U (extendedField G U base hG X) := by
  intro i j hij
  let p := rootWalk G base hG j
  have hi : extendedField G U base hG X i =
      pathValue U X (p.append hij.symm.toWalk) :=
    pathValue_independent hU hX _ _
  rw [hi, pathValue_append_adj hU]
  change -transport (U j i)ᴴ (pathValue U X p) +
    transport (U i j) (pathValue U X p) = 0
  rw [hU.reverse i j hij, conjTranspose_neg, conjTranspose_conjTranspose,
    transport_neg_left, neg_add_cancel]

/-- **B187, anti-kernel.**  A based matrix extends uniquely to an anti-parallel
field exactly when it satisfies the sign-twisted fixed-point equation for every
based loop.  This is the fibre form of `ker E⁺ ≅ {...}`. -/
theorem loopFixed_iff_existsUnique_antiParallel [DecidableRel G.Adj]
    (hU : IsUnitaryTransport G U) {base : ι} (hG : G.Connected)
    (X : Matrix m m ℂ) :
    LoopFixed G U base X ↔
      ∃! D : ι → Matrix m m ℂ, IsAntiParallel G U D ∧ D base = X := by
  constructor
  · intro hX
    let D := extendedField G U base hG X
    refine ⟨D, ⟨extendedField_isAntiParallel hU hG hX,
      extendedField_base hU hG hX⟩, ?_⟩
    intro Y hY
    funext i
    calc
      Y i = pathValue U (Y base) (rootWalk G base hG i) :=
        antiParallel_eq_pathValue hU hY.1 _
      _ = pathValue U X (rootWalk G base hG i) := by rw [hY.2]
      _ = D i := rfl
  · rintro ⟨D, ⟨hD, hbase⟩, hunique⟩
    rw [← hbase]
    exact IsAntiParallel.loopFixed hD

/-- The extension of a Hermitian based matrix is Hermitian at every vertex. -/
theorem extendedField_isHermitian (hU : IsUnitaryTransport G U) {base : ι}
    (hG : G.Connected) {X : Matrix m m ℂ} (hX : LoopFixed G U base X)
    (hherm : X.IsHermitian) (i : ι) :
    (extendedField G U base hG X i).IsHermitian := by
  simp only [extendedField, pathValue, Matrix.IsHermitian, conjTranspose_smul,
    star_walkSign, transport, conjTranspose_mul, conjTranspose_conjTranspose,
    hherm.eq]
  rw [Matrix.mul_assoc]

/-- Anti-parallel fields form a complex submodule. -/
def antiParallelSubmodule (G : SimpleGraph ι) (U : ι → ι → Matrix m m ℂ) :
    Submodule ℂ (ι → Matrix m m ℂ) where
  carrier := {D | IsAntiParallel G U D}
  zero_mem' := by
    intro i j hij
    simp [transport]
  add_mem' := by
    intro D E hD hE i j hij
    simp only [Pi.add_apply, transport_add]
    calc
      D i + E i + (transport (U i j) (D j) + transport (U i j) (E j)) =
          (D i + transport (U i j) (D j)) +
            (E i + transport (U i j) (E j)) := by abel
      _ = 0 := by rw [hD i j hij, hE i j hij, add_zero]
  smul_mem' := by
    intro c D hD i j hij
    simp only [Pi.smul_apply, transport_complex_smul]
    calc
      c • D i + c • transport (U i j) (D j) =
          c • (D i + transport (U i j) (D j)) := by module
      _ = 0 := by rw [hD i j hij, smul_zero]

/-- The fixed points of all signed based loop holonomies also form a complex
submodule. -/
def loopFixedSubmodule (G : SimpleGraph ι) (U : ι → ι → Matrix m m ℂ)
    (base : ι) : Submodule ℂ (Matrix m m ℂ) where
  carrier := {X | LoopFixed G U base X}
  zero_mem' := by
    intro p
    simp [transport]
  add_mem' := by
    intro X Y hX hY p
    rw [transport_add, smul_add, hX p, hY p]
  smul_mem' := by
    intro c X hX p
    calc
      walkSign p • transport (holonomy U p) (c • X) =
          c • (walkSign p • transport (holonomy U p) X) := by
        rw [transport_complex_smul]
        simp only [smul_smul]
        rw [mul_comm (walkSign p) c]
      _ = c • X := by rw [hX p]

/-- **B187, literal kernel isomorphism.**  Restriction to the base vertex and
extension along based walks are inverse complex-linear maps. -/
noncomputable def antiParallelLoopFixedLinearEquiv [DecidableRel G.Adj]
    (hU : IsUnitaryTransport G U) {base : ι} (hG : G.Connected) :
    antiParallelSubmodule G U ≃ₗ[ℂ] loopFixedSubmodule G U base where
  toFun D := ⟨D.1 base, IsAntiParallel.loopFixed D.2⟩
  invFun X := ⟨extendedField G U base hG X.1,
    extendedField_isAntiParallel hU hG X.2⟩
  map_add' := by
    intro D E
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c D
    apply Subtype.ext
    rfl
  left_inv := by
    intro D
    apply Subtype.ext
    funext i
    exact (antiParallel_eq_pathValue hU D.2 (rootWalk G base hG i)).symm
  right_inv := by
    intro X
    apply Subtype.ext
    exact extendedField_base hU hG X.2

/-- The same anti-kernel statement with `Eplus = 0` replacing its explicit
anti-parallel residual characterization. -/
theorem loopFixed_iff_existsUnique_Eplus_zero [Fintype ι] [DecidableEq ι]
    [DecidableRel G.Adj] (hU : IsUnitaryTransport G U) {base : ι}
    (hG : G.Connected) (X : Matrix m m ℂ) :
    LoopFixed G U base X ↔
      ∃! D : ι → Matrix m m ℂ, Eplus G U D = 0 ∧ D base = X := by
  rw [loopFixed_iff_existsUnique_antiParallel hU hG]
  constructor
  · rintro ⟨D, ⟨hD, hbase⟩, hunique⟩
    refine ⟨D, ⟨(Eplus_eq_zero_iff G U D).2 hD, hbase⟩, ?_⟩
    intro Y hY
    exact hunique Y ⟨(Eplus_eq_zero_iff G U Y).1 hY.1, hY.2⟩
  · rintro ⟨D, ⟨hD, hbase⟩, hunique⟩
    refine ⟨D, ⟨(Eplus_eq_zero_iff G U D).1 hD, hbase⟩, ?_⟩
    intro Y hY
    exact hunique Y ⟨(Eplus_eq_zero_iff G U Y).2 hY.1, hY.2⟩

end LoopKernel


/-= Axiom audits =-/
#print axioms norm_sq_eq_sum
#print axioms complex_re_sum
#print axioms norm_sq_eq_re_trace
#print axioms norm_sq_add
#print axioms norm_sq_sub
#print axioms cover_two_squares
#print axioms cover_two_squares_swap
#print axioms transport_real_smul
#print axioms flip_eminus_eq_eplus
#print axioms flip_eplus_eq_eminus
#print axioms Eplus_eq_zero_iff
#print axioms Eplus_eq_signTwistedTransport
#print axioms Eminus_flippedField
#print axioms Eplus_flippedField
#print axioms cover_ordered_summand_plus
#print axioms cover_inner_summand_plus
#print axioms Eminus_cover_plus
#print axioms Eplus_negField
#print axioms coverFieldMinus_eq_plus_neg
#print axioms Eminus_cover_minus
#print axioms transport_add
#print axioms transport_one
#print axioms transport_mul
#print axioms transport_neg
#print axioms transport_complex_smul
#print axioms holonomy_nil
#print axioms holonomy_cons
#print axioms antiParallel_eq_signed_transport_walk
#print axioms IsAntiParallel.loopFixed
#print axioms holonomy_append
#print axioms holonomy_mem_unitary
#print axioms walkSign_mul_self
#print axioms star_walkSign
#print axioms walkSign_nil
#print axioms walkSign_append
#print axioms walkSign_reverse
#print axioms holonomy_reverse
#print axioms transport_holonomy_reverse
#print axioms transport_conjTranspose_transport
#print axioms transport_transport_conjTranspose
#print axioms smul_transport_iff
#print axioms pathValue_independent
#print axioms transport_neg_left
#print axioms pathValue_append_adj
#print axioms LoopFixed.eq_zero_of_odd_trivial
#print axioms antiParallel_eq_pathValue
#print axioms extendedField_base
#print axioms extendedField_isAntiParallel
#print axioms extendedField_isHermitian
#print axioms antiParallelSubmodule
#print axioms loopFixedSubmodule
#print axioms antiParallelLoopFixedLinearEquiv
#print axioms loopFixed_iff_existsUnique_antiParallel
#print axioms loopFixed_iff_existsUnique_Eplus_zero

end RelationalAtlas.B187


/-! ## B188 — the two exact minima, complex and real

Integrated from `.ultramath/smwvp3cvb/m16/B188Final.lean`.
-/

set_option maxHeartbeats 800000
noncomputable section

/-! Included checked source: `B188Full.lean`. -/

/-!
# B188: the exact pentagon and the non-contextual bound

The archived card is `cards/html/B188.html`, SHA-256
`8e44c64b187ef61f9fdbab72487d04b51f77268dd511b2a207a05c80fb23300e`.
It states `p_e = Tr(P_i P_j)` for rank-one fields on an odd cycle,
`min Σ p_e = N/2 (1 - cos(π/N))` in `ℂ²` and `0` in `ℝ³`, and gives
`v_i = (c, s cos(4πi/5), s sin(4πi/5))`, `c² = 1/√5`, with
`Σ ⟨ψ|P_i|ψ⟩ = √5 > 2`.

This file uses the ordinary real dot product.  Unit vectors require
`c²+s²=1`, an implicit hypothesis omitted from the displayed coordinate
formula but forced by the card's rank-one-projector Carry hypothesis.
-/


namespace RelationalAtlas.B188

open scoped BigOperators
open Matrix

/-- The ordinary dot product on three real coordinates. -/
def dot3 (v w : Fin 3 → ℝ) : ℝ := ∑ k, v k * w k

/-- The angle in the card's pentagon witness. -/
def pentagonAngle (i : Fin 5) : ℝ := 4 * Real.pi * (i : ℕ) / 5

/-- The card's pentagon vector, with parameters `c` and `s`. -/
def pentagonVector (c s : ℝ) (i : Fin 5) : Fin 3 → ℝ :=
  ![c, s * Real.cos (pentagonAngle i), s * Real.sin (pentagonAngle i)]

lemma dot3_pentagonVector (c s : ℝ) (i j : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s j) =
      c ^ 2 + s ^ 2 * Real.cos (pentagonAngle j - pentagonAngle i) := by
  simp [dot3, pentagonVector, Fin.sum_univ_three, Real.cos_sub]
  ring

lemma pentagonAngle_zero : pentagonAngle 0 = 0 := by
  norm_num [pentagonAngle]

lemma cos_angle_succ_sub (i : Fin 5) :
    Real.cos (pentagonAngle (i + 1) - pentagonAngle i) =
      Real.cos (4 * Real.pi / 5) := by
  fin_cases i
  · congr 1
    norm_num [pentagonAngle]
  · congr 1
    norm_num [pentagonAngle]
    ring
  · congr 1
    norm_num [pentagonAngle]
    ring
  · congr 1
    norm_num [pentagonAngle]
    ring
  · norm_num [pentagonAngle]
    have h := Real.cos_sub_nat_mul_two_pi (16 * Real.pi / 5) 2
    convert h.symm using 1 <;> try ring
    rw [show Real.pi * (-4 / 5) = -(Real.pi * (4 / 5)) by ring, Real.cos_neg]

/-- All five consecutive pentagon vectors have the same overlap. -/
lemma dot3_pentagonVector_succ (c s : ℝ) (i : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s (i + 1)) =
      c ^ 2 + s ^ 2 * Real.cos (4 * Real.pi / 5) := by
  rw [dot3_pentagonVector, cos_angle_succ_sub]

/-- Every displayed pentagon vector is a unit vector when `c²+s²=1`. -/
lemma dot3_pentagonVector_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (i : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s i) = 1 := by
  rw [dot3_pentagonVector]
  simp only [sub_self, Real.cos_zero, mul_one]
  exact hcs

/-- In particular the literal pentagon parameters give unit lines. -/
lemma dot3_literal_pentagon_self {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) (hs : s ^ 2 = 1 - 1 / Real.sqrt 5) (i : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s i) = 1 := by
  apply dot3_pentagonVector_self _ i
  rw [hc, hs]
  ring

/-- The adjacent angle is the supplement of `π/5`. -/
lemma cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -Real.cos (Real.pi / 5) := by
  rw [← Real.cos_pi_sub]
  congr 1
  ring

/-- Exact orthogonality criterion for the displayed umbrella. -/
lemma dot3_pentagonVector_succ_eq_zero {c s : ℝ}
    (h : c ^ 2 = s ^ 2 * Real.cos (Real.pi / 5)) (i : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s (i + 1)) = 0 := by
  rw [dot3_pentagonVector_succ, cos_four_pi_div_five, h]
  ring

lemma sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt_five_ne_zero : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt_five_pos

lemma sq_sqrt_five : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- The two parameter relations in the card imply the orthogonality relation. -/
lemma literal_pentagon_orthogonality_relation :
    1 / Real.sqrt 5 =
      (1 - 1 / Real.sqrt 5) * Real.cos (Real.pi / 5) := by
  rw [Real.cos_pi_div_five]
  field_simp [sqrt_five_ne_zero]
  nlinarith [sq_sqrt_five]

/-- **B188, pentagon mirror edges:** with the unit-vector normalisation
`c²=1/√5`, `s²=1-1/√5`, every cyclic neighbour pair is orthogonal. -/
theorem b188_pentagon_neighbours_orthogonal {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) (hs : s ^ 2 = 1 - 1 / Real.sqrt 5) (i : Fin 5) :
    dot3 (pentagonVector c s i) (pentagonVector c s (i + 1)) = 0 := by
  apply dot3_pentagonVector_succ_eq_zero _ i
  rw [hc, hs]
  exact literal_pentagon_orthogonality_relation

/-- For rank-one real projectors `P_i = v_i v_iᵀ`, the edge overlap is
`Tr(P_iP_j) = (v_i·v_j)²`; hence all five mirror-edge `p_e` vanish. -/
theorem b188_pentagon_mirror_edges {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) (hs : s ^ 2 = 1 - 1 / Real.sqrt 5) (i : Fin 5) :
    (dot3 (pentagonVector c s i) (pentagonVector c s (i + 1))) ^ 2 = 0 := by
  rw [b188_pentagon_neighbours_orthogonal hc hs]
  norm_num

/-- The Born weight of the card's axial state `ψ=(1,0,0)` in the `i`-th
rank-one projector. -/
def axialBornWeight (c s : ℝ) (i : Fin 5) : ℝ :=
  (pentagonVector c s i 0) ^ 2

lemma five_div_sqrt_five : 5 * (1 / Real.sqrt 5) = Real.sqrt 5 := by
  field_simp [sqrt_five_ne_zero]
  nlinarith [sq_sqrt_five]

/-- **B188, exact KCBS total:** the five axial Born weights add to `√5`. -/
theorem b188_pentagon_axial_born_sum {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) :
    ∑ i : Fin 5, axialBornWeight c s i = Real.sqrt 5 := by
  simp [axialBornWeight, pentagonVector, hc]
  simpa [one_div] using five_div_sqrt_five

lemma two_lt_sqrt_five : (2 : ℝ) < Real.sqrt 5 := by
  nlinarith [sqrt_five_pos, sq_sqrt_five]

/-- The displayed strict separation from the non-contextual value two. -/
theorem b188_pentagon_axial_born_sum_gt_two {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) :
    2 < ∑ i : Fin 5, axialBornWeight c s i := by
  rw [b188_pentagon_axial_born_sum hc]
  exact two_lt_sqrt_five

/-- A deterministic non-contextual assignment to the five yes/no tests. -/
def ExclusiveAssignment (a : Fin 5 → Bool) : Prop :=
  ∀ i : Fin 5, a i = false ∨ a (i + 1) = false

/-- Exhaustive finite proof that an exclusive binary assignment on the
pentagon selects at most two vertices (its independence number is two). -/
theorem b188_pentagon_noncontextual_nat (a : Fin 5 → Bool)
    (ha : ExclusiveAssignment a) :
    (∑ i : Fin 5, if a i then 1 else 0) ≤ 2 := by
  revert a
  unfold ExclusiveAssignment
  decide

/-- The same non-contextual bound with real-valued Born weights. -/
theorem b188_pentagon_noncontextual_real (a : Fin 5 → Bool)
    (ha : ExclusiveAssignment a) :
    (∑ i : Fin 5, if a i then (1 : ℝ) else 0) ≤ 2 := by
  exact_mod_cast b188_pentagon_noncontextual_nat a ha

def oddUmbrellaAngle (m : ℕ) (i : Fin (2 * m + 1)) : ℝ :=
  2 * (m : ℝ) * Real.pi * (i : ℕ) / (2 * (m : ℝ) + 1)

def oddUmbrellaVector (c s : ℝ) (m : ℕ) (i : Fin (2 * m + 1)) : Fin 3 → ℝ :=
  ![c, s * Real.cos (oddUmbrellaAngle m i), s * Real.sin (oddUmbrellaAngle m i)]

lemma dot3_oddUmbrellaVector (c s : ℝ) (m : ℕ) (i j : Fin (2 * m + 1)) :
    dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m j) =
      c ^ 2 + s ^ 2 * Real.cos (oddUmbrellaAngle m j - oddUmbrellaAngle m i) := by
  simp [dot3, oddUmbrellaVector, Fin.sum_univ_three, Real.cos_sub]
  ring

lemma cos_oddUmbrellaAngle_succ_sub (m : ℕ) (i : Fin (2 * m + 1)) :
    Real.cos (oddUmbrellaAngle m (i + 1) - oddUmbrellaAngle m i) =
      Real.cos (2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) := by
  have hN : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  unfold oddUmbrellaAngle
  rw [Fin.val_add_one]
  split_ifs with hi
  · subst i
    simp only [Nat.cast_zero, mul_zero, zero_div, Fin.val_last, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one, zero_sub, Real.cos_neg]
    have h := Real.cos_nat_mul_two_pi_sub
      (2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) m
    convert h using 1 <;> field_simp [hN] <;> ring
  · simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma dot3_oddUmbrellaVector_succ (c s : ℝ) (m : ℕ) (i : Fin (2 * m + 1)) :
    dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m (i + 1)) =
      c ^ 2 + s ^ 2 * Real.cos (2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) := by
  rw [dot3_oddUmbrellaVector, cos_oddUmbrellaAngle_succ_sub]

lemma cos_odd_step (m : ℕ) :
    Real.cos (2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) =
      -Real.cos (Real.pi / (2 * (m : ℝ) + 1)) := by
  have hN : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  rw [← Real.cos_pi_sub]
  congr 1
  field_simp [hN]
  ring

lemma dot3_oddUmbrellaVector_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (m : ℕ) (i : Fin (2 * m + 1)) :
    dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m i) = 1 := by
  rw [dot3_oddUmbrellaVector]
  simp [hcs]

lemma dot3_oddUmbrellaVector_succ_eq_zero {c s : ℝ} (m : ℕ)
    (h : c ^ 2 = s ^ 2 * Real.cos (Real.pi / (2 * (m : ℝ) + 1)))
    (i : Fin (2 * m + 1)) :
    dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m (i + 1)) = 0 := by
  rw [dot3_oddUmbrellaVector_succ, cos_odd_step, h]
  ring



/-- The axial squared amplitude for the general odd umbrella. -/
def oddUmbrellaC2 (m : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (m : ℝ) + 1)) /
    (1 + Real.cos (Real.pi / (2 * (m : ℝ) + 1)))

/-- The transverse squared amplitude for the general odd umbrella. -/
def oddUmbrellaS2 (m : ℕ) : ℝ :=
  1 / (1 + Real.cos (Real.pi / (2 * (m : ℝ) + 1)))

lemma oddUmbrellaC2_nonneg {m : ℕ}
    (hcos : 0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1))) : 0 ≤ oddUmbrellaC2 m := by
  exact div_nonneg hcos (by linarith)

lemma oddUmbrellaS2_nonneg {m : ℕ}
    (hcos : 0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1))) : 0 ≤ oddUmbrellaS2 m := by
  exact div_nonneg (by norm_num) (by linarith)

lemma oddUmbrella_amplitudes_sum {m : ℕ}
    (hcos : 0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1))) :
    oddUmbrellaC2 m + oddUmbrellaS2 m = 1 := by
  unfold oddUmbrellaC2 oddUmbrellaS2
  field_simp
  ring

lemma oddUmbrella_amplitudes_orthogonal {m : ℕ}
    (hcos : 0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1))) :
    oddUmbrellaC2 m =
      oddUmbrellaS2 m * Real.cos (Real.pi / (2 * (m : ℝ) + 1)) := by
  unfold oddUmbrellaC2 oddUmbrellaS2
  field_simp

/-- A concrete square-root choice of the two amplitudes gives a balanced
rank-one field on every odd cycle for which `cos(π/(2m+1))` is nonnegative. -/
theorem b188_odd_umbrella_balanced {m : ℕ}
    (hcos : 0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1))) :
    ∃ c s : ℝ,
      (∀ i : Fin (2 * m + 1),
        dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m i) = 1) ∧
      (∀ i : Fin (2 * m + 1),
        (dot3 (oddUmbrellaVector c s m i)
          (oddUmbrellaVector c s m (i + 1))) ^ 2 = 0) := by
  refine ⟨Real.sqrt (oddUmbrellaC2 m), Real.sqrt (oddUmbrellaS2 m), ?_, ?_⟩
  · have hc : (Real.sqrt (oddUmbrellaC2 m)) ^ 2 = oddUmbrellaC2 m :=
      Real.sq_sqrt (oddUmbrellaC2_nonneg hcos)
    have hs : (Real.sqrt (oddUmbrellaS2 m)) ^ 2 = oddUmbrellaS2 m :=
      Real.sq_sqrt (oddUmbrellaS2_nonneg hcos)
    intro i
    apply dot3_oddUmbrellaVector_self _ m i
    rw [hc, hs]
    exact oddUmbrella_amplitudes_sum hcos
  · have hc : (Real.sqrt (oddUmbrellaC2 m)) ^ 2 = oddUmbrellaC2 m :=
      Real.sq_sqrt (oddUmbrellaC2_nonneg hcos)
    have hs : (Real.sqrt (oddUmbrellaS2 m)) ^ 2 = oddUmbrellaS2 m :=
      Real.sq_sqrt (oddUmbrellaS2_nonneg hcos)
    intro i
    rw [dot3_oddUmbrellaVector_succ_eq_zero m _ i]
    · norm_num
    · rw [hc, hs]
      exact oddUmbrella_amplitudes_orthogonal hcos

lemma cos_odd_denominator_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ Real.cos (Real.pi / (2 * (m : ℝ) + 1)) := by
  apply Real.cos_nonneg_of_mem_Icc
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  constructor
  · exact le_trans (by linarith [Real.pi_pos]) (le_of_lt (div_pos Real.pi_pos hN))
  · rw [div_le_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]

/-- **B188, real-space minimum:** on every odd cycle of length at least
three, explicit unit vectors in `ℝ³` make every edge overlap zero. -/
theorem b188_real_odd_cycle_zero {m : ℕ} (hm : 1 ≤ m) :
    ∃ c s : ℝ,
      (∀ i : Fin (2 * m + 1),
        dot3 (oddUmbrellaVector c s m i) (oddUmbrellaVector c s m i) = 1) ∧
      (∀ i : Fin (2 * m + 1),
        (dot3 (oddUmbrellaVector c s m i)
          (oddUmbrellaVector c s m (i + 1))) ^ 2 = 0) ∧
      (∑ i : Fin (2 * m + 1),
        (dot3 (oddUmbrellaVector c s m i)
          (oddUmbrellaVector c s m (i + 1))) ^ 2 = 0) := by
  obtain ⟨c, s, hunit, hedge⟩ := b188_odd_umbrella_balanced (cos_odd_denominator_nonneg hm)
  refine ⟨c, s, hunit, hedge, ?_⟩
  simp [hedge]

#print axioms dot3_oddUmbrellaVector
#print axioms cos_oddUmbrellaAngle_succ_sub
#print axioms dot3_oddUmbrellaVector_succ
#print axioms cos_odd_step
#print axioms dot3_oddUmbrellaVector_self
#print axioms b188_odd_umbrella_balanced
#print axioms cos_odd_denominator_nonneg
#print axioms b188_real_odd_cycle_zero

#print axioms b188_pentagon_noncontextual_nat
#print axioms b188_pentagon_noncontextual_real
#print axioms dot3_pentagonVector
#print axioms cos_angle_succ_sub
#print axioms dot3_pentagonVector_succ
#print axioms dot3_pentagonVector_self
#print axioms dot3_literal_pentagon_self
#print axioms b188_pentagon_neighbours_orthogonal
#print axioms b188_pentagon_mirror_edges
#print axioms b188_pentagon_axial_born_sum
#print axioms b188_pentagon_axial_born_sum_gt_two

end RelationalAtlas.B188

/-! Included checked source: `ComplexWork.lean`. -/
namespace RelationalAtlas.B188
open scoped BigOperators
open Matrix

/-- Two real coordinates, embedded in `ℂ²` below. -/
def dot2 (v w : Fin 2 → ℝ) : ℝ := ∑ k, v k * w k

/-- Half the Bloch-planar step angle used in the complex minimiser. -/
def qubitAngle (m : ℕ) (i : Fin (2 * m + 1)) : ℝ :=
  (m : ℝ) * Real.pi * (i : ℕ) / (2 * (m : ℝ) + 1)

/-- A real unit vector in `ℂ²`; rank-one projectors identify its two signs. -/
def qubitVector (m : ℕ) (i : Fin (2 * m + 1)) : Fin 2 → ℝ :=
  ![Real.cos (qubitAngle m i), Real.sin (qubitAngle m i)]

lemma dot2_qubitVector (m : ℕ) (i j : Fin (2 * m + 1)) :
    dot2 (qubitVector m i) (qubitVector m j) = Real.cos (qubitAngle m j - qubitAngle m i) := by
  simp [dot2, qubitVector, Fin.sum_univ_two, Real.cos_sub]
  ring

lemma dot2_qubitVector_self (m : ℕ) (i : Fin (2 * m + 1)) :
    dot2 (qubitVector m i) (qubitVector m i) = 1 := by
  rw [dot2_qubitVector]
  simp

lemma cos_qubitAngle_succ_sub (m : ℕ) {i : Fin (2 * m + 1)} (hi : i ≠ Fin.last (2 * m)) :
    Real.cos (qubitAngle m (i + 1) - qubitAngle m i) =
      Real.cos ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) := by
  unfold qubitAngle
  rw [Fin.val_add_one, if_neg hi]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

lemma cos_qubitAngle_last (m : ℕ) :
    Real.cos (qubitAngle m (0 : Fin (2 * m + 1)) - qubitAngle m (Fin.last (2 * m))) =
      (-1 : ℝ) ^ m * Real.cos ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) := by
  have hN : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  simp only [qubitAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, zero_sub,
    Fin.val_last, Nat.cast_mul, Nat.cast_ofNat, Real.cos_neg]
  have h := Real.cos_nat_mul_pi_sub ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) m
  convert h using 1 <;> field_simp [hN] <;> ring

lemma qubit_neighbour_overlap_sq (m : ℕ) (i : Fin (2 * m + 1)) :
    (dot2 (qubitVector m i) (qubitVector m (i + 1))) ^ 2 =
      (Real.cos ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1))) ^ 2 := by
  rw [dot2_qubitVector]
  by_cases hi : i = Fin.last (2 * m)
  · subst i
    rw [Fin.last_add_one, cos_qubitAngle_last, mul_pow, ← pow_mul]
    simp
  · rw [cos_qubitAngle_succ_sub m hi]

lemma qubit_two_step_cos (m : ℕ) :
    Real.cos (2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) =
      -Real.cos (Real.pi / (2 * (m : ℝ) + 1)) := by
  have hN : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  rw [← Real.cos_pi_sub]
  congr 1
  field_simp [hN]
  ring

lemma qubit_overlap_sq_eq_book (m : ℕ) (i : Fin (2 * m + 1)) :
    (dot2 (qubitVector m i) (qubitVector m (i + 1))) ^ 2 =
      (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) / 2 := by
  rw [qubit_neighbour_overlap_sq]
  have h := Real.cos_two_mul ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1))
  have hstep : Real.cos (2 * ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1))) =
      -Real.cos (Real.pi / (2 * (m : ℝ) + 1)) := by
    rw [show 2 * ((m : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) =
      2 * (m : ℝ) * Real.pi / (2 * (m : ℝ) + 1) by ring]
    exact qubit_two_step_cos m
  rw [hstep] at h
  nlinarith

/-- The exact edge value attained by the complex odd-cycle minimiser. -/
theorem b188_complex_odd_cycle_attained (m : ℕ) :
    (∑ i : Fin (2 * m + 1),
      (dot2 (qubitVector m i) (qubitVector m (i + 1))) ^ 2) =
        ((2 * (m : ℝ) + 1) / 2) *
          (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) := by
  simp_rw [qubit_overlap_sq_eq_book]
  simp [Finset.sum_const]
  ring

/-- The explicit real witness, viewed as a vector in `ℂ²`. -/
def complexQubitVector (m : ℕ) (i : Fin (2 * m + 1)) : Fin 2 → ℂ :=
  fun k => (qubitVector m i k : ℂ)

/-- The ordinary complex Hermitian overlap, before taking squared modulus. -/
def complexOverlap (v w : Fin 2 → ℂ) : ℂ := ∑ k, star (v k) * w k

lemma complexOverlap_of_real (v w : Fin 2 → ℝ) :
    complexOverlap (fun k => (v k : ℂ)) (fun k => (w k : ℂ)) = (dot2 v w : ℂ) := by
  simp [complexOverlap, dot2]

lemma normSq_complexOverlap_of_real (v w : Fin 2 → ℝ) :
    Complex.normSq (complexOverlap (fun k => (v k : ℂ)) (fun k => (w k : ℂ))) =
      (dot2 v w) ^ 2 := by
  rw [complexOverlap_of_real]
  simp [Complex.normSq_apply, sq]

lemma complex_qubit_overlap_normSq (m : ℕ) (i j : Fin (2 * m + 1)) :
    Complex.normSq (complexOverlap (complexQubitVector m i) (complexQubitVector m j)) =
      (dot2 (qubitVector m i) (qubitVector m j)) ^ 2 := by
  exact normSq_complexOverlap_of_real _ _

lemma complex_qubit_unit (m : ℕ) (i : Fin (2 * m + 1)) :
    Complex.normSq (complexOverlap (complexQubitVector m i) (complexQubitVector m i)) = 1 := by
  rw [complex_qubit_overlap_normSq, dot2_qubitVector_self]
  norm_num

/-- **B188, attained complex value, in the literal `ℂ²` Born model.** -/
theorem b188_complex_odd_cycle_attained_normSq (m : ℕ) :
    (∑ i : Fin (2 * m + 1),
      Complex.normSq (complexOverlap (complexQubitVector m i)
        (complexQubitVector m (i + 1)))) =
      ((2 * (m : ℝ) + 1) / 2) *
        (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) := by
  simp_rw [complex_qubit_overlap_normSq]
  exact b188_complex_odd_cycle_attained m

#print axioms dot2_qubitVector
#print axioms dot2_qubitVector_self
#print axioms qubit_neighbour_overlap_sq
#print axioms qubit_overlap_sq_eq_book
#print axioms b188_complex_odd_cycle_attained
#print axioms complex_qubit_unit
#print axioms b188_complex_odd_cycle_attained_normSq

end RelationalAtlas.B188

/-! Included checked source: `TriangleWork.lean`. -/
namespace RelationalAtlas.B188

open scoped BigOperators InnerProductSpace

/-- `p = (1+n·m)/2`, the card's rank-one-qubit edge formula. -/
def blochEdge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n m : E) : ℝ := (1 + ⟪n, m⟫_ℝ) / 2

/-- The three edges of a triangle. -/
def blochTriangle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n0 n1 n2 : E) : ℝ := blochEdge n0 n1 + blochEdge n1 n2 + blochEdge n2 n0

lemma triangle_inner_sum_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n0 n1 n2 : E) (h0 : ⟪n0, n0⟫_ℝ = 1) (h1 : ⟪n1, n1⟫_ℝ = 1)
    (h2 : ⟪n2, n2⟫_ℝ = 1) :
    -(3 / 2 : ℝ) ≤ ⟪n0, n1⟫_ℝ + ⟪n1, n2⟫_ℝ + ⟪n2, n0⟫_ℝ := by
  have h : 0 ≤ ⟪n0 + n1 + n2, n0 + n1 + n2⟫_ℝ := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, h0, h1, h2] at h
  rw [real_inner_comm n0 n1, real_inner_comm n0 n2, real_inner_comm n1 n2] at h
  rw [real_inner_comm n0 n2]
  nlinarith

/-- The triangle minimum, for Bloch vectors in any real inner-product space. -/
theorem b188_triangle_bloch_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n0 n1 n2 : E) (h0 : ⟪n0, n0⟫_ℝ = 1) (h1 : ⟪n1, n1⟫_ℝ = 1)
    (h2 : ⟪n2, n2⟫_ℝ = 1) :
    (3 / 2 : ℝ) * (1 - Real.cos (Real.pi / 3)) ≤ blochTriangle n0 n1 n2 := by
  have h := triangle_inner_sum_nonneg n0 n1 n2 h0 h1 h2
  rw [Real.cos_pi_div_three]
  dsimp [blochTriangle, blochEdge]
  nlinarith

/-- The same bound with the cyclic sum over `Fin 3`. -/
theorem b188_triangle_bloch_lower_cyclic {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : Fin 3 → E)
    (hn : ∀ i, ⟪n i, n i⟫_ℝ = 1) :
    (3 / 2 : ℝ) * (1 - Real.cos (Real.pi / 3)) ≤
      ∑ i : Fin 3, blochEdge (n i) (n (i + 1)) := by
  have h := b188_triangle_bloch_lower (n 0) (n 1) (n 2) (hn 0) (hn 1) (hn 2)
  convert h using 1 <;> norm_num [blochTriangle, Fin.sum_univ_three]

#print axioms triangle_inner_sum_nonneg
#print axioms b188_triangle_bloch_lower
#print axioms b188_triangle_bloch_lower_cyclic

end RelationalAtlas.B188

/-! Included checked source: `ParsevalWork.lean`. -/
namespace RelationalAtlas.B188

open scoped BigOperators
open Finset AddChar ZMod

variable {N : ℕ} [NeZero N]

lemma star_stdAddChar (a : ZMod N) :
    star (stdAddChar a) = stdAddChar (-a) := by
  rw [stdAddChar_apply, stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (toCircle a)).symm

lemma dft_parseval (x y : ZMod N → ℂ) :
    (N : ℂ) * ∑ j, star (x j) * y j =
      ∑ k, star (ZMod.dft x k) * ZMod.dft y k := by
  have hd (j : ZMod N) : ZMod.dft (ZMod.dft y) (-j) = (N : ℂ) * y j := by
    have h := congr_fun (ZMod.dft_dft y) (-j)
    simpa using h
  have hd2 (j : ZMod N) :
      ZMod.dft (ZMod.dft y) (-j) = ∑ k, stdAddChar (j * k) * ZMod.dft y k := by
    rw [ZMod.dft_apply]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_eq_mul]
    congr 2
    ring
  calc
    (N : ℂ) * ∑ j, star (x j) * y j =
        ∑ j, star (x j) * ((N : ℂ) * y j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j, star (x j) * ZMod.dft (ZMod.dft y) (-j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hd]
    _ = ∑ j, star (x j) * ∑ k, stdAddChar (j * k) * ZMod.dft y k := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hd2]
    _ = ∑ k, (∑ j, stdAddChar (j * k) * star (x j)) * ZMod.dft y k := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ k, star (ZMod.dft x k) * ZMod.dft y k := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, star_stdAddChar]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [neg_neg]
          ring

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod
variable {N : ℕ} [NeZero N]

/-- Adjacent-domain shift on the cyclic index. -/
def cyclicShift (x : ZMod N → ℂ) : ZMod N → ℂ := fun j => x (j + 1)

lemma dft_cyclicShift (x : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cyclicShift x) k = stdAddChar k * ZMod.dft x k := by
  simp only [cyclicShift, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  let e := Equiv.addRight (1 : ZMod N)
  refine Fintype.sum_equiv e _ _ ?_
  intro j
  simp only [e, Equiv.coe_addRight]
  change stdAddChar (-(j * k)) * x (j + 1) =
    stdAddChar k * (stdAddChar (-((j + 1) * k)) * x (j + 1))
  rw [show -((j + 1) * k) = -(j * k) + (-k) by ring, map_add_eq_mul]
  simp only [AddChar.map_neg_eq_inv]
  have hχ : stdAddChar k ≠ 0 := by
    rw [stdAddChar_apply]
    exact Circle.coe_ne_zero _
  have hχjk : stdAddChar (j * k) ≠ 0 := by
    rw [stdAddChar_apply]
    exact Circle.coe_ne_zero _
  field_simp [hχ, hχjk]

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod
variable {N : ℕ} [NeZero N]

lemma stdAddChar_re (k : ZMod N) :
    (stdAddChar k).re = Real.cos (2 * Real.pi * ((k.val : ℝ) / (N : ℝ))) := by
  rw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
    Complex.ofReal_re, Complex.sin_ofReal_im]
  rw [Complex.cos_ofReal_re]
  ring

lemma stdAddChar_add_neg (k : ZMod N) :
    stdAddChar k + stdAddChar (-k) =
      ((2 * Real.cos (2 * Real.pi * ((k.val : ℝ) / (N : ℝ))) : ℝ) : ℂ) := by
  rw [← star_stdAddChar k]
  change stdAddChar k + (starRingEnd ℂ) (stdAddChar k) = _
  rw [Complex.add_conj, stdAddChar_re]

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod
variable {N : ℕ} [NeZero N]

/-- The predecessor shift on the cyclic index. -/
def cyclicBack (x : ZMod N → ℂ) : ZMod N → ℂ := fun j => x (j - 1)

lemma dft_cyclicBack (x : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cyclicBack x) k = stdAddChar (-k) * ZMod.dft x k := by
  simp only [cyclicBack, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  let e := Equiv.addRight (1 : ZMod N)
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro j
  simp only [e, Equiv.coe_addRight]
  change stdAddChar (-k) * (stdAddChar (-(j * k)) * x j) =
    stdAddChar (-((j + 1) * k)) * x (j + 1 - 1)
  rw [show j + 1 - 1 = j by abel]
  rw [show -((j + 1) * k) = (-k) + (-(j * k)) by ring, map_add_eq_mul]
  ring

/-- The symmetric cycle operator, with diagonal parameter `c`. -/
def cycleOperator (c : ℂ) (x : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j => c * x j + cyclicShift x j + cyclicBack x j

lemma dft_cycleOperator (c : ℂ) (x : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cycleOperator c x) k =
      (c + stdAddChar k + stdAddChar (-k)) * ZMod.dft x k := by
  change ZMod.dft ((fun j => c * x j) + cyclicShift x + cyclicBack x) k = _
  rw [map_add, map_add]
  simp only [Pi.add_apply]
  rw [dft_cyclicShift, dft_cyclicBack]
  have hc := congr_fun (ZMod.dft_const_mul c x) k
  rw [hc]
  ring

/-- The real eigenvalue of the symmetric cycle operator. -/
def cycleEigenvalue (θ : ℝ) (k : ZMod N) : ℝ :=
  2 * Real.cos θ + 2 * Real.cos (2 * Real.pi * ((k.val : ℝ) / (N : ℝ)))

lemma dft_cycleOperator_cos (θ : ℝ) (x : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cycleOperator ((2 * Real.cos θ : ℝ) : ℂ) x) k =
      (cycleEigenvalue θ k : ℂ) * ZMod.dft x k := by
  rw [dft_cycleOperator]
  rw [show ((2 * Real.cos θ : ℝ) : ℂ) + stdAddChar k + stdAddChar (-k) =
      (cycleEigenvalue θ k : ℂ) by
    rw [cycleEigenvalue]
    push_cast
    rw [add_assoc, stdAddChar_add_neg]
    push_cast
    ring]

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod
variable {N : ℕ} [NeZero N]

lemma dft_cycle_quadratic (θ : ℝ) (x : ZMod N → ℂ) :
    (N : ℂ) * ∑ j, star (x j) * cycleOperator ((2 * Real.cos θ : ℝ) : ℂ) x j =
      ((∑ k, cycleEigenvalue θ k * Complex.normSq (ZMod.dft x k) : ℝ) : ℂ) := by
  rw [dft_parseval]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [show 2 * Complex.cos (θ : ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) by norm_cast]
  rw [dft_cycleOperator_cos]
  change (starRingEnd ℂ) (ZMod.dft x k) *
    ((cycleEigenvalue θ k : ℂ) * ZMod.dft x k) = _
  rw [show (starRingEnd ℂ) (ZMod.dft x k) *
      ((cycleEigenvalue θ k : ℂ) * ZMod.dft x k) =
      (cycleEigenvalue θ k : ℂ) *
        ((starRingEnd ℂ) (ZMod.dft x k) * ZMod.dft x k) by ring]
  rw [← Complex.normSq_eq_conj_mul_self]

/-- The real quadratic form of the symmetric cycle operator. -/
def cycleQuadratic (θ : ℝ) (x : ZMod N → ℝ) : ℝ :=
  ∑ j, x j * (2 * Real.cos θ * x j + x (j + 1) + x (j - 1))

lemma cycleQuadratic_cast (θ : ℝ) (x : ZMod N → ℝ) :
    ((((N : ℝ) * cycleQuadratic θ x) : ℝ) : ℂ) =
      (N : ℂ) * ∑ j, star ((x j : ℂ)) *
        cycleOperator ((2 * Real.cos θ : ℝ) : ℂ) (fun j => (x j : ℂ)) j := by
  rw [Complex.ofReal_mul]
  congr 1
  rw [cycleQuadratic]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simp only [cycleOperator, cyclicShift, cyclicBack, Complex.star_def, Complex.conj_ofReal]

lemma cycleQuadratic_cast_dft (θ : ℝ) (x : ZMod N → ℝ) :
    ((((N : ℝ) * cycleQuadratic θ x) : ℝ) : ℂ) =
      ((∑ k, cycleEigenvalue θ k *
        Complex.normSq (ZMod.dft (fun j => (x j : ℂ)) k) : ℝ) : ℂ) := by
  rw [cycleQuadratic_cast]
  exact dft_cycle_quadratic θ (fun j => (x j : ℂ))

lemma cycleQuadratic_nonneg_of_eigenvalue_nonneg (θ : ℝ)
    (hlam : ∀ k : ZMod N, 0 ≤ cycleEigenvalue θ k) (x : ZMod N → ℝ) :
    0 ≤ cycleQuadratic θ x := by
  have hsum : 0 ≤ ∑ k : ZMod N,
      cycleEigenvalue θ k * Complex.normSq (ZMod.dft (fun j => (x j : ℂ)) k) := by
    exact Finset.sum_nonneg fun k hk => mul_nonneg (hlam k) (Complex.normSq_nonneg _)
  have heq : (N : ℝ) * cycleQuadratic θ x =
      ∑ k : ZMod N, cycleEigenvalue θ k *
        Complex.normSq (ZMod.dft (fun j => (x j : ℂ)) k) :=
    Complex.ofReal_inj.mp (cycleQuadratic_cast_dft θ x)
  have hmul : 0 ≤ (N : ℝ) * cycleQuadratic θ x := by
    rw [heq]
    exact hsum
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  exact (mul_nonneg_iff_of_pos_left hN).mp hmul

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod

lemma odd_frequency_cos_lower (m k : ℕ) (hk : k < 2 * m + 1) :
    -Real.cos (Real.pi / (2 * (m : ℝ) + 1)) ≤
      Real.cos (2 * Real.pi * ((k : ℝ) / (2 * (m : ℝ) + 1))) := by
  have hN : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hlow (r : ℕ) (hr : r ≤ m) :
      -Real.cos (Real.pi / (2 * (m : ℝ) + 1)) ≤
        Real.cos (2 * Real.pi * ((r : ℝ) / (2 * (m : ℝ) + 1))) := by
    have ha0 : 0 ≤ 2 * Real.pi * ((r : ℝ) / (2 * (m : ℝ) + 1)) := by positivity
    have hab : 2 * Real.pi * ((r : ℝ) / (2 * (m : ℝ) + 1)) ≤
        2 * Real.pi * ((m : ℝ) / (2 * (m : ℝ) + 1)) := by
      gcongr
    have hbpi : 2 * Real.pi * ((m : ℝ) / (2 * (m : ℝ) + 1)) ≤ Real.pi := by
      rw [show 2 * Real.pi * ((m : ℝ) / (2 * (m : ℝ) + 1)) =
        (2 * Real.pi * (m : ℝ)) / (2 * (m : ℝ) + 1) by ring]
      apply (div_le_iff₀ hN).mpr
      nlinarith [Real.pi_pos]
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ha0 hbpi hab
    have hb : 2 * Real.pi * ((m : ℝ) / (2 * (m : ℝ) + 1)) =
        Real.pi - Real.pi / (2 * (m : ℝ) + 1) := by
      field_simp
      ring
    rw [hb, Real.cos_pi_sub] at hcos
    exact hcos
  by_cases hkm : k ≤ m
  · exact hlow k hkm
  · have hr : 2 * m + 1 - k ≤ m := by omega
    have h := hlow (2 * m + 1 - k) hr
    have hangle : 2 * Real.pi *
        (((2 * m + 1 - k : ℕ) : ℝ) / (2 * (m : ℝ) + 1)) =
        2 * Real.pi - 2 * Real.pi * ((k : ℝ) / (2 * (m : ℝ) + 1)) := by
      rw [Nat.cast_sub hk.le]
      push_cast
      field_simp
    rw [hangle, Real.cos_two_pi_sub] at h
    exact h

lemma odd_cycleEigenvalue_nonneg (m : ℕ) (k : ZMod (2 * m + 1)) :
    0 ≤ cycleEigenvalue (Real.pi / (2 * (m : ℝ) + 1)) k := by
  unfold cycleEigenvalue
  have h := odd_frequency_cos_lower m k.val k.val_lt
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  linarith

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod
variable {N : ℕ} [NeZero N]

/-- Three real Bloch coordinates. -/
def dotCyc (n : ZMod N → Fin 3 → ℝ) (i j : ZMod N) : ℝ := ∑ a : Fin 3, n i a * n j a

lemma dotCyc_comm (n : ZMod N → Fin 3 → ℝ) (i j : ZMod N) :
    dotCyc n i j = dotCyc n j i := by
  unfold dotCyc
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma sum_dotCyc_pred (n : ZMod N → Fin 3 → ℝ) :
    (∑ j, dotCyc n j (j - 1)) = ∑ j, dotCyc n j (j + 1) := by
  let e := Equiv.addRight (1 : ZMod N)
  calc
    (∑ j, dotCyc n j (j - 1)) = ∑ j, dotCyc n (j + 1) j := by
      symm
      refine Fintype.sum_equiv e _ _ ?_
      intro j
      simp only [e, Equiv.coe_addRight]
      rw [show j + 1 - 1 = j by abel]
    _ = ∑ j, dotCyc n j (j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact dotCyc_comm n (j + 1) j

lemma cycleQuadratic_expand (θ : ℝ) (x : ZMod N → ℝ) :
    cycleQuadratic θ x = 2 * Real.cos θ * (∑ j, x j * x j) +
      (∑ j, x j * x (j + 1)) + (∑ j, x j * x (j - 1)) := by
  calc
    cycleQuadratic θ x =
        ∑ j, (2 * Real.cos θ * (x j * x j) + x j * x (j + 1) + x j * x (j - 1)) := by
      unfold cycleQuadratic
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma sum_cycleQuadratic_coordinates (θ : ℝ) (n : ZMod N → Fin 3 → ℝ) :
    (∑ a : Fin 3, cycleQuadratic θ (fun i => n i a)) =
      2 * Real.cos θ * (∑ i, dotCyc n i i) + 2 * (∑ i, dotCyc n i (i + 1)) := by
  calc
    (∑ a : Fin 3, cycleQuadratic θ (fun i => n i a)) =
        ∑ a : Fin 3, (2 * Real.cos θ * (∑ i, n i a * n i a) +
          (∑ i, n i a * n (i + 1) a) + (∑ i, n i a * n (i - 1) a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact cycleQuadratic_expand θ (fun i => n i a)
    _ = (2 * Real.cos θ * (∑ i, dotCyc n i i) +
          (∑ i, dotCyc n i (i + 1))) + (∑ i, dotCyc n i (i - 1)) := by
      have hself :
          (∑ a : Fin 3, 2 * Real.cos θ * (∑ i, n i a * n i a)) =
            2 * Real.cos θ * (∑ i, dotCyc n i i) := by
        rw [← Finset.mul_sum]
        unfold dotCyc
        rw [Finset.sum_comm]
      have hsucc :
          (∑ a : Fin 3, ∑ i, n i a * n (i + 1) a) =
            ∑ i, dotCyc n i (i + 1) := by
        exact Finset.sum_comm
      have hpred :
          (∑ a : Fin 3, ∑ i, n i a * n (i - 1) a) =
            ∑ i, dotCyc n i (i - 1) := by
        exact Finset.sum_comm
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hself, hsucc, hpred]
    _ = _ := by
      rw [sum_dotCyc_pred]
      ring

lemma odd_bloch_adjacency_lower (m : ℕ) (n : ZMod (2 * m + 1) → Fin 3 → ℝ)
    (hn : ∀ i, dotCyc n i i = 1) :
    -(2 * (m : ℝ) + 1) * Real.cos (Real.pi / (2 * (m : ℝ) + 1)) ≤
      ∑ i, dotCyc n i (i + 1) := by
  have hnon : 0 ≤ ∑ a : Fin 3, cycleQuadratic (Real.pi / (2 * (m : ℝ) + 1))
      (fun i => n i a) := by
    apply Finset.sum_nonneg
    intro a ha
    exact cycleQuadratic_nonneg_of_eigenvalue_nonneg _ (odd_cycleEigenvalue_nonneg m) _
  rw [sum_cycleQuadratic_coordinates] at hnon
  have hsum : (∑ i : ZMod (2 * m + 1), dotCyc n i i) = (2 * (m : ℝ) + 1) := by
    simp [hn]
  rw [hsum] at hnon
  nlinarith

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Finset AddChar ZMod

/-- The rank-one-qubit overlap on a cyclic edge, written in Bloch coordinates. -/
def blochOverlap {m : ℕ} (n : ZMod (2 * m + 1) → Fin 3 → ℝ) (i : ZMod (2 * m + 1)) : ℝ :=
  (1 + dotCyc n i (i + 1)) / 2

lemma blochOverlap_sum_expand {m : ℕ} (n : ZMod (2 * m + 1) → Fin 3 → ℝ) :
    (∑ i, blochOverlap n i) =
      (2 * (m : ℝ) + 1) / 2 + (∑ i, dotCyc n i (i + 1)) / 2 := by
  calc
    (∑ i, blochOverlap n i) = ∑ i, ((1 : ℝ) / 2 + dotCyc n i (i + 1) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold blochOverlap
      ring
    _ = (∑ i : ZMod (2 * m + 1), (1 : ℝ) / 2) +
        (∑ i, dotCyc n i (i + 1) / 2) := by rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_div]
      simp
      ring

/-- **B188, the complete complex-qubit lower bound in Bloch coordinates.**
For every unit Bloch field on an odd cycle, the sum of edge overlaps is at
least the card's `(N/2)(1-cos(π/N))`. -/
theorem b188_complex_odd_cycle_lower {m : ℕ}
    (n : ZMod (2 * m + 1) → Fin 3 → ℝ) (hn : ∀ i, dotCyc n i i = 1) :
    ((2 * (m : ℝ) + 1) / 2) * (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) ≤
      ∑ i, blochOverlap n i := by
  have h := odd_bloch_adjacency_lower m n hn
  rw [blochOverlap_sum_expand]
  nlinarith

#print axioms dft_parseval
#print axioms dft_cyclicShift
#print axioms dft_cyclicBack
#print axioms dft_cycleOperator_cos
#print axioms dft_cycle_quadratic
#print axioms cycleQuadratic_nonneg_of_eigenvalue_nonneg
#print axioms odd_frequency_cos_lower
#print axioms odd_cycleEigenvalue_nonneg
#print axioms sum_dotCyc_pred
#print axioms sum_cycleQuadratic_coordinates
#print axioms odd_bloch_adjacency_lower
#print axioms b188_complex_odd_cycle_lower

end RelationalAtlas.B188


namespace RelationalAtlas.B188
open scoped BigOperators
open Matrix

/-- A real qubit state at Bloch half-angle `β`. -/
def realQubitState (β : ℝ) : Fin 2 → ℝ := ![Real.cos β, Real.sin β]

/-- Its Bloch vector `(sin 2β, 0, cos 2β)`. -/
def blochFromAngle (β : ℝ) : Fin 3 → ℝ :=
  ![Real.sin (2 * β), 0, Real.cos (2 * β)]

lemma qubitVector_eq_realQubitState (m : ℕ) (i : Fin (2 * m + 1)) :
    qubitVector m i = realQubitState (qubitAngle m i) := rfl

lemma dot2_realQubitState_self (β : ℝ) :
    dot2 (realQubitState β) (realQubitState β) = 1 := by
  have h := Real.sin_sq_add_cos_sq β
  simp [dot2, realQubitState, Fin.sum_univ_two]
  nlinarith

lemma dot3_blochFromAngle (β γ : ℝ) :
    dot3 (blochFromAngle β) (blochFromAngle γ) =
      2 * (dot2 (realQubitState β) (realQubitState γ)) ^ 2 - 1 := by
  have hi : dot2 (realQubitState β) (realQubitState γ) = Real.cos (γ - β) := by
    simp [dot2, realQubitState, Fin.sum_univ_two, Real.cos_sub]
    ring
  have hd : dot3 (blochFromAngle β) (blochFromAngle γ) =
      Real.cos (2 * γ - 2 * β) := by
    simp [dot3, blochFromAngle, Fin.sum_univ_three, Real.cos_sub]
    ring
  rw [hi, hd, show 2 * γ - 2 * β = 2 * (γ - β) by ring, Real.cos_two_mul]

lemma dot3_blochFromAngle_self (β : ℝ) : dot3 (blochFromAngle β) (blochFromAngle β) = 1 := by
  rw [dot3_blochFromAngle, dot2_realQubitState_self]
  norm_num

/-- The planar minimising Bloch field, reindexed from `Fin` to `ZMod`. -/
def minimisingBloch (m : ℕ) (i : ZMod (2 * m + 1)) : Fin 3 → ℝ :=
  blochFromAngle (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm i))

lemma minimisingBloch_unit (m : ℕ) (i : ZMod (2 * m + 1)) :
    dotCyc (minimisingBloch m) i i = 1 := by
  exact dot3_blochFromAngle_self _

lemma minimisingBloch_overlap (m : ℕ) (i : ZMod (2 * m + 1)) :
    blochOverlap (minimisingBloch m) i =
      (dot2 (realQubitState (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm i)))
        (realQubitState (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm (i + 1))))) ^ 2 := by
  unfold blochOverlap
  change (1 + dot3 (blochFromAngle (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm i)))
    (blochFromAngle (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm (i + 1))))) / 2 = _
  rw [show (ZMod.finEquiv (2 * m + 1)).symm (i + 1) =
    (ZMod.finEquiv (2 * m + 1)).symm i + 1 by simp]
  rw [dot3_blochFromAngle]
  ring

lemma minimisingBloch_sum_eq_qubit (m : ℕ) :
    (∑ i : ZMod (2 * m + 1), blochOverlap (minimisingBloch m) i) =
      ∑ j : Fin (2 * m + 1),
        (dot2 (qubitVector m j) (qubitVector m (j + 1))) ^ 2 := by
  simp_rw [minimisingBloch_overlap]
  refine Fintype.sum_equiv (ZMod.finEquiv (2 * m + 1)).symm _ _ ?_
  intro i
  change (dot2 (qubitVector m ((ZMod.finEquiv (2 * m + 1)).symm i))
    (qubitVector m ((ZMod.finEquiv (2 * m + 1)).symm (i + 1)))) ^ 2 = _
  simp

/-- The planar Bloch field attains precisely the universal lower bound. -/
theorem b188_minimisingBloch_attains (m : ℕ) :
    (∑ i : ZMod (2 * m + 1), blochOverlap (minimisingBloch m) i) =
      ((2 * (m : ℝ) + 1) / 2) *
        (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) := by
  rw [minimisingBloch_sum_eq_qubit]
  exact b188_complex_odd_cycle_attained m

/-- **B188's complex minimum, as an exact least value.** -/
theorem b188_complex_odd_cycle_isLeast (m : ℕ) :
    IsLeast {x : ℝ | ∃ n : ZMod (2 * m + 1) → Fin 3 → ℝ,
      (∀ i, dotCyc n i i = 1) ∧ x = ∑ i, blochOverlap n i}
      (((2 * (m : ℝ) + 1) / 2) *
        (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1)))) := by
  constructor
  · refine ⟨minimisingBloch m, minimisingBloch_unit m, ?_⟩
    exact (b188_minimisingBloch_attains m).symm
  · rintro x ⟨n, hn, rfl⟩
    exact b188_complex_odd_cycle_lower n hn

#print axioms dot3_blochFromAngle
#print axioms minimisingBloch_unit
#print axioms minimisingBloch_overlap
#print axioms b188_minimisingBloch_attains
#print axioms b188_complex_odd_cycle_isLeast

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Matrix

/-- The Bloch vector of a possibly unnormalised two-component spinor. -/
def blochOfComplex (v : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2 * (v 0 * star (v 1)).re, 2 * (v 0 * star (v 1)).im,
    Complex.normSq (v 0) - Complex.normSq (v 1)]

/-- The polynomial spinor/Bloch overlap identity.  No normalisation is needed. -/
lemma dot3_blochOfComplex (v w : Fin 2 → ℂ) :
    dot3 (blochOfComplex v) (blochOfComplex w) =
      2 * Complex.normSq (complexOverlap v w) -
        (Complex.normSq (v 0) + Complex.normSq (v 1)) *
          (Complex.normSq (w 0) + Complex.normSq (w 1)) := by
  simp [dot3, blochOfComplex, complexOverlap, Fin.sum_univ_three, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

lemma blochOfComplex_overlap_of_unit {v w : Fin 2 → ℂ}
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (hw : Complex.normSq (w 0) + Complex.normSq (w 1) = 1) :
    dot3 (blochOfComplex v) (blochOfComplex w) =
      2 * Complex.normSq (complexOverlap v w) - 1 := by
  rw [dot3_blochOfComplex, hv, hw]
  ring

lemma blochOfComplex_self_of_unit {v : Fin 2 → ℂ}
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    dot3 (blochOfComplex v) (blochOfComplex v) = 1 := by
  rw [blochOfComplex_overlap_of_unit hv hv]
  have hov : Complex.normSq (complexOverlap v v) = 1 := by
    unfold complexOverlap
    rw [Fin.sum_univ_two]
    change Complex.normSq ((starRingEnd ℂ) (v 0) * v 0 +
      (starRingEnd ℂ) (v 1) * v 1) = 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_add, hv]
    norm_num
  rw [hov]
  norm_num

/-- **B188 lower bound for literal normalised vectors in `ℂ²`.** -/
theorem b188_complex_odd_cycle_lower_normSq {m : ℕ}
    (v : ZMod (2 * m + 1) → Fin 2 → ℂ)
    (hv : ∀ i, Complex.normSq (v i 0) + Complex.normSq (v i 1) = 1) :
    ((2 * (m : ℝ) + 1) / 2) * (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) ≤
      ∑ i, Complex.normSq (complexOverlap (v i) (v (i + 1))) := by
  let n := fun i => blochOfComplex (v i)
  have hn : ∀ i, dotCyc n i i = 1 := by
    intro i
    exact blochOfComplex_self_of_unit (hv i)
  have h := b188_complex_odd_cycle_lower n hn
  have ho : ∀ i : ZMod (2 * m + 1), blochOverlap n i =
      Complex.normSq (complexOverlap (v i) (v (i + 1))) := by
    intro i
    unfold blochOverlap
    change (1 + dot3 (blochOfComplex (v i)) (blochOfComplex (v (i + 1)))) / 2 = _
    rw [blochOfComplex_overlap_of_unit (hv i) (hv (i + 1))]
    ring
  rw [show (∑ i, blochOverlap n i) =
    ∑ i, Complex.normSq (complexOverlap (v i) (v (i + 1))) by
      apply Finset.sum_congr rfl
      intro i hi
      exact ho i] at h
  exact h

#print axioms dot3_blochOfComplex
#print axioms blochOfComplex_overlap_of_unit
#print axioms blochOfComplex_self_of_unit
#print axioms b188_complex_odd_cycle_lower_normSq

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators
open Matrix

/-- The complex minimiser on the `ZMod` cycle. -/
def complexMinimisingField (m : ℕ) (i : ZMod (2 * m + 1)) : Fin 2 → ℂ :=
  complexQubitVector m ((ZMod.finEquiv (2 * m + 1)).symm i)

lemma complexMinimisingField_unit (m : ℕ) (i : ZMod (2 * m + 1)) :
    Complex.normSq (complexMinimisingField m i 0) +
      Complex.normSq (complexMinimisingField m i 1) = 1 := by
  have h := Real.sin_sq_add_cos_sq
    (qubitAngle m ((ZMod.finEquiv (2 * m + 1)).symm i))
  simp [complexMinimisingField, complexQubitVector, qubitVector, Complex.normSq_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith

lemma complexMinimisingField_attains (m : ℕ) :
    (∑ i : ZMod (2 * m + 1), Complex.normSq (complexOverlap
      (complexMinimisingField m i) (complexMinimisingField m (i + 1)))) =
      ((2 * (m : ℝ) + 1) / 2) *
        (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1))) := by
  rw [show (∑ i : ZMod (2 * m + 1), Complex.normSq (complexOverlap
      (complexMinimisingField m i) (complexMinimisingField m (i + 1)))) =
      ∑ j : Fin (2 * m + 1), Complex.normSq (complexOverlap
        (complexQubitVector m j) (complexQubitVector m (j + 1))) by
    refine Fintype.sum_equiv (ZMod.finEquiv (2 * m + 1)).symm _ _ ?_
    intro i
    change Complex.normSq (complexOverlap
      (complexQubitVector m ((ZMod.finEquiv (2 * m + 1)).symm i))
      (complexQubitVector m ((ZMod.finEquiv (2 * m + 1)).symm (i + 1)))) = _
    simp]
  exact b188_complex_odd_cycle_attained_normSq m

/-- **B188's full `ℂ²` minimum:** exact least value among all normalised
spinor fields on an odd cycle. -/
theorem b188_complex_odd_cycle_isLeast_normSq (m : ℕ) :
    IsLeast {x : ℝ | ∃ v : ZMod (2 * m + 1) → Fin 2 → ℂ,
      (∀ i, Complex.normSq (v i 0) + Complex.normSq (v i 1) = 1) ∧
      x = ∑ i, Complex.normSq (complexOverlap (v i) (v (i + 1)))}
      (((2 * (m : ℝ) + 1) / 2) *
        (1 - Real.cos (Real.pi / (2 * (m : ℝ) + 1)))) := by
  constructor
  · exact ⟨complexMinimisingField m, complexMinimisingField_unit m,
      (complexMinimisingField_attains m).symm⟩
  · rintro x ⟨v, hv, rfl⟩
    exact b188_complex_odd_cycle_lower_normSq v hv

#print axioms complexMinimisingField_unit
#print axioms complexMinimisingField_attains
#print axioms b188_complex_odd_cycle_isLeast_normSq

end RelationalAtlas.B188

namespace RelationalAtlas.B188
open scoped BigOperators

/-- **B188's real minimum:** exact least value zero for unit real fields. -/
theorem b188_real_odd_cycle_isLeast {m : ℕ} (hm : 1 ≤ m) :
    IsLeast {x : ℝ | ∃ v : Fin (2 * m + 1) → Fin 3 → ℝ,
      (∀ i, dot3 (v i) (v i) = 1) ∧
      x = ∑ i, (dot3 (v i) (v (i + 1))) ^ 2} 0 := by
  constructor
  · obtain ⟨c, s, hunit, hedge, hsum⟩ := b188_real_odd_cycle_zero hm
    exact ⟨oddUmbrellaVector c s m, hunit, hsum.symm⟩
  · rintro x ⟨v, hv, rfl⟩
    exact Finset.sum_nonneg fun i hi => sq_nonneg _

/-- The KCBS contradiction in one inequality: every deterministic assignment
respecting adjacent exclusivity is strictly below the quantum axial total. -/
theorem b188_pentagon_contextuality_gap {c s : ℝ}
    (hc : c ^ 2 = 1 / Real.sqrt 5) (a : Fin 5 → Bool)
    (ha : ExclusiveAssignment a) :
    (∑ i : Fin 5, if a i then (1 : ℝ) else 0) <
      ∑ i : Fin 5, axialBornWeight c s i := by
  have hnc := b188_pentagon_noncontextual_real a ha
  have hq := b188_pentagon_axial_born_sum_gt_two (s := s) hc
  linarith

#print axioms b188_real_odd_cycle_isLeast
#print axioms b188_pentagon_contextuality_gap

end RelationalAtlas.B188


/-! Full dependency audit: every theorem and lemma declared above. -/

#print axioms RelationalAtlas.B188.dot3_pentagonVector
#print axioms RelationalAtlas.B188.pentagonAngle_zero
#print axioms RelationalAtlas.B188.cos_angle_succ_sub
#print axioms RelationalAtlas.B188.dot3_pentagonVector_succ
#print axioms RelationalAtlas.B188.dot3_pentagonVector_self
#print axioms RelationalAtlas.B188.dot3_literal_pentagon_self
#print axioms RelationalAtlas.B188.cos_four_pi_div_five
#print axioms RelationalAtlas.B188.dot3_pentagonVector_succ_eq_zero
#print axioms RelationalAtlas.B188.sqrt_five_pos
#print axioms RelationalAtlas.B188.sqrt_five_ne_zero
#print axioms RelationalAtlas.B188.sq_sqrt_five
#print axioms RelationalAtlas.B188.literal_pentagon_orthogonality_relation
#print axioms RelationalAtlas.B188.b188_pentagon_neighbours_orthogonal
#print axioms RelationalAtlas.B188.b188_pentagon_mirror_edges
#print axioms RelationalAtlas.B188.five_div_sqrt_five
#print axioms RelationalAtlas.B188.b188_pentagon_axial_born_sum
#print axioms RelationalAtlas.B188.two_lt_sqrt_five
#print axioms RelationalAtlas.B188.b188_pentagon_axial_born_sum_gt_two
#print axioms RelationalAtlas.B188.b188_pentagon_noncontextual_nat
#print axioms RelationalAtlas.B188.b188_pentagon_noncontextual_real
#print axioms RelationalAtlas.B188.dot3_oddUmbrellaVector
#print axioms RelationalAtlas.B188.cos_oddUmbrellaAngle_succ_sub
#print axioms RelationalAtlas.B188.dot3_oddUmbrellaVector_succ
#print axioms RelationalAtlas.B188.cos_odd_step
#print axioms RelationalAtlas.B188.dot3_oddUmbrellaVector_self
#print axioms RelationalAtlas.B188.dot3_oddUmbrellaVector_succ_eq_zero
#print axioms RelationalAtlas.B188.oddUmbrellaC2_nonneg
#print axioms RelationalAtlas.B188.oddUmbrellaS2_nonneg
#print axioms RelationalAtlas.B188.oddUmbrella_amplitudes_sum
#print axioms RelationalAtlas.B188.oddUmbrella_amplitudes_orthogonal
#print axioms RelationalAtlas.B188.b188_odd_umbrella_balanced
#print axioms RelationalAtlas.B188.cos_odd_denominator_nonneg
#print axioms RelationalAtlas.B188.b188_real_odd_cycle_zero
#print axioms RelationalAtlas.B188.dot2_qubitVector
#print axioms RelationalAtlas.B188.dot2_qubitVector_self
#print axioms RelationalAtlas.B188.cos_qubitAngle_succ_sub
#print axioms RelationalAtlas.B188.cos_qubitAngle_last
#print axioms RelationalAtlas.B188.qubit_neighbour_overlap_sq
#print axioms RelationalAtlas.B188.qubit_two_step_cos
#print axioms RelationalAtlas.B188.qubit_overlap_sq_eq_book
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_attained
#print axioms RelationalAtlas.B188.complexOverlap_of_real
#print axioms RelationalAtlas.B188.normSq_complexOverlap_of_real
#print axioms RelationalAtlas.B188.complex_qubit_overlap_normSq
#print axioms RelationalAtlas.B188.complex_qubit_unit
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_attained_normSq
#print axioms RelationalAtlas.B188.triangle_inner_sum_nonneg
#print axioms RelationalAtlas.B188.b188_triangle_bloch_lower
#print axioms RelationalAtlas.B188.b188_triangle_bloch_lower_cyclic
#print axioms RelationalAtlas.B188.star_stdAddChar
#print axioms RelationalAtlas.B188.dft_parseval
#print axioms RelationalAtlas.B188.dft_cyclicShift
#print axioms RelationalAtlas.B188.stdAddChar_re
#print axioms RelationalAtlas.B188.stdAddChar_add_neg
#print axioms RelationalAtlas.B188.dft_cyclicBack
#print axioms RelationalAtlas.B188.dft_cycleOperator
#print axioms RelationalAtlas.B188.dft_cycleOperator_cos
#print axioms RelationalAtlas.B188.dft_cycle_quadratic
#print axioms RelationalAtlas.B188.cycleQuadratic_cast
#print axioms RelationalAtlas.B188.cycleQuadratic_cast_dft
#print axioms RelationalAtlas.B188.cycleQuadratic_nonneg_of_eigenvalue_nonneg
#print axioms RelationalAtlas.B188.odd_frequency_cos_lower
#print axioms RelationalAtlas.B188.odd_cycleEigenvalue_nonneg
#print axioms RelationalAtlas.B188.dotCyc_comm
#print axioms RelationalAtlas.B188.sum_dotCyc_pred
#print axioms RelationalAtlas.B188.cycleQuadratic_expand
#print axioms RelationalAtlas.B188.sum_cycleQuadratic_coordinates
#print axioms RelationalAtlas.B188.odd_bloch_adjacency_lower
#print axioms RelationalAtlas.B188.blochOverlap_sum_expand
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_lower
#print axioms RelationalAtlas.B188.qubitVector_eq_realQubitState
#print axioms RelationalAtlas.B188.dot2_realQubitState_self
#print axioms RelationalAtlas.B188.dot3_blochFromAngle
#print axioms RelationalAtlas.B188.dot3_blochFromAngle_self
#print axioms RelationalAtlas.B188.minimisingBloch_unit
#print axioms RelationalAtlas.B188.minimisingBloch_overlap
#print axioms RelationalAtlas.B188.minimisingBloch_sum_eq_qubit
#print axioms RelationalAtlas.B188.b188_minimisingBloch_attains
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_isLeast
#print axioms RelationalAtlas.B188.dot3_blochOfComplex
#print axioms RelationalAtlas.B188.blochOfComplex_overlap_of_unit
#print axioms RelationalAtlas.B188.blochOfComplex_self_of_unit
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_lower_normSq
#print axioms RelationalAtlas.B188.complexMinimisingField_unit
#print axioms RelationalAtlas.B188.complexMinimisingField_attains
#print axioms RelationalAtlas.B188.b188_complex_odd_cycle_isLeast_normSq
#print axioms RelationalAtlas.B188.b188_real_odd_cycle_isLeast
#print axioms RelationalAtlas.B188.b188_pentagon_contextuality_gap


/-! ## B189 — the scalar rapidity, audited against the pinned companion

Integrated from `.ultramath/smwvp3cvb/m12/B189.lean`.
-/

/-!
# B189: one scalar edge is one reflecting step

The card's scalar books are `E⁻ = (di - dj)^2` and `E⁺ = (di + dj)^2`.
This file checks the pinned Smith coordinate and proves the book and boost
clauses that the external mapping does not cover. Positivity is assumed only
where the logarithm/tanh formula or the bounds on the reflection coefficient
need it.
-/

namespace RelationalAtlas.B189

open Real

/-- The reflection coefficient of a scalar edge. -/
noncomputable def gamma (di dj : ℝ) : ℝ := (di - dj) / (di + dj)

/-- The connection-energy book of a scalar edge. -/
noncomputable def eminus (di dj : ℝ) : ℝ := (di - dj) ^ 2

/-- The opposite book of a scalar edge. -/
noncomputable def eplus (di dj : ℝ) : ℝ := (di + dj) ^ 2

/-- `tanh t = (exp (2*t) - 1)/(exp (2*t) + 1)`. -/
theorem tanh_exp (t : ℝ) :
    tanh t = (exp (2 * t) - 1) / (exp (2 * t) + 1) := by
  have h2 : exp (2 * t) = exp t * exp t := by rw [← exp_add]; ring_nf
  have hn : exp (-t) = (exp t)⁻¹ := exp_neg t
  have he : 0 < exp t := exp_pos t
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, h2, hn]
  have h1 : exp t + (exp t)⁻¹ ≠ 0 := by positivity
  have h3 : exp t * exp t + 1 ≠ 0 := by positivity
  field_simp

/-- For every `z > 0`, `(z - 1)/(z + 1) = tanh (log z / 2)`. -/
theorem smith_coordinate (z : ℝ) (hz : 0 < z) :
    (z - 1) / (z + 1) = tanh (log z / 2) := by
  rw [tanh_exp]
  have h : 2 * (log z / 2) = log z := by ring
  rw [h, exp_log hz]

/-- The ratio of the two books is the square of the reflection coefficient. -/
theorem book_ratio (di dj : ℝ) :
    eminus di dj / eplus di dj = (gamma di dj) ^ 2 := by
  rw [eminus, eplus, gamma, div_pow]

/-- Flux balance: the difference of the two books is `4 * di * dj`. -/
theorem book_difference (di dj : ℝ) :
    eplus di dj - eminus di dj = 4 * di * dj := by
  rw [eplus, eminus]
  ring

/-- The reflection coefficient is the tanh of half the log ratio. -/
theorem gamma_eq_tanh (di dj : ℝ) (hi : 0 < di) (hj : 0 < dj) :
    gamma di dj = tanh (log (di / dj) / 2) := by
  rw [← smith_coordinate (di / dj) (div_pos hi hj), gamma]
  have hj0 : dj ≠ 0 := hj.ne'
  have hs : di + dj ≠ 0 := by linarith
  field_simp

/-- `tanh` adds by the velocity-addition law. -/
theorem tanh_add_div (a b : ℝ) :
    tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b) := by
  have ca : cosh a ≠ 0 := (cosh_pos a).ne'
  have cb : cosh b ≠ 0 := (cosh_pos b).ne'
  have hc : cosh a * cosh b ≠ 0 := by positivity
  have hs : cosh a * cosh b + sinh a * sinh b ≠ 0 := by
    rw [← cosh_add]
    exact (cosh_pos _).ne'
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh,
    sinh_add, cosh_add]
  rw [div_add_div _ _ ca cb, div_mul_div_comm, one_add_div hc,
    div_div_div_cancel_right₀ hc]

/-- The boost `di ↦ exp φ * di`, `dj ↦ exp (-φ) * dj` adds `φ` to rapidity. -/
theorem gamma_boost (di dj φ : ℝ) (hi : 0 < di) (hj : 0 < dj) :
    gamma (exp φ * di) (exp (-φ) * dj) =
      (gamma di dj + tanh φ) / (1 + gamma di dj * tanh φ) := by
  have harg :
      log ((exp φ * di) / (exp (-φ) * dj)) / 2 = log (di / dj) / 2 + φ := by
    rw [log_div (mul_ne_zero (exp_pos _).ne' hi.ne')
        (mul_ne_zero (exp_pos _).ne' hj.ne'),
      log_mul (exp_pos _).ne' hi.ne', log_mul (exp_pos _).ne' hj.ne',
      log_div hi.ne' hj.ne', log_exp, log_exp]
    ring
  rw [gamma_eq_tanh _ _ (mul_pos (exp_pos _) hi) (mul_pos (exp_pos _) hj),
    gamma_eq_tanh _ _ hi hj, harg, tanh_add_div]

/-- Positive endpoints give a reflection coefficient strictly inside the unit disk. -/
theorem gamma_mem_unit_interval (di dj : ℝ) (hi : 0 < di) (hj : 0 < dj) :
    -1 < gamma di dj ∧ gamma di dj < 1 := by
  have hs : 0 < di + dj := by linarith
  constructor
  · rw [gamma, lt_div_iff₀ hs]
    linarith
  · rw [gamma, div_lt_one hs]
    linarith

/-- Positive endpoints give `|Γ| < 1`. -/
theorem abs_gamma_lt_one (di dj : ℝ) (hi : 0 < di) (hj : 0 < dj) :
    |gamma di dj| < 1 := by
  exact abs_lt.mpr (gamma_mem_unit_interval di dj hi hj)

/-- Exchanging the ends negates the reflection coefficient, including the
formal zero-denominator case of Lean's total division. -/
theorem gamma_swap (di dj : ℝ) : gamma dj di = -gamma di dj := by
  by_cases h : di + dj = 0
  · have h' : dj + di = 0 := by linarith
    simp [gamma, h, h']
  · have h' : dj + di ≠ 0 := by simpa [add_comm] using h
    rw [gamma, gamma]
    field_simp
    ring

/-- Exchanging the ends leaves the connection-energy book unchanged. -/
theorem eminus_swap (di dj : ℝ) : eminus dj di = eminus di dj := by
  rw [eminus, eminus]
  ring

/-- Exchanging the ends leaves the opposite book unchanged. -/
theorem eplus_swap (di dj : ℝ) : eplus dj di = eplus di dj := by
  rw [eplus, eplus, add_comm]

/-- A matched edge has zero reflection coefficient and zero connection energy. -/
theorem matched_edge (d : ℝ) : gamma d d = 0 ∧ eminus d d = 0 := by
  simp [gamma, eminus]

/-- The round-trip identity checked by the pinned companion kernel. -/
theorem round_trip (t : ℝ) : 1 - tanh t ^ 2 = 1 / cosh t ^ 2 := by
  have hc := (cosh_pos t).ne'
  rw [tanh_eq_sinh_div_cosh]
  field_simp
  linarith [cosh_sq_sub_sinh_sq t]

/-- At a zero endpoint the log/tanh display is false if positivity is dropped:
`di = 0`, `dj = 1` gives `Γ = -1`, while the totalized log/tanh expression is `0`. -/
theorem zero_endpoint_not_tanh :
    gamma 0 1 ≠ tanh (log ((0 : ℝ) / 1) / 2) := by
  norm_num [gamma]

#print axioms RelationalAtlas.B189.tanh_exp
#print axioms RelationalAtlas.B189.smith_coordinate
#print axioms RelationalAtlas.B189.book_ratio
#print axioms RelationalAtlas.B189.book_difference
#print axioms RelationalAtlas.B189.gamma_eq_tanh
#print axioms RelationalAtlas.B189.tanh_add_div
#print axioms RelationalAtlas.B189.gamma_boost
#print axioms RelationalAtlas.B189.gamma_mem_unit_interval
#print axioms RelationalAtlas.B189.abs_gamma_lt_one
#print axioms RelationalAtlas.B189.gamma_swap
#print axioms RelationalAtlas.B189.eminus_swap
#print axioms RelationalAtlas.B189.eplus_swap
#print axioms RelationalAtlas.B189.matched_edge
#print axioms RelationalAtlas.B189.round_trip
#print axioms RelationalAtlas.B189.zero_endpoint_not_tanh

end RelationalAtlas.B189


/-! ## B192 — the signless Laplacian gap is a bipartiteness question

Integrated from `.ultramath/smwvp3cvb/m15/B192.lean`.
-/

/-!
# B192: the scalar opposite energy and the signless Laplacian

The support graph uses nonzero edge weights. Isolated vertices are one-vertex
components and are bipartite.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace AtlasB192

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite symmetric nonnegative loop-free weighted graph. -/
structure WeightData (n : Type*) [DecidableEq n] where
  weight : Matrix n n ℝ
  transpose : weightᵀ = weight
  nonneg : ∀ i j, 0 ≤ weight i j
  diag : ∀ i, weight i i = 0

namespace WeightData

variable (W : WeightData n)

/-- The graph of nonzero weights. -/
def graph : SimpleGraph n where
  Adj i j := W.weight i j ≠ 0
  symm := ⟨by
    intro i j h
    have he := congrFun (congrFun W.transpose j) i
    simp only [Matrix.transpose_apply] at he
    rwa [← he]⟩
  loopless := ⟨by
    intro i h
    exact h (W.diag i)⟩

@[simp] lemma graph_adj (i j : n) : W.graph.Adj i j ↔ W.weight i j ≠ 0 := Iff.rfl

lemma weight_pos_of_adj {i j : n} (h : W.graph.Adj i j) : 0 < W.weight i j :=
  lt_of_le_of_ne (W.nonneg i j) (Ne.symm h)

lemma weight_eq_zero_of_not_adj {i j : n} (h : ¬ W.graph.Adj i j) : W.weight i j = 0 :=
  not_ne_iff.mp h

end WeightData

/-- Weighted degree. -/
noncomputable def deg (w : Matrix n n ℝ) (i : n) : ℝ := ∑ j, w i j

/-- The signless Laplacian `Deg + w`. -/
noncomputable def signless (w : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (deg w) + w

/-- Its real quadratic form. -/
noncomputable def signlessForm (w : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  d ⬝ᵥ (signless w *ᵥ d)


/-- The ordered-pair sum local to the plus connection energy. -/
noncomputable def edgeSum (w : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (d i + d j) ^ 2

lemma signless_isHermitian (W : WeightData n) : (signless W.weight).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact (Matrix.isSymm_diagonal _).add W.transpose

lemma dotProduct_diagonal_mulVec (a d : n → ℝ) :
    d ⬝ᵥ (Matrix.diagonal a *ᵥ d) = ∑ i, a i * d i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma dotProduct_mulVec_expand (w : Matrix n n ℝ) (d : n → ℝ) :
    d ⬝ᵥ (w *ᵥ d) = ∑ i, ∑ j, d i * w i j * d j := by
  simp only [dotProduct, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma signlessForm_eq_expansion (W : WeightData n) (d : n → ℝ) :
    signlessForm W.weight d =
      (∑ i, ∑ j, W.weight i j * d i ^ 2) +
        ∑ i, ∑ j, W.weight i j * d i * d j := by
  unfold signlessForm signless
  rw [Matrix.add_mulVec, dotProduct_add, dotProduct_diagonal_mulVec,
    dotProduct_mulVec_expand]
  congr 1
  · simp only [deg, Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma edgeSum_swap (W : WeightData n) (d : n → ℝ) :
    (∑ i, ∑ j, W.weight i j * d j ^ 2) =
      ∑ i, ∑ j, W.weight i j * d i ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he := congrFun (congrFun W.transpose j) i
  simp only [Matrix.transpose_apply] at he
  simp only [← he]

/-- `dᵀ(Deg+w)d` is half the ordered edge sum of `w(d_i+d_j)²`. -/
theorem signlessForm_eq_half_edgeSum (W : WeightData n) (d : n → ℝ) :
    signlessForm W.weight d = edgeSum W.weight d / 2 := by
  rw [signlessForm_eq_expansion]
  unfold edgeSum
  have hsq (i j : n) : W.weight i j * (d i + d j) ^ 2 =
      W.weight i j * d i ^ 2 + 2 * (W.weight i j * d i * d j) +
        W.weight i j * d j ^ 2 := by ring
  simp_rw [hsq]
  simp only [Finset.sum_add_distrib]
  rw [edgeSum_swap]
  have htwo (f : n → n → ℝ) :
      (∑ i, ∑ j, 2 * f i j) = 2 * ∑ i, ∑ j, f i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [htwo]
  ring

lemma edgeSum_nonneg (W : WeightData n) (d : n → ℝ) : 0 ≤ edgeSum W.weight d := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (W.nonneg i j) (sq_nonneg _)

lemma signlessForm_nonneg (W : WeightData n) (d : n → ℝ) :
    0 ≤ signlessForm W.weight d := by
  rw [signlessForm_eq_half_edgeSum]
  exact div_nonneg (edgeSum_nonneg W d) (by norm_num)

/-- Positive semidefiniteness of the weighted signless Laplacian. -/
theorem signless_posSemidef (W : WeightData n) : (signless W.weight).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (signless_isHermitian W)
  intro d
  change 0 ≤ d ⬝ᵥ (signless W.weight *ᵥ d)
  exact signlessForm_nonneg W d


/-- A field which is anti-parallel across every edge of positive weight. -/
def IsAlternating (G : SimpleGraph n) (d : n → ℝ) : Prop :=
  ∀ i j, G.Adj i j → d i + d j = 0

lemma edgeSum_eq_zero_terms (W : WeightData n) (d : n → ℝ)
    (h : edgeSum W.weight d = 0) (i j : n) :
    W.weight i j * (d i + d j) ^ 2 = 0 := by
  have hnn (i : n) : 0 ≤ ∑ j, W.weight i j * (d i + d j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (W.nonneg i j) (sq_nonneg _)
  have hout : ∑ j, W.weight i j * (d i + d j) ^ 2 = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp
    · simpa only [edgeSum] using h
    · exact Finset.mem_univ i
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (W.nonneg i j) (sq_nonneg _))).mp hout j (Finset.mem_univ j)

/-- Zero quadratic form is precisely the anti-parallel edge condition. -/
theorem signlessForm_eq_zero_iff_alternating (W : WeightData n) (d : n → ℝ) :
    signlessForm W.weight d = 0 ↔ IsAlternating W.graph d := by
  constructor
  · intro h i j hij
    have he : edgeSum W.weight d = 0 := by
      rw [signlessForm_eq_half_edgeSum] at h
      linarith
    have hz := edgeSum_eq_zero_terms W d he i j
    have hs : (d i + d j) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hij
    exact sq_eq_zero_iff.mp hs
  · intro h
    rw [signlessForm_eq_half_edgeSum]
    have he : edgeSum W.weight d = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hij : W.graph.Adj i j
      · rw [h i j hij]
        norm_num
      · rw [W.weight_eq_zero_of_not_adj hij]
        norm_num
    rw [he]
    norm_num

/-- The kernel of the signless Laplacian consists exactly of the alternating
sections on its support graph. -/
theorem signless_mulVec_eq_zero_iff_alternating (W : WeightData n) (d : n → ℝ) :
    signless W.weight *ᵥ d = 0 ↔ IsAlternating W.graph d := by
  rw [← (signless_posSemidef W).dotProduct_mulVec_zero_iff]
  simpa only [star_trivial, signlessForm] using signlessForm_eq_zero_iff_alternating W d


section GraphZeroModes

variable {G : SimpleGraph n} {d : n → ℝ}

lemma alternating_sq_of_walk (h : IsAlternating G d) {u v : n}
    (p : G.Walk u v) : d v ^ 2 = d u ^ 2 := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      rw [ih]
      have ha : d v = -d u := by linarith [h _ _ huv]
      rw [ha]
      ring

/-- A nonzero alternating section makes its whole connected component
bipartite: after showing it is everywhere nonzero there, its sign is a proper
coloring. -/
theorem exists_bipartite_component_of_nonzero_alternating
    (h : IsAlternating G d) (hd : d ≠ 0) :
    ∃ C : G.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  obtain ⟨r, hr⟩ : ∃ r, d r ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hd (funext fun i => hn i)
  let C := G.connectedComponentMk r
  refine ⟨C, ?_⟩
  have hrC : r ∈ C.supp := rfl
  have hnz (v : C) : d v.val ≠ 0 := by
    obtain ⟨p⟩ := C.reachable_of_mem_supp hrC v.prop
    have hs := alternating_sq_of_walk h p
    intro hv
    rw [hv] at hs
    have hz : d r ^ 2 = 0 := by nlinarith
    exact hr (sq_eq_zero_iff.mp hz)
  refine ⟨SimpleGraph.Coloring.mk
    (fun v : C => if 0 < d v.val then (0 : Fin 2) else 1) ?_⟩
  intro u v huv
  have ha : d u.val + d v.val = 0 := h _ _ huv
  have hu := hnz u
  have hv := hnz v
  by_cases hup : 0 < d u.val
  · by_cases hvp : 0 < d v.val
    · exfalso
      nlinarith
    · simp only [hup, hvp, ite_true, ite_false]
      norm_num
  · by_cases hvp : 0 < d v.val
    · simp only [hup, hvp, ite_true, ite_false]
      norm_num
    · exfalso
      have hun : d u.val < 0 := lt_of_le_of_ne (le_of_not_gt hup) hu
      have hvn : d v.val < 0 := lt_of_le_of_ne (le_of_not_gt hvp) hv
      nlinarith

/-- Conversely, a two-coloring of one connected component gives a global
alternating field, supported on that component and taking values `±1` there. -/
theorem nonzero_alternating_of_bipartite_component
    {C : G.ConnectedComponent} (hC : C.toSimpleGraph.IsBipartite) :
    ∃ d : n → ℝ, d ≠ 0 ∧ IsAlternating G d := by
  classical
  rcases hC with ⟨χ⟩
  let dc : C → ℝ := fun v => if χ v = 0 then 1 else -1
  have hdc (v : C) : dc v ≠ 0 := by
    simp only [dc]
    split_ifs <;> norm_num
  have hantiC {u v : C} (huv : C.toSimpleGraph.Adj u v) : dc u + dc v = 0 := by
    have hne := χ.valid huv
    simp only [dc]
    generalize hu : χ u = cu at hne ⊢
    generalize hv : χ v = cv at hne ⊢
    fin_cases cu <;> fin_cases cv <;> norm_num at *
  let d : n → ℝ := fun i => if hi : i ∈ C.supp then dc ⟨i, hi⟩ else 0
  refine ⟨d, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := C.nonempty_supp
    intro hz
    have he := congrFun hz r
    simp only [d, dif_pos hr, Pi.zero_apply] at he
    exact hdc ⟨r, hr⟩ he
  · intro i j hij
    by_cases hi : i ∈ C.supp
    · have hj : j ∈ C.supp := C.mem_supp_of_adj_mem_supp hi hij
      simp only [d, dif_pos hi, dif_pos hj]
      exact hantiC ((C.toSimpleGraph_adj hi hj).2 hij)
    · have hj : j ∉ C.supp := by
        intro hj
        exact hi ((C.mem_supp_congr_adj hij).2 hj)
      simp only [d, dif_neg hi, dif_neg hj, add_zero]

/-- Exact component formulation of the zero-mode condition, including
one-vertex (isolated) components. -/
theorem exists_nonzero_alternating_iff_bipartite_component (G : SimpleGraph n) :
    (∃ d : n → ℝ, d ≠ 0 ∧ IsAlternating G d) ↔
      ∃ C : G.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  constructor
  · rintro ⟨d, hd, h⟩
    exact exists_bipartite_component_of_nonzero_alternating h hd
  · rintro ⟨C, hC⟩
    exact nonzero_alternating_of_bipartite_component hC

end GraphZeroModes

/-- **B192 kernel theorem.** A weighted signless Laplacian has a nontrivial
real kernel exactly when some component of its support graph is bipartite. -/
theorem exists_signless_zeroMode_iff_bipartite_component (W : WeightData n) :
    (∃ d : n → ℝ, d ≠ 0 ∧ signless W.weight *ᵥ d = 0) ↔
      ∃ C : W.graph.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  simp only [← exists_nonzero_alternating_iff_bipartite_component W.graph]
  exact exists_congr fun d => and_congr_right fun _ => signless_mulVec_eq_zero_iff_alternating W d


section Spectrum

/-- Failure of matrix-multiply injectivity is exactly a nonzero kernel vector. -/
lemma not_injective_mulVec_iff_exists_zeroMode (A : Matrix n n ℝ) :
    ¬ Function.Injective A.mulVec ↔ ∃ d : n → ℝ, d ≠ 0 ∧ A *ᵥ d = 0 := by
  constructor
  · intro h
    obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp h
    refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
    rw [Matrix.mulVec_sub, hxy, sub_self]
  · rintro ⟨d, hd, hAd⟩ hinj
    apply hd
    apply hinj
    simpa using hAd

variable [Nonempty n]

/-- Least eigenvalue of a real Hermitian matrix, as a finite minimum. -/
noncomputable def minEigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

lemma minEigenvalue_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    minEigenvalue hA ≤ hA.eigenvalues i := by
  exact Finset.inf'_le hA.eigenvalues (Finset.mem_univ i)

lemma le_minEigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian) {a : ℝ}
    (ha : ∀ i, a ≤ hA.eigenvalues i) : a ≤ minEigenvalue hA := by
  exact Finset.le_inf' Finset.univ_nonempty hA.eigenvalues (fun i _ => ha i)

lemma minEigenvalue_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    0 ≤ minEigenvalue hA.1 := by
  exact le_minEigenvalue hA.1 (fun i => hA.eigenvalues_nonneg i)

/-- For positive semidefinite matrices the least eigenvalue vanishes exactly
when the matrix has a kernel. -/
theorem minEigenvalue_eq_zero_iff_not_injective {A : Matrix n n ℝ}
    (hA : A.PosSemidef) :
    minEigenvalue hA.1 = 0 ↔ ¬ Function.Injective A.mulVec := by
  constructor
  · intro hz hinj
    have hpos : ∀ i, 0 < hA.1.eigenvalues i :=
      hA.1.posDef_iff_eigenvalues_pos.mp (hA.posDef_iff_mulVec_injective.mpr hinj)
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hA.1.eigenvalues
    rw [show minEigenvalue hA.1 = hA.1.eigenvalues i from heq] at hz
    linarith [hpos i]
  · intro hni
    apply le_antisymm _ (minEigenvalue_nonneg hA)
    by_contra hnot
    have hpos : ∀ i, 0 < hA.1.eigenvalues i := by
      intro i
      have hi : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
      by_contra hn
      have hzero : hA.1.eigenvalues i = 0 := le_antisymm (le_of_not_gt hn) hi
      have hle : minEigenvalue hA.1 ≤ 0 := by
        calc
          minEigenvalue hA.1 ≤ hA.1.eigenvalues i := minEigenvalue_le hA.1 i
          _ = 0 := hzero
      have hge : 0 < minEigenvalue hA.1 := lt_of_not_ge hnot
      linarith
    exact hni (hA.posDef_iff_mulVec_injective.mp
      (hA.1.posDef_iff_eigenvalues_pos.mpr hpos))

/-- **B192 spectral zero criterion.** -/
theorem minEigenvalue_signless_eq_zero_iff_bipartite_component (W : WeightData n) :
    minEigenvalue (signless_isHermitian W) = 0 ↔
      ∃ C : W.graph.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  rw [minEigenvalue_eq_zero_iff_not_injective (signless_posSemidef W),
    not_injective_mulVec_iff_exists_zeroMode]
  exact exists_signless_zeroMode_iff_bipartite_component W

/-- Positive-gap form: the opposite has a gap exactly when no component is
bipartite (equivalently, in the usual graph formulation, every component has
an odd cycle). -/
theorem minEigenvalue_signless_pos_iff_no_bipartite_component (W : WeightData n) :
    0 < minEigenvalue (signless_isHermitian W) ↔
      ¬ ∃ C : W.graph.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  constructor
  · intro hp hb
    have hz := (minEigenvalue_signless_eq_zero_iff_bipartite_component W).2 hb
    linarith
  · intro hno
    have hne : minEigenvalue (signless_isHermitian W) ≠ 0 := by
      intro hz
      exact hno ((minEigenvalue_signless_eq_zero_iff_bipartite_component W).1 hz)
    exact lt_of_le_of_ne (minEigenvalue_nonneg (signless_posSemidef W)) (Ne.symm hne)

end Spectrum


section Rayleigh

variable [Nonempty n]
open Unitary

lemma posSemidef_sub_smul_one_of_le_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (a : ℝ) (ha : ∀ i, a ≤ hA.eigenvalues i) :
    (A - a • (1 : Matrix n n ℝ)).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal hA.eigenvalues - a • 1
  have hDeq : D = Matrix.diagonal (fun i => hA.eigenvalues i - a) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  have hD : D.PosSemidef := by
    rw [hDeq]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (ha i)
  have hsp : A = (U : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues * star (U : Matrix n n ℝ) := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hU : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hid : (1 : Matrix n n ℝ) = (U : Matrix n n ℝ) * 1 * star (U : Matrix n n ℝ) := by
    rw [Matrix.mul_one, hU]
  have heq : A - a • (1 : Matrix n n ℝ) = (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) := by
    rw [hsp, hid]
    simp only [D, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul]
  rw [heq]
  exact Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff.mpr hD

/-- The variational lower bound for the minimum Hermitian eigenvalue, in
squared-Euclidean-norm form. -/
theorem dotProduct_mulVec_ge_minEigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (d : n → ℝ) :
    minEigenvalue hA * (∑ i, d i ^ 2) ≤ d ⬝ᵥ (A *ᵥ d) := by
  have hshift := posSemidef_sub_smul_one_of_le_eigenvalues hA
    (minEigenvalue hA) (minEigenvalue_le hA)
  have h := hshift.dotProduct_mulVec_nonneg d
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at h
  have hnorm : d ⬝ᵥ d = ∑ i, d i ^ 2 := by
    simp only [dotProduct, pow_two]
  rw [hnorm] at h
  linarith

/-- **B192's unprojected Rayleigh/Fiedler bound.** -/
theorem signless_rayleigh_min (W : WeightData n) (d : n → ℝ) :
    minEigenvalue (signless_isHermitian W) * (∑ i, d i ^ 2) ≤ signlessForm W.weight d := by
  exact dotProduct_mulVec_ge_minEigenvalue (signless_isHermitian W) d

end Rayleigh


section ScalarConnection

/-- Squared-magnitude weights of a scalar complex connection. -/
noncomputable def scalarWeights (A : Matrix n n ℂ) : Matrix n n ℝ :=
  fun i j => ‖A i j‖ ^ 2

lemma skew_apply_neg_star {A : Matrix n n ℂ} (hA : Aᴴ = -A) (i j : n) :
    A j i = -star (A i j) := by
  have h := congrFun (congrFun hA j) i
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  calc
    A j i = -(-A j i) := by simp
    _ = -star (A i j) := by rw [← h]

/-- The squared magnitudes of a loop-free skew connection form the weight
data used above.  Unitarity is not needed for this scalar weighted form. -/
noncomputable def scalarWeightData (A : Matrix n n ℂ) (hA : Aᴴ = -A)
    (hdiag : ∀ i, A i i = 0) : WeightData n where
  weight := scalarWeights A
  transpose := by
    ext i j
    simp only [Matrix.transpose_apply, scalarWeights]
    rw [skew_apply_neg_star hA i j, norm_neg, norm_star]
  nonneg := by
    intro i j
    exact sq_nonneg _
  diag := by
    intro i
    simp [scalarWeights, hdiag i]

/-- Scalar vertex field plus complex transport. -/
noncomputable def scalarH (A : Matrix n n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => (d i : ℂ)) + A

lemma scalarH_square_sub_starSquare (A : Matrix n n ℂ) (hA : Aᴴ = -A) (d : n → ℝ) :
    scalarH A d ^ 2 - (scalarH A d)ᴴ ^ 2 =
      2 • (Matrix.diagonal (fun i => (d i : ℂ)) * A +
        A * Matrix.diagonal (fun i => (d i : ℂ))) := by
  have hd : star (fun i => (d i : ℂ)) = (fun i => (d i : ℂ)) := by
    funext i
    simp
  rw [scalarH, Matrix.conjTranspose_add, Matrix.diagonal_conjTranspose, hd, hA]
  noncomm_ring

lemma complex_norm_sq_eq_sum (X : Matrix n n ℂ) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

lemma norm_sq_real_smul_any {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (a : ℝ) (x : α) : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma complex_norm_sq_real_smul (a : ℝ) (X : Matrix n n ℂ) :
    ‖a • X‖ ^ 2 = a ^ 2 * ‖X‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

@[simp] lemma scalarH_anticommutator_apply (A : Matrix n n ℂ) (d : n → ℝ) (i j : n) :
    (Matrix.diagonal (fun i => (d i : ℂ)) * A +
      A * Matrix.diagonal (fun i => (d i : ℂ))) i j =
        (d i : ℂ) * A i j + A i j * (d j : ℂ) := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- **B192's displayed square-comparison identity in scalar form.**  The
normalized Frobenius energy is exactly the signless quadratic form. -/
theorem scalar_oppositeEnergy_eq_signlessForm
    (A : Matrix n n ℂ) (hA : Aᴴ = -A) (hdiag : ∀ i, A i i = 0) (d : n → ℝ) :
    ‖scalarH A d ^ 2 - (scalarH A d)ᴴ ^ 2‖ ^ 2 / 8 =
      signlessForm (scalarWeightData A hA hdiag).weight d := by
  rw [signlessForm_eq_half_edgeSum, scalarH_square_sub_starSquare A hA d,
    complex_norm_sq_eq_sum]
  have hterm (i j : n) :
      ‖(2 : ℕ) • ((d i : ℂ) * A i j + A i j * (d j : ℂ))‖ ^ 2 =
        4 * (‖A i j‖ ^ 2 * (d i + d j) ^ 2) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_sq_real_smul_any]
    have he : (d i : ℂ) * A i j + A i j * (d j : ℂ) = (d i + d j) • A i j := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp only [Matrix.smul_apply, scalarH_anticommutator_apply]
  simp_rw [hterm]
  have hfour (f : n → n → ℝ) :
      (∑ i, ∑ j, 4 * f i j) = 4 * ∑ i, ∑ j, f i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hfour]
  unfold edgeSum scalarWeightData scalarWeights
  ring

end ScalarConnection


section DegenerateChecks

/-- One undirected edge of weight `a`. -/
noncomputable def edgeWeightData (a : ℝ) (ha : 0 ≤ a) : WeightData (Fin 2) where
  weight := !![0, a; a, 0]
  transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ha]
  diag := by
    intro i
    fin_cases i <;> simp

lemma edge_alternating_form (a : ℝ) (ha : 0 ≤ a) :
    signlessForm (edgeWeightData a ha).weight ![1, -1] = 0 := by
  simp [signlessForm, signless, deg, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, edgeWeightData]

lemma edge_parallel_form (a : ℝ) (ha : 0 ≤ a) :
    signlessForm (edgeWeightData a ha).weight ![1, 1] = 4 * a := by
  simp [signlessForm, signless, deg, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, edgeWeightData]
  ring

/-- A single isolated vertex. -/
noncomputable def isolatedWeightData : WeightData (Fin 1) where
  weight := 0
  transpose := by simp
  nonneg := by simp
  diag := by simp

/-- Isolated vertices are indeed zero modes; the spectral minimum vanishes. -/
theorem isolated_minEigenvalue :
    minEigenvalue (signless_isHermitian isolatedWeightData) = 0 := by
  rw [minEigenvalue_eq_zero_iff_not_injective (signless_posSemidef isolatedWeightData),
    not_injective_mulVec_iff_exists_zeroMode]
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have he := congrFun h 0
    norm_num at he
  · funext i
    fin_cases i
    simp [signless, deg, isolatedWeightData, Matrix.mulVec, dotProduct]

/-- Unit weights on the triangle. -/
noncomputable def triangleWeightData : WeightData (Fin 3) where
  weight := fun i j => if i = j then 0 else 1
  transpose := by
    ext i j
    change (if j = i then (0 : ℝ) else 1) = if i = j then 0 else 1
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  nonneg := by
    intro i j
    split_ifs <;> norm_num
  diag := by simp

/-- The odd-cycle case: an alternating/kernel field on the triangle is zero. -/
theorem triangle_zero_mode_trivial {d : Fin 3 → ℝ}
    (hd : signless triangleWeightData.weight *ᵥ d = 0) : d = 0 := by
  have h := (signless_mulVec_eq_zero_iff_alternating triangleWeightData d).mp hd
  have h01 : d 0 + d 1 = 0 := h 0 1 (by norm_num [WeightData.graph, triangleWeightData])
  have h02 : d 0 + d 2 = 0 := h 0 2 (by norm_num [WeightData.graph, triangleWeightData])
  have h12 : d 1 + d 2 = 0 := h 1 2 (by norm_num [WeightData.graph, triangleWeightData])
  have hd0 : d 0 = 0 := by nlinarith
  have hd1 : d 1 = 0 := by nlinarith
  have hd2 : d 2 = 0 := by nlinarith
  funext i
  fin_cases i
  · simpa using hd0
  · simpa using hd1
  · simpa using hd2

end DegenerateChecks

#print axioms signlessForm_eq_half_edgeSum
#print axioms signless_posSemidef
#print axioms signlessForm_eq_zero_iff_alternating
#print axioms signless_mulVec_eq_zero_iff_alternating
#print axioms exists_nonzero_alternating_iff_bipartite_component
#print axioms exists_signless_zeroMode_iff_bipartite_component
#print axioms minEigenvalue_eq_zero_iff_not_injective
#print axioms minEigenvalue_signless_eq_zero_iff_bipartite_component
#print axioms minEigenvalue_signless_pos_iff_no_bipartite_component
#print axioms posSemidef_sub_smul_one_of_le_eigenvalues
#print axioms signless_rayleigh_min
#print axioms scalar_oppositeEnergy_eq_signlessForm
#print axioms edge_alternating_form
#print axioms edge_parallel_form
#print axioms isolated_minEigenvalue
#print axioms triangle_zero_mode_trivial

end AtlasB192


/-! ## B193 — the integer minimisation and the two worst cases

Integrated from `.ultramath/smwvp3cvb/m8/B193.lean`.
-/

open Real

noncomputable section

namespace RelationalAtlas.B193

/-- The representative of a total twist in `(-π, π]`. -/
def residue (d : ℝ) : ℝ := (d : Real.Angle).toReal

/-- The equally distributed candidate for one edge of the lower book. -/
def floorCandidate (N : ℕ) (d : ℝ) (w : ℤ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos ((d - 2 * π * (w : ℝ)) / (N : ℝ)))

/-- The exact closed form of the lower-book minimum. -/
def closedFloor (N : ℕ) (d : ℝ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos (residue d / (N : ℝ)))

lemma neg_pi_lt_residue (d : ℝ) : -π < residue d :=
  Real.Angle.neg_pi_lt_toReal (d : Real.Angle)

lemma residue_le_pi (d : ℝ) : residue d ≤ π :=
  Real.Angle.toReal_le_pi (d : Real.Angle)

lemma abs_residue_le_pi (d : ℝ) : |residue d| ≤ π :=
  Real.Angle.abs_toReal_le_pi (d : Real.Angle)

/-- Among the `N`-th roots of an angle, the root nearest zero has largest
cosine.  The proof is the nonnegative product
`cos a - cos(a+2b) = 2 sin(a+b) sin b`. -/
lemma cos_root_le {N : ℕ} (hN : 0 < N) {Δ : ℝ}
    (hΔlo : -π ≤ Δ) (hΔhi : Δ ≤ π) (k : Fin N) :
    Real.cos (Δ / (N : ℝ) + (k : ℝ) * (2 * π / (N : ℝ))) ≤
      Real.cos (Δ / (N : ℝ)) := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  by_cases hk : k.val = 0
  · have : (k : ℝ) = 0 := by exact_mod_cast hk
    simp [this]
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast k.isLt
    let b : ℝ := (k : ℝ) * π / (N : ℝ)
    have hb0 : 0 ≤ b := by dsimp [b]; positivity
    have hbπ : b ≤ π := by
      dsimp [b]
      apply (div_le_iff₀ hn).2
      nlinarith [Real.pi_pos]
    have hab0 : 0 ≤ Δ / (N : ℝ) + b := by
      rw [show Δ / (N : ℝ) + b = (Δ + (k : ℝ) * π) / (N : ℝ) by
        dsimp [b]; ring]
      apply div_nonneg _ hn.le
      nlinarith [Real.pi_pos]
    have habπ : Δ / (N : ℝ) + b ≤ π := by
      rw [show Δ / (N : ℝ) + b = (Δ + (k : ℝ) * π) / (N : ℝ) by
        dsimp [b]; ring]
      apply (div_le_iff₀ hn).2
      nlinarith [Real.pi_pos]
    have hsinab : 0 ≤ Real.sin (Δ / (N : ℝ) + b) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hab0 habπ
    have hsinb : 0 ≤ Real.sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb0 hbπ
    have hdiff : Real.cos (Δ / (N : ℝ)) - Real.cos (Δ / (N : ℝ) + 2 * b) =
        2 * Real.sin (Δ / (N : ℝ) + b) * Real.sin b := by
      rw [Real.cos_sub_cos]
      rw [show (Δ / (N : ℝ) + (Δ / (N : ℝ) + 2 * b)) / 2 =
          Δ / (N : ℝ) + b by ring]
      rw [show (Δ / (N : ℝ) - (Δ / (N : ℝ) + 2 * b)) / 2 = -b by ring]
      rw [Real.sin_neg]
      ring
    have hshift : (k : ℝ) * (2 * π / (N : ℝ)) = 2 * b := by
      dsimp [b]
      ring
    rw [hshift]
    nlinarith [mul_nonneg hsinab hsinb]

/-- Every winding number gives at least the closed-form lower floor. -/
lemma closedFloor_le_floorCandidate {N : ℕ} (hN : 0 < N) (d : ℝ) (w : ℤ) :
    closedFloor N d ≤ floorCandidate N d w := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  let δ : ℝ := residue d
  let θ : ℝ := (d - 2 * π * (w : ℝ)) / (N : ℝ)
  have hθ : N • ((θ : ℝ) : Real.Angle) = (d : Real.Angle) := by
    rw [← Real.Angle.coe_nsmul]
    apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨-w, ?_⟩
    dsimp [θ]
    push_cast
    simp only [nsmul_eq_mul]
    field_simp
    <;> ring
  have hδ : N • ((δ / (N : ℝ) : ℝ) : Real.Angle) = (d : Real.Angle) := by
    rw [← Real.Angle.coe_nsmul]
    rw [← Real.Angle.coe_toReal (d : Real.Angle)]
    apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    refine ⟨0, ?_⟩
    dsimp [δ, residue]
    simp only [nsmul_eq_mul, Int.cast_zero, mul_zero]
    field_simp
    <;> ring
  obtain ⟨k, hk⟩ := (Real.Angle.nsmul_eq_iff hN0).mp (hθ.trans hδ.symm)
  have hk' : ((θ : ℝ) : Real.Angle) =
      (((δ / (N : ℝ) + (k : ℝ) * (2 * π / (N : ℝ))) : ℝ) : Real.Angle) := by
    rw [hk, Real.Angle.coe_add, Real.Angle.natCast_mul_eq_nsmul]
  have hcos : Real.cos θ = Real.cos (δ / (N : ℝ) + (k : ℝ) * (2 * π / (N : ℝ))) := by
    have := congrArg Real.Angle.cos hk'
    simpa only [Real.Angle.cos_coe] using this
  have hle := cos_root_le hN (Real.Angle.neg_pi_lt_toReal (d : Real.Angle)).le
    (Real.Angle.toReal_le_pi (d : Real.Angle)) k
  change Real.cos (δ / (N : ℝ) + (k : ℝ) * (2 * π / (N : ℝ))) ≤
    Real.cos (δ / (N : ℝ)) at hle
  have hnreal : (0 : ℝ) ≤ (N : ℝ) := by positivity
  dsimp [closedFloor, floorCandidate]
  change 4 * (N : ℝ) * (1 - Real.cos (δ / (N : ℝ))) ≤
    4 * (N : ℝ) * (1 - Real.cos θ)
  rw [hcos]
  nlinarith


/-- The canonical representative is attained by an integer winding. -/
lemma floorCandidate_attained (N : ℕ) (d : ℝ) :
    ∃ w : ℤ, floorCandidate N d w = closedFloor N d := by
  obtain ⟨z, hz⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    (Real.Angle.coe_toReal (d : Real.Angle))
  refine ⟨-z, ?_⟩
  have hw : d - 2 * π * ((-z : ℤ) : ℝ) = residue d := by
    push_cast
    change d - 2 * π * (-(z : ℝ)) = (d : Real.Angle).toReal
    nlinarith
  simp only [floorCandidate, closedFloor, hw]

/-- **B193, exact one-book minimum.**  The integer minimisation is attained and
its value is the canonical-residue expression. -/
theorem oneBook_minimum {N : ℕ} (hN : 0 < N) (d : ℝ) :
    IsLeast (Set.range (floorCandidate N d)) (closedFloor N d) := by
  constructor
  · obtain ⟨w, hw⟩ := floorCandidate_attained N d
    exact ⟨w, hw⟩
  · rintro _ ⟨w, rfl⟩
    exact closedFloor_le_floorCandidate hN d w

/-- The opposite book is the lower book with the displayed twist shift. -/
def oppositeCandidate (N : ℕ) (d : ℝ) (w : ℤ) : ℝ :=
  floorCandidate N (d + (N : ℝ) * π) w

/-- The values available when one may choose either book. -/
def bothAttainable (N : ℕ) (d : ℝ) : Set ℝ :=
  Set.range (floorCandidate N d) ∪ Set.range (oppositeCandidate N d)

/-- Windings on the `π`-lattice, rather than the original `2π`-lattice. -/
def halfCandidate (N : ℕ) (d : ℝ) (w : ℤ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos ((d - π * (w : ℝ)) / (N : ℝ)))

/-- The closed form on the `π`-lattice, as used by both books on an odd ring. -/
def closedBothFloor (N : ℕ) (d : ℝ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos (residue (2 * d) / (2 * (N : ℝ))))

lemma closedBothFloor_le_halfCandidate {N : ℕ} (hN : 0 < N) (d : ℝ) (w : ℤ) :
    closedBothFloor N d ≤ halfCandidate N d w := by
  have h := closedFloor_le_floorCandidate (N := 2 * N) (by omega) (2 * d) w
  dsimp [closedFloor, floorCandidate] at h
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have heq : (2 * d - 2 * π * (w : ℝ)) / ((2 * N : ℕ) : ℝ) =
      (d - π * (w : ℝ)) / (N : ℝ) := by
    push_cast
    field_simp
    <;> ring
  rw [heq] at h
  dsimp [closedBothFloor, halfCandidate]
  push_cast at h
  nlinarith

lemma halfCandidate_attained {N : ℕ} (hN : 0 < N) (d : ℝ) :
    ∃ w : ℤ, halfCandidate N d w = closedBothFloor N d := by
  obtain ⟨w, hw⟩ := floorCandidate_attained (2 * N) (2 * d)
  refine ⟨w, ?_⟩
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have heq : (2 * d - 2 * π * (w : ℝ)) / ((2 * N : ℕ) : ℝ) =
      (d - π * (w : ℝ)) / (N : ℝ) := by
    push_cast
    field_simp
    <;> ring
  dsimp [floorCandidate, closedFloor] at hw
  rw [heq] at hw
  dsimp [halfCandidate, closedBothFloor]
  push_cast at hw
  nlinarith

theorem halfLattice_minimum {N : ℕ} (hN : 0 < N) (d : ℝ) :
    IsLeast (Set.range (halfCandidate N d)) (closedBothFloor N d) := by
  constructor
  · obtain ⟨w, hw⟩ := halfCandidate_attained hN d
    exact ⟨w, hw⟩
  · rintro _ ⟨w, rfl⟩
    exact closedBothFloor_le_halfCandidate hN d w

/-- On an odd ring the two books together parametrise precisely the `π`-lattice.
The even windings belong to the lower book and the odd ones to the opposite. -/
theorem bothAttainable_eq_halfLattice {N : ℕ} (hN : Odd N) (d : ℝ) :
    bothAttainable N d = Set.range (halfCandidate N d) := by
  obtain ⟨m, hm⟩ := hN
  have hcast : (N : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  ext e
  constructor
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · refine ⟨2 * w, ?_⟩
      dsimp [floorCandidate, halfCandidate]
      push_cast
      congr 2
      ring
    · refine ⟨2 * w - (N : ℤ), ?_⟩
      dsimp [oppositeCandidate, floorCandidate, halfCandidate]
      push_cast
      rw [hcast]
      congr 2
      ring
  · rintro ⟨w, rfl⟩
    rcases Int.even_or_odd w with ⟨r, hr⟩ | ⟨r, hr⟩
    · left
      refine ⟨r, ?_⟩
      dsimp [floorCandidate, halfCandidate]
      rw [hr]
      push_cast
      congr 2
      ring
    · right
      refine ⟨r + m + 1, ?_⟩
      dsimp [oppositeCandidate, floorCandidate, halfCandidate]
      rw [hr]
      push_cast
      rw [hcast]
      congr 2
      ring

/-- **B193, both books on odd rings.**  Their common minimisation is the exact
`π`-lattice minimum. -/
theorem oddRing_twoBooks_minimum {N : ℕ} (hN0 : 0 < N) (hN : Odd N) (d : ℝ) :
    IsLeast (bothAttainable N d) (closedBothFloor N d) := by
  rw [bothAttainable_eq_halfLattice hN d]
  exact halfLattice_minimum hN0 d


/-- On an even ring the twist `Nπ` is an integer multiple of `2π`, so the
second book has exactly the same candidates as the first. -/
theorem bothAttainable_eq_oneBook {N : ℕ} (hN : Even N) (d : ℝ) :
    bothAttainable N d = Set.range (floorCandidate N d) := by
  obtain ⟨m, hm⟩ := hN
  have hcast : (N : ℝ) = (m : ℝ) + (m : ℝ) := by exact_mod_cast hm
  ext e
  constructor
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact ⟨w, rfl⟩
    · refine ⟨w - (m : ℤ), ?_⟩
      dsimp [oppositeCandidate, floorCandidate]
      push_cast
      rw [hcast]
      congr 2
      ring
  · rintro ⟨w, rfl⟩
    exact Or.inl ⟨w, rfl⟩

/-- Cosine form of the winding-floor comparison. -/
lemma cos_floorCandidate_le {N : ℕ} (hN : 0 < N) (d : ℝ) (w : ℤ) :
    Real.cos ((d - 2 * π * (w : ℝ)) / (N : ℝ)) ≤
      Real.cos (residue d / (N : ℝ)) := by
  have h := closedFloor_le_floorCandidate hN d w
  dsimp [closedFloor, floorCandidate] at h
  have hfactor : (0 : ℝ) < 4 * (N : ℝ) := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  nlinarith [h, hfactor]

/-- The Born-total candidate attached to a Fourier winding. -/
def bornCandidate (N : ℕ) (d : ℝ) (w : ℤ) : ℝ :=
  (N : ℝ) / 2 * (1 + Real.cos ((d - 2 * π * (w : ℝ)) / (N : ℝ)))

/-- The maximum Born total, with `residue d` playing the role of the card's
canonical `δ`. -/
def closedBorn (N : ℕ) (d : ℝ) : ℝ :=
  (N : ℝ) / 2 * (1 + Real.cos (residue d / (N : ℝ)))

/-- **B193, Born companion.**  The same integer-winding argument proves the
maximum `(N/2)(1+cos(δ/N))`, with attainment. -/
theorem born_maximum {N : ℕ} (hN : 0 < N) (d : ℝ) :
    IsGreatest (Set.range (bornCandidate N d)) (closedBorn N d) := by
  constructor
  · obtain ⟨z, hz⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.coe_toReal (d : Real.Angle))
    refine ⟨-z, ?_⟩
    have hw : d - 2 * π * ((-z : ℤ) : ℝ) = residue d := by
      push_cast
      change d - 2 * π * (-(z : ℝ)) = (d : Real.Angle).toReal
      nlinarith
    simp only [bornCandidate, closedBorn, hw]
  · rintro _ ⟨w, rfl⟩
    have hc := cos_floorCandidate_le hN d w
    have hfactor : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
    have hc' : 1 + Real.cos ((d - 2 * π * (w : ℝ)) / (N : ℝ)) ≤
        1 + Real.cos (residue d / (N : ℝ)) := by linarith
    exact mul_le_mul_of_nonneg_left hc' hfactor

/-- The advertised one-book worst value. -/
def oneWorst (N : ℕ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos (π / (N : ℝ)))

/-- The advertised worst value after optimising between the two books. -/
def bothWorst (N : ℕ) : ℝ :=
  4 * (N : ℝ) * (1 - Real.cos (π / (2 * (N : ℝ))))

lemma cos_pi_div_le_cos_residue_div {N : ℕ} (hN : 0 < N) (d : ℝ) :
    Real.cos (π / (N : ℝ)) ≤ Real.cos (residue d / (N : ℝ)) := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpi : 0 ≤ π / (N : ℝ) := by positivity
  rw [← Real.cos_abs (π / (N : ℝ)), ← Real.cos_abs (residue d / (N : ℝ)),
    abs_of_nonneg hpi]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
  · apply (div_le_iff₀ hn).2
    nlinarith [Real.pi_pos]
  · rw [abs_div, abs_of_nonneg hn.le]
    exact div_le_div_of_nonneg_right (abs_residue_le_pi d) hn.le

lemma closedFloor_le_oneWorst {N : ℕ} (hN : 0 < N) (d : ℝ) :
    closedFloor N d ≤ oneWorst N := by
  have hfactor : (0 : ℝ) ≤ 4 * (N : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (cos_pi_div_le_cos_residue_div hN d) 1) hfactor

lemma closedBothFloor_le_bothWorst {N : ℕ} (hN : 0 < N) (d : ℝ) :
    closedBothFloor N d ≤ bothWorst N := by
  have hcos := cos_pi_div_le_cos_residue_div (N := 2 * N) (by omega) (2 * d)
  push_cast at hcos
  have hfactor : (0 : ℝ) ≤ 4 * (N : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcos 1) hfactor

lemma closedFloor_pi (N : ℕ) : closedFloor N π = oneWorst N := by
  simp [closedFloor, oneWorst, residue]

lemma closedBothFloor_halfPi (N : ℕ) : closedBothFloor N (π / 2) = bothWorst N := by
  have h : 2 * (π / 2) = π := by ring
  simp [closedBothFloor, bothWorst, residue, h]

/-- The set of all exact one-book minima as the total twist varies. -/
def minimizedOneFloors (N : ℕ) : Set ℝ :=
  {e | ∃ d : ℝ, IsLeast (Set.range (floorCandidate N d)) e}

/-- The set of all exact minima after choosing either book. -/
def minimizedBothFloors (N : ℕ) : Set ℝ :=
  {e | ∃ d : ℝ, IsLeast (bothAttainable N d) e}

/-- **B193, one-book worst case.**  The maximum over twist of the exact integer
minimum is `4N(1-cos(π/N))`, attained at total twist `π`. -/
theorem oneBook_worst {N : ℕ} (hN : 0 < N) :
    IsGreatest (minimizedOneFloors N) (oneWorst N) := by
  constructor
  · refine ⟨π, ?_⟩
    rw [← closedFloor_pi N]
    exact oneBook_minimum hN π
  · rintro e ⟨d, hd⟩
    have he := hd.unique (oneBook_minimum hN d)
    rw [he]
    exact closedFloor_le_oneWorst hN d

/-- **B193, odd-ring two-book worst case.**  The exact displayed improvement
from `π/N` to `π/(2N)` is attained at total twist `π/2`. -/
theorem oddRing_twoBooks_worst {N : ℕ} (hN0 : 0 < N) (hN : Odd N) :
    IsGreatest (minimizedBothFloors N) (bothWorst N) := by
  constructor
  · refine ⟨π / 2, ?_⟩
    rw [← closedBothFloor_halfPi N]
    exact oddRing_twoBooks_minimum hN0 hN (π / 2)
  · rintro e ⟨d, hd⟩
    have he := hd.unique (oddRing_twoBooks_minimum hN0 hN d)
    rw [he]
    exact closedBothFloor_le_bothWorst hN0 d

/-- On even rings using both books does not change the floor or its worst case. -/
theorem evenRing_twoBooks_worst {N : ℕ} (hN0 : 0 < N) (hN : Even N) :
    IsGreatest (minimizedBothFloors N) (oneWorst N) := by
  have hmin : minimizedBothFloors N = minimizedOneFloors N := by
    ext e
    simp only [minimizedBothFloors, minimizedOneFloors, Set.mem_setOf_eq,
      bothAttainable_eq_oneBook hN]
  rw [hmin]
  exact oneBook_worst hN0

/-- Degenerate loop `N = 1`: the combined worst value is `4`. -/
theorem bothWorst_one : bothWorst 1 = 4 := by
  norm_num [bothWorst, Real.cos_pi_div_two]

/-- Even boundary `N = 2`: the unchanged one-book worst value is `8`. -/
theorem oneWorst_two : oneWorst 2 = 8 := by
  norm_num [oneWorst, Real.cos_pi_div_two]

/-- The card's exact `N = 3` one-book worst value. -/
theorem oneWorst_three : oneWorst 3 = 6 := by
  norm_num [oneWorst, Real.cos_pi_div_three]

/-- The card's exact `N = 5` one-book worst value `15 - 5√5`. -/
theorem oneWorst_five : oneWorst 5 = 15 - 5 * Real.sqrt 5 := by
  norm_num [oneWorst, Real.cos_pi_div_five]
  <;> ring

/-- The card's exact even-ring `N = 4` worst value. -/
theorem oneWorst_four : oneWorst 4 = 16 - 8 * Real.sqrt 2 := by
  norm_num [oneWorst]
  ring

/-- The card's exact `N = 3` two-book improvement, `12 - 6√3`. -/
theorem bothWorst_three : bothWorst 3 = 12 - 6 * Real.sqrt 3 := by
  norm_num [bothWorst]
  ring

#print axioms neg_pi_lt_residue
#print axioms residue_le_pi
#print axioms abs_residue_le_pi
#print axioms cos_root_le
#print axioms closedFloor_le_floorCandidate
#print axioms floorCandidate_attained
#print axioms oneBook_minimum
#print axioms closedBothFloor_le_halfCandidate
#print axioms halfCandidate_attained
#print axioms halfLattice_minimum
#print axioms bothAttainable_eq_halfLattice
#print axioms oddRing_twoBooks_minimum
#print axioms bothAttainable_eq_oneBook
#print axioms cos_floorCandidate_le
#print axioms born_maximum
#print axioms cos_pi_div_le_cos_residue_div
#print axioms closedFloor_le_oneWorst
#print axioms closedBothFloor_le_bothWorst
#print axioms closedFloor_pi
#print axioms closedBothFloor_halfPi
#print axioms oneBook_worst
#print axioms oddRing_twoBooks_worst
#print axioms evenRing_twoBooks_worst
#print axioms bothWorst_one
#print axioms oneWorst_two
#print axioms oneWorst_three
#print axioms oneWorst_five
#print axioms oneWorst_four
#print axioms bothWorst_three

end RelationalAtlas.B193


/-! ## B196 — minimality is |c| >= 2, so the card is closed at the boundary

Integrated from `.ultramath/smwvp3cvb/m2/B196.lean`.
-/

/-!
# B196: the prime-trace recurrence and its constant continued fraction

The finite convergents are indexed so that `cf c 0 = c` and `cf c (n+1)`
has one further denominator.  Thus `cf 2 n = (n+2)/(n+1)`, and the error
after `n+1` entries is `1/(n+1)`.

No precarious analytical facts are used for non-convergence: multiplication
of two consecutive convergents gives a polynomial equation for any possible
real limit.
-/

namespace RelationalAtlas.B196

open Filter Matrix
open scoped Topology Matrix

/-- The traceless part of the recurrence companion matrix. -/
noncomputable def companionTraceless (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c / 2, -1; 1, -c / 2]

/-- The algebraic reason for the three regimes in B196. -/
theorem companionTraceless_sq (c : ℝ) :
    companionTraceless c * companionTraceless c =
      (c ^ 2 / 4 - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionTraceless, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- At either coalescence the traceless companion is nonzero and nilpotent. -/
theorem companionTraceless_nilpotent_of_sq_eq_four {c : ℝ} (hc : c ^ 2 = 4) :
    companionTraceless c ≠ 0 ∧ companionTraceless c * companionTraceless c = 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [companionTraceless] at he
  · rw [companionTraceless_sq, hc]
    norm_num

/-- The three-term recurrence on the card. -/
def RecSolves (c : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ n, t (n + 2) = c * t (n + 1) - t n

/-- Nonvanishing of this initial Casoratian makes two solutions independent. -/
def Casoratian (f d : ℕ → ℝ) : ℝ :=
  f 1 * d 0 - f 0 * d 1

/-- The usual ratio definition of a minimal solution, with independence and
nonzero denominators made explicit. -/
def MinimalPair (c : ℝ) (f d : ℕ → ℝ) : Prop :=
  RecSolves c f ∧ RecSolves c d ∧ Casoratian f d ≠ 0 ∧
    (∀ n, d n ≠ 0) ∧ Tendsto (fun n => f n / d n) atTop (𝓝 0)

/-- There is a minimal solution of the recurrence with parameter `c`. -/
def HasMinimal (c : ℝ) : Prop :=
  ∃ f d : ℕ → ℝ, MinimalPair c f d

/-- The finite truncations of `c - 1/(c - 1/(c - ...))`. -/
noncomputable def cf (c : ℝ) : ℕ → ℝ
  | 0 => c
  | n + 1 => c - 1 / cf c n

lemma cf_zero (c : ℝ) : cf c 0 = c := rfl

@[simp] lemma cf_step (c : ℝ) (n : ℕ) :
    cf c (n + 1) = c - 1 / cf c n := rfl

/-- Multiplying consecutive convergents eliminates the reciprocal. -/
lemma cf_mul_self {c : ℝ} (hnz : ∀ n, cf c n ≠ 0) (n : ℕ) :
    cf c (n + 1) * cf c n = c * cf c n - 1 := by
  rw [cf_step]
  field_simp [hnz n]

/-- If all convergents are genuine (no zero division), there is no real limit
in the oscillatory regime `|c| < 2`. -/
theorem cf_not_tendsto_of_abs_lt_two {c L : ℝ}
    (hc : |c| < 2) (hnz : ∀ n, cf c n ≠ 0) :
    ¬ Tendsto (cf c) atTop (𝓝 L) := by
  intro h
  have hshift : Tendsto (fun n => cf c (n + 1)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  have hp : Tendsto (fun n => cf c (n + 1) * cf c n) atTop (𝓝 (L * L)) :=
    hshift.mul h
  have hp' : Tendsto (fun n => c * cf c n - 1) atTop (𝓝 (L * L)) :=
    hp.congr (cf_mul_self hnz)
  have hq : Tendsto (fun n => c * cf c n - 1) atTop (𝓝 (c * L - 1)) :=
    (h.const_mul c).sub_const 1
  have hlim : L * L = c * L - 1 := tendsto_nhds_unique hp' hq
  have hc2 : c ^ 2 < (2 : ℝ) ^ 2 :=
    sq_lt_sq.2 (by simpa using hc)
  nlinarith [sq_nonneg (2 * L - c)]

/-- Negating `c` negates every finite convergent, including at zero division. -/
lemma cf_negative (c : ℝ) : ∀ n, cf (-c) n = -cf c n
  | 0 => rfl
  | n + 1 => by
      rw [cf_step, cf_step, cf_negative c n]
      simp only [one_div, inv_neg]
      ring

lemma one_lt_cf_of_two_lt {c : ℝ} (hc : 2 < c) : ∀ n, 1 < cf c n
  | 0 => lt_trans (by norm_num) hc
  | n + 1 => by
      have hx := one_lt_cf_of_two_lt hc n
      have hx0 : 0 < cf c n := lt_trans (by norm_num) hx
      have hi : 1 / cf c n < 1 := (div_lt_iff₀ hx0).2 (by simpa using hx)
      rw [cf_step]
      linarith

lemma cf_ne_zero_of_two_lt {c : ℝ} (hc : 2 < c) (n : ℕ) : cf c n ≠ 0 :=
  ne_of_gt (lt_trans (by norm_num) (one_lt_cf_of_two_lt hc n))

lemma two_lt_param {r : ℝ} (hr : 1 < r) : 2 < r + r⁻¹ := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hs : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.2 hr)
  have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hrne
  apply (mul_lt_mul_iff_left₀ hr0).1
  nlinarith

/-- Exact propagation of the error about the dominant fixed point `r`. -/
lemma cf_error_param {r : ℝ} (hr : 1 < r) (n : ℕ) :
    cf (r + r⁻¹) (n + 1) - r =
      (cf (r + r⁻¹) n - r) / (r * cf (r + r⁻¹) n) := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans (by norm_num) hr)
  have hx0 : cf (r + r⁻¹) n ≠ 0 :=
    cf_ne_zero_of_two_lt (two_lt_param hr) n
  rw [cf_step]
  set x := cf (r + r⁻¹) n
  field_simp [hr0, hx0]
  ring

/-- Explicit geometric error control outside the critical circle. -/
theorem cf_error_bound_param {r : ℝ} (hr : 1 < r) (n : ℕ) :
    |cf (r + r⁻¹) n - r| ≤ (r⁻¹) ^ (n + 1) := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hc : 2 < r + r⁻¹ := two_lt_param hr
  induction n with
  | zero =>
      simp [cf_zero, abs_of_pos (inv_pos.2 hr0)]
  | succ n ih =>
      have hx : 1 < cf (r + r⁻¹) n := one_lt_cf_of_two_lt hc n
      have hx0 : 0 < cf (r + r⁻¹) n := lt_trans (by norm_num) hx
      rw [cf_error_param hr, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hx0]
      calc
        |cf (r + r⁻¹) n - r| / (r * cf (r + r⁻¹) n)
            ≤ (r⁻¹) ^ (n + 1) / r := by
              apply div_le_div₀ (pow_nonneg (inv_nonneg.2 hr0.le) _) ih hr0
              exact le_mul_of_one_le_right hr0.le hx.le
        _ = (r⁻¹) ^ (n + 1 + 1) := by
              simp [div_eq_mul_inv, pow_succ]

/-- All positive-branch convergents lie on the dominant side of `r`. -/
lemma dominant_lt_cf {r : ℝ} (hr : 1 < r) : ∀ n, r < cf (r + r⁻¹) n
  | 0 => by
      have hi : 0 < r⁻¹ := inv_pos.2 (lt_trans (by norm_num) hr)
      simp [cf_zero]
      linarith
  | n + 1 => by
      have hr0 : 0 < r := lt_trans (by norm_num) hr
      have ih := dominant_lt_cf hr n
      have hx0 : 0 < cf (r + r⁻¹) n := lt_trans hr0 ih
      have he := cf_error_param hr n
      have hp : 0 < cf (r + r⁻¹) (n + 1) - r := by
        rw [cf_error_param hr]
        exact div_pos (sub_pos.2 ih) (mul_pos hr0 hx0)
      linarith

/-- The sharper geometric rate is quadratic in the index: the error at the
`n`-th stage is at most `|r⁻¹|^(2n+1)`. -/
theorem cf_error_bound_param_quadratic {r : ℝ} (hr : 1 < r) (n : ℕ) :
    |cf (r + r⁻¹) n - r| ≤ (r⁻¹) ^ (2 * n + 1) := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  induction n with
  | zero => simp [cf_zero, abs_of_pos (inv_pos.2 hr0)]
  | succ n ih =>
      have hx : r < cf (r + r⁻¹) n := dominant_lt_cf hr n
      have hx0 : 0 < cf (r + r⁻¹) n := lt_trans hr0 hx
      rw [cf_error_param hr, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hx0]
      calc
        |cf (r + r⁻¹) n - r| / (r * cf (r + r⁻¹) n)
            ≤ (r⁻¹) ^ (2 * n + 1) / (r * r) := by
              apply div_le_div₀ (pow_nonneg (inv_nonneg.2 hr0.le) _) ih
                (mul_pos hr0 hr0)
              exact mul_le_mul_of_nonneg_left hx.le hr0.le
        _ = (r⁻¹) ^ (2 * (n + 1) + 1) := by
              rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
              simp only [div_eq_mul_inv, _root_.mul_inv_rev]
              ring

/-- Pincherle convergence, with a geometric error, for a dominant root `r > 1`. -/
theorem cf_tendsto_param {r : ℝ} (hr : 1 < r) :
    Tendsto (cf (r + r⁻¹)) atTop (𝓝 r) := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hq : |(r⁻¹)| < 1 := by
    rw [abs_inv, abs_of_pos hr0]
    exact (inv_lt_one₀ hr0).2 hr
  have hg : Tendsto (fun n : ℕ => (r⁻¹) ^ (n + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).comp (tendsto_add_atTop_nat 1)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
  simpa [Real.norm_eq_abs] using cf_error_bound_param hr n

/-- The negative branch of the dominant root follows by exact sign symmetry. -/
theorem cf_tendsto_negative_param {r : ℝ} (hr : 1 < r) :
    Tendsto (cf (-(r + r⁻¹))) atTop (𝓝 (-r)) := by
  have heq : cf (-(r + r⁻¹)) = fun n => -cf (r + r⁻¹) n := by
    funext n
    exact cf_negative _ n
  rw [heq]
  exact (cf_tendsto_param hr).neg

/-- Convergence to the characteristic root which is outside the unit circle,
on either the positive or the negative branch. -/
theorem cf_tendsto_dominant {r : ℝ} (hr : 1 < |r|) :
    Tendsto (cf (r + r⁻¹)) atTop (𝓝 r) := by
  rcases le_total 0 r with hrp | hrn
  · have hrpos : 1 < r := by rwa [abs_of_nonneg hrp] at hr
    exact cf_tendsto_param hrpos
  · have hs : 1 < -r := by rwa [abs_of_nonpos hrn] at hr
    have heq : r + r⁻¹ = -((-r) + (-r)⁻¹) := by
      simp only [inv_neg]
      ring
    rw [heq]
    simpa using cf_tendsto_negative_param hs

/-- At the double root `c = 2`, all finite convergents are rational functions
of their length. -/
theorem cf_two_exact (n : ℕ) :
    cf 2 n = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [cf_zero]
  | succ n ih =>
      rw [cf_step, ih]
      have h0 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The critical error is exactly the reciprocal of the number of entries. -/
theorem cf_two_error (n : ℕ) : cf 2 n - 1 = 1 / ((n : ℝ) + 1) := by
  rw [cf_two_exact]
  have h0 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Algebraic (rather than geometric) convergence at `c = 2`. -/
theorem cf_two_tendsto : Tendsto (cf 2) atTop (𝓝 1) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h' := h.add_const 1
  have heq : cf 2 = fun n : ℕ => 1 / ((n : ℝ) + 1) + 1 := by
    funext n
    linarith [cf_two_error n]
  rw [heq]
  simpa using h'

/-- By sign symmetry the same critical asymptotic holds at `c = -2`. -/
theorem cf_negative_two_tendsto : Tendsto (cf (-2)) atTop (𝓝 (-1)) := by
  have heq : cf (-2) = fun n => -cf 2 n := by
    funext n
    exact cf_negative _ n
  rw [heq]
  have h := cf_two_tendsto.neg
  norm_num at h ⊢
  exact h

lemma pow_recSolves {c a : ℝ} (ha : a ^ 2 = c * a - 1) :
    RecSolves c (fun n => a ^ n) := by
  intro n
  calc
    a ^ (n + 2) = a ^ 2 * a ^ n := by ring
    _ = (c * a - 1) * a ^ n := by rw [ha]
    _ = c * a ^ (n + 1) - a ^ n := by ring

lemma inv_characteristic_root {c r : ℝ} (hr : r ≠ 0)
    (ha : r ^ 2 = c * r - 1) : (r⁻¹) ^ 2 = c * r⁻¹ - 1 := by
  field_simp [hr]
  nlinarith

/-- Both roots of the reciprocal quadratic supply independent solutions. -/
theorem hasMinimal_param {r : ℝ} (hr : 1 < |r|) :
    HasMinimal (r + r⁻¹) := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hroot : r ^ 2 = (r + r⁻¹) * r - 1 := by
    field_simp [hr0]
    ring
  have hiroot : (r⁻¹) ^ 2 = (r + r⁻¹) * r⁻¹ - 1 :=
    inv_characteristic_root hr0 hroot
  refine ⟨fun n => (r⁻¹) ^ n, fun n => r ^ n,
    pow_recSolves hiroot, pow_recSolves hroot, ?_, ?_, ?_⟩
  · simp only [Casoratian, pow_zero, pow_one, one_mul, mul_one]
    intro heq
    have hi : r⁻¹ = r := sub_eq_zero.1 heq
    have hmul := congrArg (fun x : ℝ => x * r) hi
    rw [inv_mul_cancel₀ hr0] at hmul
    have hs : |r| ^ 2 = 1 := by rw [sq_abs]; nlinarith
    nlinarith [abs_nonneg r]
  · exact fun n => pow_ne_zero n hr0
  · have hq : |r⁻¹ / r| < 1 := by
      have hp : 0 < |r| := lt_trans (by norm_num) hr
      rw [abs_div, abs_inv]
      apply (div_lt_iff₀ hp).2
      rw [one_mul]
      exact lt_trans ((inv_lt_one₀ hp).2 hr) hr
    simpa only [div_pow] using tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq

/-- The root parametrization used above covers every positive supercritical
real parameter.  The larger root is the dominant characteristic root. -/
lemma exists_dominant_param_of_two_lt {c : ℝ} (hc : 2 < c) :
    ∃ r : ℝ, 1 < r ∧ c = r + r⁻¹ := by
  let s : ℝ := Real.sqrt (c ^ 2 - 4)
  let r : ℝ := (c + s) / 2
  have hs : s ^ 2 = c ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 1 < r := by
    dsimp [r]
    nlinarith
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans (by norm_num) hr)
  have hroot : r ^ 2 = c * r - 1 := by
    dsimp [r]
    nlinarith [hs]
  refine ⟨r, hr, ?_⟩
  field_simp [hr0]
  nlinarith

/-- Every real parameter outside the critical interval has a root `r` with
`|r| > 1`. -/
lemma exists_dominant_param_of_two_lt_abs {c : ℝ} (hc : 2 < |c|) :
    ∃ r : ℝ, 1 < |r| ∧ c = r + r⁻¹ := by
  rcases le_total 0 c with hcp | hcn
  · have hcpos : 2 < c := by rwa [abs_of_nonneg hcp] at hc
    obtain ⟨r, hr, hcr⟩ := exists_dominant_param_of_two_lt hcpos
    exact ⟨r, by rwa [abs_of_pos (lt_trans (by norm_num) hr)], hcr⟩
  · have hcneg : 2 < -c := by rwa [abs_of_nonpos hcn] at hc
    obtain ⟨r, hr, hcr⟩ := exists_dominant_param_of_two_lt hcneg
    refine ⟨-r, ?_, ?_⟩
    · rwa [abs_neg, abs_of_pos (lt_trans (by norm_num) hr)]
    · simp only [inv_neg]
      linarith

/-- For every supercritical real `c`, the continued fraction converges to the
unique characteristic root outside the unit circle. -/
theorem cf_tendsto_of_two_lt_abs {c : ℝ} (hc : 2 < |c|) :
    ∃ r : ℝ, 1 < |r| ∧ c = r + r⁻¹ ∧ Tendsto (cf c) atTop (𝓝 r) := by
  obtain ⟨r, hr, rfl⟩ := exists_dominant_param_of_two_lt_abs hc
  exact ⟨r, hr, rfl, cf_tendsto_dominant hr⟩

/-- The forward half of the displayed minimal-solution criterion is valid. -/
theorem hasMinimal_of_two_lt_abs {c : ℝ} (hc : 2 < |c|) : HasMinimal c := by
  obtain ⟨r, hr, rfl⟩ := exists_dominant_param_of_two_lt_abs hc
  exact hasMinimal_param hr

/-- B196's displayed unqualified `minimal solution iff |c| > 2` is false at
`c = 2`: here are a decaying ratio, independent solutions, and all witnesses. -/
theorem hasMinimal_two : HasMinimal 2 := by
  refine ⟨fun _ => 1, fun n => (n : ℝ) + 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    norm_num [RecSolves]
  · intro n
    push_cast
    ring
  · norm_num [Casoratian]
  · intro n
    positivity
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- An explicit Lean refutation of the literal boundary-free equivalence. -/
theorem not_unqualified_minimal_iff :
    ¬ (∀ c : ℝ, HasMinimal c ↔ 2 < |c|) := by
  intro h
  have hm := (h 2).1 hasMinimal_two
  norm_num at hm

/-- The card's `n = 40` critical witness: our index `39` counts forty entries. -/
theorem card_witness_c_two : cf 2 39 - 1 = 1 / 40 := by
  rw [cf_two_error]
  norm_num

/-- The card's geometric witness for `c = 2.5`, where `r = 2`: forty entries
already have error much smaller than `10⁻¹⁵`. -/
theorem card_witness_c_two_point_five :
    |cf (5 / 2 : ℝ) 39 - 2| < 1 / (10 : ℝ) ^ 15 := by
  have h := cf_error_bound_param_quadratic (r := 2) (by norm_num) 39
  have hc : (2 : ℝ) + (2 : ℝ)⁻¹ = 5 / 2 := by norm_num
  rw [hc] at h
  have hb : ((2 : ℝ)⁻¹) ^ (2 * 39 + 1) < 1 / (10 : ℝ) ^ 15 := by
    norm_num
  exact lt_of_le_of_lt h hb

/-- The published oscillation witness for `c = 1.5`: the jump from thirty-nine
to forty entries has size greater than one, checked by rational arithmetic. -/
theorem card_witness_c_one_point_five :
    1 < |cf (3 / 2 : ℝ) 39 - cf (3 / 2 : ℝ) 38| := by
  norm_num [cf]

/-- A quadratic invariant of the order-two recurrence. -/
def recInvariant (c x y : ℝ) : ℝ := x ^ 2 - c * x * y + y ^ 2

lemma recInvariant_step {c : ℝ} {t : ℕ → ℝ} (ht : RecSolves c t) (n : ℕ) :
    recInvariant c (t (n + 2)) (t (n + 1)) =
      recInvariant c (t (n + 1)) (t n) := by
  rw [ht n]
  unfold recInvariant
  ring

lemma recInvariant_iterate {c : ℝ} {t : ℕ → ℝ} (ht : RecSolves c t) (n : ℕ) :
    recInvariant c (t (n + 1)) (t n) = recInvariant c (t 1) (t 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [recInvariant_step ht n, ih]

lemma recInvariant_comm (c x y : ℝ) :
    recInvariant c x y = recInvariant c y x := by
  unfold recInvariant
  ring

lemma first_sq_le_recInvariant (c x y : ℝ) :
    (1 - c ^ 2 / 4) * x ^ 2 ≤ recInvariant c x y := by
  unfold recInvariant
  nlinarith [sq_nonneg (y - c * x / 2)]

lemma second_sq_le_recInvariant (c x y : ℝ) :
    (1 - c ^ 2 / 4) * y ^ 2 ≤ recInvariant c x y := by
  unfold recInvariant
  nlinarith [sq_nonneg (x - c * y / 2)]

lemma solution_sq_le {c : ℝ} (hc : |c| < 2) {t : ℕ → ℝ}
    (ht : RecSolves c t) (n : ℕ) :
    t n ^ 2 ≤ recInvariant c (t 1) (t 0) / (1 - c ^ 2 / 4) := by
  have hc2 : c ^ 2 < (2 : ℝ) ^ 2 := sq_lt_sq.2 (by simpa using hc)
  have hd : 0 < 1 - c ^ 2 / 4 := by nlinarith
  cases n with
  | zero =>
      apply (le_div_iff₀ hd).2
      have h := second_sq_le_recInvariant c (t 1) (t 0)
      nlinarith
  | succ n =>
      apply (le_div_iff₀ hd).2
      have h := first_sq_le_recInvariant c (t (n + 1)) (t n)
      rw [recInvariant_iterate ht n] at h
      nlinarith

lemma abs_mul_le_of_sq_le {a b K : ℝ} (ha : a ^ 2 ≤ K) (hb : b ^ 2 ≤ K) :
    |a * b| ≤ K := by
  have hK : 0 ≤ K := le_trans (sq_nonneg a) ha
  have hs : |a| ^ 2 = a ^ 2 := sq_abs a
  have ht : |b| ^ 2 = b ^ 2 := sq_abs b
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]

/-- The Casoratian at an arbitrary consecutive pair. -/
def CasoratianAt (f d : ℕ → ℝ) (n : ℕ) : ℝ :=
  f (n + 1) * d n - f n * d (n + 1)

lemma casoratianAt_step {c : ℝ} {f d : ℕ → ℝ}
    (hf : RecSolves c f) (hd : RecSolves c d) (n : ℕ) :
    CasoratianAt f d (n + 1) = CasoratianAt f d n := by
  unfold CasoratianAt
  rw [show n + 1 + 1 = n + 2 by omega, hf n, hd n]
  ring

lemma casoratianAt_eq {c : ℝ} {f d : ℕ → ℝ}
    (hf : RecSolves c f) (hd : RecSolves c d) (n : ℕ) :
    CasoratianAt f d n = Casoratian f d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [casoratianAt_step hf hd n, ih]

lemma casoratianAt_div {f d : ℕ → ℝ} (hd : ∀ n, d n ≠ 0) (n : ℕ) :
    CasoratianAt f d n / (d (n + 1) * d n) =
      f (n + 1) / d (n + 1) - f n / d n := by
  unfold CasoratianAt
  field_simp [hd n, hd (n + 1)]

/-- No nonzero-ratio minimal solution occurs in the oscillatory regime.  The
proof uses only the invariant and constancy of the Casoratian. -/
theorem not_hasMinimal_of_abs_lt_two {c : ℝ} (hc : |c| < 2) :
    ¬ HasMinimal c := by
  rintro ⟨f, d, hf, hd, hcas, hdnz, hratio⟩
  let K : ℝ := recInvariant c (d 1) (d 0) / (1 - c ^ 2 / 4)
  have hdsq : ∀ n, d n ^ 2 ≤ K := solution_sq_le hc hd
  have hK : 0 < K := by
    have h0 := hdsq 0
    have hp : 0 < d 0 ^ 2 := sq_pos_of_ne_zero (hdnz 0)
    exact lt_of_lt_of_le hp h0
  have hden : ∀ n, |d (n + 1) * d n| ≤ K := by
    intro n
    exact abs_mul_le_of_sq_le (hdsq (n + 1)) (hdsq n)
  have hshift : Tendsto (fun n => f (n + 1) / d (n + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hratio
  have hdif : Tendsto (fun n => f (n + 1) / d (n + 1) - f n / d n)
      atTop (𝓝 0) := by
    simpa using hshift.sub hratio
  have hquot : Tendsto (fun n => Casoratian f d / (d (n + 1) * d n))
      atTop (𝓝 0) := by
    apply hdif.congr
    intro n
    rw [← casoratianAt_div hdnz n, casoratianAt_eq hf hd n]
  have heps : 0 < |Casoratian f d| / (2 * K) :=
    div_pos (abs_pos.2 hcas) (mul_pos (by norm_num) hK)
  have hev := (Metric.tendsto_atTop.1 hquot) _ heps
  simp only [Real.dist_eq, sub_zero] at hev
  obtain ⟨n, hn⟩ := hev
  have hn := hn n le_rfl
  have hdenpos : 0 < |d (n + 1) * d n| :=
    abs_pos.2 (mul_ne_zero (hdnz (n + 1)) (hdnz n))
  have hlower : |Casoratian f d| / K ≤
      |Casoratian f d / (d (n + 1) * d n)| := by
    rw [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hdenpos (hden n)
  have hhalf : |Casoratian f d| / (2 * K) = (|Casoratian f d| / K) / 2 := by
    field_simp
  rw [hhalf] at hn
  have hA : 0 < |Casoratian f d| / K := div_pos (abs_pos.2 hcas) hK
  nlinarith

/-- The remaining negative double-root case. -/
theorem hasMinimal_negative_two : HasMinimal (-2) := by
  refine ⟨fun n => (-1 : ℝ) ^ n, fun n => ((n : ℝ) + 1) * (-1 : ℝ) ^ n,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [pow_add, pow_one, pow_two]
    ring
  · intro n
    simp only [pow_add, pow_one, pow_two]
    push_cast
    ring
  · norm_num [Casoratian]
  · intro n
    exact mul_ne_zero (by positivity) (pow_ne_zero n (by norm_num))
  · have heq : (fun n : ℕ => ((-1 : ℝ) ^ n) / (((n : ℝ) + 1) * (-1 : ℝ) ^ n)) =
        fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      funext n
      have hp : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hp]
    change Tendsto (fun n : ℕ =>
      ((-1 : ℝ) ^ n) / (((n : ℝ) + 1) * (-1 : ℝ) ^ n)) atTop (𝓝 0)
    rw [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The exact repair of B196's boundary-free statement: under the standard
ratio definition, minimality holds precisely on and outside the critical set. -/
theorem hasMinimal_iff_two_le_abs {c : ℝ} : HasMinimal c ↔ 2 ≤ |c| := by
  constructor
  · intro h
    apply le_of_not_gt
    intro hc
    exact not_hasMinimal_of_abs_lt_two (by simpa using hc) h
  · intro hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · exact hasMinimal_of_two_lt_abs hlt
    · rcases le_total 0 c with hcp | hcn
      · have hceq : c = 2 := by
          rw [abs_of_nonneg hcp] at heq
          linarith
        rw [hceq]
        exact hasMinimal_two
      · have hceq : c = -2 := by
          rw [abs_of_nonpos hcn] at heq
          linarith
        rw [hceq]
        exact hasMinimal_negative_two

/-- B196 in its original spectral scaling.  The equality cases are included. -/
theorem hasMinimal_scaled_iff {q lambda : ℝ} (hq : 0 < q) :
    HasMinimal (lambda / Real.sqrt q) ↔ 2 * Real.sqrt q ≤ |lambda| := by
  rw [hasMinimal_iff_two_le_abs, abs_div, abs_of_pos (Real.sqrt_pos.2 hq),
    le_div_iff₀ (Real.sqrt_pos.2 hq)]

/- Axiom audit: every proved declaration in this file. -/
#print axioms companionTraceless_sq
#print axioms companionTraceless_nilpotent_of_sq_eq_four
#print axioms cf_zero
#print axioms cf_step
#print axioms cf_mul_self
#print axioms cf_not_tendsto_of_abs_lt_two
#print axioms cf_negative
#print axioms one_lt_cf_of_two_lt
#print axioms cf_ne_zero_of_two_lt
#print axioms two_lt_param
#print axioms cf_error_param
#print axioms cf_error_bound_param
#print axioms dominant_lt_cf
#print axioms cf_error_bound_param_quadratic
#print axioms cf_tendsto_param
#print axioms cf_tendsto_negative_param
#print axioms cf_tendsto_dominant
#print axioms cf_two_exact
#print axioms cf_two_error
#print axioms cf_two_tendsto
#print axioms cf_negative_two_tendsto
#print axioms pow_recSolves
#print axioms inv_characteristic_root
#print axioms hasMinimal_param
#print axioms exists_dominant_param_of_two_lt
#print axioms exists_dominant_param_of_two_lt_abs
#print axioms cf_tendsto_of_two_lt_abs
#print axioms hasMinimal_of_two_lt_abs
#print axioms hasMinimal_two
#print axioms not_unqualified_minimal_iff
#print axioms card_witness_c_two
#print axioms card_witness_c_two_point_five
#print axioms card_witness_c_one_point_five
#print axioms recInvariant_step
#print axioms recInvariant_iterate
#print axioms recInvariant_comm
#print axioms first_sq_le_recInvariant
#print axioms second_sq_le_recInvariant
#print axioms solution_sq_le
#print axioms abs_mul_le_of_sq_le
#print axioms casoratianAt_step
#print axioms casoratianAt_eq
#print axioms casoratianAt_div
#print axioms not_hasMinimal_of_abs_lt_two
#print axioms hasMinimal_negative_two
#print axioms hasMinimal_iff_two_le_abs
#print axioms hasMinimal_scaled_iff

end RelationalAtlas.B196


/-! ## B196 — the boundary witness, graph-realised

Integrated from `.ultramath/smwvp3cvb/m14/B196Boundary.lean`.
-/

/-!
# B196: the repeated-root boundary really has a minimal solution

The published card displays `minimal solution ↔ |λ| > 2√q`.  We use the
standard ratio meaning of a minimal solution of a scalar three-term
recurrence: a nowhere-zero solution `t` is minimal when `t n / s n → 0`
for every solution `s` which is not a scalar multiple of `t`.

At `c = 2r`, with `r² = 1`, the general solution is
`s n = r^n * (a + b*n)`.  The solution `t n = r^n` is minimal, also at
`|c| = 2`.  In particular `q = 1`, `λ = -2` gives `c = -2` and refutes the
unqualified displayed equivalence.  (The negative adjacency eigenvalue `-2`
of an even cycle makes that scalar boundary case non-principal.)
-/

noncomputable section

namespace B196Boundary

open Filter
open scoped Topology

/-- The card's ascending three-term recurrence, shifted to natural indices. -/
def Recurrence (c : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ n, t (n + 2) = c * t (n + 1) - t n

/-- `s` is a scalar multiple of `t`, as sequences. -/
def Proportional (s t : ℕ → ℝ) : Prop :=
  ∃ a : ℝ, ∀ n, s n = a * t n

/-- Standard ratio-minimality for a nonzero solution of the recurrence. -/
def IsMinimalSolution (c : ℝ) (t : ℕ → ℝ) : Prop :=
  Recurrence c t ∧ (∀ n, t n ≠ 0) ∧
    ∀ s : ℕ → ℝ, Recurrence c s → ¬ Proportional s t →
      Tendsto (fun n => t n / s n) atTop (𝓝 0)

/-- The fundamental repeated-root solution. -/
def fundamental (r : ℝ) : ℕ → ℝ := fun n => r ^ n

/-- Every boundary solution has this affine-coefficient form. -/
def boundarySolution (r a b : ℝ) : ℕ → ℝ :=
  fun n => r ^ n * (a + b * (n : ℝ))

lemma fundamental_recurrence {r : ℝ} (hr : r ^ 2 = 1) :
    Recurrence (2 * r) (fundamental r) := by
  intro n
  simp only [fundamental]
  have hsucc : r ^ (n + 1) = r ^ n * r := by rw [pow_succ]
  have hnext : r ^ (n + 2) = r ^ n := by rw [pow_add, hr, mul_one]
  rw [hnext, hsucc]
  ring_nf
  rw [hr]
  ring

lemma fundamental_ne_zero {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    fundamental r n ≠ 0 := by
  exact pow_ne_zero n hr

lemma boundarySolution_recurrence {r a b : ℝ} (hr : r ^ 2 = 1) :
    Recurrence (2 * r) (boundarySolution r a b) := by
  intro n
  simp only [boundarySolution]
  have hsucc : r ^ (n + 1) = r ^ n * r := by rw [pow_succ]
  have hnext : r ^ (n + 2) = r ^ n := by rw [pow_add, hr, mul_one]
  rw [hnext, hsucc]
  push_cast
  ring_nf
  rw [hr]
  ring

/-- Closed-form classification at the double root. -/
lemma recurrence_eq_boundarySolution {r : ℝ} (hr : r ^ 2 = 1)
    {s : ℕ → ℝ} (hs : Recurrence (2 * r) s) (n : ℕ) :
    s n = boundarySolution r (s 0) (r * s 1 - s 0) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [boundarySolution]
  | one =>
      simp only [boundarySolution, pow_one, Nat.cast_one, mul_one]
      rw [show r * (s 0 + (r * s 1 - s 0)) = r * r * s 1 by ring]
      rw [← pow_two, hr, one_mul]
  | more n ih0 ih1 =>
      rw [hs n, ih1, ih0]
      simp only [boundarySolution]
      have hsucc : r ^ (n + 1) = r ^ n * r := by rw [pow_succ]
      have hnext : r ^ (n + 2) = r ^ n := by rw [pow_add, hr, mul_one]
      rw [hnext, hsucc]
      have hr3 : r ^ 3 = r := by
        calc
          r ^ 3 = r ^ 2 * r := by ring
          _ = r := by rw [hr, one_mul]
      push_cast
      ring_nf
      rw [hr, hr3]
      ring

lemma nonproportional_slope_ne_zero {r : ℝ} (hr : r ^ 2 = 1)
    {s : ℕ → ℝ} (hs : Recurrence (2 * r) s)
    (hind : ¬ Proportional s (fundamental r)) :
    r * s 1 - s 0 ≠ 0 := by
  intro hb
  apply hind
  refine ⟨s 0, fun n => ?_⟩
  rw [recurrence_eq_boundarySolution hr hs n]
  simp [boundarySolution, fundamental, hb, mul_comm]

lemma ratio_boundarySolution {r a b : ℝ} (hr : r ≠ 0) (n : ℕ) :
    fundamental r n / boundarySolution r a b n = 1 / (a + b * (n : ℝ)) := by
  by_cases hzero : a + b * (n : ℝ) = 0
  · simp [boundarySolution, hzero]
  · simp only [fundamental, boundarySolution]
    field_simp [pow_ne_zero n hr, hzero]

lemma ratio_tendsto_zero {r a b : ℝ} (hr : r ≠ 0) (hb : b ≠ 0) :
    Tendsto (fun n => fundamental r n / boundarySolution r a b n)
      atTop (𝓝 0) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) a (0 : ℝ) hb
  have h' : Tendsto (fun n : ℕ => (1 : ℝ) / (a + b * (n : ℝ)))
      atTop (𝓝 0) := by
    convert h using 1 <;> simp
  apply h'.congr'
  filter_upwards [] with n
  exact (ratio_boundarySolution hr n).symm

/-- **The boundary solution is minimal in the standard ratio sense.** -/
theorem fundamental_isMinimalSolution {r : ℝ} (hr : r ^ 2 = 1) :
    IsMinimalSolution (2 * r) (fundamental r) := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  refine ⟨fundamental_recurrence hr, fundamental_ne_zero hr0, ?_⟩
  intro s hs hind
  have hb := nonproportional_slope_ne_zero hr hs hind
  have heq : (fun n => fundamental r n / s n) =
      (fun n => fundamental r n /
        boundarySolution r (s 0) (r * s 1 - s 0) n) := by
    funext n
    rw [recurrence_eq_boundarySolution hr hs n]
  rw [heq]
  exact ratio_tendsto_zero hr0 hb

/-- The positive boundary `c = 2` is already a counterexample to the
unqualified minimal-solution equivalence. -/
theorem minimal_at_c_eq_two : IsMinimalSolution (2 : ℝ) (fun _ => 1) := by
  have h := fundamental_isMinimalSolution (r := (1 : ℝ)) (by norm_num)
  have hf : fundamental (1 : ℝ) = (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    simp [fundamental]
  rw [hf] at h
  simpa only [mul_one] using h

/-- The negative boundary `c = -2`, with witnesses `t n = (-1)^n` and the
independent comparison solution `s n = (-1)^n*n`. -/
theorem minimal_at_c_eq_neg_two :
    IsMinimalSolution (-2 : ℝ) (fun n : ℕ => (-1 : ℝ) ^ n) := by
  have h := fundamental_isMinimalSolution (r := (-1 : ℝ)) (by norm_num)
  norm_num only [mul_neg, mul_one] at h
  exact h

/-- The four-cycle, as an explicit symmetric `2`-regular adjacency matrix. -/
def cycle4Adjacency : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

/-- The alternating, nonconstant adjacency mode of the four-cycle. -/
def cycle4Alternating : Fin 4 → ℝ := ![1, -1, 1, -1]

lemma cycle4_regular (i : Fin 4) :
    ∑ j, cycle4Adjacency i j = 2 := by
  fin_cases i <;> norm_num [cycle4Adjacency, Fin.sum_univ_four]

lemma cycle4_alternating_eigenvector :
    cycle4Adjacency.mulVec cycle4Alternating = (-2 : ℝ) • cycle4Alternating := by
  funext i
  fin_cases i <;>
    norm_num [cycle4Adjacency, cycle4Alternating, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

lemma cycle4_alternating_nonconstant :
    cycle4Alternating 0 ≠ cycle4Alternating 1 := by
  norm_num [cycle4Alternating]

/-- The displayed forward implication `minimal ⇒ |λ| > 2√q` is false:
`q = 1`, `λ = -2` has equality at the boundary but a minimal solution. -/
theorem literal_minimal_iff_counterexample :
    ∃ q lambda c : ℝ, q = 1 ∧ lambda = -2 ∧ c = lambda / Real.sqrt q ∧
      IsMinimalSolution c (fun n : ℕ => (-1 : ℝ) ^ n) ∧
      ¬ |lambda| > 2 * Real.sqrt q := by
  refine ⟨1, -2, -2, rfl, rfl, ?_, minimal_at_c_eq_neg_two, ?_⟩
  · norm_num
  · norm_num


/-- A graph-realised counterexample: the alternating mode of `C₄` has
`q = 1`, `λ = -2`, `c = -2`, hence it is on (not outside) the Ramanujan
boundary, while its recurrence has a minimal solution.  Nonconstancy of the
eigenvector records that this is not the principal constant mode. -/
theorem graph_realised_literal_counterexample :
    ∃ (A : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ)
      (q lambda c : ℝ),
      (∀ i, ∑ j, A i j = q + 1) ∧
      A.mulVec v = lambda • v ∧ v 0 ≠ v 1 ∧
      q = 1 ∧ lambda = -2 ∧ c = lambda / Real.sqrt q ∧
      IsMinimalSolution c (fun n : ℕ => (-1 : ℝ) ^ n) ∧
      ¬ |lambda| > 2 * Real.sqrt q := by
  refine ⟨cycle4Adjacency, cycle4Alternating, 1, -2, -2,
    ?_, cycle4_alternating_eigenvector, cycle4_alternating_nonconstant,
    rfl, rfl, ?_, minimal_at_c_eq_neg_two, ?_⟩
  · intro i
    simpa only [one_add_one_eq_two] using cycle4_regular i
  · norm_num
  · norm_num

#print axioms cycle4_regular
#print axioms cycle4_alternating_eigenvector
#print axioms cycle4_alternating_nonconstant
#print axioms graph_realised_literal_counterexample

#print axioms Recurrence
#print axioms Proportional
#print axioms IsMinimalSolution
#print axioms fundamental_recurrence
#print axioms fundamental_ne_zero
#print axioms boundarySolution_recurrence
#print axioms recurrence_eq_boundarySolution
#print axioms nonproportional_slope_ne_zero
#print axioms ratio_boundarySolution
#print axioms ratio_tendsto_zero
#print axioms fundamental_isMinimalSolution
#print axioms minimal_at_c_eq_two
#print axioms minimal_at_c_eq_neg_two
#print axioms literal_minimal_iff_counterexample

end B196Boundary


/-! ## B197 — the triangle polynomial as its two primitive-cycle factors

Integrated from `.ultramath/smwvp3cvb/m1/B197.lean`.
-/

/-!
# B197: the cubic invariant of a phased triangular circulant

The algebraic results are proved for two inverse off-diagonal phases `z` and `w`.
The Hermitian phased case is the specialisation `z = exp (φ I)`,
`w = exp (-φ I)`.  No result in this file depends on the earlier atlas files.
-/

open scoped ComplexConjugate Kronecker
open Matrix

namespace RelationalAtlas.B197

/-- The two opposite cyclic phase factors.-/
def cubicData (z w : ℂ) : ℂ := z ^ 3 + w ^ 3

/-- A three-circulant with diagonal `d`, forward coupling `t*z`, and
backward coupling `t*w`. -/
def tri (d t z w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![d, t*z, t*w;
     t*w, d, t*z;
     t*z, t*w, d]

/-- The characteristic cubic displayed on card B197. -/
def charCubic (v d t C : ℂ) : ℂ :=
  (v-d)^3 - 3*t^2*(v-d) - t^3*C

/-- The cycle-zeta factor displayed on card B197. -/
def zetaInverse (C u : ℂ) : ℂ := 1 - C*u^3 + u^6

lemma inverse_phases_cube {z w : ℂ} (h : z*w = 1) : z^3*w^3 = 1 := by
  calc
    z^3*w^3 = (z*w)^3 := by ring
    _ = 1 := by rw [h]; norm_num

/-- The determinant of the phased circulant is the elementary symmetric
polynomial `e₃` of its three eigenvalues. -/
theorem det_tri {z w : ℂ} (h : z*w = 1) (d t : ℂ) :
    (tri d t z w).det = d^3 - 3*d*t^2 + t^3*cubicData z w := by
  simp [tri, cubicData, Matrix.det_fin_three]
  linear_combination (-3*d*t^2) * h

/-- The characteristic polynomial, evaluated at a scalar `v`, has exactly the
card's normal form. -/
theorem det_sub_tri {z w : ℂ} (h : z*w = 1) (v d t : ℂ) :
    (v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - tri d t z w).det =
      charCubic v d t (cubicData z w) := by
  simp [tri, charCubic, cubicData, Matrix.det_fin_three]
  linear_combination (-3*t^2*(v-d)) * h

/-- Quadratic trace record of the triangle. -/
theorem trace_tri_sq {z w : ℂ} (h : z*w = 1) (d t : ℂ) :
    (tri d t z w * tri d t z w).trace = 3*d^2 + 6*t^2 := by
  simp [tri, Matrix.trace_fin_three]
  linear_combination (6*t^2) * h

/-- Cubic trace record; the last term is `3*t^3*C₃`, equivalently
`6*t^3*cos(3φ)` in the Hermitian phase specialisation. -/
theorem trace_tri_cubed {z w : ℂ} (h : z*w = 1) (d t : ℂ) :
    (tri d t z w * tri d t z w * tri d t z w).trace =
      3*d^3 + 18*d*t^2 + 3*t^3*cubicData z w := by
  simp [tri, cubicData, Matrix.trace_fin_three]
  linear_combination (18*d*t^2) * h

/-- `1-C₃u³+u⁶` is exactly the product of the two oppositely oriented
primitive-cycle factors. -/
theorem zetaInverse_factor {z w : ℂ} (h : z*w = 1) (u : ℂ) :
    zetaInverse (cubicData z w) u =
      (1-z^3*u^3) * (1-w^3*u^3) := by
  have h3 := inverse_phases_cube h
  unfold zetaInverse cubicData
  calc
    1 - (z^3+w^3)*u^3 + u^6 =
        1 - (z^3+w^3)*u^3 + (z^3*w^3)*u^6 := by rw [h3]; ring
    _ = (1-z^3*u^3)*(1-w^3*u^3) := by ring

/-- The complex phase used in the card.-/
noncomputable def phase (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

lemma phase_mul_neg (φ : ℝ) : phase φ * phase (-φ) = 1 := by
  unfold phase
  rw [← Complex.exp_add]
  convert Complex.exp_zero
  push_cast
  ring

lemma phase_cubed (φ : ℝ) : phase φ ^ 3 = phase (3*φ) := by
  unfold phase
  rw [pow_three, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The circulant's cubic datum is exactly `2 cos(3φ)`. -/
theorem cubicData_phase (φ : ℝ) :
    cubicData (phase φ) (phase (-φ)) = 2*(Real.cos (3*φ) : ℂ) := by
  rw [cubicData, phase_cubed, phase_cubed]
  unfold phase
  have harg : (3 : ℝ) * (-φ) = -(3*φ) := by ring
  rw [harg]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- The card's three real parameters use a Hermitian circulant. -/
noncomputable def phasedTri (d t φ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  tri (d : ℂ) (t : ℂ) (phase φ) (phase (-φ))

theorem det_phasedTri (d t φ : ℝ) :
    (phasedTri d t φ).det =
      (d:ℂ)^3 - 3*(d:ℂ)*(t:ℂ)^2 +
        (t:ℂ)^3*(2*(Real.cos (3*φ) : ℂ)) := by
  rw [phasedTri, det_tri (phase_mul_neg φ), cubicData_phase]

theorem trace_phasedTri_sq (d t φ : ℝ) :
    (phasedTri d t φ * phasedTri d t φ).trace =
      3*(d:ℂ)^2 + 6*(t:ℂ)^2 := by
  exact trace_tri_sq (phase_mul_neg φ) _ _

theorem trace_phasedTri_cubed (d t φ : ℝ) :
    (phasedTri d t φ * phasedTri d t φ * phasedTri d t φ).trace =
      3*(d:ℂ)^3 + 18*(d:ℂ)*(t:ℂ)^2 +
        6*(t:ℂ)^3*(Real.cos (3*φ) : ℂ) := by
  rw [phasedTri, trace_tri_cubed (phase_mul_neg φ), cubicData_phase]
  ring

theorem zetaInverse_phase (φ u : ℝ) :
    zetaInverse (2*(Real.cos (3*φ) : ℂ)) (u:ℂ) =
      (1-phase φ^3*(u:ℂ)^3) * (1-phase (-φ)^3*(u:ℂ)^3) := by
  rw [← cubicData_phase]
  exact zetaInverse_factor (phase_mul_neg φ) _

/-- A concrete primitive cube root of unity. -/
noncomputable def omega : ℂ := (-1/2 : ℂ) + (Real.sqrt 3/2 : ℂ)*Complex.I

lemma omega_sq : omega^2 = -omega - 1 := by
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

lemma omega_sum : 1 + omega + omega^2 = 0 := by
  rw [omega_sq]
  ring

lemma omega_cubed : omega^3 = 1 := by
  calc
    omega^3 = omega*omega^2 := by ring
    _ = omega*(-omega-1) := by rw [omega_sq]
    _ = -(omega^2+omega) := by ring
    _ = 1 := by rw [omega_sq]; ring

lemma star_omega : star omega = omega^2 := by
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

lemma conj_omega : (starRingEnd ℂ) omega = omega^2 := star_omega

/-- The unnormalised three-point Fourier matrix. -/
noncomputable def dft : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1;
     1, omega, omega^2;
     1, omega^2, omega]

/-- The three eigenvalues carried by the columns of `dft`. -/
noncomputable def triSpectrum (d t z w : ℂ) : Fin 3 → ℂ :=
  ![d+t*(z+w), d+t*(z*omega+w*omega^2), d+t*(z*omega^2+w*omega)]

/-- `dft` diagonalises the triangular circulant on the right. -/
theorem tri_mul_dft (d t z w : ℂ) :
    tri d t z w * dft = dft * Matrix.diagonal (triSpectrum d t z w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tri, dft, triSpectrum, Matrix.mul_apply, Fin.sum_univ_three,
      omega_sq] <;> try (ring_nf; done)
  all_goals
    first
    | linear_combination t*(w-z)*omega_sum
    | linear_combination t*(z-w)*omega_sum

/-- Fourier orthogonality in unnormalised form. -/
theorem dft_mul_conjTranspose : dft * dftᴴ = (3:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dft, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      conj_omega, omega_sq] <;> try (ring_nf; done)
  all_goals
    first
    | linear_combination omega_sum
    | linear_combination -omega_sum
    | linear_combination (2:ℂ)*omega_sum
    | linear_combination (-2:ℂ)*omega_sum

/-- The unnormalised Fourier diagonalisation, written exactly as a matrix
identity with a factor three. -/
theorem dft_diagonalisation (d t z w : ℂ) :
    dft * Matrix.diagonal (triSpectrum d t z w) * dftᴴ = (3:ℂ) • tri d t z w := by
  calc
    dft * Matrix.diagonal (triSpectrum d t z w) * dftᴴ =
        (tri d t z w * dft) * dftᴴ := by rw [tri_mul_dft]
    _ = tri d t z w * (dft * dftᴴ) := by rw [Matrix.mul_assoc]
    _ = (3:ℂ) • tri d t z w := by rw [dft_mul_conjTranspose, Matrix.mul_smul,
      Matrix.mul_one]

/-- Normalisation used to make the Fourier matrix unitary. -/
noncomputable def fourierScale : ℂ := (Real.sqrt 3 : ℂ)⁻¹

/-- The unitary three-point Fourier matrix. -/
noncomputable def fourier : Matrix (Fin 3) (Fin 3) ℂ := fourierScale • dft

lemma fourierScale_sq : (3:ℂ)*fourierScale^2 = 1 := by
  have hs : (Real.sqrt 3 : ℂ)^2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : (Real.sqrt 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  calc
    (3:ℂ)*fourierScale^2 = (Real.sqrt 3 : ℂ)^2 * fourierScale^2 := by rw [hs]
    _ = ((Real.sqrt 3 : ℂ) * fourierScale)^2 := by ring
    _ = 1 := by rw [fourierScale, mul_inv_cancel₀ hc]; norm_num

lemma fourier_conjTranspose : fourierᴴ = fourierScale • dftᴴ := by
  simp [fourier, fourierScale]

theorem fourier_mul_conjTranspose :
    fourier * fourierᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [fourier_conjTranspose]
  simp only [fourier, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [dft_mul_conjTranspose]
  simp only [smul_smul]
  rw [show fourierScale * fourierScale * 3 = 1 by
    linear_combination fourierScale_sq]
  exact one_smul _ _

theorem fourier_conjTranspose_mul :
    fourierᴴ * fourier = (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  mul_eq_one_comm.2 fourier_mul_conjTranspose

theorem tri_mul_fourier (d t z w : ℂ) :
    tri d t z w * fourier = fourier * Matrix.diagonal (triSpectrum d t z w) := by
  simp only [fourier, Matrix.mul_smul, Matrix.smul_mul]
  rw [tri_mul_dft]

/-- The exact `Φ = F diag(x) F*` formula on the card, with the unitary
Fourier matrix defined above. -/
theorem fourier_diagonalisation (d t z w : ℂ) :
    tri d t z w = fourier * Matrix.diagonal (triSpectrum d t z w) * fourierᴴ := by
  calc
    tri d t z w = tri d t z w * 1 := by rw [Matrix.mul_one]
    _ = tri d t z w * (fourier * fourierᴴ) := by rw [fourier_mul_conjTranspose]
    _ = (tri d t z w * fourier) * fourierᴴ := by rw [Matrix.mul_assoc]
    _ = fourier * Matrix.diagonal (triSpectrum d t z w) * fourierᴴ := by
      rw [tri_mul_fourier]

/-- Conjugation of the complex phase is the opposite phase. -/
lemma star_phase (φ : ℝ) : star (phase φ) = phase (-φ) := by
  unfold phase
  change (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma conj_phase (φ : ℝ) : (starRingEnd ℂ) (phase φ) = phase (-φ) := star_phase φ

/-- A real phased triangular circulant is Hermitian. -/
theorem phasedTri_hermitian (d t φ : ℝ) : (phasedTri d t φ)ᴴ = phasedTri d t φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phasedTri, tri, Matrix.conjTranspose_apply, conj_phase]

/-- Multiplication of phases adds their angles. -/
lemma phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The explicit cube root is the phase at `2π/3`. -/
lemma omega_eq_phase : omega = phase (2*Real.pi/3) := by
  unfold omega phase
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h : 2*Real.pi/3 = 2*(Real.pi/3) := by ring
  rw [h, Real.cos_two_mul, Real.sin_two_mul, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  norm_num
  ring

/-- A full turn is the trivial phase. -/
lemma phase_two_pi : phase (2*Real.pi) = 1 := by
  unfold phase
  convert Complex.exp_two_pi_mul_I using 1
  push_cast
  ring

/-- The trigonometric form of the three Fourier eigenvalues. -/
theorem triSpectrum_phase (d t φ : ℝ) :
    triSpectrum (d:ℂ) (t:ℂ) (phase φ) (phase (-φ)) =
      ![(d:ℂ)+2*(t:ℂ)*(Real.cos φ : ℂ),
        (d:ℂ)+2*(t:ℂ)*(Real.cos (φ+2*Real.pi/3) : ℂ),
        (d:ℂ)+2*(t:ℂ)*(Real.cos (φ+4*Real.pi/3) : ℂ)] := by
  have hpair (a : ℝ) : phase a + phase (-a) = 2*Complex.cos (a : ℂ) := by
    have h : phase a + phase (-a) = 2*(Real.cos a : ℂ) := by
      unfold phase
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring
    simpa only [Complex.ofReal_cos] using h
  have hθ : omega = phase (2*Real.pi/3) := omega_eq_phase
  have hθ2 : omega^2 = phase (4*Real.pi/3) := by
    rw [hθ, show (4:ℝ)*Real.pi/3 = 2*(2*Real.pi/3) by ring]
    rw [show phase (2*(2*Real.pi/3)) = phase (2*Real.pi/3)^2 by
      rw [show (2:ℝ)*(2*Real.pi/3) = 2*Real.pi/3+2*Real.pi/3 by ring,
        phase_add]; ring]
  have hforward1 : phase φ*omega = phase (φ+2*Real.pi/3) := by
    rw [hθ, ← phase_add]
  have hforward2 : phase φ*omega^2 = phase (φ+4*Real.pi/3) := by
    rw [hθ2, ← phase_add]
  have hback1 : phase (-φ)*omega^2 = phase (-(φ+2*Real.pi/3)) := by
    rw [hθ2, ← phase_add]
    have ht : 4*Real.pi/3 = -(2*Real.pi/3)+2*Real.pi := by ring
    rw [ht, show -φ+(-(2*Real.pi/3)+2*Real.pi) =
      (-(φ+2*Real.pi/3))+2*Real.pi by ring, phase_add, phase_two_pi, mul_one]
  have hback2 : phase (-φ)*omega = phase (-(φ+4*Real.pi/3)) := by
    rw [hθ, ← phase_add]
    have ht : 2*Real.pi/3 = -(4*Real.pi/3)+2*Real.pi := by ring
    rw [ht, show -φ+(-(4*Real.pi/3)+2*Real.pi) =
      (-(φ+4*Real.pi/3))+2*Real.pi by ring, phase_add, phase_two_pi, mul_one]
  funext j
  fin_cases j
  · simp [triSpectrum]
    rw [hpair]
    ring
  · simp [triSpectrum]
    rw [hforward1, hback1, hpair]
    push_cast
    ring
  · simp [triSpectrum]
    rw [hforward2, hback2, hpair]
    push_cast
    ring

/-- Conjugation by a connection matrix on matrix-valued fields. -/
def adjointTransport {n : Type*} [Fintype n] [DecidableEq n]
    (U X : Matrix n n ℂ) : Matrix n n ℂ := U * X * Uᴴ

/-- The representation of `adjointTransport` on vectorised matrix fields. -/
def transportMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := Uᴴᵀ ⊗ₖ U

theorem vec_adjointTransport {n : Type*} [Fintype n] [DecidableEq n]
    (U X : Matrix n n ℂ) :
    Matrix.vec (adjointTransport U X) = transportMatrix U *ᵥ Matrix.vec X := by
  symm
  simpa [adjointTransport, transportMatrix] using
    Matrix.kronecker_mulVec_vec U X Uᴴᵀ

theorem trace_transportMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) :
    (transportMatrix U).trace = Uᴴ.trace * U.trace := by
  simp [transportMatrix, Matrix.trace_kronecker, Matrix.trace_transpose]

/-- Central scalar phases act trivially on `End(E)`. -/
theorem adjointTransport_phase_scalar {n : Type*} [Fintype n] [DecidableEq n]
    (φ : ℝ) (X : Matrix n n ℂ) :
    adjointTransport (phase φ • (1 : Matrix n n ℂ)) X = X := by
  simp [adjointTransport, smul_smul, star_phase]
  rw [mul_comm, phase_mul_neg, one_smul]

/-- Any unitary transport preserves the determinant, hence all characteristic
polynomial data, including the cubic record. -/
theorem det_adjointTransport {n : Type*} [Fintype n] [DecidableEq n]
    {U X : Matrix n n ℂ} (hU : U*Uᴴ = 1) :
    (adjointTransport U X).det = X.det := by
  have hd := congrArg Matrix.det hU
  simp only [Matrix.det_mul, Matrix.det_one] at hd
  simp only [adjointTransport, Matrix.det_mul]
  linear_combination X.det * hd

/-- A noncentral rank-two diagonal phase. -/
noncomputable def rankTwoPhase (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![phase φ, 0; 0, 1]

theorem rankTwoPhase_unitary (φ : ℝ) :
    rankTwoPhase φ * (rankTwoPhase φ)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoPhase, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, conj_phase, phase_mul_neg]

theorem rankTwoPhase_cubed (φ : ℝ) :
    rankTwoPhase φ ^ 3 = rankTwoPhase (3*φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoPhase, pow_three, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show phase φ * (phase φ * phase φ) = phase φ ^ 3 by ring, phase_cubed]

/-- In the vectorised representation, the rank-two transport on the third
power has trace `2+C₃`; its eigenvalues are `1,1,e^{3iφ},e^{-3iφ}`. -/
theorem trace_rankTwoPhase_transport_cubed (φ : ℝ) :
    (transportMatrix (rankTwoPhase φ ^ 3)).trace =
      2 + cubicData (phase φ) (phase (-φ)) := by
  rw [rankTwoPhase_cubed, trace_transportMatrix]
  simp [rankTwoPhase, Matrix.trace_fin_two, star_phase]
  rw [cubicData, phase_cubed, phase_cubed]
  have harg : (3:ℝ)*(-φ) = -(3*φ) := by ring
  rw [harg]
  linear_combination phase_mul_neg (3*φ)

/-- Mathlib's characteristic polynomial agrees with the displayed normal form
at every evaluation point. -/
theorem eval_charpoly_tri {z w : ℂ} (h : z*w = 1) (v d t : ℂ) :
    (tri d t z w).charpoly.eval v = charCubic v d t (cubicData z w) := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  exact det_sub_tri h v d t

/-- Consequently the cubic factors over precisely the three Fourier
eigenvalues. -/
theorem charCubic_eq_prod {z w : ℂ} (h : z*w = 1) (v d t : ℂ) :
    charCubic v d t (cubicData z w) =
      (v-triSpectrum d t z w 0) * (v-triSpectrum d t z w 1) *
        (v-triSpectrum d t z w 2) := by
  have hmat : v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - tri d t z w =
      adjointTransport fourier
        (v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.diagonal (triSpectrum d t z w)) := by
    calc
      v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - tri d t z w =
          v • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
            fourier * Matrix.diagonal (triSpectrum d t z w) * fourierᴴ := by
              rw [fourier_diagonalisation]
      _ = adjointTransport fourier
          (v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.diagonal (triSpectrum d t z w)) := by
        simp [adjointTransport, Matrix.mul_sub, Matrix.sub_mul,
          fourier_mul_conjTranspose]
  rw [← det_sub_tri h]
  rw [hmat, det_adjointTransport fourier_mul_conjTranspose]
  rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal]
  simp [Fin.prod_univ_three]

/-- A concrete quadratic-book collision with different cubic records: equal
coupling and zero diagonal give the same `Tr Φ²` at phases `0` and `π/3`,
while the determinant changes from `2` to `-2`. -/
theorem same_quadratic_book_different_cubic :
    (phasedTri 0 1 0 * phasedTri 0 1 0).trace =
        (phasedTri 0 1 (Real.pi/3) * phasedTri 0 1 (Real.pi/3)).trace ∧
      (phasedTri 0 1 0).det ≠ (phasedTri 0 1 (Real.pi/3)).det := by
  constructor
  · rw [trace_phasedTri_sq, trace_phasedTri_sq]
  · rw [det_phasedTri, det_phasedTri]
    have hp : 3*(Real.pi/3) = Real.pi := by ring
    have h0 : (3:ℝ)*0 = 0 := by norm_num
    rw [h0, Real.cos_zero, hp, Real.cos_pi]
    norm_num


/- Axiom audit for every proved declaration in this file. -/
section AxiomAudit
#print axioms inverse_phases_cube
#print axioms det_tri
#print axioms det_sub_tri
#print axioms trace_tri_sq
#print axioms trace_tri_cubed
#print axioms zetaInverse_factor
#print axioms phase_mul_neg
#print axioms phase_cubed
#print axioms cubicData_phase
#print axioms det_phasedTri
#print axioms trace_phasedTri_sq
#print axioms trace_phasedTri_cubed
#print axioms zetaInverse_phase
#print axioms omega_sq
#print axioms omega_sum
#print axioms omega_cubed
#print axioms star_omega
#print axioms conj_omega
#print axioms tri_mul_dft
#print axioms dft_mul_conjTranspose
#print axioms dft_diagonalisation
#print axioms fourierScale_sq
#print axioms fourier_conjTranspose
#print axioms fourier_mul_conjTranspose
#print axioms fourier_conjTranspose_mul
#print axioms tri_mul_fourier
#print axioms fourier_diagonalisation
#print axioms star_phase
#print axioms conj_phase
#print axioms phasedTri_hermitian
#print axioms phase_add
#print axioms omega_eq_phase
#print axioms phase_two_pi
#print axioms triSpectrum_phase
#print axioms vec_adjointTransport
#print axioms trace_transportMatrix
#print axioms adjointTransport_phase_scalar
#print axioms det_adjointTransport
#print axioms rankTwoPhase_unitary
#print axioms rankTwoPhase_cubed
#print axioms trace_rankTwoPhase_transport_cubed
#print axioms eval_charpoly_tri
#print axioms charCubic_eq_prod
#print axioms same_quadratic_book_different_cubic
end AxiomAudit

end RelationalAtlas.B197


/-! ## B200 — the shift sign in the explanation (REFUTATION)

Integrated from `.ultramath/smwvp3cvb/m4/B200_refutation.lean`.
-/

/-!
# B200: refutation of the printed shift direction

The card says: “Shifting `Z` by `hI` makes its top Hermitian eigenvalue zero
and gives `[[0, 1], [-1, -2h/s]]` up to rotation.”  With the card's convention
`Z = h₁σ_z + h₂σ_x + sJ` and `J = [[0,1],[-1,0]]`, the sign is wrong.
At `h₁ = h = s = 1`, `h₂ = 0`, the Hermitian part of `Z + I` is
`diag(2,0)`.  It has eigenvalue `2`, so its top eigenvalue is not zero.
The valid statement uses `Z - I`: after division by `s`, it is exactly the
printed companion matrix, and its Hermitian part is `diag(0,-2)`.
-/

namespace B200ShiftRefutation

noncomputable section

open Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ


def sigmaZ : M2 := !![1, 0; 0, -1]

def sigmaX : M2 := !![0, 1; 1, 0]

def centeredJ : M2 := !![0, 1; -1, 0]

/-- The card's centred matrix in the local B200 convention. -/
def koideZ (h₁ h₂ s : ℝ) : M2 :=
  h₁ • sigmaZ + h₂ • sigmaX + s • centeredJ

/-- Hermitian (here real symmetric) part, with the same normalization as B183. -/
def hermPart (M : M2) : M2 := (2 : ℝ)⁻¹ • (M + M.transpose)

/-- The companion matrix printed in B200's explanation. -/
def companion (h s : ℝ) : M2 := !![0, 1; -1, -(2 * h / s)]

/-- A finite real symmetric matrix has top eigenvalue zero precisely when its
spectrum is nonpositive and zero occurs as an eigenvalue.  `IsSymm` is included
to rule out using eigenvalues of a nonsymmetric real matrix. -/
def TopEigenvalueZero (M : M2) : Prop :=
  M.IsSymm ∧
    (∀ μ : ℝ, ∀ v : Fin 2 → ℝ, v ≠ 0 → M *ᵥ v = μ • v → μ ≤ 0) ∧
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M *ᵥ v = 0

def smallRoot : ℝ := (2 * Real.sqrt 3 - Real.sqrt 6) / 6

def largeRoot : ℝ := (Real.sqrt 3 + Real.sqrt 6) / 3

def koideQ (m₁ m₂ m₃ : ℝ) : ℝ :=
  (m₁ + m₂ + m₃) / (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃) ^ 2

def koideS (m₁ m₂ m₃ : ℝ) : ℝ :=
  (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃) / Real.sqrt 3

def koideH (m₁ m₂ m₃ : ℝ) : ℝ :=
  Real.sqrt ((m₁ + m₂ + m₃) - (koideS m₁ m₂ m₃) ^ 2)

lemma roots_sum : 2 * smallRoot + largeRoot = Real.sqrt 3 := by
  unfold smallRoot largeRoot
  ring

lemma masses_sum : 2 * smallRoot ^ 2 + largeRoot ^ 2 = 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  calc
    2 * smallRoot ^ 2 + largeRoot ^ 2 =
        (2 * Real.sqrt 3 ^ 2 + Real.sqrt 6 ^ 2) / 6 := by
      unfold smallRoot largeRoot
      ring
    _ = 2 := by rw [h3, h6]; norm_num

lemma smallRoot_pos : 0 < smallRoot := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h3nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h6nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hcmp : Real.sqrt 6 < 2 * Real.sqrt 3 := by
    by_contra! hle
    have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ 2 * Real.sqrt 3) hle
    nlinarith
  unfold smallRoot
  linarith

lemma largeRoot_pos : 0 < largeRoot := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  unfold largeRoot
  linarith

lemma sqrt_small_mass : Real.sqrt (smallRoot ^ 2) = smallRoot :=
  Real.sqrt_sq smallRoot_pos.le

lemma sqrt_large_mass : Real.sqrt (largeRoot ^ 2) = largeRoot :=
  Real.sqrt_sq largeRoot_pos.le

lemma witness_S : koideS (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 1 := by
  unfold koideS
  rw [sqrt_small_mass, sqrt_large_mass]
  have h := roots_sum
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith

lemma witness_H : koideH (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 1 := by
  unfold koideH
  rw [witness_S]
  have hm := masses_sum
  have hs : smallRoot ^ 2 + smallRoot ^ 2 + largeRoot ^ 2 = 2 := by nlinarith
  rw [hs]
  norm_num

lemma witness_Q : koideQ (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 2 / 3 := by
  unfold koideQ
  rw [sqrt_small_mass, sqrt_large_mass]
  have hr := roots_sum
  have hm := masses_sum
  have hs : smallRoot ^ 2 + smallRoot ^ 2 + largeRoot ^ 2 = 2 := by nlinarith
  rw [hs]
  have hsum : smallRoot + smallRoot + largeRoot = Real.sqrt 3 := by nlinarith
  rw [hsum, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma roots_lt : smallRoot < largeRoot := by
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  unfold smallRoot largeRoot
  linarith

lemma witness_unequal : smallRoot ^ 2 ≠ largeRoot ^ 2 := by
  intro heq
  have hroots : smallRoot = largeRoot :=
    (sq_eq_sq₀ smallRoot_pos.le largeRoot_pos.le).mp heq
  exact (ne_of_lt roots_lt) hroots


/-- Non-vacuity under the card's full setup: explicit positive unequal masses
really do give `s = h = 1` (and `Q = 2/3`). -/
theorem positive_unequal_masses_realise_witness :
    0 < smallRoot ^ 2 ∧ 0 < largeRoot ^ 2 ∧
      smallRoot ^ 2 ≠ largeRoot ^ 2 ∧
      koideS (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 1 ∧
      koideH (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 1 ∧
      koideQ (smallRoot ^ 2) (smallRoot ^ 2) (largeRoot ^ 2) = 2 / 3 := by
  exact ⟨pow_pos smallRoot_pos 2, pow_pos largeRoot_pos 2,
    witness_unequal, witness_S, witness_H, witness_Q⟩

lemma koideZ_eq (h₁ h₂ s : ℝ) :
    koideZ h₁ h₂ s = !![h₁, h₂ + s; h₂ - s, -h₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [koideZ, sigmaZ, sigmaX, centeredJ] <;> ring

/-- The witness lies on the card's null cone and is nonzero nilpotent. -/
theorem witness_null_cone :
    koideZ 1 0 1 ≠ 0 ∧ (koideZ 1 0 1) ^ 2 = 0 := by
  rw [koideZ_eq]
  constructor
  · intro h
    have h00 := congrArg (fun M : M2 => M 0 0) h
    norm_num at h00
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- This is the exact Hermitian part after the printed `+hI` shift. -/
theorem hermPart_plus_shift :
    hermPart (koideZ 1 0 1 + (1 : M2)) = !![2, 0; 0, 0] := by
  rw [koideZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hermPart, Matrix.transpose_apply, Matrix.one_apply]

/-- The standard basis vector `e₀` is nonzero. -/
lemma e0_ne_zero : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-- After the printed shift, `e₀` is an eigenvector with positive eigenvalue
`2`; hence the top Hermitian eigenvalue cannot be zero. -/
theorem hermPart_plus_shift_eigenvalue_two :
    hermPart (koideZ 1 0 1 + (1 : M2)) *ᵥ ![1, 0] =
      (2 : ℝ) • ![1, 0] := by
  rw [hermPart_plus_shift]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Formal negation of the card's printed `+hI` top-eigenvalue assertion. -/
theorem printed_plus_shift_top_eigenvalue_zero_false :
    ¬ TopEigenvalueZero (hermPart (koideZ 1 0 1 + (1 : M2))) := by
  intro htop
  have hle := htop.2.1 2 ![1, 0] e0_ne_zero hermPart_plus_shift_eigenvalue_two
  norm_num at hle

/-- The sign-corrected shift gives exactly the printed companion matrix. -/
theorem corrected_minus_shift_eq_companion :
    koideZ 1 0 1 - (1 : M2) = companion 1 1 := by
  rw [koideZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [companion, Matrix.one_apply]

/-- The corrected shift indeed has zero as its top Hermitian eigenvalue: its
Hermitian part is `diag(0,-2)`. -/
theorem hermPart_corrected_minus_shift :
    hermPart (koideZ 1 0 1 - (1 : M2)) = !![0, 0; 0, -2] := by
  rw [koideZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hermPart, Matrix.transpose_apply, Matrix.one_apply]

/-- General form of the correction away from the numerical witness. -/
theorem corrected_shift_scaled_companion {h s : ℝ} (hs : s ≠ 0) :
    koideZ h 0 s - h • (1 : M2) = s • companion h s := by
  rw [koideZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, Matrix.one_apply] <;> field_simp <;> ring

#print axioms roots_sum
#print axioms masses_sum
#print axioms smallRoot_pos
#print axioms largeRoot_pos
#print axioms sqrt_small_mass
#print axioms sqrt_large_mass
#print axioms witness_S
#print axioms witness_H
#print axioms witness_Q
#print axioms roots_lt
#print axioms witness_unequal
#print axioms positive_unequal_masses_realise_witness
#print axioms koideZ_eq
#print axioms witness_null_cone
#print axioms hermPart_plus_shift
#print axioms e0_ne_zero
#print axioms hermPart_plus_shift_eigenvalue_two
#print axioms printed_plus_shift_top_eigenvalue_zero_false
#print axioms corrected_minus_shift_eq_companion
#print axioms hermPart_corrected_minus_shift
#print axioms corrected_shift_scaled_companion

end
end B200ShiftRefutation


/-! ## B191 — the shift identities and the centred balance

Integrated from `.ultramath/smwvp3cvb/m13/B191.lean`.
-/

/-!
# B191 — scalar shifts, the opposite book, and the trace/trace-free split

Self-contained; all matrix norms are Frobenius norms. `transport U T = U T Uᴴ`.
Edge sums use an arbitrary finite set of oriented edges.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace AtlasB191

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The self-commutator on the card. -/
def selfComm (H : Matrix n n ℂ) : Matrix n n ℂ := H * Hᴴ - Hᴴ * H

/-- A real scalar baseline does not change the self-commutator. -/
theorem selfComm_add_real_scalar (c : ℝ) (H : Matrix n n ℂ) :
    selfComm (H + (c : ℂ) • (1 : Matrix n n ℂ)) = selfComm H := by
  have hc : star (c : ℂ) = (c : ℂ) := by simp
  unfold selfComm
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, hc]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul]
  module

/-- The exact square comparison after adding a real scalar multiple of `I`. -/
theorem square_sub_starSquare_add_real_scalar (c : ℝ) (H : Matrix n n ℂ) :
    (H + (c : ℂ) • (1 : Matrix n n ℂ)) ^ 2 -
        (H + (c : ℂ) • (1 : Matrix n n ℂ))ᴴ ^ 2 =
      H ^ 2 - Hᴴ ^ 2 + ((2 * c : ℝ) : ℂ) • (H - Hᴴ) := by
  have hc : star (c : ℂ) = (c : ℂ) := by simp
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, hc]
  simp only [pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, smul_smul]
  module

/-- With `H = D + A`, `D` Hermitian and `A` skew-Hermitian, this is `+4cA`. -/
theorem square_sub_starSquare_shift_D_add_A (c : ℝ) (D A : Matrix n n ℂ)
    (hD : Dᴴ = D) (hA : Aᴴ = -A) :
    ((D + A) + (c : ℂ) • (1 : Matrix n n ℂ)) ^ 2 -
        ((D + A) + (c : ℂ) • (1 : Matrix n n ℂ))ᴴ ^ 2 =
      (D + A) ^ 2 - (D + A)ᴴ ^ 2 + ((4 * c : ℝ) : ℂ) • A := by
  rw [square_sub_starSquare_add_real_scalar]
  have hdiff : D + A - (D + A)ᴴ = (2 : ℂ) • A := by
    rw [conjTranspose_add, hD, hA]
    module
  rw [hdiff, smul_smul]
  norm_num
  ring_nf

/-- Unitary conjugation, written `U(T)` on the card. -/
def transport (U T : Matrix n n ℂ) : Matrix n n ℂ := U * T * Uᴴ

lemma transport_one {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) :
    transport U 1 = 1 := by
  rw [transport, Matrix.mul_one, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff).1 hU]

lemma transport_add (U X Y : Matrix n n ℂ) :
    transport U (X + Y) = transport U X + transport U Y := by
  simp only [transport, Matrix.mul_add, Matrix.add_mul]

lemma transport_sub (U X Y : Matrix n n ℂ) :
    transport U (X - Y) = transport U X - transport U Y := by
  simp only [transport, Matrix.mul_sub, Matrix.sub_mul]

lemma transport_smul (c : ℂ) (U T : Matrix n n ℂ) :
    transport U (c • T) = c • transport U T := by
  simp only [transport, Matrix.mul_smul, Matrix.smul_mul]

lemma trace_transport {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (T : Matrix n n ℂ) : (transport U T).trace = T.trace := by
  calc
    (transport U T).trace = (Uᴴ * (U * T)).trace := by
      rw [transport, Matrix.trace_mul_comm]
    _ = ((Uᴴ * U) * T).trace :=
      congrArg Matrix.trace (Matrix.mul_assoc Uᴴ U T).symm
    _ = T.trace := by
      rw [← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 hU, Matrix.one_mul]

/-- Frobenius norm squared as an entry sum. -/
lemma norm_sq_eq_sum {m k α : Type*} [Fintype m] [Fintype k]
    [SeminormedAddCommGroup α] (X : Matrix m k α) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- Frobenius energy is the real part of the Gram trace. -/
lemma norm_sq_eq_re_trace {m k 𝕜 : Type*} [Fintype m] [Fintype k] [RCLike 𝕜]
    (X : Matrix m k 𝕜) : ‖X‖ ^ 2 = RCLike.re (trace (Xᴴ * X)) := by
  rw [norm_sq_eq_sum, Finset.sum_comm]
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma norm_sq_add (X Y : Matrix n n ℂ) :
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

lemma norm_sq_sub (X Y : Matrix n n ℂ) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 - 2 * (Xᴴ * Y).trace.re := by
  have h := norm_sq_add X (-Y)
  simpa [sub_eq_add_neg, Matrix.mul_neg, trace_neg] using h

/-- A real scalar on `I` has squared Frobenius norm `r c²`. -/
lemma norm_sq_real_scalar_one (c : ℝ) :
    ‖(c : ℂ) • (1 : Matrix n n ℂ)‖ ^ 2 = (Fintype.card n : ℝ) * c ^ 2 := by
  rw [norm_sq_eq_re_trace]
  simp only [conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    trace_smul, trace_one, smul_eq_mul]
  norm_num
  ring

/-- The scalar identity and a trace-free matrix are Frobenius-orthogonal. -/
lemma scalar_one_trace_orthogonal (c : ℝ) {T : Matrix n n ℂ}
    (hT : T.trace = 0) :
    (((c : ℂ) • (1 : Matrix n n ℂ))ᴴ * T).trace = 0 := by
  simp [hT]

/-- Minus-book split for one edge. -/
theorem edge_minus_split {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (ci cj : ℝ) (Ti Tj : Matrix n n ℂ) (hTi : Ti.trace = 0)
    (hTj : Tj.trace = 0) :
    ‖((ci : ℂ) • (1 : Matrix n n ℂ) + Ti) -
        transport U ((cj : ℂ) • 1 + Tj)‖ ^ 2 =
      (Fintype.card n : ℝ) * (ci - cj) ^ 2 +
        ‖Ti - transport U Tj‖ ^ 2 := by
  have hdecomp :
      ((ci : ℂ) • (1 : Matrix n n ℂ) + Ti) -
          transport U ((cj : ℂ) • 1 + Tj) =
        (((ci - cj : ℝ) : ℂ) • (1 : Matrix n n ℂ)) +
          (Ti - transport U Tj) := by
    rw [transport_add, transport_smul, transport_one hU]
    push_cast
    module
  have htr : (Ti - transport U Tj).trace = 0 := by
    rw [trace_sub, trace_transport hU, hTi, hTj, sub_zero]
  rw [hdecomp, norm_sq_add, norm_sq_real_scalar_one,
    scalar_one_trace_orthogonal (ci - cj) htr]
  simp

/-- Plus-book split for one edge. -/
theorem edge_plus_split {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (ci cj : ℝ) (Ti Tj : Matrix n n ℂ) (hTi : Ti.trace = 0)
    (hTj : Tj.trace = 0) :
    ‖((ci : ℂ) • (1 : Matrix n n ℂ) + Ti) +
        transport U ((cj : ℂ) • 1 + Tj)‖ ^ 2 =
      (Fintype.card n : ℝ) * (ci + cj) ^ 2 +
        ‖Ti + transport U Tj‖ ^ 2 := by
  have hdecomp :
      ((ci : ℂ) • (1 : Matrix n n ℂ) + Ti) +
          transport U ((cj : ℂ) • 1 + Tj) =
        (((ci + cj : ℝ) : ℂ) • (1 : Matrix n n ℂ)) +
          (Ti + transport U Tj) := by
    rw [transport_add, transport_smul, transport_one hU]
    push_cast
    module
  have htr : (Ti + transport U Tj).trace = 0 := by
    rw [trace_add, trace_transport hU, hTi, hTj, add_zero]
  rw [hdecomp, norm_sq_add, norm_sq_real_scalar_one,
    scalar_one_trace_orthogonal (ci + cj) htr]
  simp

variable {ι α : Type*}

/-- The summed minus book on a finite collection of edges. -/
noncomputable def minusBook (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (D : ι → Matrix n n ℂ) : ℝ :=
  ∑ e ∈ s, ‖D (left e) - transport (U e) (D (right e))‖ ^ 2

/-- The summed plus book on the same edges. -/
noncomputable def plusBook (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (D : ι → Matrix n n ℂ) : ℝ :=
  ∑ e ∈ s, ‖D (left e) + transport (U e) (D (right e))‖ ^ 2

/-- The displayed summed split for `E⁻`. -/
theorem minusBook_split (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (c : ι → ℝ) (T : ι → Matrix n n ℂ)
    (hU : ∀ e ∈ s, U e ∈ unitaryGroup n ℂ) (hT : ∀ i, (T i).trace = 0) :
    minusBook s left right U (fun i => (c i : ℂ) • 1 + T i) =
      (Fintype.card n : ℝ) * ∑ e ∈ s, (c (left e) - c (right e)) ^ 2 +
        ∑ e ∈ s, ‖T (left e) - transport (U e) (T (right e))‖ ^ 2 := by
  unfold minusBook
  calc
    _ = ∑ e ∈ s, ((Fintype.card n : ℝ) * (c (left e) - c (right e)) ^ 2 +
        ‖T (left e) - transport (U e) (T (right e))‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro e he
      exact edge_minus_split (hU e he) _ _ _ _ (hT _) (hT _)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The displayed summed split for `E⁺`. -/
theorem plusBook_split (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (c : ι → ℝ) (T : ι → Matrix n n ℂ)
    (hU : ∀ e ∈ s, U e ∈ unitaryGroup n ℂ) (hT : ∀ i, (T i).trace = 0) :
    plusBook s left right U (fun i => (c i : ℂ) • 1 + T i) =
      (Fintype.card n : ℝ) * ∑ e ∈ s, (c (left e) + c (right e)) ^ 2 +
        ∑ e ∈ s, ‖T (left e) + transport (U e) (T (right e))‖ ^ 2 := by
  unfold plusBook
  calc
    _ = ∑ e ∈ s, ((Fintype.card n : ℝ) * (c (left e) + c (right e)) ^ 2 +
        ‖T (left e) + transport (U e) (T (right e))‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro e he
      exact edge_plus_split (hU e he) _ _ _ _ (hT _) (hT _)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Adding the same constant at every vertex leaves the minus book unchanged. -/
theorem minusBook_add_uniform (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (D : ι → Matrix n n ℂ) (c : ℝ)
    (hU : ∀ e ∈ s, U e ∈ unitaryGroup n ℂ) :
    minusBook s left right U (fun i => D i + (c : ℂ) • 1) =
      minusBook s left right U D := by
  unfold minusBook
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  rw [transport_add, transport_smul, transport_one (hU e he)]
  module

/-- For a trace-free baseline, a uniform real shift increases the summed plus
book by exactly `4r c²` per edge. Centering is essential: without it an
additional term linear in `c` remains. -/
theorem plusBook_add_uniform_of_traceFree (s : Finset α) (left right : α → ι)
    (U : α → Matrix n n ℂ) (T : ι → Matrix n n ℂ) (c : ℝ)
    (hU : ∀ e ∈ s, U e ∈ unitaryGroup n ℂ) (hT : ∀ i, (T i).trace = 0) :
    plusBook s left right U (fun i => T i + (c : ℂ) • 1) =
      plusBook s left right U T +
        (4 * (Fintype.card n : ℝ) * s.card * c ^ 2) := by
  have hshift : ∀ e ∈ s,
      ‖(T (left e) + (c : ℂ) • (1 : Matrix n n ℂ)) +
          transport (U e) (T (right e) + (c : ℂ) • 1)‖ ^ 2 =
        ‖T (left e) + transport (U e) (T (right e))‖ ^ 2 +
          4 * (Fintype.card n : ℝ) * c ^ 2 := by
    intro e he
    have hdecomp :
        (T (left e) + (c : ℂ) • (1 : Matrix n n ℂ)) +
            transport (U e) (T (right e) + (c : ℂ) • 1) =
          (((2 * c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) +
            (T (left e) + transport (U e) (T (right e))) := by
      rw [transport_add, transport_smul, transport_one (hU e he)]
      push_cast
      module
    have htr : (T (left e) + transport (U e) (T (right e))).trace = 0 := by
      rw [trace_add, trace_transport (hU e he), hT, hT, add_zero]
    rw [hdecomp, norm_sq_add, norm_sq_real_scalar_one,
      scalar_one_trace_orthogonal]
    · simp only [Complex.zero_re, mul_zero, add_zero]
      push_cast
      ring
    · simpa [Matrix.conjTranspose_smul] using htr
  unfold plusBook
  calc
    _ = ∑ e ∈ s, (‖T (left e) + transport (U e) (T (right e))‖ ^ 2 +
        4 * (Fintype.card n : ℝ) * c ^ 2) := by
      apply Finset.sum_congr rfl
      exact hshift
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ### Centered rank-`k` projectors

Let `o = Re Tr(P UQU*)`.  For rank-`k` orthogonal projectors the uncentered
local books are `2k ∓ 2o`.  Centering both projectors by `k/r` leaves the minus
book alone and changes the plus book to `2k + 2o − 4k²/r`.
-/

/-- A Hermitian idempotent matrix. -/
def IsOrthoProjector (P : Matrix n n ℂ) : Prop := P.IsHermitian ∧ P * P = P

lemma transport_isOrthoProjector {U Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hQ : IsOrthoProjector Q) :
    IsOrthoProjector (transport U Q) := by
  constructor
  · show (transport U Q)ᴴ = transport U Q
    simp [transport, Matrix.conjTranspose_mul, hQ.1.eq, Matrix.mul_assoc]
  · calc
      transport U Q * transport U Q = U * (Q * (Uᴴ * U) * Q) * Uᴴ := by
        simp only [transport]
        noncomm_ring
      _ = U * (Q * Q) * Uᴴ := by
        rw [← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 hU]
        simp
      _ = transport U Q := by rw [hQ.2]; rfl

lemma norm_sq_isOrthoProjector {P : Matrix n n ℂ} (hP : IsOrthoProjector P) :
    ‖P‖ ^ 2 = P.trace.re := by
  rw [norm_sq_eq_re_trace, hP.1.eq, hP.2]
  rfl

lemma uncentered_minus_projector {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) (k : ℝ)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    ‖P - transport U Q‖ ^ 2 = 2 * k - 2 * (P * transport U Q).trace.re := by
  have hQ' := transport_isOrthoProjector hU hQ
  rw [norm_sq_sub, norm_sq_isOrthoProjector hP, norm_sq_isOrthoProjector hQ',
    hP.1.eq, trace_transport hU, hPtr, hQtr]
  simp only [Complex.ofReal_re]
  ring

lemma uncentered_plus_projector {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) (k : ℝ)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    ‖P + transport U Q‖ ^ 2 = 2 * k + 2 * (P * transport U Q).trace.re := by
  have hQ' := transport_isOrthoProjector hU hQ
  rw [norm_sq_add, norm_sq_isOrthoProjector hP, norm_sq_isOrthoProjector hQ',
    hP.1.eq, trace_transport hU, hPtr, hQtr]
  simp only [Complex.ofReal_re]
  ring

lemma scalar_trace_right_re (X : Matrix n n ℂ) (a : ℝ) :
    (Xᴴ * ((a : ℂ) • (1 : Matrix n n ℂ))).trace.re = a * X.trace.re := by
  simp only [mul_smul_comm, mul_one, trace_smul, smul_eq_mul, trace_conjTranspose]
  simp

lemma centered_minus_projector {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) (k a : ℝ)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    ‖(P - (a : ℂ) • (1 : Matrix n n ℂ)) -
        transport U (Q - (a : ℂ) • 1)‖ ^ 2 =
      2 * k - 2 * (P * transport U Q).trace.re := by
  have hdecomp : (P - (a : ℂ) • (1 : Matrix n n ℂ)) -
      transport U (Q - (a : ℂ) • 1) = P - transport U Q := by
    rw [transport_sub, transport_smul, transport_one hU]
    module
  rw [hdecomp, uncentered_minus_projector hU hP hQ k hPtr hQtr]

lemma centered_plus_projector {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) (k a : ℝ)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    ‖(P - (a : ℂ) • (1 : Matrix n n ℂ)) +
        transport U (Q - (a : ℂ) • 1)‖ ^ 2 =
      2 * k + 2 * (P * transport U Q).trace.re -
        8 * a * k + 4 * (Fintype.card n : ℝ) * a ^ 2 := by
  have hdecomp : (P - (a : ℂ) • (1 : Matrix n n ℂ)) +
      transport U (Q - (a : ℂ) • 1) =
      (P + transport U Q) - (((2 * a : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
    rw [transport_sub, transport_smul, transport_one hU]
    push_cast
    module
  rw [hdecomp, norm_sq_sub, uncentered_plus_projector hU hP hQ k hPtr hQtr,
    norm_sq_real_scalar_one, scalar_trace_right_re, trace_add, trace_transport hU,
    hPtr, hQtr]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

/-- **Uncentered balance.** With normalized overlap `ρ = Re Tr(PUQU*)/k`,
the two uncentered books agree exactly at `ρ = 0`. -/
theorem uncentered_balance_iff {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) {k : ℝ} (hk : k ≠ 0)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    ‖P - transport U Q‖ ^ 2 = ‖P + transport U Q‖ ^ 2 ↔
      (P * transport U Q).trace.re / k = 0 := by
  rw [uncentered_minus_projector hU hP hQ k hPtr hQtr,
    uncentered_plus_projector hU hP hQ k hPtr hQtr]
  constructor
  · intro h
    have ho : (P * transport U Q).trace.re = 0 := by linarith
    simp [ho]
  · intro h
    have ho : (P * transport U Q).trace.re = 0 := by simpa [hk] using h
    rw [ho]
    ring

/-- **Centered balance.** After subtracting `k/r` times the identity from
both projectors, the books agree exactly when the normalized overlap is `k/r`. -/
theorem centered_balance_iff [Nonempty n] {U P Q : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hP : IsOrthoProjector P)
    (hQ : IsOrthoProjector Q) {k : ℝ} (hk : k ≠ 0)
    (hPtr : P.trace = (k : ℂ)) (hQtr : Q.trace = (k : ℂ)) :
    let a := k / (Fintype.card n : ℝ)
    ‖(P - (a : ℂ) • (1 : Matrix n n ℂ)) -
        transport U (Q - (a : ℂ) • 1)‖ ^ 2 =
      ‖(P - (a : ℂ) • 1) + transport U (Q - (a : ℂ) • 1)‖ ^ 2 ↔
        (P * transport U Q).trace.re / k = k / (Fintype.card n : ℝ) := by
  intro a
  have ha : a = k / (Fintype.card n : ℝ) := rfl
  rw [centered_minus_projector hU hP hQ k a hPtr hQtr,
    centered_plus_projector hU hP hQ k a hPtr hQtr]
  have hr : (Fintype.card n : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    have ho : (P * transport U Q).trace.re = 2 * a * k -
        (Fintype.card n : ℝ) * a ^ 2 := by linarith
    rw [ho, ha]
    field_simp [hk, hr]
    ring
  · intro h
    have ho : (P * transport U Q).trace.re = k ^ 2 / (Fintype.card n : ℝ) := by
      calc
        (P * transport U Q).trace.re =
            ((P * transport U Q).trace.re / k) * k := by field_simp [hk]
        _ = (k / (Fintype.card n : ℝ)) * k := by rw [h]
        _ = k ^ 2 / (Fintype.card n : ℝ) := by ring
    rw [ho, ha]
    field_simp [hr]
    ring

/-! #### Why the trace-free hypothesis matters for the prose “adds `4rc²`” -/

/-- On one scalar edge with unshifted endpoint `1`, transport `1`, and shift
`c = 1`, the plus book becomes `16`, while the old book plus only the quadratic
term is `8`.  Uncentered shifts also have a linear contribution; this does not
affect the card's displayed trace/trace-free split. -/
theorem plusBook_uncentered_witness :
    (plusBook (Finset.univ : Finset Unit) (fun _ : Unit => ()) (fun _ => ())
        (fun _ : Unit => (1 : Matrix Unit Unit ℂ))
        (fun _ => (1 : Matrix Unit Unit ℂ) + ((1 : ℝ) : ℂ) • 1)) = 16 ∧
      (plusBook (Finset.univ : Finset Unit) (fun _ : Unit => ()) (fun _ => ())
          (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) (fun _ => 1) +
        4 * (Fintype.card Unit : ℝ) * (Finset.univ : Finset Unit).card *
          (1 : ℝ) ^ 2) = 8 := by
  constructor <;>
    norm_num [plusBook, transport, norm_sq_eq_sum, Matrix.mul_apply,
      Matrix.ofNat_apply]

/-- The displayed one-site rotation matrix. -/
def J₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- **One-site identity.** For every real symmetric `2×2` matrix. -/
theorem one_site_MJ_add_JM (a b d : ℝ) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]
    M * J₂ + J₂ * M = (M.trace : ℝ) • J₂ := by
  intro M
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M, J₂, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]

/-- The companion one-site norm budget: the commutator and anti-commutator
with `J` have squared norms adding to four times the squared norm of `M`. -/
theorem one_site_two_squared_norms (a b d : ℝ) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]
    ‖M * J₂ - J₂ * M‖ ^ 2 + ‖M * J₂ + J₂ * M‖ ^ 2 = 4 * ‖M‖ ^ 2 := by
  intro M
  simp only [norm_sq_eq_sum]
  norm_num [M, J₂, Matrix.mul_apply, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

#print axioms selfComm_add_real_scalar
#print axioms square_sub_starSquare_add_real_scalar
#print axioms square_sub_starSquare_shift_D_add_A
#print axioms transport_one
#print axioms transport_add
#print axioms transport_sub
#print axioms transport_smul
#print axioms trace_transport
#print axioms norm_sq_eq_sum
#print axioms norm_sq_eq_re_trace
#print axioms norm_sq_add
#print axioms norm_sq_sub
#print axioms norm_sq_real_scalar_one
#print axioms scalar_one_trace_orthogonal
#print axioms edge_minus_split
#print axioms edge_plus_split
#print axioms minusBook_split
#print axioms plusBook_split
#print axioms minusBook_add_uniform
#print axioms plusBook_add_uniform_of_traceFree
#print axioms transport_isOrthoProjector
#print axioms norm_sq_isOrthoProjector
#print axioms uncentered_minus_projector
#print axioms uncentered_plus_projector
#print axioms scalar_trace_right_re
#print axioms centered_minus_projector
#print axioms centered_plus_projector
#print axioms uncentered_balance_iff
#print axioms centered_balance_iff
#print axioms plusBook_uncentered_witness
#print axioms one_site_MJ_add_JM
#print axioms one_site_two_squared_norms

end AtlasB191


/-! ## B201 — the two derivative laws, the Lax invariants and the 32 budget

Integrated from `.ultramath/smwvp3cvb/m9/B201.lean`.
-/


namespace RelationalAtlas.B201

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section FugledePrelude
open scoped Matrix.Norms.L2Operator

/-- Fuglede's theorem in the form needed for the `K²` stationary test. -/
lemma commute_square_star_of_isStarNormal {K : Matrix n n ℂ}
    (h : IsStarNormal (K ^ 2)) : Commute (K ^ 2) Kᴴ := by
  have hXK : Commute (K ^ 2) K := Commute.pow_self K 2
  have hKXstar : Commute K (star (K ^ 2)) := h.commute_star_right hXK.symm
  have hXKstar : Commute (K ^ 2) (star K) := hKXstar.symm.star_right
  simpa only [Matrix.star_eq_conjTranspose] using hXKstar

end FugledePrelude

end RelationalAtlas.B201

open Matrix
open scoped Matrix.Norms.Frobenius

namespace RelationalAtlas.B201

def cinner (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

lemma cinner_self (z : ℂ) : cinner z z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [cinner, pow_two]

lemma norm_sq_eq_sum {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma complex_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

noncomputable local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix n n ℂ) where
  inner M N := ∑ i, ∑ j, cinner (M i j) (N i j)
  norm_sq_eq_re_inner M := by
    simp [norm_sq_eq_sum, cinner_self]
  conj_inner_symm M N := by
    simp [cinner, mul_comm]
  add_left M N P := by
    simp [cinner, add_mul, Finset.sum_add_distrib]
    ring
  smul_left M N r := by
    simp [cinner, Finset.mul_sum, mul_assoc, mul_add]


example {K : ℝ → Matrix n n ℂ} {K' : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K K' t) :
    HasDerivAt (fun t => ‖K t‖ ^ 2) (2 * inner ℝ (K t) K') t := by
  exact hK.norm_sq

example (M N : Matrix n n ℂ) :
    inner ℝ M N = ∑ i, ∑ j, cinner (M i j) (N i j) := by
  rfl

example (M N : Matrix n n ℂ) :
    inner ℝ M N = (Matrix.trace (Mᴴ * N)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [complex_re_sum]
  simp_rw [complex_re_sum]
  change (∑ i, ∑ j, cinner (M i j) (N i j)) = _
  simp only [cinner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring


/-- The commutator, with the sign convention of the card. -/
def comm (M N : Matrix n n ℂ) : Matrix n n ℂ := M * N - N * M

/-- The self-commutator `C = [K,K*]`. -/
def defect (K : Matrix n n ℂ) : Matrix n n ℂ := comm K Kᴴ

/-- The two books, including the card's factor `1/8`. -/
noncomputable def oppositeBook (K : Matrix n n ℂ) : ℝ :=
  (1 / 8 : ℝ) * ‖K ^ 2 - (Kᴴ) ^ 2‖ ^ 2
noncomputable def connectionBook (K : Matrix n n ℂ) : ℝ :=
  (1 / 8 : ℝ) * ‖defect K‖ ^ 2

/-- Complex Frobenius pairing, before taking the real part. -/
def pair (M N : Matrix n n ℂ) : ℂ := Matrix.trace (Mᴴ * N)

lemma inner_eq_pair (M N : Matrix n n ℂ) : inner ℝ M N = (pair M N).re := by
  unfold pair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [complex_re_sum]
  simp_rw [complex_re_sum]
  change (∑ i, ∑ j, cinner (M i j) (N i j)) = _
  simp only [cinner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma defect_hermitian (K : Matrix n n ℂ) : (defect K)ᴴ = defect K := by
  simp [defect, comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]

lemma pair_flow_direction (K : Matrix n n ℂ) :
    pair K (comm (defect K) K) = pair (defect K) (defect K) := by
  simp only [pair, defect_hermitian, comm, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_assoc]
  have h1 : Matrix.trace (Kᴴ * (defect K * K)) =
      Matrix.trace (defect K * (K * Kᴴ)) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Kᴴ (defect K * K)
  have h2 : Matrix.trace (Kᴴ * (K * defect K)) =
      Matrix.trace (defect K * (Kᴴ * K)) := by
    rw [← Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (Kᴴ * K) (defect K)
  rw [h1, h2, ← Matrix.trace_sub, ← Matrix.mul_sub]
  congr 1


lemma inner_flow_direction (K : Matrix n n ℂ) :
    inner ℝ K (comm (defect K) K) = ‖defect K‖ ^ 2 := by
  calc
    inner ℝ K (comm (defect K) K) = (pair (defect K) (defect K)).re := by
      rw [inner_eq_pair, pair_flow_direction]
    _ = inner ℝ (defect K) (defect K) := (inner_eq_pair _ _).symm
    _ = ‖defect K‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- The relaxation velocity, `K̇ = -2[C,K]`. -/
noncomputable def velocity (K : Matrix n n ℂ) : Matrix n n ℂ :=
  (-2 : ℝ) • comm (defect K) K

lemma hasDerivAt_conjTranspose {K : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) :
    HasDerivAt (fun s => (K s)ᴴ) Vᴴ t := by
  apply hasDerivAt_pi.2
  intro j
  apply hasDerivAt_pi.2
  intro i
  simpa only [Matrix.conjTranspose_apply] using
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hK i) j).star

lemma hasDerivAt_matrix_mul {K L : ℝ → Matrix n n ℂ}
    {V W : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) (hL : HasDerivAt L W t) :
    HasDerivAt (fun s => K s * L s) (V * L t + K t * W) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hK i) k).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hL k) j)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Pi.mul_apply, ← Finset.sum_add_distrib] using h

lemma hasDerivAt_defect {K : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) :
    HasDerivAt (fun s => defect (K s))
      (comm V (K t)ᴴ + comm (K t) Vᴴ) t := by
  have h := (hasDerivAt_matrix_mul hK (hasDerivAt_conjTranspose hK)).sub
    (hasDerivAt_matrix_mul (hasDerivAt_conjTranspose hK) hK)
  have heq : (V * (K t)ᴴ + K t * Vᴴ) - (Vᴴ * K t + (K t)ᴴ * V) =
      comm V (K t)ᴴ + comm (K t) Vᴴ := by
    simp only [comm]
    abel
  exact h.congr_deriv heq

/-- The finite-time form of the card's integrated `32` budget. -/
theorem hasDerivAt_frobeniusSq_flow {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) :
    HasDerivAt (fun s => ‖K s‖ ^ 2) (-32 * connectionBook (K t)) t := by
  convert hK.norm_sq using 1
  simp only [velocity, real_inner_smul_right, inner_flow_direction, connectionBook]
  ring

lemma pair_conj (M N : Matrix n n ℂ) : star (pair M N) = pair N M := by
  symm
  simpa only [pair, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
    Matrix.trace_conjTranspose (Mᴴ * N)

lemma pair_comm_left {C K V : Matrix n n ℂ} (hC : Cᴴ = C) :
    pair C (comm V Kᴴ) = pair (comm C K) V := by
  simp only [pair, comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hC, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle' C V Kᴴ]

lemma pair_comm_right {C K V : Matrix n n ℂ} (hC : Cᴴ = C) :
    pair C (comm K Vᴴ) = star (pair (comm C K) V) := by
  rw [pair_conj]
  simp only [pair, comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hC, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle' C K Vᴴ]
  rw [← Matrix.trace_mul_cycle' Vᴴ K C]



lemma pair_add_right (M N P : Matrix n n ℂ) :
    pair M (N + P) = pair M N + pair M P := by
  simp only [pair, Matrix.mul_add, Matrix.trace_add]

lemma inner_defect_tangent (K V : Matrix n n ℂ) :
    inner ℝ (defect K) (comm V Kᴴ + comm K Vᴴ) =
      2 * inner ℝ (comm (defect K) K) V := by
  rw [inner_eq_pair, pair_add_right, pair_comm_left (defect_hermitian K),
    pair_comm_right (defect_hermitian K), inner_eq_pair]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- **B201, connection-book derivative.**  No normality or graph hypothesis is
needed, and the factor `1/8` yields exactly the displayed derivative. -/
theorem hasDerivAt_connectionBook_flow {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) :
    HasDerivAt (fun s => connectionBook (K s)) (-‖comm (defect (K t)) (K t)‖ ^ 2) t := by
  have hC := hasDerivAt_defect hK
  have h := HasDerivAt.const_mul (1 / 8 : ℝ) hC.norm_sq
  have heq : (1 / 8 : ℝ) *
      (2 * inner ℝ (defect (K t))
        (comm (velocity (K t)) (K t)ᴴ + comm (K t) (velocity (K t))ᴴ)) =
      -‖comm (defect (K t)) (K t)‖ ^ 2 := by
    rw [inner_defect_tangent]
    simp only [velocity, real_inner_smul_right, ← real_inner_self_eq_norm_sq]
    ring
  exact h.congr_deriv heq



lemma pair_sub_right (M N P : Matrix n n ℂ) :
    pair M (N - P) = pair M N - pair M P := by
  simp only [pair, Matrix.mul_sub, Matrix.trace_sub]

lemma pair_conjTranspose_right (M N : Matrix n n ℂ) :
    pair M Nᴴ = star (pair Mᴴ N) := by
  rw [pair_conj]
  exact Matrix.trace_mul_comm Mᴴ Nᴴ

lemma pair_adj_self_comm (C X : Matrix n n ℂ) :
    pair Xᴴ (comm C X) = 0 := by
  simp only [pair, comm, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle' X C X]
  simp

lemma pair_comm_self_adj (C X : Matrix n n ℂ) :
    pair X (comm C X) = Matrix.trace (C * comm X Xᴴ) := by
  simp only [pair, comm, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle' C X Xᴴ]
  rw [Matrix.trace_mul_comm C (Xᴴ * X)]
  rw [Matrix.mul_assoc]

lemma trace_rotate4_right (A B C D : Matrix n n ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (D * A * B * C) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A * B * C) D

lemma trace_rotate4_left (A B C D : Matrix n n ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm A (B * C * D)

lemma pair_comm_comm_sq {X K : Matrix n n ℂ} (hXK : Commute X K) :
    Matrix.trace (comm K Kᴴ * comm X Xᴴ) =
      pair (comm X Kᴴ) (comm X Kᴴ) := by
  have h1 : Matrix.trace (K * (Xᴴ * (X * Kᴴ))) =
      Matrix.trace (Kᴴ * (K * (Xᴴ * X))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_right K Xᴴ X Kᴴ
  have h2a : Matrix.trace (Xᴴ * (K * (X * Kᴴ))) =
      Matrix.trace (Kᴴ * (Xᴴ * (K * X))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_right Xᴴ K X Kᴴ
  have h2b : Matrix.trace (Kᴴ * (Xᴴ * (K * X))) =
      Matrix.trace (Kᴴ * (Xᴴ * (X * K))) := by rw [← hXK.eq]
  have h2c : Matrix.trace (Kᴴ * (Xᴴ * (X * K))) =
      Matrix.trace (K * (Kᴴ * (Xᴴ * X))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_right Kᴴ Xᴴ X K
  have h3a : Matrix.trace (K * (Xᴴ * (Kᴴ * X))) =
      Matrix.trace (Xᴴ * (Kᴴ * (X * K))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_left K Xᴴ Kᴴ X
  have h3b : Matrix.trace (Xᴴ * (Kᴴ * (X * K))) =
      Matrix.trace (Xᴴ * (Kᴴ * (K * X))) := by rw [hXK.eq]
  have h3c : Matrix.trace (Xᴴ * (Kᴴ * (K * X))) =
      Matrix.trace (Kᴴ * (K * (X * Xᴴ))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_left Xᴴ Kᴴ K X
  have h4 : Matrix.trace (Xᴴ * (K * (Kᴴ * X))) =
      Matrix.trace (K * (Kᴴ * (X * Xᴴ))) := by
    simpa only [Matrix.mul_assoc] using trace_rotate4_left Xᴴ K Kᴴ X
  unfold pair comm
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.mul_assoc]
  rw [h1, h2a, h2b, h2c, h3a, h3b, h3c, h4]
  ring


/-- The anti-self-commutator is exactly the opposite-book obstruction. -/
lemma obstruction_eq_comm_square (K : Matrix n n ℂ) :
    defect K * K + K * defect K = comm (K ^ 2) Kᴴ := by
  simp only [defect, comm, pow_two]
  noncomm_ring

lemma pair_square_defect (K : Matrix n n ℂ) :
    pair (K ^ 2) (comm (defect K) (K ^ 2)) =
      pair (comm (K ^ 2) Kᴴ) (comm (K ^ 2) Kᴴ) := by
  rw [pair_comm_self_adj]
  exact pair_comm_comm_sq (Commute.pow_self K 2)

noncomputable def laxMatrix (K : Matrix n n ℂ) : Matrix n n ℂ :=
  (-2 : ℝ) • defect K

lemma velocity_eq_comm_lax (K : Matrix n n ℂ) :
    velocity K = comm (laxMatrix K) K := by
  simp [velocity, laxMatrix, comm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

lemma lax_hermitian (K : Matrix n n ℂ) : (laxMatrix K)ᴴ = laxMatrix K := by
  simp [laxMatrix, Matrix.conjTranspose_smul, defect_hermitian]

lemma comm_smul_left (r : ℝ) (C X : Matrix n n ℂ) :
    comm (r • C) X = r • comm C X := by
  simp [comm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

lemma pair_neg_left (M N : Matrix n n ℂ) : pair (-M) N = -pair M N := by
  simp [pair, Matrix.conjTranspose_neg]

lemma pair_sub_left (M N P : Matrix n n ℂ) :
    pair (M - N) P = pair M P - pair N P := by
  simp [pair, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

lemma inner_sub_conjTranspose {S Y : Matrix n n ℂ} (hS : Sᴴ = -S) :
    inner ℝ S (Y - Yᴴ) = 2 * inner ℝ S Y := by
  rw [inner_eq_pair, inner_eq_pair, pair_sub_right, pair_conjTranspose_right, hS,
    pair_neg_left]
  simp only [map_neg, star_neg, Complex.sub_re, Complex.neg_re,
    Complex.star_def, Complex.conj_re]
  ring

lemma skewSquare_hermitian (K : Matrix n n ℂ) :
    (K ^ 2 - (Kᴴ) ^ 2)ᴴ = -(K ^ 2 - (Kᴴ) ^ 2) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_pow,
    Matrix.conjTranspose_conjTranspose]
  abel

lemma inner_skewSquare_comm (C K : Matrix n n ℂ) :
    inner ℝ (K ^ 2 - (Kᴴ) ^ 2) (comm C (K ^ 2)) =
      inner ℝ (K ^ 2) (comm C (K ^ 2)) := by
  rw [inner_eq_pair, inner_eq_pair, pair_sub_left, ← Matrix.conjTranspose_pow K 2,
    pair_adj_self_comm]
  simp

lemma inner_square_defect (K : Matrix n n ℂ) :
    inner ℝ (K ^ 2) (comm (defect K) (K ^ 2)) =
      ‖comm (K ^ 2) Kᴴ‖ ^ 2 := by
  calc
    inner ℝ (K ^ 2) (comm (defect K) (K ^ 2)) =
        (pair (comm (K ^ 2) Kᴴ) (comm (K ^ 2) Kᴴ)).re := by
      rw [inner_eq_pair, pair_square_defect]
    _ = inner ℝ (comm (K ^ 2) Kᴴ) (comm (K ^ 2) Kᴴ) := (inner_eq_pair _ _).symm
    _ = ‖comm (K ^ 2) Kᴴ‖ ^ 2 := real_inner_self_eq_norm_sq _

lemma inner_square_lax (K : Matrix n n ℂ) :
    inner ℝ (K ^ 2) (comm (laxMatrix K) (K ^ 2)) =
      -2 * ‖comm (K ^ 2) Kᴴ‖ ^ 2 := by
  rw [laxMatrix, comm_smul_left, real_inner_smul_right, inner_square_defect]

lemma hasDerivAt_sq {K : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) :
    HasDerivAt (fun s => (K s) ^ 2) (V * K t + K t * V) t := by
  simpa only [pow_two] using hasDerivAt_matrix_mul hK hK

lemma hasDerivAt_skewSquare {K : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) :
    HasDerivAt (fun s => (K s) ^ 2 - (K s)ᴴ ^ 2)
      ((V * K t + K t * V) - (V * K t + K t * V)ᴴ) t := by
  have h := (hasDerivAt_sq hK).sub (hasDerivAt_sq (hasDerivAt_conjTranspose hK))
  have heq : (V * K t + K t * V) - (Vᴴ * (K t)ᴴ + (K t)ᴴ * Vᴴ) =
      (V * K t + K t * V) - (V * K t + K t * V)ᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
    abel
  exact h.congr_deriv heq

lemma lax_square_tangent (K : Matrix n n ℂ) :
    velocity K * K + K * velocity K = comm (laxMatrix K) (K ^ 2) := by
  rw [velocity_eq_comm_lax]
  simp only [comm, pow_two]
  noncomm_ring

/-- **B201, opposite-book derivative. -/
theorem hasDerivAt_oppositeBook_flow {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) :
    HasDerivAt (fun s => oppositeBook (K s)) (-‖comm ((K t) ^ 2) (K t)ᴴ‖ ^ 2) t := by
  have hS := hasDerivAt_skewSquare hK
  rw [lax_square_tangent] at hS
  have h := HasDerivAt.const_mul (1 / 8 : ℝ) hS.norm_sq
  have heq : (1 / 8 : ℝ) *
      (2 * inner ℝ ((K t) ^ 2 - (K t)ᴴ ^ 2)
        (comm (laxMatrix (K t)) (K t ^ 2) -
          (comm (laxMatrix (K t)) (K t ^ 2))ᴴ)) =
      -‖comm ((K t) ^ 2) (K t)ᴴ‖ ^ 2 := by
    rw [inner_sub_conjTranspose (skewSquare_hermitian (K t)),
      inner_skewSquare_comm, inner_square_lax]
    ring
  exact h.congr_deriv heq



/-- The literal displayed RHS, `-(‖CK + KC‖²)`, with no re-normalization. -/
theorem hasDerivAt_oppositeBook_flow_literal {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) :
    HasDerivAt (fun s => oppositeBook (K s))
      (-‖defect (K t) * K t + K t * defect (K t)‖ ^ 2) t := by
  rw [obstruction_eq_comm_square]
  exact hasDerivAt_oppositeBook_flow hK

lemma trace_comm (L X : Matrix n n ℂ) : Matrix.trace (comm L X) = 0 := by
  rw [comm, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

lemma hasDerivAt_trace {K : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K V t) :
    HasDerivAt (fun s => Matrix.trace (K s)) (Matrix.trace V) t := by
  unfold Matrix.trace Matrix.diag
  apply HasDerivAt.fun_sum
  intro i hi
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hK i) i

/-- Every Lax tangent `K̇ = [L,K]` has the same tangent on every power. -/
lemma hasDerivAt_lax_pow {K : ℝ → Matrix n n ℂ} {L : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (comm L (K t)) t) (m : ℕ) :
    HasDerivAt (fun s => (K s) ^ m) (comm L ((K t) ^ m)) t := by
  induction m with
  | zero =>
      have hz : HasDerivAt (fun _ : ℝ => (1 : Matrix n n ℂ))
          (0 : Matrix n n ℂ) t := by
        apply hasDerivAt_pi.2
        intro i
        apply hasDerivAt_pi.2
        intro j
        by_cases hij : i = j
        · subst j
          simpa using hasDerivAt_const t (1 : ℂ)
        · simpa [Matrix.one_apply, hij] using hasDerivAt_const t (0 : ℂ)
      simpa [comm] using hz
  | succ m ih =>
      have h := hasDerivAt_matrix_mul ih hK
      simp only [pow_succ]
      convert h using 1
      simp only [comm]
      noncomm_ring

/-- Infinitesimal isospectrality in its exact power-trace form: every
`Tr(K^m)` is stationary along every Lax flow. -/
theorem hasDerivAt_trace_pow_lax {K : ℝ → Matrix n n ℂ} {L : Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (comm L (K t)) t) (m : ℕ) :
    HasDerivAt (fun s => Matrix.trace ((K s) ^ m)) 0 t := by
  have h := hasDerivAt_trace (hasDerivAt_lax_pow hK m)
  simpa only [trace_comm] using h

/-- The card's particular relaxation flow is Lax, hence all power traces are
instantaneously stationary. -/
theorem hasDerivAt_trace_pow_flow {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) (m : ℕ) :
    HasDerivAt (fun s => Matrix.trace ((K s) ^ m)) 0 t := by
  have hKl : HasDerivAt K (comm (laxMatrix (K t)) (K t)) t := by
    simpa only [← velocity_eq_comm_lax] using hK
  exact hasDerivAt_trace_pow_lax hKl m



lemma comm_eq_zero_iff_commute (A B : Matrix n n ℂ) :
    comm A B = 0 ↔ Commute A B := by
  exact sub_eq_zero

lemma normal_square_of_obstruction_zero {K : Matrix n n ℂ}
    (h : comm (K ^ 2) Kᴴ = 0) : IsStarNormal (K ^ 2) := by
  have hc : Commute (K ^ 2) Kᴴ := (comm_eq_zero_iff_commute _ _).1 h
  have hc2 : Commute (K ^ 2) ((Kᴴ) ^ 2) := hc.pow_right 2
  refine ⟨?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_pow] using hc2.symm

lemma obstruction_zero_of_normal_square {K : Matrix n n ℂ}
    (h : IsStarNormal (K ^ 2)) : comm (K ^ 2) Kᴴ = 0 := by
  exact (comm_eq_zero_iff_commute _ _).2 (commute_square_star_of_isStarNormal h)

lemma obstruction_zero_iff_normal_square (K : Matrix n n ℂ) :
    comm (K ^ 2) Kᴴ = 0 ↔ IsStarNormal (K ^ 2) := by
  exact ⟨normal_square_of_obstruction_zero, obstruction_zero_of_normal_square⟩

/-- The displayed `dE⁺ = 0 ↔ K² normal`, at a point of any curve satisfying
the relaxation-flow tangent. -/
theorem deriv_oppositeBook_eq_zero_iff {K : ℝ → Matrix n n ℂ} {t : ℝ}
    (hK : HasDerivAt K (velocity (K t)) t) :
    deriv (fun s => oppositeBook (K s)) t = 0 ↔ IsStarNormal ((K t) ^ 2) := by
  have h := hasDerivAt_oppositeBook_flow hK
  rw [← obstruction_zero_iff_normal_square]
  rw [h.deriv]
  constructor
  · intro hz
    have hn : ‖comm ((K t) ^ 2) (K t)ᴴ‖ = 0 := by
      nlinarith [sq_nonneg ‖comm ((K t) ^ 2) (K t)ᴴ‖]
    exact norm_eq_zero.mp hn
  · intro hz
    rw [hz]
    simp



lemma diagonal_skewSquare (v : n → ℂ) :
    (Matrix.diagonal v) ^ 2 - (Matrix.diagonal v)ᴴ ^ 2 =
      Matrix.diagonal (fun i => v i ^ 2 - star (v i) ^ 2) := by
  simp [Matrix.diagonal_pow, Matrix.diagonal_conjTranspose, Matrix.diagonal_sub]

/-- The terminal formula on a spectral diagonal: exactly one half of the sum
of the squared imaginary parts of the squared eigenvalues. -/
theorem oppositeBook_diagonal (v : n → ℂ) :
    oppositeBook (Matrix.diagonal v) =
      (1 / 2 : ℝ) * ∑ i, ((v i) ^ 2).im ^ 2 := by
  classical
  rw [oppositeBook, diagonal_skewSquare, norm_sq_eq_sum]
  calc
    (1 / 8 : ℝ) * (∑ i, ∑ j, ‖(Matrix.diagonal
        (fun i => v i ^ 2 - star (v i) ^ 2)) i j‖ ^ 2) =
        (1 / 8 : ℝ) * ∑ i, ‖v i ^ 2 - star (v i) ^ 2‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.diagonal_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2),
        norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num),
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = (1 / 8 : ℝ) * ∑ i, 4 * ((v i) ^ 2).im ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.sq_norm, Complex.normSq_apply, ← star_pow]
      simp only [Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im]
      ring
    _ = (1 / 2 : ℝ) * ∑ i, ((v i) ^ 2).im ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-- Finite-interval version of the card's `32`-budget.  Integrability is the
only analytic assumption beyond satisfying the flow at every time. -/
theorem integral_connectionBook_flow {K : ℝ → Matrix n n ℂ}
    (hK : ∀ t, HasDerivAt K (velocity (K t)) t) {a b : ℝ}
    (hint : IntervalIntegrable (fun t => connectionBook (K t))
      MeasureTheory.volume a b) :
    32 * (∫ t in a..b, connectionBook (K t)) = ‖K a‖ ^ 2 - ‖K b‖ ^ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s => ‖K s‖ ^ 2) (-32 * connectionBook (K x)) x :=
    fun x _ => hasDerivAt_frobeniusSq_flow (hK x)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint.const_mul (-32 : ℝ))
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith


lemma norm_sq_eq_re_trace (X : Matrix n n ℂ) :
    ‖X‖ ^ 2 = (Matrix.trace (Xᴴ * X)).re := by
  rw [← real_inner_self_eq_norm_sq X, inner_eq_pair]
  rfl

lemma norm_unitary_mul {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    ‖U * X‖ = ‖X‖ := by
  have hu : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').1 hU
  have hsq : ‖U * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [norm_sq_eq_re_trace, norm_sq_eq_re_trace, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hu, Matrix.one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

lemma norm_mul_unitary (X : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖X * U‖ = ‖X‖ := by
  rw [← Matrix.frobenius_norm_conjTranspose (X * U), Matrix.conjTranspose_mul,
    ← Matrix.star_eq_conjTranspose U, norm_unitary_mul (Unitary.star_mem hU),
    Matrix.frobenius_norm_conjTranspose]

noncomputable def unitaryConj (U K : Matrix n n ℂ) : Matrix n n ℂ := U * K * Uᴴ

lemma unitaryConj_sq {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (K : Matrix n n ℂ) :
    (unitaryConj U K) ^ 2 = unitaryConj U (K ^ 2) := by
  have hu : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').1 hU
  simp only [unitaryConj, pow_two]
  calc
    (U * K * Uᴴ) * (U * K * Uᴴ) = U * K * (Uᴴ * U) * K * Uᴴ := by
      simp only [Matrix.mul_assoc]
    _ = U * K * K * Uᴴ := by rw [hu, Matrix.mul_one]
    _ = (U * (K * K)) * Uᴴ := by simp only [Matrix.mul_assoc]

lemma unitaryConj_adj (U K : Matrix n n ℂ) :
    (unitaryConj U K)ᴴ = unitaryConj U Kᴴ := by
  simp [unitaryConj, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma unitaryConj_skewSquare {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) :
    (unitaryConj U K) ^ 2 - (unitaryConj U K)ᴴ ^ 2 =
      unitaryConj U (K ^ 2 - (Kᴴ) ^ 2) := by
  rw [unitaryConj_sq hU, unitaryConj_adj, unitaryConj_sq hU]
  simp [unitaryConj, Matrix.mul_sub, Matrix.sub_mul]

/-- Both books' opposite half is unitarily invariant. -/
theorem oppositeBook_unitaryConj {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) :
    oppositeBook (unitaryConj U K) = oppositeBook K := by
  rw [oppositeBook, oppositeBook, unitaryConj_skewSquare hU]
  have hUs : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU
  unfold unitaryConj
  rw [norm_mul_unitary _ hUs, norm_unitary_mul hU]

/-- The terminal formula transported to a supplied unitary spectral normal
form. -/
theorem oppositeBook_unitary_diagonal {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℂ) :
    oppositeBook (unitaryConj U (Matrix.diagonal v)) =
      (1 / 2 : ℝ) * ∑ i, ((v i) ^ 2).im ^ 2 := by
  rw [oppositeBook_unitaryConj hU, oppositeBook_diagonal]

lemma frobeniusSq_diagonal (v : n → ℂ) :
    ‖Matrix.diagonal v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.diagonal_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2),
    norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num),
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma frobeniusSq_unitaryConj {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) :
    ‖unitaryConj U K‖ ^ 2 = ‖K‖ ^ 2 := by
  have hUs : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU
  unfold unitaryConj
  rw [norm_mul_unitary _ hUs, norm_unitary_mul hU]

lemma frobeniusSq_unitary_diagonal {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℂ) :
    ‖unitaryConj U (Matrix.diagonal v)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [frobeniusSq_unitaryConj hU, frobeniusSq_diagonal]



/-- Conditional improper form of the exact `32`-budget.  The two analytic
inputs are integrability of `E⁻` and convergence of `‖K(t)‖²`; these are the
global inputs not encoded by a one-point derivative statement. -/
theorem integral_connectionBook_Ioi_of_flow {K : ℝ → Matrix n n ℂ}
    (hK : ∀ t, HasDerivAt K (velocity (K t)) t) (L : ℝ)
    (hInt : MeasureTheory.IntegrableOn (fun t => connectionBook (K t))
      (Set.Ici 0) MeasureTheory.volume)
    (hlim : Filter.Tendsto (fun t => ‖K t‖ ^ 2) Filter.atTop (nhds L)) :
    32 * (∫ t in Set.Ioi 0, connectionBook (K t) ∂MeasureTheory.volume) =
      ‖K 0‖ ^ 2 - L := by
  have hIoi : MeasureTheory.IntegrableOn (fun t => connectionBook (K t))
      (Set.Ioi 0) MeasureTheory.volume := hInt.mono_set Set.Ioi_subset_Ici_self
  have hEq : (fun T : ℝ => 32 * (∫ t in 0..T, connectionBook (K t))) =ᶠ[Filter.atTop]
      (fun T => ‖K 0‖ ^ 2 - ‖K T‖ ^ 2) := by
    apply Filter.eventually_atTop.2
    refine ⟨0, fun T hT => integral_connectionBook_flow hK ?_⟩
    have hsubset : Set.uIcc 0 T ⊆ Set.Ici 0 := by
      rw [Set.uIcc_of_le hT]
      exact Set.Icc_subset_Ici_self
    exact (hInt.mono_set hsubset).intervalIntegrable
  have hleft := (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hIoi Filter.tendsto_id).const_mul 32
  have hright := hlim.const_sub (‖K 0‖ ^ 2)
  have hright' : Filter.Tendsto
      (fun T : ℝ => 32 * (∫ t in 0..T, connectionBook (K t))) Filter.atTop
      (nhds (‖K 0‖ ^ 2 - L)) := Filter.Tendsto.congr' hEq.symm hright
  exact tendsto_nhds_unique hleft hright'

/-- The budget with a spectral normal form for the limiting Frobenius norm. -/
theorem integral_connectionBook_Ioi_spectral_limit {K : ℝ → Matrix n n ℂ}
    (hK : ∀ t, HasDerivAt K (velocity (K t)) t) (v : n → ℂ)
    (hInt : MeasureTheory.IntegrableOn (fun t => connectionBook (K t))
      (Set.Ici 0) MeasureTheory.volume)
    (hlim : Filter.Tendsto (fun t => ‖K t‖ ^ 2) Filter.atTop
      (nhds (∑ i, ‖v i‖ ^ 2))) :
    32 * (∫ t in Set.Ioi 0, connectionBook (K t) ∂MeasureTheory.volume) =
      ‖K 0‖ ^ 2 - ∑ i, ‖v i‖ ^ 2 :=
  integral_connectionBook_Ioi_of_flow hK _ hInt hlim



lemma continuous_frobeniusSq {X : Type*} [TopologicalSpace X]
    {K : X → Matrix n n ℂ} (hK : Continuous K) :
    Continuous (fun x => ‖K x‖ ^ 2) := by
  have heq : (fun x => ‖K x‖ ^ 2) =
      (fun x => ∑ i, ∑ j, ‖K x i j‖ ^ 2) := funext (fun _ => norm_sq_eq_sum _)
  rw [heq]
  apply continuous_finset_sum Finset.univ
  intro i hi
  apply continuous_finset_sum Finset.univ
  intro j hj
  exact (((continuous_apply j).comp ((continuous_apply i).comp hK)).norm).pow 2

lemma continuous_defect : Continuous (fun K : Matrix n n ℂ => defect K) := by
  have hId : Continuous (fun K : Matrix n n ℂ => K) := continuous_id
  have hAdj : Continuous (fun K : Matrix n n ℂ => Kᴴ) := hId.matrix_conjTranspose
  exact (hId.matrix_mul hAdj).sub (hAdj.matrix_mul hId)

lemma continuous_connectionBook : Continuous (connectionBook (n := n)) := by
  change Continuous (fun K : Matrix n n ℂ => (1 / 8 : ℝ) * ‖defect K‖ ^ 2)
  exact (continuous_frobeniusSq continuous_defect).const_mul (1 / 8)

lemma continuous_skewSquare : Continuous (fun K : Matrix n n ℂ => K ^ 2 - Kᴴ ^ 2) := by
  have hId : Continuous (fun K : Matrix n n ℂ => K) := continuous_id
  have hAdj : Continuous (fun K : Matrix n n ℂ => Kᴴ) := hId.matrix_conjTranspose
  have hsq : Continuous (fun K : Matrix n n ℂ => K ^ 2) := by
    simpa only [pow_two] using hId.matrix_mul hId
  have hAsq : Continuous (fun K : Matrix n n ℂ => Kᴴ ^ 2) := by
    simpa only [pow_two] using hAdj.matrix_mul hAdj
  exact hsq.sub hAsq

lemma continuous_oppositeBook : Continuous (oppositeBook (n := n)) := by
  change Continuous (fun K : Matrix n n ℂ => (1 / 8 : ℝ) * ‖K ^ 2 - Kᴴ ^ 2‖ ^ 2)
  exact (continuous_frobeniusSq continuous_skewSquare).const_mul (1 / 8)

lemma tendsto_connectionBook {K : ℝ → Matrix n n ℂ} {N : Matrix n n ℂ}
    (hK : Filter.Tendsto K Filter.atTop (nhds N)) :
    Filter.Tendsto (fun t => connectionBook (K t)) Filter.atTop
      (nhds (connectionBook N)) :=
  continuous_connectionBook.continuousAt.tendsto.comp hK

lemma tendsto_oppositeBook {K : ℝ → Matrix n n ℂ} {N : Matrix n n ℂ}
    (hK : Filter.Tendsto K Filter.atTop (nhds N)) :
    Filter.Tendsto (fun t => oppositeBook (K t)) Filter.atTop
      (nhds (oppositeBook N)) :=
  continuous_oppositeBook.continuousAt.tendsto.comp hK

lemma unitaryConj_mul {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A B : Matrix n n ℂ) : unitaryConj U (A * B) = unitaryConj U A * unitaryConj U B := by
  have hu : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').1 hU
  simp only [unitaryConj]
  calc
    U * (A * B) * Uᴴ = U * A * (Uᴴ * U) * B * Uᴴ := by
      rw [hu, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = (U * A * Uᴴ) * (U * B * Uᴴ) := by simp only [Matrix.mul_assoc]

lemma unitaryConj_defect {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (K : Matrix n n ℂ) : defect (unitaryConj U K) = unitaryConj U (defect K) := by
  simp only [defect, comm, unitaryConj_adj, ← unitaryConj_mul hU]
  simp [unitaryConj, Matrix.mul_sub, Matrix.sub_mul]

/-- The connection book is also unitarily invariant. -/
theorem connectionBook_unitaryConj {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (K : Matrix n n ℂ) :
    connectionBook (unitaryConj U K) = connectionBook K := by
  rw [connectionBook, connectionBook, unitaryConj_defect hU]
  have hUs : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU
  unfold unitaryConj
  rw [norm_mul_unitary _ hUs, norm_unitary_mul hU]

lemma defect_diagonal (v : n → ℂ) : defect (Matrix.diagonal v) = 0 := by
  simp [defect, comm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    mul_comm]

lemma connectionBook_unitary_diagonal_zero {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℂ) :
    connectionBook (unitaryConj U (Matrix.diagonal v)) = 0 := by
  rw [connectionBook_unitaryConj hU, connectionBook, defect_diagonal]
  simp

/-- Conditional terminal opposite book from convergence to a unitary spectral
normal form. -/
theorem tendsto_oppositeBook_spectral_limit {K : ℝ → Matrix n n ℂ}
    {U : Matrix n n ℂ} (v : n → ℂ)
    (hK : Filter.Tendsto K Filter.atTop
      (nhds (unitaryConj U (Matrix.diagonal v))))
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Filter.Tendsto (fun t => oppositeBook (K t)) Filter.atTop
      (nhds ((1 / 2 : ℝ) * ∑ i, ((v i) ^ 2).im ^ 2)) := by
  rw [← oppositeBook_unitary_diagonal hU]
  exact tendsto_oppositeBook hK

/-- Conditional terminal connection book: it vanishes at the normal limit. -/
theorem tendsto_connectionBook_spectral_limit_zero {K : ℝ → Matrix n n ℂ}
    {U : Matrix n n ℂ} (v : n → ℂ)
    (hK : Filter.Tendsto K Filter.atTop
      (nhds (unitaryConj U (Matrix.diagonal v))))
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Filter.Tendsto (fun t => connectionBook (K t)) Filter.atTop (nhds 0) := by
  rw [← connectionBook_unitary_diagonal_zero hU]
  exact tendsto_connectionBook hK



/-- Along a globally supplied relaxation flow, the connection book is
nonincreasing. -/
theorem antitone_connectionBook_flow {K : ℝ → Matrix n n ℂ}
    (hK : ∀ t, HasDerivAt K (velocity (K t)) t) :
    Antitone (fun t => connectionBook (K t)) := by
  apply antitone_of_deriv_nonpos
    (fun t => (hasDerivAt_connectionBook_flow (hK t)).differentiableAt)
  intro t
  rw [(hasDerivAt_connectionBook_flow (hK t)).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Along a globally supplied relaxation flow, the opposite book is
nonincreasing. -/
theorem antitone_oppositeBook_flow {K : ℝ → Matrix n n ℂ}
    (hK : ∀ t, HasDerivAt K (velocity (K t)) t) :
    Antitone (fun t => oppositeBook (K t)) := by
  apply antitone_of_deriv_nonpos
    (fun t => (hasDerivAt_oppositeBook_flow_literal (hK t)).differentiableAt)
  intro t
  rw [(hasDerivAt_oppositeBook_flow_literal (hK t)).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)


end RelationalAtlas.B201

/- Automated axiom audit: every theorem and lemma in this file. -/
#print axioms RelationalAtlas.B201.commute_square_star_of_isStarNormal
#print axioms RelationalAtlas.B201.cinner_self
#print axioms RelationalAtlas.B201.norm_sq_eq_sum
#print axioms RelationalAtlas.B201.complex_re_sum
#print axioms RelationalAtlas.B201.inner_eq_pair
#print axioms RelationalAtlas.B201.defect_hermitian
#print axioms RelationalAtlas.B201.pair_flow_direction
#print axioms RelationalAtlas.B201.inner_flow_direction
#print axioms RelationalAtlas.B201.hasDerivAt_conjTranspose
#print axioms RelationalAtlas.B201.hasDerivAt_matrix_mul
#print axioms RelationalAtlas.B201.hasDerivAt_defect
#print axioms RelationalAtlas.B201.hasDerivAt_frobeniusSq_flow
#print axioms RelationalAtlas.B201.pair_conj
#print axioms RelationalAtlas.B201.pair_comm_left
#print axioms RelationalAtlas.B201.pair_comm_right
#print axioms RelationalAtlas.B201.pair_add_right
#print axioms RelationalAtlas.B201.inner_defect_tangent
#print axioms RelationalAtlas.B201.hasDerivAt_connectionBook_flow
#print axioms RelationalAtlas.B201.pair_sub_right
#print axioms RelationalAtlas.B201.pair_conjTranspose_right
#print axioms RelationalAtlas.B201.pair_adj_self_comm
#print axioms RelationalAtlas.B201.pair_comm_self_adj
#print axioms RelationalAtlas.B201.trace_rotate4_right
#print axioms RelationalAtlas.B201.trace_rotate4_left
#print axioms RelationalAtlas.B201.pair_comm_comm_sq
#print axioms RelationalAtlas.B201.obstruction_eq_comm_square
#print axioms RelationalAtlas.B201.pair_square_defect
#print axioms RelationalAtlas.B201.velocity_eq_comm_lax
#print axioms RelationalAtlas.B201.lax_hermitian
#print axioms RelationalAtlas.B201.comm_smul_left
#print axioms RelationalAtlas.B201.pair_neg_left
#print axioms RelationalAtlas.B201.pair_sub_left
#print axioms RelationalAtlas.B201.inner_sub_conjTranspose
#print axioms RelationalAtlas.B201.skewSquare_hermitian
#print axioms RelationalAtlas.B201.inner_skewSquare_comm
#print axioms RelationalAtlas.B201.inner_square_defect
#print axioms RelationalAtlas.B201.inner_square_lax
#print axioms RelationalAtlas.B201.hasDerivAt_sq
#print axioms RelationalAtlas.B201.hasDerivAt_skewSquare
#print axioms RelationalAtlas.B201.lax_square_tangent
#print axioms RelationalAtlas.B201.hasDerivAt_oppositeBook_flow
#print axioms RelationalAtlas.B201.hasDerivAt_oppositeBook_flow_literal
#print axioms RelationalAtlas.B201.trace_comm
#print axioms RelationalAtlas.B201.hasDerivAt_trace
#print axioms RelationalAtlas.B201.hasDerivAt_lax_pow
#print axioms RelationalAtlas.B201.hasDerivAt_trace_pow_lax
#print axioms RelationalAtlas.B201.hasDerivAt_trace_pow_flow
#print axioms RelationalAtlas.B201.comm_eq_zero_iff_commute
#print axioms RelationalAtlas.B201.normal_square_of_obstruction_zero
#print axioms RelationalAtlas.B201.obstruction_zero_of_normal_square
#print axioms RelationalAtlas.B201.obstruction_zero_iff_normal_square
#print axioms RelationalAtlas.B201.deriv_oppositeBook_eq_zero_iff
#print axioms RelationalAtlas.B201.diagonal_skewSquare
#print axioms RelationalAtlas.B201.oppositeBook_diagonal
#print axioms RelationalAtlas.B201.integral_connectionBook_flow
#print axioms RelationalAtlas.B201.norm_sq_eq_re_trace
#print axioms RelationalAtlas.B201.norm_unitary_mul
#print axioms RelationalAtlas.B201.norm_mul_unitary
#print axioms RelationalAtlas.B201.unitaryConj_sq
#print axioms RelationalAtlas.B201.unitaryConj_adj
#print axioms RelationalAtlas.B201.unitaryConj_skewSquare
#print axioms RelationalAtlas.B201.oppositeBook_unitaryConj
#print axioms RelationalAtlas.B201.oppositeBook_unitary_diagonal
#print axioms RelationalAtlas.B201.frobeniusSq_diagonal
#print axioms RelationalAtlas.B201.frobeniusSq_unitaryConj
#print axioms RelationalAtlas.B201.frobeniusSq_unitary_diagonal
#print axioms RelationalAtlas.B201.integral_connectionBook_Ioi_of_flow
#print axioms RelationalAtlas.B201.integral_connectionBook_Ioi_spectral_limit
#print axioms RelationalAtlas.B201.continuous_frobeniusSq
#print axioms RelationalAtlas.B201.continuous_defect
#print axioms RelationalAtlas.B201.continuous_connectionBook
#print axioms RelationalAtlas.B201.continuous_skewSquare
#print axioms RelationalAtlas.B201.continuous_oppositeBook
#print axioms RelationalAtlas.B201.tendsto_connectionBook
#print axioms RelationalAtlas.B201.tendsto_oppositeBook
#print axioms RelationalAtlas.B201.unitaryConj_mul
#print axioms RelationalAtlas.B201.unitaryConj_defect
#print axioms RelationalAtlas.B201.connectionBook_unitaryConj
#print axioms RelationalAtlas.B201.defect_diagonal
#print axioms RelationalAtlas.B201.connectionBook_unitary_diagonal_zero
#print axioms RelationalAtlas.B201.tendsto_oppositeBook_spectral_limit
#print axioms RelationalAtlas.B201.tendsto_connectionBook_spectral_limit_zero
#print axioms RelationalAtlas.B201.antitone_connectionBook_flow
#print axioms RelationalAtlas.B201.antitone_oppositeBook_flow


/-! ## B204 — the Schur factorisation and the protection condition

Integrated from `.ultramath/smwvp3cvb/m10/B204.lean`.
-/

/-!
# B204: the one-site Schur-remainder formula for determinant log-odds

For a real covariance block `C`, define its offset by
`τ(C) = log (det (1 - C) / det C)`.  We extend a block by one site,
using the last index `Unit`, and prove the two Schur determinant factorizations
and both the exponential and logarithmic forms of B204.
-/

open Matrix
open scoped Matrix

namespace RelationalAtlas.B204

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The symmetric block matrix obtained by adding one site to `CB`. -/
def extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) :
    Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ :=
  Matrix.fromBlocks CB c cᵀ (fun _ _ => cxx)

/-- The Schur remainder on the occupied side. -/
def s1 (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) : ℝ :=
  cxx - (cᵀ * CB⁻¹ * c) () ()

/-- The Schur remainder on the empty side. -/
def s0 (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) : ℝ :=
  1 - cxx - (cᵀ * (1 - CB)⁻¹ * c) () ()

/-- The empty/full determinant odds, i.e. `exp τ`. -/
def expOffset {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ) : ℝ :=
  (1 - C).det / C.det

/-- The determinant log-odds, empty side over full side. -/
def offset {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ) : ℝ :=
  Real.log (expOffset C)

lemma one_sub_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) :
    1 - extend CB c cxx =
      Matrix.fromBlocks (1 - CB) (-c) (-cᵀ) (fun _ _ => 1 - cxx) := by
  ext (i | i) (j | j) <;>
    simp [extend, Matrix.fromBlocks, Matrix.one_apply]

lemma det_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ)
    (hCB : IsUnit CB.det) :
    (extend CB c cxx).det = CB.det * s1 CB c cxx := by
  letI := Matrix.invertibleOfIsUnitDet CB hCB
  rw [extend, Matrix.det_fromBlocks₁₁ CB c cᵀ (fun _ _ => cxx),
    Matrix.det_eq_elem_of_subsingleton _ ()]
  simp [s1, Matrix.invOf_eq_nonsing_inv]
  left
  rfl

lemma det_one_sub_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ)
    (hCB : IsUnit (1 - CB).det) :
    (1 - extend CB c cxx).det = (1 - CB).det * s0 CB c cxx := by
  letI := Matrix.invertibleOfIsUnitDet (1 - CB) hCB
  rw [one_sub_extend, Matrix.det_fromBlocks₁₁ (1 - CB) (-c) (-cᵀ)
    (fun _ _ => 1 - cxx), Matrix.det_eq_elem_of_subsingleton _ ()]
  simp [s0, Matrix.invOf_eq_nonsing_inv, Matrix.neg_mul, Matrix.mul_neg]
  left
  rfl

/-- The exponential form of the one-site identity.  No positivity is needed here:
nonsingularity of the two interior diagonal blocks suffices. -/
lemma expOffset_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ)
    (hCB : IsUnit CB.det) (hECB : IsUnit (1 - CB).det) :
    expOffset (extend CB c cxx) =
      expOffset CB * (s0 CB c cxx / s1 CB c cxx) := by
  unfold expOffset
  rw [det_one_sub_extend CB c cxx hECB, det_extend CB c cxx hCB]
  exact (div_mul_div_comm _ _ _ _).symm

/-- The leading principal block of the extension really is `CB`. -/
lemma submatrix_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) :
    (extend CB c cxx).submatrix Sum.inl Sum.inl = CB := by
  ext i j
  rfl

/-- The leading principal block of the complementary extension is `1 - CB`. -/
lemma submatrix_one_sub_extend (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (cxx : ℝ) :
    (1 - extend CB c cxx).submatrix Sum.inl Sum.inl = 1 - CB := by
  ext i j
  simp [extend, Matrix.fromBlocks, Matrix.one_apply]

lemma posDef_interior {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) : CB.PosDef := by
  rw [← submatrix_extend CB c cxx]
  exact hC.submatrix Sum.inl_injective

lemma posDef_one_sub_interior {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (1 - extend CB c cxx).PosDef) : (1 - CB).PosDef := by
  rw [← submatrix_one_sub_extend CB c cxx]
  exact hC.submatrix Sum.inl_injective

lemma isUnit_det_interior {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) : IsUnit CB.det :=
  (Matrix.isUnit_iff_isUnit_det CB).mp (posDef_interior hC).isUnit

lemma isUnit_det_one_sub_interior {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (1 - extend CB c cxx).PosDef) : IsUnit (1 - CB).det :=
  (Matrix.isUnit_iff_isUnit_det (1 - CB)).mp (posDef_one_sub_interior hC).isUnit

/-- Occupancy positivity gives a positive full-side Schur remainder. -/
lemma s1_pos {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) : 0 < s1 CB c cxx := by
  have hdet : (extend CB c cxx).det = CB.det * s1 CB c cxx :=
    det_extend CB c cxx (isUnit_det_interior hC)
  have hprod : 0 < CB.det * s1 CB c cxx := by
    rw [← hdet]
    exact hC.det_pos
  exact (mul_pos_iff_of_pos_left (posDef_interior hC).det_pos).mp hprod

/-- Strictly below the identity gives a positive empty-side Schur remainder. -/
lemma s0_pos {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (1 - extend CB c cxx).PosDef) : 0 < s0 CB c cxx := by
  have hdet : (1 - extend CB c cxx).det = (1 - CB).det * s0 CB c cxx :=
    det_one_sub_extend CB c cxx (isUnit_det_one_sub_interior hC)
  have hprod : 0 < (1 - CB).det * s0 CB c cxx := by
    rw [← hdet]
    exact hC.det_pos
  exact (mul_pos_iff_of_pos_left (posDef_one_sub_interior hC).det_pos).mp hprod

lemma expOffset_pos {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n ℝ}
    (hC : C.PosDef) (hEC : (1 - C).PosDef) : 0 < expOffset C :=
  div_pos hEC.det_pos hC.det_pos

/-- The literal `0 < C < I` hypotheses imply the displayed exponential identity. -/
lemma expOffset_extend_of_posDef {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef) :
    expOffset (extend CB c cxx) =
      expOffset CB * (s0 CB c cxx / s1 CB c cxx) :=
  expOffset_extend CB c cxx (isUnit_det_interior hC)
    (isUnit_det_one_sub_interior hEC)

/-- A protected interior has unit determinant odds. -/
lemma expOffset_eq_one_of_protected {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosDef) (hprotected : C.det = (1 - C).det) :
    expOffset C = 1 := by
  unfold expOffset
  rw [← hprotected, div_self hC.det_pos.ne']

/-- Protected-interior form: the old block contributes no factor. -/
lemma expOffset_extend_protected {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef)
    (hprotected : CB.det = (1 - CB).det) :
    expOffset (extend CB c cxx) = s0 CB c cxx / s1 CB c cxx := by
  rw [expOffset_extend_of_posDef hC hEC,
    expOffset_eq_one_of_protected (posDef_interior hC) hprotected, one_mul]

/-- `exp (offset C)` recovers the determinant odds under `0 < C < I`. -/
lemma exp_offset {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n ℝ}
    (hC : C.PosDef) (hEC : (1 - C).PosDef) :
    Real.exp (offset C) = expOffset C :=
  Real.exp_log (expOffset_pos hC hEC)

/-- The displayed statement with the exponential symbols written explicitly. -/
theorem B204_exponential {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef) :
    Real.exp (offset (extend CB c cxx)) =
      Real.exp (offset CB) * (s0 CB c cxx / s1 CB c cxx) := by
  rw [exp_offset hC hEC, expOffset_extend_of_posDef hC hEC,
    exp_offset (posDef_interior hC) (posDef_one_sub_interior hEC)]

/-- Logarithmic form: the old offset carries over and the two remainders add
exactly one log-odds factor. -/
theorem B204_logarithmic {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef) :
    offset (extend CB c cxx) =
      offset CB + Real.log (s0 CB c cxx / s1 CB c cxx) := by
  unfold offset
  rw [expOffset_extend_of_posDef hC hEC]
  exact Real.log_mul
    (expOffset_pos (posDef_interior hC) (posDef_one_sub_interior hEC)).ne'
    (div_pos (s0_pos hEC) (s1_pos hC)).ne'

/-- The second displayed formula, for a protected interior. -/
theorem B204_protected {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef)
    (hprotected : CB.det = (1 - CB).det) :
    offset (extend CB c cxx) = Real.log (s0 CB c cxx / s1 CB c cxx) := by
  rw [B204_logarithmic hC hEC]
  have hzero : offset CB = 0 := by
    unfold offset
    rw [expOffset_eq_one_of_protected (posDef_interior hC) hprotected, Real.log_one]
  rw [hzero, zero_add]

/-- Trading the two Schur remainders reverses the protected offset's sign. -/
theorem B204_negative_iff {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef)
    (hprotected : CB.det = (1 - CB).det) :
    offset (extend CB c cxx) < 0 ↔ s0 CB c cxx < s1 CB c cxx := by
  rw [B204_protected hC hEC hprotected,
    Real.log_neg_iff (div_pos (s0_pos hEC) (s1_pos hC)),
    div_lt_one (s1_pos hC)]

/-- Positive protected offset is exactly the reverse residual inequality. -/
theorem B204_positive_iff {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef)
    (hprotected : CB.det = (1 - CB).det) :
    0 < offset (extend CB c cxx) ↔ s1 CB c cxx < s0 CB c cxx := by
  rw [B204_protected hC hEC hprotected,
    Real.log_pos_iff (div_pos (s0_pos hEC) (s1_pos hC)).le,
    one_lt_div (s1_pos hC)]

/-- The zero protected offset occurs exactly when the two residuals coincide. -/
theorem B204_zero_iff {CB : Matrix m m ℝ} {c : Matrix m Unit ℝ} {cxx : ℝ}
    (hC : (extend CB c cxx).PosDef) (hEC : (1 - extend CB c cxx).PosDef)
    (hprotected : CB.det = (1 - CB).det) :
    offset (extend CB c cxx) = 0 ↔ s0 CB c cxx = s1 CB c cxx := by
  rw [B204_protected hC hEC hprotected]
  constructor
  · intro hlog
    have hone : s0 CB c cxx / s1 CB c cxx = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos (s0_pos hEC) (s1_pos hC)) hlog
    exact (div_eq_one_iff_eq (s1_pos hC).ne').mp hone
  · intro heq
    rw [heq, div_self (s1_pos hC).ne', Real.log_one]

/-- In the one-dimensional case, protection is precisely symmetry about `1/2`.
In particular it does not follow from `0 < C < I` alone. -/
lemma protected_fin_one_iff (C : Matrix (Fin 1) (Fin 1) ℝ) :
    C.det = (1 - C).det ↔ C 0 0 = 1 / 2 := by
  rw [Matrix.det_fin_one, Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq]
  constructor <;> intro h <;> linarith

end

end RelationalAtlas.B204

#print axioms RelationalAtlas.B204.one_sub_extend
#print axioms RelationalAtlas.B204.det_extend
#print axioms RelationalAtlas.B204.det_one_sub_extend
#print axioms RelationalAtlas.B204.expOffset_extend
#print axioms RelationalAtlas.B204.submatrix_extend
#print axioms RelationalAtlas.B204.submatrix_one_sub_extend
#print axioms RelationalAtlas.B204.posDef_interior
#print axioms RelationalAtlas.B204.posDef_one_sub_interior
#print axioms RelationalAtlas.B204.isUnit_det_interior
#print axioms RelationalAtlas.B204.isUnit_det_one_sub_interior
#print axioms RelationalAtlas.B204.s1_pos
#print axioms RelationalAtlas.B204.s0_pos
#print axioms RelationalAtlas.B204.expOffset_pos
#print axioms RelationalAtlas.B204.expOffset_extend_of_posDef
#print axioms RelationalAtlas.B204.expOffset_eq_one_of_protected
#print axioms RelationalAtlas.B204.expOffset_extend_protected
#print axioms RelationalAtlas.B204.exp_offset
#print axioms RelationalAtlas.B204.B204_exponential
#print axioms RelationalAtlas.B204.B204_logarithmic
#print axioms RelationalAtlas.B204.B204_protected
#print axioms RelationalAtlas.B204.B204_negative_iff
#print axioms RelationalAtlas.B204.B204_positive_iff
#print axioms RelationalAtlas.B204.B204_zero_iff
#print axioms RelationalAtlas.B204.protected_fin_one_iff


/-! ## B205 — the symmetry kernel, and even blocks that carry half modes

Integrated from `.ultramath/smwvp3cvb/m7/B205.lean`.
-/
/-
B205: Rice--Mele odd-block pin, Nambu pairing, and a dimer-limit correction.

Source read directly from the pinned v7 archive:
`cards/html/B205.html`, SHA-256
`7484a8a88420c77e59cac5a2437fe31e9aa1165458d87eb0405b702efe343e54`.
The card says "Rice--Mele: ν = ½ in odd blocks only", "Kitaev: two modes
→ ½ at every length", "c ↦ ic reverses every pairing term", and "Nambu
spectrum paired ν ↔ 1 − ν ⇒ offset 0".  Its Carry hypotheses impose no
nonzero-hopping condition, and its Check hypotheses are `v=0` and `|μ|<2t`.

This file proves the symmetry algebra in a real finite gauge.  The matrix `C`
is a restricted single-particle correlation matrix and `S` is the relevant
sublattice/particle-hole symmetry.  No diagonalizability is assumed: the
odd-block theorem obtains an actual eigenvector from the determinant.

The phrase "odd blocks only" is false literally at the allowed dimer limit
`t1=1, t2=0, v=0`: an explicit two-dimer witness below has an even block
`B0,A1` with restricted correlation `(1/2) • 1`.  Thus existence in odd blocks
is general, but exclusion in even blocks requires an extra nondegeneracy
hypothesis.  The topological Majorana convergence rate and the many-body
Kitaev statement are not formalized here.
-/


noncomputable section

namespace AtlasB205

open Matrix

variable {n : Type*}

/-- The matrix whose determinant vanishes exactly at an occupation eigenvalue `ν`. -/
def charMatrix [DecidableEq n] (C : Matrix n n ℝ) (ν : ℝ) : Matrix n n ℝ :=
  ν • 1 - C

/-- Half-filled ground-state correlation associated with a flattened Hamiltonian `Γ`. -/
def correlation [DecidableEq n] (Γ : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (1 - Γ)

/-- `S C S = 1 - C` is occupation pairing `ν ↔ 1 - ν`. -/
def SelfDual [Fintype n] [DecidableEq n] (C S : Matrix n n ℝ) : Prop :=
  S * C * S = 1 - C

lemma correlation_selfDual [Fintype n] [DecidableEq n] {Γ S : Matrix n n ℝ}
    (hS : S * S = 1) (hΓ : S * Γ * S = -Γ) :
    SelfDual (correlation Γ) S := by
  unfold SelfDual correlation
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hS, hΓ]
  module

lemma selfDual_conj_charMatrix [Fintype n] [DecidableEq n] {C S : Matrix n n ℝ}
    (hS : S * S = 1) (hC : SelfDual C S) (ν : ℝ) :
    S * charMatrix C ν * S = -charMatrix C (1 - ν) := by
  unfold charMatrix
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hS]
  rw [show S * C * S = 1 - C from hC]
  module

lemma selfDual_det_charMatrix [Fintype n] [DecidableEq n] {C S : Matrix n n ℝ}
    (hS : S * S = 1) (hC : SelfDual C S) (ν : ℝ) :
    (charMatrix C ν).det =
      (-1 : ℝ) ^ Fintype.card n * (charMatrix C (1 - ν)).det := by
  have hdetS : S.det * S.det = 1 := by
    calc
      S.det * S.det = (S * S).det := (Matrix.det_mul S S).symm
      _ = 1 := by rw [hS, Matrix.det_one]
  have hconj := congrArg Matrix.det (selfDual_conj_charMatrix hS hC ν)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_neg] at hconj
  calc
    (charMatrix C ν).det = S.det * ((charMatrix C ν).det * S.det) := by
      calc
        (charMatrix C ν).det = (S.det * S.det) * (charMatrix C ν).det := by
          rw [hdetS, one_mul]
        _ = S.det * ((charMatrix C ν).det * S.det) := by ring
    _ = (-1 : ℝ) ^ Fintype.card n * (charMatrix C (1 - ν)).det := by
      simpa only [mul_assoc] using hconj

lemma selfDual_det_half [Fintype n] [DecidableEq n] {C S : Matrix n n ℝ}
    (hS : S * S = 1) (hC : SelfDual C S) (hodd : Odd (Fintype.card n)) :
    (charMatrix C (1 / 2 : ℝ)).det = 0 := by
  have h := selfDual_det_charMatrix hS hC (1 / 2 : ℝ)
  have hν : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hν, hodd.neg_one_pow] at h
  linarith

/-- Odd-dimensional self-duality forces an actual half-occupation eigenvector. -/
theorem exists_half_mode_of_selfDual_of_odd [Fintype n] [DecidableEq n]
    {C S : Matrix n n ℝ} (hS : S * S = 1) (hC : SelfDual C S)
    (hodd : Odd (Fintype.card n)) :
    ∃ x : n → ℝ, x ≠ 0 ∧ C *ᵥ x = (1 / 2 : ℝ) • x := by
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (selfDual_det_half hS hC hodd)
  refine ⟨x, hx0, ?_⟩
  have hx' : (1 / 2 : ℝ) • x - C *ᵥ x = 0 := by
    simpa [charMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec] using hx
  exact (sub_eq_zero.mp hx').symm

lemma mul_selfDual [Fintype n] [DecidableEq n] {C S : Matrix n n ℝ}
    (hS : S * S = 1) (hC : SelfDual C S) : C * S = S * (1 - C) := by
  calc
    C * S = (S * S) * (C * S) := by rw [hS, Matrix.one_mul]
    _ = S * (S * C * S) := by simp only [Matrix.mul_assoc]
    _ = S * (1 - C) := by rw [show S * C * S = 1 - C from hC]

/-- Direct Rice--Mele form: an odd, no-staggering block has a half mode. -/
theorem riceMele_odd_block_half_mode [Fintype n] [DecidableEq n]
    {Γ S : Matrix n n ℝ} (hS : S * S = 1) (hΓ : S * Γ * S = -Γ)
    (hodd : Odd (Fintype.card n)) :
    ∃ x : n → ℝ, x ≠ 0 ∧ correlation Γ *ᵥ x = (1 / 2 : ℝ) • x :=
  exists_half_mode_of_selfDual_of_odd hS (correlation_selfDual hS hΓ) hodd

/-- Self-duality pairs every eigenvector, not merely the determinant spectrum. -/
theorem selfDual_eigenvector_pair [Fintype n] [DecidableEq n]
    {C S : Matrix n n ℝ} (hS : S * S = 1) (hC : SelfDual C S)
    {ν : ℝ} {x : n → ℝ} (hx : C *ᵥ x = ν • x) :
    C *ᵥ (S *ᵥ x) = (1 - ν) • (S *ᵥ x) := by
  calc
    C *ᵥ (S *ᵥ x) = (C * S) *ᵥ x := Matrix.mulVec_mulVec x C S
    _ = (S * (1 - C)) *ᵥ x := congrArg (fun M : Matrix n n ℝ => M *ᵥ x) (mul_selfDual hS hC)
    _ = S *ᵥ ((1 - C) *ᵥ x) := (Matrix.mulVec_mulVec x S (1 - C)).symm
    _ = S *ᵥ ((1 - ν) • x) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_smul, one_smul]
    _ = (1 - ν) • (S *ᵥ x) := Matrix.mulVec_smul S (1 - ν) x

lemma selfDual_paired_vector_ne_zero [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S * S = 1) {x : n → ℝ} (hx : x ≠ 0) :
    S *ᵥ x ≠ 0 := by
  intro hSx
  apply hx
  have h := congrArg (fun y : n → ℝ => S *ᵥ y) hSx
  rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec] at h
  simpa using h

/-- A single fermionic phase twist `c ↦ i*c`. -/
def phaseTwist (c : ℂ) : ℂ := Complex.I * c

/-- Number-conserving hopping, including the onsite chemical-potential special case. -/
def hoppingTerm (cᵢ cⱼ : ℂ) : ℂ := star cᵢ * cⱼ

/-- Annihilates a pair; this is the non-number-conserving Kitaev factor. -/
def pairingTerm (cᵢ cⱼ : ℂ) : ℂ := cᵢ * cⱼ

/-- The Hermitian-conjugate, pair-creation factor. -/
def creationPairingTerm (cᵢ cⱼ : ℂ) : ℂ := star cᵢ * star cⱼ

lemma star_phaseTwist (c : ℂ) : star (phaseTwist c) = -Complex.I * star c := by
  simp [phaseTwist, star_mul]
  ring

/-- The phase twist leaves every hopping and chemical-potential term fixed. -/
theorem phaseTwist_hoppingTerm (cᵢ cⱼ : ℂ) :
    hoppingTerm (phaseTwist cᵢ) (phaseTwist cⱼ) = hoppingTerm cᵢ cⱼ := by
  unfold hoppingTerm
  rw [star_phaseTwist]
  calc
    (-Complex.I * star cᵢ) * (Complex.I * cⱼ) =
        -(Complex.I * Complex.I) * (star cᵢ * cⱼ) := by ring
    _ = star cᵢ * cⱼ := by rw [Complex.I_mul_I]; ring

/-- The phase twist reverses every pair-annihilation term. -/
theorem phaseTwist_pairingTerm (cᵢ cⱼ : ℂ) :
    pairingTerm (phaseTwist cᵢ) (phaseTwist cⱼ) = -pairingTerm cᵢ cⱼ := by
  unfold pairingTerm phaseTwist
  calc
    (Complex.I * cᵢ) * (Complex.I * cⱼ) =
        (Complex.I * Complex.I) * (cᵢ * cⱼ) := by ring
    _ = -(cᵢ * cⱼ) := by rw [Complex.I_mul_I]; ring

/-- Its Hermitian conjugate is reversed as well, so the whole pairing
Hamiltonian changes sign, not just one side of it. -/
theorem phaseTwist_creationPairingTerm (cᵢ cⱼ : ℂ) :
    creationPairingTerm (phaseTwist cᵢ) (phaseTwist cⱼ) =
      -creationPairingTerm cᵢ cⱼ := by
  unfold creationPairingTerm
  rw [star_phaseTwist, star_phaseTwist]
  calc
    (-Complex.I * star cᵢ) * (-Complex.I * star cⱼ) =
        (Complex.I * Complex.I) * (star cᵢ * star cⱼ) := by ring
    _ = -(star cᵢ * star cⱼ) := by rw [Complex.I_mul_I]; ring

/-- Log-odds offset of one occupation. -/
def logOdds (ν : ℝ) : ℝ := Real.log (ν / (1 - ν))

/-- A Nambu pair has exactly cancelling log-odds, hence zero pair offset. -/
theorem logOdds_add_complement {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    logOdds ν + logOdds (1 - ν) = 0 := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hν1' : 1 - ν ≠ 0 := sub_ne_zero.mpr hν1.ne.symm
  have hratio : (1 - ν) / (1 - (1 - ν)) = (ν / (1 - ν))⁻¹ := by
    rw [show 1 - (1 - ν) = ν by ring]
    field_simp
  unfold logOdds
  rw [hratio, Real.log_inv]
  ring

/-- The two Rice--Mele dimers `A0-B0` and `A1-B1`, in the site order
`A0,B0,A1,B1`.  This is the no-staggering chain at `t1=1`, `t2=0`. -/
def dimerGamma : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

def dimerS : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, 1, -1]

/-- Occupation of the negative-energy band.  Since `dimerGamma² = 1`,
this is the ground-state spectral projector. -/
def dimerC : Matrix (Fin 4) (Fin 4) ℝ := correlation dimerGamma

/-- The even interval `B0,A1` (positions 1 and 2 in the zero-based order). -/
def blockIndex : Fin 2 → Fin 4 := ![1, 2]

def evenBlockC : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => dimerC (blockIndex i) (blockIndex j)

lemma dimerGamma_sq : dimerGamma * dimerGamma = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dimerGamma, Matrix.mul_apply, Fin.sum_univ_four]

lemma dimerS_sq : dimerS * dimerS = 1 := by
  rw [dimerS, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

lemma dimerS_gamma : SelfDual dimerC dimerS := by
  apply correlation_selfDual dimerS_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dimerS, dimerGamma, Matrix.mul_apply, Fin.sum_univ_four]

lemma dimerC_projector : dimerC * dimerC = dimerC := by
  unfold dimerC correlation
  have h := dimerGamma_sq
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, h]
  module

lemma dimerC_transpose : dimerCᵀ = dimerC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dimerC, correlation, dimerGamma, Matrix.transpose_apply]

lemma dimerC_trace : dimerC.trace = 2 := by
  norm_num [dimerC, correlation, dimerGamma, Matrix.trace, Fin.sum_univ_four]

/-- The refutation of the unqualified phrase "odd blocks only": the allowed,
no-staggering dimer limit has an even block whose restricted correlation is
exactly half the identity. -/
theorem evenBlockC_eq_half_one : evenBlockC = (1 / 2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenBlockC, dimerC, correlation, dimerGamma, blockIndex]

theorem evenBlockC_half_mode (x : Fin 2 → ℝ) :
    evenBlockC *ᵥ x = (1 / 2 : ℝ) • x := by
  rw [evenBlockC_eq_half_one, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem evenBlockC_nontrivial_half_mode :
    ∃ x : Fin 2 → ℝ, x ≠ 0 ∧ evenBlockC *ᵥ x = (1 / 2 : ℝ) • x := by
  refine ⟨![1, 0], by intro h; have h0 := congrFun h 0; norm_num at h0,
    evenBlockC_half_mode _⟩

/-- Packaged Lean counterexample: length two is even, while the compressed
no-staggering ground-state projector has a nonzero `ν=1/2` eigenvector. -/
theorem riceMele_odd_only_counterexample :
    Even (Fintype.card (Fin 2)) ∧
      dimerC * dimerC = dimerC ∧ dimerCᵀ = dimerC ∧ dimerC.trace = 2 ∧
      SelfDual dimerC dimerS ∧
      ∃ x : Fin 2 → ℝ, x ≠ 0 ∧ evenBlockC *ᵥ x = (1 / 2 : ℝ) • x :=
  ⟨by norm_num, dimerC_projector, dimerC_transpose, dimerC_trace,
    dimerS_gamma, evenBlockC_nontrivial_half_mode⟩

#print axioms correlation_selfDual
#print axioms selfDual_conj_charMatrix
#print axioms selfDual_det_charMatrix
#print axioms selfDual_det_half
#print axioms exists_half_mode_of_selfDual_of_odd
#print axioms mul_selfDual
#print axioms riceMele_odd_block_half_mode
#print axioms selfDual_eigenvector_pair
#print axioms selfDual_paired_vector_ne_zero
#print axioms star_phaseTwist
#print axioms phaseTwist_hoppingTerm
#print axioms phaseTwist_pairingTerm
#print axioms phaseTwist_creationPairingTerm
#print axioms logOdds_add_complement
#print axioms dimerGamma_sq
#print axioms dimerS_sq
#print axioms dimerS_gamma
#print axioms dimerC_projector
#print axioms dimerC_transpose
#print axioms dimerC_trace
#print axioms evenBlockC_eq_half_one
#print axioms evenBlockC_half_mode
#print axioms evenBlockC_nontrivial_half_mode
#print axioms riceMele_odd_only_counterexample

end AtlasB205


/-! ## shared finite-matrix kernel for the block

Integrated from `.ultramath/smwvp3cvb/m6/SixthBatchMatrix.lean`.
-/
/-
Self-contained finite-matrix infrastructure for the sixth book batch.

The energy is the squared Frobenius norm, not its square root.  The file keeps
unitary and projector hypotheses separate from the purely algebraic formulas.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace SixthBatchMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared Frobenius norm as an entry sum. -/
def frobSq (X : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (X i j)

/-- The Born weights of a change of basis. -/
def bornWeights (U : Matrix n n ℂ) : Matrix n n ℝ :=
  fun i j => Complex.normSq (U i j)

/-- The real transition overlap used in the rank-projector formula. -/
def transitionOverlap (P Q U : Matrix n n ℂ) : ℝ :=
  (P * (U * Q * Uᴴ)).trace.re

lemma frobSq_nonneg (X : Matrix n n ℂ) : 0 ≤ frobSq X := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma frobSq_eq_zero_iff (X : Matrix n n ℂ) : frobSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext i j
    have hij : Complex.normSq (X i j) = 0 := by
      have hi : ∑ j, Complex.normSq (X i j) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).1 h i
          (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Complex.normSq_nonneg _)).1 hi j (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp hij
  · rintro rfl
    simp [frobSq]

lemma frobSq_eq_re_trace (X : Matrix n n ℂ) :
    frobSq X = (Xᴴ * X).trace.re := by
  rw [frobSq, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma frobSq_conjTranspose (X : Matrix n n ℂ) : frobSq Xᴴ = frobSq X := by
  simp only [frobSq, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact Complex.normSq_conj _

lemma frobSq_add (X Y : Matrix n n ℂ) :
    frobSq (X + Y) = frobSq X + frobSq Y + 2 * (Xᴴ * Y).trace.re := by
  rw [frobSq_eq_re_trace, frobSq_eq_re_trace, frobSq_eq_re_trace]
  have hc : (Yᴴ * X).trace = star ((Xᴴ * Y).trace) := by
    calc
      (Yᴴ * X).trace = ((Xᴴ * Y)ᴴ).trace := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = star ((Xᴴ * Y).trace) := Matrix.trace_conjTranspose _
  have hre : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re]
  rw [hre]
  ring

lemma frobSq_neg (X : Matrix n n ℂ) : frobSq (-X) = frobSq X := by
  simp [frobSq]

lemma frobSq_sub (X Y : Matrix n n ℂ) :
    frobSq (X - Y) = frobSq X + frobSq Y - 2 * (Xᴴ * Y).trace.re := by
  have h := frobSq_add X (-Y)
  simpa [sub_eq_add_neg, Matrix.mul_neg, Matrix.trace_neg, frobSq_neg] using h

lemma frobSq_parallelogram (X Y : Matrix n n ℂ) :
    frobSq (X - Y) + frobSq (X + Y) = 2 * frobSq X + 2 * frobSq Y := by
  rw [frobSq_sub, frobSq_add]
  ring

lemma frobSq_real_smul (r : ℝ) (X : Matrix n n ℂ) :
    frobSq (r • X) = r ^ 2 * frobSq X := by
  have h : ∀ i j, Complex.normSq ((r • X) i j) =
      r ^ 2 * Complex.normSq (X i j) := by
    intro i j
    change Complex.normSq ((r : ℂ) * X i j) = _
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  simp only [frobSq, h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- The two unnormalised Hermitian/skew books have the fixed Frobenius budget. -/
lemma frobSq_adjoint_books_budget (X : Matrix n n ℂ) :
    frobSq (X + Xᴴ) + frobSq (X - Xᴴ) = 4 * frobSq X := by
  rw [frobSq_add, frobSq_sub, frobSq_conjTranspose]
  ring

/-- The same two books differ by four times the real trace of the square. -/
lemma frobSq_adjoint_books_difference (X : Matrix n n ℂ) :
    frobSq (X + Xᴴ) - frobSq (X - Xᴴ) = 4 * (X ^ 2).trace.re := by
  have hc : (Xᴴ * Xᴴ).trace = star ((X * X).trace) := by
    calc
      (Xᴴ * Xᴴ).trace = ((X * X)ᴴ).trace := by rw [Matrix.conjTranspose_mul]
      _ = star ((X * X).trace) := Matrix.trace_conjTranspose _
  have hre : (Xᴴ * Xᴴ).trace.re = (X * X).trace.re := by
    rw [hc, RCLike.star_def, Complex.conj_re]
  rw [frobSq_add, frobSq_sub]
  rw [hre]
  simp only [pow_two]
  ring


section Unitary

lemma frobSq_unitary_mul {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X : Matrix n n ℂ) : frobSq (U * X) = frobSq X := by
  have hU' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hU
  rw [frobSq_eq_re_trace, frobSq_eq_re_trace, Matrix.conjTranspose_mul]
  rw [show Xᴴ * Uᴴ * (U * X) = Xᴴ * (Uᴴ * U) * X by noncomm_ring]
  rw [hU', Matrix.mul_one]

lemma frobSq_mul_unitary (X : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : frobSq (X * U) = frobSq X := by
  have hUH : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU
  rw [← frobSq_conjTranspose (X * U), Matrix.conjTranspose_mul,
    frobSq_unitary_mul hUH, frobSq_conjTranspose]

lemma frobSq_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X : Matrix n n ℂ) : frobSq (U * X * Uᴴ) = frobSq X := by
  have hUH : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU
  rw [frobSq_mul_unitary _ hUH, frobSq_unitary_mul hU]

lemma trace_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X : Matrix n n ℂ) : (U * X * Uᴴ).trace = X.trace := by
  have hU' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hU
  calc
    (U * X * Uᴴ).trace = (U * (X * Uᴴ)).trace := by rw [Matrix.mul_assoc]
    _ = ((X * Uᴴ) * U).trace := Matrix.trace_mul_comm _ _
    _ = (X * (Uᴴ * U)).trace := by rw [Matrix.mul_assoc]
    _ = X.trace := by rw [hU', Matrix.mul_one]

lemma bornWeights_col_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (j : n) : ∑ i, bornWeights U i j = 1 := by
  have hU' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hU
  have h := congrArg (fun M : Matrix n n ℂ => (M j j).re) hU'
  simpa [bornWeights, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum] using h

lemma bornWeights_row_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (i : n) : ∑ j, bornWeights U i j = 1 := by
  have hU' : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).1 hU
  have h := congrArg (fun M : Matrix n n ℂ => (M i i).re) hU'
  simpa [bornWeights, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, Complex.re_sum] using h

lemma bornWeights_nonneg (U : Matrix n n ℂ) (i j : n) : 0 ≤ bornWeights U i j :=
  Complex.normSq_nonneg _

lemma bornWeights_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ j, bornWeights U i j = Fintype.card n := by
  calc
    (∑ i, ∑ j, bornWeights U i j) = ∑ _i : n, (1 : ℝ) :=
      Finset.sum_congr rfl fun i _ => bornWeights_row_sum hU i
    _ = Fintype.card n := by simp

end Unitary

section BornExpansion

/-- The Born-sum formula requires no unitarity: unitarity is used only for the
row and column sums of `W`. -/
lemma frobSq_diagonal_mul_sub_mul_diagonal (lambda mu : n → ℝ) (U : Matrix n n ℂ) :
    frobSq (Matrix.diagonal (fun i => (lambda i : ℂ)) * U -
      U * Matrix.diagonal (fun j => (mu j : ℂ))) =
    ∑ i, ∑ j, bornWeights U i j * (lambda i - mu j) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (lambda i : ℂ) * U i j - U i j * (mu j : ℂ) =
      U i j * ((lambda i - mu j : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [frobSq, bornWeights, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  rw [h, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- The opposite Born book, again with no unitarity hypothesis. -/
lemma frobSq_diagonal_mul_add_mul_diagonal (lambda mu : n → ℝ) (U : Matrix n n ℂ) :
    frobSq (Matrix.diagonal (fun i => (lambda i : ℂ)) * U +
      U * Matrix.diagonal (fun j => (mu j : ℂ))) =
    ∑ i, ∑ j, bornWeights U i j * (lambda i + mu j) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (lambda i : ℂ) * U i j + U i j * (mu j : ℂ) =
      U i j * ((lambda i + mu j : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [frobSq, bornWeights, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  rw [h, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Negating one diagonal field exchanges the two displayed Born sums. -/
lemma born_sum_neg (lambda mu : n → ℝ) (U : Matrix n n ℂ) :
    (∑ i, ∑ j, bornWeights U i j * (lambda i - (-mu j)) ^ 2) =
      ∑ i, ∑ j, bornWeights U i j * (lambda i + mu j) ^ 2 := by
  simp

end BornExpansion

section Projectors

lemma frobSq_of_projector {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) :
    frobSq P = P.trace.re := by
  rw [frobSq_eq_re_trace, hP, hPP]

lemma trace_conjugate_projector {Q U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : (U * Q * Uᴴ).trace.re = Q.trace.re := by
  rw [trace_unitary_conj hU]

/-- Exact projector energy in numerator form; no rank or nonzero-rank assumption
is needed. -/
lemma frobSq_projector_sub_conjugate {P Q U : Matrix n n ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    frobSq (P - U * Q * Uᴴ) =
      P.trace.re + Q.trace.re - 2 * transitionOverlap P Q U := by
  have hT : (U * Q * Uᴴ)ᴴ = U * Q * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
  have hTT : (U * Q * Uᴴ) * (U * Q * Uᴴ) = U * Q * Uᴴ := by
    have hU' : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hU
    calc
      (U * Q * Uᴴ) * (U * Q * Uᴴ) = U * Q * (Uᴴ * U) * Q * Uᴴ := by noncomm_ring
      _ = U * (Q * Q) * Uᴴ := by rw [hU']; noncomm_ring
      _ = U * Q * Uᴴ := by rw [hQQ]
  rw [frobSq_sub, hP, frobSq_of_projector hP hPP, frobSq_of_projector hT hTT,
    trace_conjugate_projector hU]
  rfl

lemma frobSq_projector_add_conjugate {P Q U : Matrix n n ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    frobSq (P + U * Q * Uᴴ) =
      P.trace.re + Q.trace.re + 2 * transitionOverlap P Q U := by
  have hT : (U * Q * Uᴴ)ᴴ = U * Q * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
  have hTT : (U * Q * Uᴴ) * (U * Q * Uᴴ) = U * Q * Uᴴ := by
    have hU' : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hU
    calc
      (U * Q * Uᴴ) * (U * Q * Uᴴ) = U * Q * (Uᴴ * U) * Q * Uᴴ := by noncomm_ring
      _ = U * (Q * Q) * Uᴴ := by rw [hU']; noncomm_ring
      _ = U * Q * Uᴴ := by rw [hQQ]
  rw [frobSq_add, hP, frobSq_of_projector hP hPP, frobSq_of_projector hT hTT,
    trace_conjugate_projector hU]
  rfl

/-- Rank-normalized form of the minus projector book. -/
lemma frobSq_projector_sub_eq_two_rank {P Q U : Matrix n n ℂ} {k : ℕ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hk : k ≠ 0)
    (htrP : P.trace = (k : ℂ)) (htrQ : Q.trace = (k : ℂ)) :
    frobSq (P - U * Q * Uᴴ) =
      2 * (k : ℝ) * (1 - transitionOverlap P Q U / (k : ℝ)) := by
  rw [frobSq_projector_sub_conjugate hP hPP hQ hQQ hU, htrP, htrQ]
  simp only [Complex.natCast_re]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp
  ring

/-- Rank-normalized form of the plus projector book. -/
lemma frobSq_projector_add_eq_two_rank {P Q U : Matrix n n ℂ} {k : ℕ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hk : k ≠ 0)
    (htrP : P.trace = (k : ℂ)) (htrQ : Q.trace = (k : ℂ)) :
    frobSq (P + U * Q * Uᴴ) =
      2 * (k : ℝ) * (1 + transitionOverlap P Q U / (k : ℝ)) := by
  rw [frobSq_projector_add_conjugate hP hPP hQ hQQ hU, htrP, htrQ]
  simp only [Complex.natCast_re]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp
  ring

end Projectors


section FlowAlgebra

/-- The commutator measuring departure from normality. -/
def normalCommutator (K : Matrix n n ℂ) : Matrix n n ℂ := K * Kᴴ - Kᴴ * K

/-- The opposite normalization used in the energy books: `‖[K,K*]‖² / 8`. -/
def normalEnergy (K : Matrix n n ℂ) : ℝ := frobSq (normalCommutator K) / 8

lemma normalCommutator_isHermitian (K : Matrix n n ℂ) :
    (normalCommutator K)ᴴ = normalCommutator K := by
  simp [normalCommutator, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]

/-- The Lax tangent is the negative double bracket in the displayed
normalization. -/
def relaxationTangent (K : Matrix n n ℂ) : Matrix n n ℂ :=
  (-2 : ℝ) • (normalCommutator K * K - K * normalCommutator K)

/-- Exact quadratic expansion of Frobenius energy along a real straight path. -/
lemma frobSq_add_real_smul (K V : Matrix n n ℂ) (t : ℝ) :
    frobSq (K + t • V) =
      frobSq K + t * (2 * (Kᴴ * V).trace.re) + t ^ 2 * frobSq V := by
  rw [frobSq_add, frobSq_real_smul]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  ring

/-- A double-bracket trace identity.  No normality or spectral hypothesis is
needed. -/
lemma trace_adjoint_mul_doubleBracket (K : Matrix n n ℂ) :
    (Kᴴ * (normalCommutator K * K - K * normalCommutator K)).trace.re =
      frobSq (normalCommutator K) := by
  let C := normalCommutator K
  have h₁ : (Kᴴ * (C * K)).trace = (C * (K * Kᴴ)).trace := by
    calc
      (Kᴴ * (C * K)).trace = ((C * K) * Kᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (C * (K * Kᴴ)).trace := by rw [Matrix.mul_assoc]
  have h₂ : (Kᴴ * (K * C)).trace = (C * (Kᴴ * K)).trace := by
    calc
      (Kᴴ * (K * C)).trace = ((Kᴴ * K) * C).trace := by rw [Matrix.mul_assoc]
      _ = (C * (Kᴴ * K)).trace := Matrix.trace_mul_comm _ _
  have htrace : (Kᴴ * (C * K - K * C)).trace = (C * C).trace := by
    calc
      (Kᴴ * (C * K - K * C)).trace =
          (Kᴴ * (C * K)).trace - (Kᴴ * (K * C)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub]
      _ = (C * (K * Kᴴ)).trace - (C * (Kᴴ * K)).trace := by rw [h₁, h₂]
      _ = (C * (K * Kᴴ - Kᴴ * K)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub]
      _ = (C * C).trace := by rfl
  rw [htrace]
  change (C * C).trace.re = frobSq C
  rw [frobSq_eq_re_trace, normalCommutator_isHermitian]

/-- Along the exact Lax tangent, the derivative of squared Frobenius norm is
`-32` times the normal energy.  This is the local identity behind the constant
in the integrated budget. -/
lemma hasDerivAt_frobSq_relaxationTangent (K : Matrix n n ℂ) :
    HasDerivAt (fun t : ℝ => frobSq (K + t • relaxationTangent K))
      (-32 * normalEnergy K) 0 := by
  let C := normalCommutator K
  let D := C * K - K * C
  have hbase : HasDerivAt
      (fun t : ℝ => frobSq K + t * (2 * (Kᴴ * ((-2 : ℝ) • D)).trace.re) +
        t ^ 2 * frobSq ((-2 : ℝ) • D))
      (2 * (Kᴴ * ((-2 : ℝ) • D)).trace.re) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (frobSq K)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (2 * (Kᴴ * ((-2 : ℝ) • D)).trace.re))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (frobSq ((-2 : ℝ) • D))) using 1
    · ext t
      simp [id]
    · simp [id]
  have hpath : HasDerivAt
      (fun t : ℝ => frobSq K + t * (2 * (Kᴴ * ((-2 : ℝ) • D)).trace.re) +
        t ^ 2 * frobSq ((-2 : ℝ) • D))
      (-32 * normalEnergy K) 0 := by
    have htrace : (Kᴴ * ((-2 : ℝ) • D)).trace.re = -2 * frobSq C := by
      simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
      rw [show (Kᴴ * D).trace.re = frobSq C from trace_adjoint_mul_doubleBracket K]
      ring
    rw [htrace] at hbase
    convert hbase using 1
    · ext t
      rw [htrace]
    · simp only [normalEnergy]
      ring
  have hfun : (fun t : ℝ => frobSq (K + t • relaxationTangent K)) =
      (fun t : ℝ => frobSq K + t * (2 * (Kᴴ * ((-2 : ℝ) • D)).trace.re) +
        t ^ 2 * frobSq ((-2 : ℝ) • D)) := by
    funext t
    rw [frobSq_add_real_smul]
    rfl
  rw [hfun]
  exact hpath

/-- The same identity without derivative notation, as an exact quadratic in the
path parameter. -/
lemma frobSq_relaxation_path (K : Matrix n n ℂ) (t : ℝ) :
    frobSq (K + t • relaxationTangent K) =
      frobSq K + t * (-32 * normalEnergy K) + 4 * t ^ 2 *
        frobSq (normalCommutator K * K - K * normalCommutator K) := by
  rw [frobSq_add_real_smul, relaxationTangent, frobSq_real_smul]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  rw [trace_adjoint_mul_doubleBracket]
  simp only [normalEnergy]
  ring

end FlowAlgebra

section RealQuadratic

/-- Ordered-pair opposite energy with a plus sign on every edge. -/
def oppositeEdgeForm (w : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (d i + d j) ^ 2

/-- Ordered-pair connection energy with a minus sign on every edge. -/
def connectionEdgeForm (w : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (d i - d j) ^ 2

/-- Signless Laplacian `Deg + w`, with row-sum degree. -/
def signlessLaplacian (w : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => ∑ j, w i j) + w

/-- Ordinary Laplacian `Deg - w`, with row-sum degree. -/
def connectionLaplacian (w : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => ∑ j, w i j) - w

/-- The quadratic form as an explicit ordered sum. -/
def quadraticForm (M : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  ∑ i, ∑ j, d i * M i j * d j

lemma quadraticForm_add (M N : Matrix n n ℝ) (d : n → ℝ) :
    quadraticForm (M + N) d = quadraticForm M d + quadraticForm N d := by
  simp only [quadraticForm, Matrix.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

lemma quadraticForm_sub (M N : Matrix n n ℝ) (d : n → ℝ) :
    quadraticForm (M - N) d = quadraticForm M d - quadraticForm N d := by
  simp only [quadraticForm, Matrix.sub_apply]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma quadraticForm_diagonal (a d : n → ℝ) :
    quadraticForm (Matrix.diagonal a) d = ∑ i, a i * d i * d i := by
  simp only [quadraticForm, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_ite, ite_mul, mul_comm]

lemma oppositeEdgeForm_eq_two_mul_quadraticForm {w : Matrix n n ℝ}
    (hw : ∀ i j, w i j = w j i) (d : n → ℝ) :
    oppositeEdgeForm w d = 2 * quadraticForm (signlessLaplacian w) d := by
  have hswap : (∑ i, ∑ j, w i j * (d j) ^ 2) =
      ∑ i, ∑ j, w i j * (d i) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hw]
  have hdeg : (∑ i, (∑ j, w i j) * d i * d i) =
      ∑ i, ∑ j, w i j * (d i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ j, w i j) * d i * d i = (∑ j, w i j) * (d i) ^ 2 := by ring
      _ = ∑ j, w i j * (d i) ^ 2 := Finset.sum_mul _ _ _
  have hadj : quadraticForm w d = ∑ i, ∑ j, w i j * d i * d j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hQ : quadraticForm (signlessLaplacian w) d =
      (∑ i, ∑ j, w i j * (d i) ^ 2) + ∑ i, ∑ j, w i j * d i * d j := by
    rw [signlessLaplacian, quadraticForm_add, quadraticForm_diagonal, hdeg, hadj]
  rw [hQ]
  simp only [oppositeEdgeForm]
  have hpoint : ∀ i j, w i j * (d i + d j) ^ 2 =
      w i j * (d i) ^ 2 + w i j * d i * d j + w i j * d i * d j +
        w i j * (d j) ^ 2 := by
    intros
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  linear_combination hswap

lemma connectionEdgeForm_eq_two_mul_quadraticForm {w : Matrix n n ℝ}
    (hw : ∀ i j, w i j = w j i) (d : n → ℝ) :
    connectionEdgeForm w d = 2 * quadraticForm (connectionLaplacian w) d := by
  have hswap : (∑ i, ∑ j, w i j * (d j) ^ 2) =
      ∑ i, ∑ j, w i j * (d i) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hw]
  have hdeg : (∑ i, (∑ j, w i j) * d i * d i) =
      ∑ i, ∑ j, w i j * (d i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ j, w i j) * d i * d i = (∑ j, w i j) * (d i) ^ 2 := by ring
      _ = ∑ j, w i j * (d i) ^ 2 := Finset.sum_mul _ _ _
  have hadj : quadraticForm w d = ∑ i, ∑ j, w i j * d i * d j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hQ : quadraticForm (connectionLaplacian w) d =
      (∑ i, ∑ j, w i j * (d i) ^ 2) - ∑ i, ∑ j, w i j * d i * d j := by
    rw [connectionLaplacian, quadraticForm_sub, quadraticForm_diagonal, hdeg, hadj]
  rw [hQ]
  simp only [connectionEdgeForm]
  have hpoint : ∀ i j, w i j * (d i - d j) ^ 2 =
      w i j * (d i) ^ 2 - w i j * d i * d j - w i j * d i * d j +
        w i j * (d j) ^ 2 := by
    intros
    ring
  simp only [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linear_combination hswap

lemma oppositeEdgeForm_nonneg {w : Matrix n n ℝ} (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    0 ≤ oppositeEdgeForm w d := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hw i j) (sq_nonneg _)

lemma connectionEdgeForm_nonneg {w : Matrix n n ℝ} (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    0 ≤ connectionEdgeForm w d := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hw i j) (sq_nonneg _)

/-- Vanishing of the opposite form is exactly the local alternating-field
condition on every positively weighted ordered pair. -/
lemma oppositeEdgeForm_eq_zero_iff {w : Matrix n n ℝ} (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    oppositeEdgeForm w d = 0 ↔ ∀ i j, w i j = 0 ∨ d i + d j = 0 := by
  constructor
  · intro h i j
    have hterms : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, w i j * (d i + d j) ^ 2 = 0 := by
      have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, w i j * (d i + d j) ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h
      intro i hi_mem
      have hnonneg' : ∀ j ∈ Finset.univ, 0 ≤ w i j * (d i + d j) ^ 2 :=
        fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg').1 (hi i hi_mem)
    have hterm := hterms i (Finset.mem_univ i) j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with hwij | hsq
    · exact Or.inl hwij
    · exact Or.inr (sq_eq_zero_iff.mp hsq)
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rcases h i j with hwij | hd
    · rw [hwij, zero_mul]
    · rw [hd]
      simp

/-- Vanishing of the connection form is exactly equality across every
positively weighted ordered pair. -/
lemma connectionEdgeForm_eq_zero_iff {w : Matrix n n ℝ} (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    connectionEdgeForm w d = 0 ↔ ∀ i j, w i j = 0 ∨ d i - d j = 0 := by
  constructor
  · intro h i j
    have hterms : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, w i j * (d i - d j) ^ 2 = 0 := by
      have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, w i j * (d i - d j) ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h
      intro i hi_mem
      have hnonneg' : ∀ j ∈ Finset.univ, 0 ≤ w i j * (d i - d j) ^ 2 :=
        fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg').1 (hi i hi_mem)
    have hterm := hterms i (Finset.mem_univ i) j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with hwij | hsq
    · exact Or.inl hwij
    · exact Or.inr (sq_eq_zero_iff.mp hsq)
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rcases h i j with hwij | hd
    · rw [hwij, zero_mul]
    · rw [hd]
      simp

lemma quadraticForm_signless_nonneg {w : Matrix n n ℝ}
    (hsymm : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    0 ≤ quadraticForm (signlessLaplacian w) d := by
  have h := oppositeEdgeForm_nonneg hw d
  rw [oppositeEdgeForm_eq_two_mul_quadraticForm hsymm] at h
  linarith

lemma quadraticForm_signless_eq_zero_iff {w : Matrix n n ℝ}
    (hsymm : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j) (d : n → ℝ) :
    quadraticForm (signlessLaplacian w) d = 0 ↔ ∀ i j, w i j = 0 ∨ d i + d j = 0 := by
  constructor
  · intro h
    apply (oppositeEdgeForm_eq_zero_iff hw d).1
    rw [oppositeEdgeForm_eq_two_mul_quadraticForm hsymm, h, mul_zero]
  · intro h
    have he := (oppositeEdgeForm_eq_zero_iff hw d).2 h
    rw [oppositeEdgeForm_eq_two_mul_quadraticForm hsymm] at he
    linarith

end RealQuadratic


/-! ## Axiom audit -/

#print axioms SixthBatchMatrix.frobSq_nonneg
#print axioms SixthBatchMatrix.frobSq_eq_zero_iff
#print axioms SixthBatchMatrix.frobSq_eq_re_trace
#print axioms SixthBatchMatrix.frobSq_conjTranspose
#print axioms SixthBatchMatrix.frobSq_add
#print axioms SixthBatchMatrix.frobSq_neg
#print axioms SixthBatchMatrix.frobSq_sub
#print axioms SixthBatchMatrix.frobSq_parallelogram
#print axioms SixthBatchMatrix.frobSq_real_smul
#print axioms SixthBatchMatrix.frobSq_adjoint_books_budget
#print axioms SixthBatchMatrix.frobSq_adjoint_books_difference
#print axioms SixthBatchMatrix.frobSq_unitary_mul
#print axioms SixthBatchMatrix.frobSq_mul_unitary
#print axioms SixthBatchMatrix.frobSq_unitary_conj
#print axioms SixthBatchMatrix.trace_unitary_conj
#print axioms SixthBatchMatrix.bornWeights_col_sum
#print axioms SixthBatchMatrix.bornWeights_row_sum
#print axioms SixthBatchMatrix.bornWeights_nonneg
#print axioms SixthBatchMatrix.bornWeights_sum
#print axioms SixthBatchMatrix.frobSq_diagonal_mul_sub_mul_diagonal
#print axioms SixthBatchMatrix.frobSq_diagonal_mul_add_mul_diagonal
#print axioms SixthBatchMatrix.born_sum_neg
#print axioms SixthBatchMatrix.frobSq_of_projector
#print axioms SixthBatchMatrix.trace_conjugate_projector
#print axioms SixthBatchMatrix.frobSq_projector_sub_conjugate
#print axioms SixthBatchMatrix.frobSq_projector_add_conjugate
#print axioms SixthBatchMatrix.frobSq_projector_sub_eq_two_rank
#print axioms SixthBatchMatrix.frobSq_projector_add_eq_two_rank
#print axioms SixthBatchMatrix.normalCommutator_isHermitian
#print axioms SixthBatchMatrix.frobSq_add_real_smul
#print axioms SixthBatchMatrix.trace_adjoint_mul_doubleBracket
#print axioms SixthBatchMatrix.hasDerivAt_frobSq_relaxationTangent
#print axioms SixthBatchMatrix.frobSq_relaxation_path
#print axioms SixthBatchMatrix.quadraticForm_add
#print axioms SixthBatchMatrix.quadraticForm_sub
#print axioms SixthBatchMatrix.quadraticForm_diagonal
#print axioms SixthBatchMatrix.oppositeEdgeForm_eq_two_mul_quadraticForm
#print axioms SixthBatchMatrix.connectionEdgeForm_eq_two_mul_quadraticForm
#print axioms SixthBatchMatrix.oppositeEdgeForm_nonneg
#print axioms SixthBatchMatrix.connectionEdgeForm_nonneg
#print axioms SixthBatchMatrix.oppositeEdgeForm_eq_zero_iff
#print axioms SixthBatchMatrix.connectionEdgeForm_eq_zero_iff
#print axioms SixthBatchMatrix.quadraticForm_signless_nonneg
#print axioms SixthBatchMatrix.quadraticForm_signless_eq_zero_iff

end SixthBatchMatrix

