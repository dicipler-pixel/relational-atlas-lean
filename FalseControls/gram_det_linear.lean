import RelationalAtlas.Basic
-- The Gram invariant is the square of the determinant: for X = 2·I₁ it is 4, not 2.
example : ((2 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 2).det = 2 := by
  simp [Matrix.det_fin_one]; norm_num
