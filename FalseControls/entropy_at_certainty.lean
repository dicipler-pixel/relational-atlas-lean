import RelationalAtlas.Basic
-- A channel at certainty contributes nothing: H(1) = 0, not log 2.
example : Real.binEntropy 1 = Real.log 2 := by
  rw [Real.binEntropy_one]; norm_num
