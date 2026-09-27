import RelationalAtlas.Basic
-- Past the critical angle the transmitted sine is cosh y ≥ 1; at y = 0 it is 1, not 1/2.
example : Real.cosh 0 = 1 / 2 := by simp
