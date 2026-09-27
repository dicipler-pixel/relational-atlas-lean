# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* Only bridges graded THEOREM whose content is finite algebra are formalized. Bridges graded
  MEASURED, DERIVED, CONJECTURE or READING are not.
* B1 (`4 det g ≥ |Ω|²`) is proved in iqgt-grassmannian-lean, not here. B9 (winding), B11 (dilogarithm volumes), B27 (dissipation floor), B28
  (mixed states), B29 (heat-kernel coefficients), B32, B37, B42, B43, B44, B55–B57, B60, B64,
  B65, B67, B70, B72, B73, B78, B79, B81 and B84 are not formalized here.
* B6 restates the binary entropy's properties from Mathlib. The free-fermion construction
  `S = Σ H(ν_k)` is cited, not proved.
* B48 is Mathlib's block-determinant theorem, restated. That the interface has this block form
  is the paper's claim and is not formalized.
* B51 proves the reduction and both directions of the unit-circle correspondence for `u`. The
  classification of the eight knots is not formalized.
