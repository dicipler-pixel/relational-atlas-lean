# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* Bridges graded THEOREM whose content is finite algebra were formalized first. Later batches also
  formalized kernels for seven cards graded CONJECTURE (B4, B49, B53, B58, B62, B76, B125); each of
  those carries a correction record saying which part of the claim survived. MEASURED and READING
  cards have no kernel unless the ledger names a finite algebraic fragment.
* B1 (`4 det g ≥ |Ω|²`) is proved in iqgt-grassmannian-lean, not here. Every card graded THEOREM
  now has a local kernel named in the ledger; what remains unmapped is 23 cards graded MEASURED,
  6 graded READING and 1 DERIVED.
* A kernel is a finite statement, and several cards' kernels leave their cited theorems outside:
  B11 does not formalise the Bloch–Wigner dilogarithm or Thurston–Zagier; B29 does not formalise the
  operator-side reduction; B140 proves the bound for circular contours and does not tie δ to the
  spectral distance; B164 does not formalise the global magnetostatic step; B9 does not formalise
  codimension two or the comparison with spectral flow; B36 does not prove the fold metric, the
  finiteness of K or the arcsin√ε distance.
* B70's displayed metric dichotomy is false as written and is recorded as refuted, with the
  counterexamples in `RelationalAtlas/Extended11.lean`; its spectral half is unaffected.
* B6 restates the binary entropy's properties from Mathlib. The free-fermion construction
  `S = Σ H(ν_k)` is cited, not proved.
* B48 is Mathlib's block-determinant theorem, restated. That the interface has this block form
  is the paper's claim and is not formalized.
* B51 proves the reduction and both directions of the unit-circle correspondence for `u`. The
  classification of the eight knots is not formalized.
* The Atlas card core formalizes only each card's finite algebraic kernel, as its own comments
  say: not the physical readings, measured exponents, continuum limits or genericity claims.
  B56 proves the rank obstruction only; B90 proves the normal forms, not that they are generic.

## Published 207-card edition

The [coverage ledger](atlas/coverage/README.md) links the edition at
https://doi.org/10.5281/zenodo.23590925 to exact local and external declarations.
Its coverage statuses do not certify a whole card or raise its source grade. External
snapshots are not imported by this Lake build; their recorded CI or committed verification
reports retain their own scope. A missing mapping means open audit work in the inspected
scope, not proof that no formalization exists elsewhere. The ledger integrity validator
checks IDs, declarations, source hashes and provenance, not mathematical equivalence of
English prose to Lean statements.
