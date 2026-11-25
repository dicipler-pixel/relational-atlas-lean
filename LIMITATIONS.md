# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* Bridges graded THEOREM whose content is finite algebra were formalized first. Later batches also
  formalized kernels for seven cards graded CONJECTURE (B4, B49, B53, B58, B62, B76, B125); each of
  those carries a correction record saying which part of the claim survived. MEASURED and READING
  cards have no kernel unless the ledger names a finite algebraic fragment.
* B1 (`4 det g ≥ |Ω|²`) is proved in iqgt-grassmannian-lean, not here. Of the theorem-grade cards,
  B9 (winding), B11 (dilogarithm volumes), B29 (heat-kernel coefficients), B36, B70, B140 and B164
  are still unmapped here, as is the derived card B34; every other theorem-grade card has a local
  kernel named in the ledger.
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
