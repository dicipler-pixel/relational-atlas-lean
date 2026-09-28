# Provenance

`RelationalAtlas/Basic.lean` and the three files in `FalseControls/` were written for this
repository from *The Operator-First Atlas* (Plate XIII, "The Bridges"), in the edition of
27 August 2026. The Zenodo record (DOI 10.5281/zenodo.21972561) is dated 18 August 2026, so a
bridge numbered here may postdate the deposited edition. Each theorem names its bridge.

## The Atlas card core

`RelationalAtlas/AtlasFormalCore.lean` is a byte-identical copy of `AtlasFormalCore.lean` from
the Atlas card formalization in the private research repository (source revision
`f4e682ff428b5e941a3da7d2a1b211dc925bdbc6`, Actions run 34684818137, conclusion success),
as archived in the *Light Keeps the Ledger* Research Edition 7.2 proofs package. It was first
checked against Lean v4.33.0 and Mathlib v4.33.0; this repository checks it against v4.34.1.
SHA-256 `7e6c433b0c0e1fcfc0bec2a2c3244db4c43b62e1b8465d0b3c2cde6c1ad13e1a`.

The four files `FalseControls/atlas_*.lean` are that run's false controls, with only the import
line changed to this repository's module name.
