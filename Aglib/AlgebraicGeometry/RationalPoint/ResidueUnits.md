# ResidueUnits

`Scheme.RationalPoint.functionField_charZero` transfers characteristic zero
through the actual constants embedding of an integral scheme.
`residueUnitsMap` is `Units.map q.residueEquiv.toRingHom.toMonoidHom` on the
actual local residue field, and its minus-one equation is preserved.
`level_isUnit` retains characteristic zero and a nonzero natural level.
The source additive `UnitsAdd` map is excluded from this algebraic-geometric
leaf. These maps supply no DVR valuation or K-theory residue data.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSectionResidue`.
  SHA-256: `134c4ea7aa69096267a16db0e9395d6ebcdef6b4089a840d50f96e7261993379`.
  Selected source ranges: `[[18, 29], [35, 49]]`.
  - `functionField_charZero` → `AlgebraicGeometry.Scheme.RationalPoint.functionField_charZero`.
  - `residueUnitsMap` → `AlgebraicGeometry.Scheme.RationalPoint.residueUnitsMap`.
  - `residueUnitsMap_neg_one` → `AlgebraicGeometry.Scheme.RationalPoint.residueUnitsMap_neg_one`.
  - `level_isUnit` → `AlgebraicGeometry.Scheme.RationalPoint.level_isUnit`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
