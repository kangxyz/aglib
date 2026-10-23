# Low-dimensional algebraic function fields

- [DimensionOne](DimensionOne.lean) constructs an actual rational-function algebra on the original
  fraction field of an integrally normalized domain, with the original constant
  field tower. A finite-type domain of dimension at most one has a fraction field
  algebraic over the constants or over that one-variable rational function field.
- [ResidueField](ResidueField.lean) applies this to the actual prime quotient and native ideal
  residue field. The original ring need not be a domain, reduced or irreducible.

These are algebraic coordinate suppliers, not etale-cohomology vanishing
assertions. Scheme coordinate maps belong to `AlgebraicGeometry.ResidueField`;
original-cohomology applications belong to `AlgebraicGeometry.EtaleCohomology`.
