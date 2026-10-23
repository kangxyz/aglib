# Dimension-bounded Noether normalization

[DimensionOne](DimensionOne.lean) applies native lying over and maximal-ideal contraction to an
integral injection of domains. Dimension at most one descends to the source.
The native Noether normalization of a finite-type domain therefore uses zero
or one variable. No perfectness or separable-generation premise is added.

Actual fraction-field and prime-residue-field consumers live in
`FieldTheory.FunctionField`, rather than adding scheme hypotheses here.
