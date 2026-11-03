# Differential coordinates over an expanded series base

[Differentials](Differentials.lean) uses the original coefficient inclusion
`E → k` followed by expansion by the prime characteristic `p`.
The base is `E[[U,V]]` with variables acting as `u^p,v^p`, not merely
the constant field. The two-coordinate basis uses a surjective coefficient
map; the three-coordinate basis retains an actual coefficient power basis
and derivation, ordered before the two spatial differentials.

[FractionRing](FractionRing.lean) preserves the original series and
fraction-field maps, their scalar towers and Frobenius coefficient series.
No finite absolute `p`-rank is imposed.

[Coordinates](Coordinates.lean) starts with an actual equivalence
`k[[X,Y]] ≃ R`, the original fraction field of `R` and an element without
a `p`th root there. It constructs the finite expanded coefficient base,
integral differential basis, nonzero differential and corresponding
original fraction-field ranks on that same `R`.
The complete regular surface entrance uses these exact coordinates.

Present consumers include [Differential trace in purely inseparable prime degree](../../Kaehler/PureDegreePTrace/README.md).
