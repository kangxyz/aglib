# Height-one normalized valuations and Kummer exponents

`Valuation.lean` exposes `Algebra.Kummer`.

For a Noetherian UFD domain with a normalization monoid and its specified fraction field, the
literal height-one prime localization is a DVR. Its valuation is normalized by uniformizer
value exp(-1), and its integer order is positive one on a uniformizer. The signed order of a
nonzero fraction is proved equal to the normalized factor exponent. Divisibility at every
actual height-one prime is equivalent to FactorizationDivisible for the same nonzero parameter,
including level zero. The final finite-etale integral-closure consequence retains positive n,
invertibility and the original normal Noetherian UFD assumptions. No residue/cohomology
dictionary or purity theorem is used.

The valuation is built from the actual `Localization.AtPrime P` and its canonical
map to the specified fraction field. The all-height-one-prime quantifier is retained.

Source: `R5Lab.Aglib.RingTheory.Kummer.Valuation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d6914b205d525a4df4e5146feeb1ce30a485140820150252dd9bf84bc62b634c`.

Source correspondence and compilation coverage have separate records in the assigned
scratch handoff; this document does not assign mathematical closure status.
