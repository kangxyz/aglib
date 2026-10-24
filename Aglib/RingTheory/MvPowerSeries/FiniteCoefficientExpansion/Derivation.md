# Coefficient derivations over an expanded series base

For fields `E → k` with their given algebra map, an actual
`δ : Derivation E k k` extends coefficientwise to the original
`MvPowerSeries (Fin 2) k`. Its coefficient at `n` on a series `f` is
exactly `δ (coeff n f)`. Additivity and scalar linearity are coefficientwise;
the Leibniz rule follows from the finite Cauchy sum for each product coefficient.

For every nonzero natural number `q`, the map kills the original
`FiniteCoefficientExpansion.scalarMap q hq`, which first applies the
coefficient map and then expands both variables. Consequently
`coefficientDerivationOverExpansion` is an algebraic derivation over the
actual source series ring under `scalarAlgebra q hq`. Its coefficient
formula is retained. It sends `C a` to `C (δ a)` and both variables to zero.

No characteristic or continuity assumption is needed for this construction.
The intended consumer is the coefficient coordinate in the algebraic Kähler
basis over `E[[u^p,v^p]]`, using the actual degree-p coefficient presentation
in `NonPowerComplement`. Spatial partial derivatives, algebraic generation
and assembly of the full differential basis remain separate consumer work.

This module supplies the coefficientwise derivation for a single-coefficient
construction. It supplies no fixed-family intersection theorem or B7
trace/cohomology result. Its source basis is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
