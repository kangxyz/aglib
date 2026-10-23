# Finite generation from an adic quotient

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module.
`Module.finite_of_isPrecomplete_of_isHausdorff` proves that `M` is finite
when `R` is `I`-adically precomplete, `M` is `I`-adically separated, and
`M / I M` is finite over `R`. The target need not be precomplete, and neither
the ring nor the module is assumed Noetherian. The ring and module may lie
in different universes.

The proof lifts a finite free presentation of the quotient through its
literal quotient map. `IsPrecomplete.pi_of_finite` makes the finite free
source precomplete, using Mathlib's canonical finite-product completion
equivalence. Mathlib's `surjective_of_mkQ_comp_surjective` then makes the
lift surjective. There is no second implementation of coefficient lifting.

`Module.finite_of_isPrecomplete_of_isHausdorff_quotient` accepts finite
generation over `R / I` instead. It restricts the quotient's scalars through
the original coefficient map before applying the same criterion.

For an `R`-algebra `B`, `Module.finite_of_isPrecomplete_of_le_jacobson`
derives separatedness from `IsNoetherianRing B` and the actual containment
`I.map (algebraMap R B) ≤ Ideal.jacobson ⊥`. Its input is finite generation
of `B / I B`; module finiteness of `B` is its conclusion.

The intended complete-curve consumer has `I` equal to the maximal ideal of
the complete local base. Finite generation of `B / t B` for a nonzero
`t ∈ I` implies finite generation of `B / I B`. Integrality supplies the
Jacobson containment. Noetherianity of the normalization must be supplied
independently before the Noetherian-target criterion applies. These results
do not prove that normalization theorem, or finiteness of the normalization
of a two-dimensional graph.

This is new source over Aglib base
`22f7532679eec4295167fcf885cf8b1b0981d899`, using Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`, particularly
`RingTheory/AdicCompletion/Functoriality.lean` and
`RingTheory/AdicCompletion/Noetherian.lean`.
