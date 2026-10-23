# Serre vanishing along a closed projective embedding

[ClosedImmersion.lean](ClosedImmersion.lean) owns the generic native
`Scheme.Cohomology.embeddedTensorTwist` and
`Scheme.Cohomology.embeddedTensorTwist_serreVanishing` implementations.
The names in `Surfaces/Contraction/ProjectiveSections.lean` are transparent
adapters to these declarations with the same tensor objects and theorem types.

For a commutative Noetherian ring A, an actual closed immersion
`p : X → ProjectiveSpace A I`, an actual coordinate labeling `I ≃ Fin (r+1)`,
and an affine-locally finite-type module F, one bound kills all positive
cohomology of every larger actual tensor twist `p*O(d) ⊗ F`.
No relative flatness, Cartier divisor, curve, or surface premise is used.

The proof retains coherent closed direct image, the original projective Serre
bound, the actual closed-immersion projection-formula isomorphism, and the
original projective-embedding cohomology equivalence. These same maps and
objects serve both the Cartier filtration and positive-degree P1 consumers.
The original structural coefficient action in the cohomology comparison is
unchanged. No vanishing family is assumed.
