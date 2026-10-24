# Native mapping cocones

`Map.lean` uses the native `CochainComplex.mappingCocone`, which is the
original mapping cone shifted by minus one. `mappingCocone.map` is exactly
the corresponding shifted native cone map. Its first and second projection
equations retain all chain-level signs. `ext_to_term` gives extensionality
using the two original projections, and `lift_zero_naturality` proves strict
naturality of the original cocone lift with zero homotopy coordinate.

These statements use a preadditive category with binary biproducts and
integer-indexed cochain complexes. They require neither enough injectives,
Grothendieckness, nor boundedness. The unbounded injective-step family consumes
them; no competing cone or derived-category carrier is introduced.

The generic short-exact augmentation quasi-isomorphism is developed separately
in `ShortExact.lean` by its assigned owner. See that leaf for its exact status
and hypotheses; the map/projection family alone proves no such existence or
quasi-isomorphism statement.
