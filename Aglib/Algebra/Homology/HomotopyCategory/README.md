# Bounded-below homotopy comparison

[Plus](Plus/README.md) studies an already defined shift-compatible triangulated comparison on Mathlib's actual bounded-below homotopy category. Under both actual lower and upper zero-term bounds, the comparison can be checked on its original single terms.

The proof route uses actual stupid truncation layers and distinguished triangles. It asserts neither a natural replacement/model choice nor an unbounded-above extension of the term comparison.

[Adjunction](Adjunction.lean) lifts the original additive adjunction to
integer cochain homotopy categories. The native quotient unit, counit
and both chain-adjoint formulas are retained. It depends on the sole
degreewise [homological-complex adjunction](../HomologicalComplex/Adjunction.lean).
The source is copied unchanged from Aglib checkpoint f87a691.
