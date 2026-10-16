# Homotopy categories

[Adjunction](Adjunction.lean) localizes an actual additive adjunction between
abelian categories to the integer-cochain homotopy categories. The original
quotient-factor squares and the literal chain unit, counit and adjoint-map
equations are retained. It requires no K-injectivity or derived-category choice.

[Plus](Plus/README.md) studies an already defined shift-compatible triangulated comparison on Mathlib's actual bounded-below homotopy category. Under both actual lower and upper zero-term bounds, the comparison can be checked on its original single terms.

The Plus proof route uses actual stupid truncation layers and distinguished triangles. It asserts neither a natural replacement/model choice nor an unbounded-above extension of the term comparison.
