# Ordinary homological complexes

[Adjunction](Adjunction.lean) lifts a supplied additive adjunction between
abelian categories to Mathlib's actual homological complexes of any supplied
`ComplexShape`. The unit and counit act in each degree by the original unit and
counit. The independent object and morphism universes, abelian hypotheses and
both additive-functor hypotheses are retained.

This leaf does not import homotopy or derived categories. The corresponding
integer-cochain homotopy adjunction is the higher
[HomotopyCategory/Adjunction](../HomotopyCategory/Adjunction.lean); the
[K-injective target Hom comparison](../DerivedCategory/KInjective/README.md)
is higher again. The first present consumers are these two interfaces and the
existing geometric chain adjunctions for open restriction/direct image and
extension by zero.
