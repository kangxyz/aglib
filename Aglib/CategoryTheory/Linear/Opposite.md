# Scalars on the native opposite category

[Opposite.lean](Opposite.lean) supplies the explicit native structure
`CategoryTheory.Linear.opposite R C` for a preadditive R-linear category C
and a semiring R. The ring, object and morphism universes are independent.

The module structure on `X → Y` in the opposite category is transported
through the original additive equivalence `unop` to `Y.unop → X.unop`.
Linearity of composition follows from the opposite original composition
law. This construction introduces neither a replacement category nor an
action on its objects.

The structure is instance-reducible and is not registered globally.
Consumers explicitly install it locally. The current consumer is the
[fixed-coefficient derived dual](../../Algebra/Homology/ModuleCat/HomComplex/Derived.lean),
where source multiplication must retain the actual scalar action through
opposite localization.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the principal; the author retains coupled proof repair.
