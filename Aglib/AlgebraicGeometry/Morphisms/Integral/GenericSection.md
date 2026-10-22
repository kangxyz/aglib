# Generic lifts through integral morphisms

Let `X` be an integral scheme with `NormalStalks X`, let `f : X ⟶ P`, and let
`q : Y ⟶ P` be integral. A specified map `g : Spec X.functionField ⟶ Y`
whose composite with `q` is the original generic inclusion followed by `f`
has a unique extension `l : X ⟶ Y` over `P`.

`Scheme.integralGenericLift` is the actual extension.
`integralGenericLift_over` and `integralGenericLift_generic` retain the two
original triangles. `existsUnique_integralGenericLift` states existence and
uniqueness together. The target `Y` need not be reduced, integral or normal.
No Noetherian, dimension, properness, finite-type or smoothness premise is used.
Every finite morphism is an available integral target.

The construction takes the literal pullback `Y ×_P X`, lifts the supplied
generic point into it, and applies the native relative-normalization universal
property. The existing normal-stalk theorem identifies the normalization of
`X`'s own generic inclusion with `X`. Its two native normalization equations
give the two claimed triangles. Uniqueness follows from the actual dominant
generic inclusion, reducedness of `X`, and separatedness of an integral morphism.

The current consumer is the lifting step for common surface domination:
after constructing a map from a regular scheme to the finite projective
product in the native proper Chow modification, its specified generic lift
through the actual finite map extends by this theorem. Constructing that map
and principalizing its actual base ideals remain separate obligations.
