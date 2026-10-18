# Scalar restriction and canonical base change

[Algebra](Algebra.lean) gives `extendScalarsAlgebraObjIso` for a specified
algebra structure. It identifies the original scalar-extension object along
`algebraMap` with the original algebra tensor product. Both directions
retain each pure tensor, and the coefficient square uses the original
`LinearMap.baseChange`. No flatness or finiteness premise is needed.

[Finiteness](Finiteness.lean) owns `ModuleCat.finite_extendScalars` and
`ModuleCat.projective_extendScalars` for arbitrary maps of commutative rings, with
independent ring and module universes. The finite-projective complex
family consumes these native module statements by public import.

[Exactness](Exactness.lean), imported as `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness`, gives `ModuleCat.shortExact_of_restrictScalars`. An actual module short complex is short exact when its restriction along the supplied ring homomorphism is short exact. Source and target are rings; this lower statement has no scheme or commutativity premise merely from its geometric consumers.

The underlying maps are the original module maps. Tensor/direct-image and scalar comparison arguments use this reflection after constructing their actual coefficient action. Restriction does not supply an unstated finite-generation or Noetherian property.

[Additive](Additive.lean) proves additivity of the native `extendScalars` functor
with independent ring and module carrier universes. [Flat](Flat.lean) proves
that it preserves actual short-complex exactness, finite limits and finite
colimits when the specified ring homomorphism is flat. The explicit
`RingHom.Flat` premise avoids choosing an unrelated ambient algebra structure.

[Homology](Homology.lean) defines `ModuleCat.homologyBaseChangeMap` and
`HomologicalComplex.extendScalarsHomologyMap` from the original scalar
adjunction unit. Their unit, pure-tensor and naturality formulas identify the
actual forward map. When scalar extension preserves homology the map is the
inverse native homology comparison. In a rightmost degree with zero outgoing
differential it is an isomorphism for every ring map, without flatness. The
generic adjunction construction lives in
[ShortComplex/Adjunction](../../../Homology/ShortComplex/Adjunction.lean).

[Homology/Forget](Homology/Forget.lean) identifies the underlying additive
scalar-extension unit with the literal unit pure tensor. Its comparison with
native additive homology, including a subsequent actual complex map and
commutative square, is shared by geometric Cech base change. Exactness is used
only in the homology formulas; the original unit itself needs no flatness.

[BaseChange](BaseChange.lean), imported as `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange`, defines `ModuleCat.scalarBaseChangeMap` for a commuting square of commutative-ring maps `R → S`, `R → T`, `S → P`, `T → P`. For an arbitrary `S`-module `M`, this is the original scalar-adjunction mate from `T ⊗[R] M` to `P ⊗[S] M`, with the displayed scalar restrictions. `scalarBaseChangeMap_unit` and `scalarBaseChangeMap_one_tmul` retain its original units and the literal unit-tensor formula. `scalarBaseChangeMap_isIso_of_isPushout` identifies the actual map with the inverse native `Algebra.IsPushout.cancelBaseChange` equivalence and proves invertibility on every module over a commutative-ring pushout. No flatness, Noetherianity or finite-generation hypothesis is used. The [affine geometric comparison](../../../../AlgebraicGeometry/Modules/BaseChange/README.md) consumes this exact map.

[Homology/Composition](Homology/Composition.lean) proves composition of
the original homology mates through the native scalar-extension
composition isomorphism, without flatness, finiteness or Noetherianity.
The literal scalar units compose by the same original pure-tensor map.
The three rings share the universe required by the native composition
isomorphism; carrier and complex-index universes remain independent.
[Homology/Forget](Homology/Forget.lean) owns the sole short-complex
additive-unit calculation; its original complex version delegates to it.

[Coinduction](Coinduction/README.md) treats the original native right
adjoints to scalar restriction. It supplies ordinary composition with its
unit/counit equations, preservation of injectives, and composition of the
installed D+ right-derived functors with their original units. The ring
universes and supplied derived-category sizes remain independent; no
commutativity or flatness premise is added. Its Ext and regular-principal
refinements identify original homology and compute principal-equation purity;
geometric sheaf purity remains a separate consumer.
