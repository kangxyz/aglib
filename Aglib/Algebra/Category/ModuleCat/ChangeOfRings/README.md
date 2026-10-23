# Scalar restriction and canonical base change

[Surjective](Surjective.lean) identifies the original scalar-adjunction
unit along a surjective ring map `f` with `M -> M / (ker f) M`.
Its actual kernel and surjectivity give fullness of scalar extension on
morphisms with projective source. No finiteness, nilpotence or flatness is
required. Prescribed square-zero isomorphism lifting consumes this map.

[Algebra](Algebra.lean) gives `extendScalarsAlgebraObjIso` for a specified
algebra structure. It identifies the original scalar-extension object along
`algebraMap` with the original algebra tensor product. Both directions
retain each pure tensor, and the coefficient square uses the original
`LinearMap.baseChange`. No flatness or finiteness premise is needed.

[Finiteness](Finiteness.lean) owns `ModuleCat.finite_extendScalars` and
`ModuleCat.projective_extendScalars` for arbitrary maps of commutative rings, with
independent ring and module universes. The finite-projective complex
family consumes these native module statements by public import.

[SpanSingleton](SpanSingleton.lean) gives `ModuleCat.extendScalars_map_toSpanSingleton_comp`:
extension of scalars of `a ↦ a • x`, followed by `e` with `e (1 ⊗ x) = y`, is `b ↦ b • y` after
`scalarExtensionUnit`, with the hypothesis stated through the scalar-extension adjunction. Its
consumer is the affine base change of
[Grassmannian/Quotient](../../../../AlgebraicGeometry/Grassmannian/README.md).

[UnitTensor](UnitTensor.lean) evaluates scalar extension on unit pure tensors
through composites and congruences: `ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul`
computes `C ⊗_A M ≅ C ⊗_B (B ⊗_A M) ⟶ C ⊗_B N ⟶ P` on `1 ⊗ m` for maps given
on unit pure tensors, and `ModuleCat.extendScalarsCongrIso` is extension along
equal ring maps, with `_hom_one_tmul`. The rings share one universe and the
modules live in the next one, as in Mathlib's `extendScalarsComp`; the
cohomology base-change leaves `Transitivity` and `Composite` consume them.

[Exactness](Exactness.lean), imported as `Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness`, gives `ModuleCat.shortExact_of_restrictScalars`. An actual module short complex is short exact when its restriction along the supplied ring homomorphism is short exact. Source and target are rings; this lower statement has no scheme or commutativity premise merely from its geometric consumers.

`ModuleCat.extendScalars_map_exact_of_surjective`, in the same leaf, proves
right exactness of scalar extension along a map of commutative rings: it
preserves exactness of `M₁ → M₂ → M₃ → 0`, as left tensoring through
`φ.toAlgebra`. Nitsure's Lemma 3.1
(`AlgebraicGeometry/Cohomology/Projective/LargeTwistBaseChange`) consumes it.

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

The same cancellation gives `ModuleCat.flat_extendScalars_of_isPushout`
(Stacks Project, Tag 00HI): for a pushout square of commutative rings and a
module flat over the base, its scalar extension is flat over the other corner.
Base change of relative flatness (`AlgebraicGeometry/Modules/Flat/Relative/BaseChange`)
consumes it.

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
commutativity or flatness premise is added to these general comparisons.
Its commutative-ring refinements identify original Ext and compute the
regular-principal coefficient object and the ring-coefficient object for a
finite weakly regular list. These local algebraic calculations are inputs
to geometric sheaf-purity and canonical-duality comparisons.

[PresentationExt](PresentationExt.lean) detects maps from iterated scalar extensions on the double
unit tensors of a specified original source presentation.

[PresentationCompatibility](PresentationCompatibility.lean) packages the original scalar-extended presentation
square as a named predicate. Four original unit-tensor equations prove the
whole square, without linearity assumptions on the auxiliary coordinate
functions or any flatness or finiteness premise.

[PresentationUnit](PresentationUnit.lean) retains the inverse-coordinate unit image as a regular
predicate. The original presentation factorization and its pure-tensor image
prove it by abstract isomorphism cancellation before concrete specialization.
