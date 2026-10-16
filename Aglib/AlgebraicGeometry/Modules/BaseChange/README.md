# The canonical pullback/direct-image mate

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Basic`, constructs `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f g M`. For the actual fibre square, its source is `g* f_* M` and target is the direct image of the pulled-back module. It is the mate of the original counit, with the actual pullback-composition comparisons.

`structureModuleBaseChangeMap` specializes it to the actual unit module. `pullbackStructureUnitIso` identifies the pulled-back structure module with the source unit. `fieldSections` and `moduleFibre` give actual field-valued section/fibre modules and scalar-preserving map/isomorphism interfaces.

`AffineModuleBaseChange` remains explicit: for affine `f`, quasicoherent coefficients and arbitrary `g`, this constructed map is invertible. No flatness of `g` is assumed. `structureModuleBaseChangeMap_isIso` takes that family as `hbase`; the map construction itself does not.

[OpenImmersion](OpenImmersion.lean) supplies the canonical `openBaseChange` isomorphism from actual restriction adjunction and pullback square. [Field fibres/rank](../LocallyFree/README.md), coherent pushforward and [relative evaluation/cohomology](../../Cohomology/BaseChange/README.md) consume these exact maps. Schemes and coefficient fields keep universe `u` in the fibre interface.

[Cartesian](Cartesian.lean) constructs the actual comparison on a supplied cartesian square. [Coefficients](../../BaseChange/Coefficients/README.md) packages arbitrary over-scheme/algebra coefficient pullbacks and polynomial/Laurent naturality; [OpenImmersion](OpenImmersion/README.md) gives the actual generic open-base-change comparison and section formulas without quasicoherence or coherence. General cartesian comparison-map construction does not assert unconditional invertibility.
