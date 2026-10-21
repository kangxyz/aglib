# Open models and finite gluing

Import `Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing`.

`Scheme.exists_open_model_of_isLimit` constructs a model of any
quasi-compact open `U` in an actual base change of a finitely presented
scheme at stage `i`. The bases form a cofiltered diagram of affine schemes
with a specified limit cone. The result is an actual open `V` in the
canonical base-change diagram at a later stage, with LFP, QC and QS
structural map and an isomorphism from its literal `Over.pullback` to the
original `U` over the limit. It permits nonaffine opens and nonseparated
finitely presented models.

The construction applies native quasi-compact-open descent to the concrete
base-change limit cone. `Scheme.isPullback_baseChangeCone` proves that each
cone projection is cartesian. Restricting this square to the descended
open produces the required over-category isomorphism.

`Scheme.baseChangeDiagramMapHom` transports an actual map between modeled
charts along a later-stage arrow. Its two projection equations, naturality
and compatibility with the limit-cone comparison identify the map.
`Scheme.exists_baseChange_map_eq_of_isLimit` detects equality of two actual
`Over` morphisms at a later stage from equality of their literal base-change
maps. Its source map is QC and its target map locally of finite type.

`Scheme.exists_isIso_baseChange_map_of_isLimit` detects isomorphism of the
literal base change of a given map of finitely presented stage schemes.
It imposes no flatness or injectivity condition on transition maps. The
proof descends an inverse, detects both inverse equations at finite stages,
and transports them to one common stage. The more general
`exists_isIso_baseChangeNatTrans_of_isLimit` applies to compatible maps of
the canonical base-change systems with a specified isomorphism at the limit.
Both eventual-isomorphism statements need only locally finite presentation
and quasi-compactness of the source structural map; quasi-separatedness is
required only for the target structural map.

For an existing native `Scheme.GlueData`,
`GlueData.quasiSeparatedSpace_of_compact_overlaps` proves that affine
charts with quasi-compact overlaps glue to a quasi-separated scheme.
`GlueData.compactSpace_of_finite` proves quasi-compactness for finitely
many affine charts. `GlueData.toBase` glues the given compatible structural
maps, and `GlueData.finitePresentation_toBase` proves LFP, QC and QS when
the base is affine and the chart maps are LFP.

These supply the open-model and gluing steps used by
[Schemes](Schemes.md), which descends arbitrary finitely presented qcqs
schemes and finite functors of such schemes. Its proof arranges the actual
overlap identifications and their cocycles at one stage. No assumption of a
pre-existing family of general scheme models is hidden in the open-model
theorem.

Native dependencies are Mathlib's `AffineTransitionLimit`, `Gluing`, and
pullback/restriction APIs at revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

`Scheme.exists_iso_between_baseChanges_of_isLimit` is the bounded
existence corollary for two already supplied FP models and a given iso of
their literal limit base changes. It returns an actual `Over` iso between
the literal original models at one later stage. The construction uses Hom
descent, eventual isomorphism and native pullback pasting. This corollary
does not state equality of a particular final iso with the supplied limit
map; that stronger comparison is separate from the property-transfer use.
No flatness or injectivity of transition maps is assumed.
