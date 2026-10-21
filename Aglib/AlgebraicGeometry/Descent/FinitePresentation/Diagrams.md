# Common stages for finite scheme data

Import `Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams`.

For `D : I ⥤ Scheme`, a stage `i`, and `f : X ⟶ D.obj i`,
`Scheme.baseChangeDiagram D i f` is the concrete functor
`Over.post D ⋙ Over.pullback f ⋙ Over.forget X`. Its objects are the literal
pullbacks `pullback (D.map j.hom) f`. `Scheme.baseChangeCone` has point
`pullback (c.π.app i) f`, and `Scheme.isLimitBaseChangeCone` proves it is
limiting when `I` is cofiltered and `c` is a limit cone.

Affine transition maps remain affine. If `f` is quasi-compact and the bases
are quasi-compact, the source system is quasi-compact. The analogous
quasi-separated statement uses `QuasiSeparated f` and quasi-separated bases.
These are proved properties of the constructed diagram, rather than an
assumed family of models or comparison squares.

`Scheme.exists_hom_between_baseChanges_of_isLimit` descends an actual map
between the limit base changes of two stage schemes. It constructs a map
between the literal pullbacks at a later stage, preserving its base triangle
and equality after the canonical limit-cone projections. The source model
is QC and QS, the target is LFP, and the base diagram is affine. This bridge
uses native factorization and reconstructs the stage map by the universal
property of the actual target pullback.

`Scheme.exists_common_stage_factorizations_of_locallyOfFinitePresentation`
puts a finite family of limit morphisms at a single stage, with all original
structural triangles. The source systems may differ, but share the same
cofiltered category. Their objects must be qcqs, transitions affine, and
targets locally of finite presentation.

`Scheme.exists_common_stage_equalities_of_locallyOfFiniteType` puts finitely
many equations at a common later stage. Its targets need only be locally
of finite type, and its source objects quasi-compact. Neither theorem
assumes separatedness of a target. The empty finite family is allowed.

The finite-family results aggregate the native factorization and eventual
equality theorems in Mathlib's `AlgebraicGeometry/AffineTransitionLimit.lean`
at revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. They do not themselves
construct general nonaffine object models or descend an arbitrary finite
functor with its composition laws. Their immediate consumer is the finite
map and equation data in scheme gluing.
