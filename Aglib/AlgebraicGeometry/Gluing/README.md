# Gluing on actual scheme covers

[OpenImmersion](OpenImmersion.lean) proves coverage, overlap equality, the
cartesian overlap square, compactness and separatedness criteria for Mathlib's
actual open-immersion pushout. Its declarations belong to `Scheme`,
`Scheme.OpenNormalizationGluing` and `Scheme.SeparatedGluing`. The normalization
map API starts from a supplied map of one chart and its actual overlap equation;
its finiteness conclusion also requires the displayed inverse-image equality.
[Coproduct](Coproduct.lean) compares a doubled open pushout with the coproduct
of its pushouts. `Scheme.OpenPushout.coprodDesc_proper_of_proper` proves
properness of `coprod.desc p q` for two proper maps to the same base;
`coprodDesc_proper p` retains the repeated-map specialization.

[ProperModification](ProperModification.lean), in
`Scheme.OpenPushout.Modification`, replaces one actual open chart by a supplied
proper modification that is an isomorphism on the overlap. It constructs the
pushout, both open charts, their cartesian squares, the proper map to the original
scheme and the actual isomorphism on the unchanged open. It does not construct
the input proper modification. [SourceOpenCover](SourceOpenCover.lean), in
`Scheme.SourceOpenCover`, glues actual two-open maps and tests cartesian squares
on arbitrary supplied open source charts.

[ReducedClosedUnion](ReducedClosedUnion.lean) proves binary reduced closed-cover
descent into an arbitrary scheme. The ambient scheme and both covering pieces
are reduced; their intersection is the literal scheme pullback, including its
nilpotents. No separatedness condition on the target is needed. The file proves
the ring pullback from the two surjective maps and zero kernel intersection,
then constructs the scheme pushout, descent and exact base triangles.

[FiniteClosedCover](FiniteClosedCover.lean) constructs each actual finite union
from the intersection of the component kernel ideals. Joint uniqueness holds
for reduced closed pieces covering a reduced ambient scheme. Existence of
finite descent retains reducedness of every actual partial-union overlap used
by the induction. Pairwise overlap reducedness alone is not substituted for
that condition. The isomorphism and `Over` APIs retain both full-pullback
compatibilities and both sets of partial-overlap conditions.

[TwoPoint](TwoPoint.lean) identifies two complementary rational open charts with
the actual spectrum of a product of fields. It uses Mathlib's canonical
`coprodSpec`, preserves both literal projection maps and proves the exact
structure-map triangle.

The new graph and curve constructions consume these interfaces. Provenance is
recorded in each leaf; no native module imports its R5 source.

## Cartesian open pushout maps and schematic density

[OpenPushoutMap](OpenPushoutMap.lean), imported as
`Aglib.AlgebraicGeometry.Gluing.OpenPushoutMap`, studies the native
`pushout.map f g f' g' b c a hf hg`, in `Scheme.OpenPushoutMap`.
All four gluing arrows are open immersions.
`isPullback_inl` uses the opposite overlap square `IsPullback a g g' c`,
while `isPullback_inr` uses `IsPullback a f f' b`.
`isAffineHom` needs both squares cartesian and both chart maps `b,c` affine.
The projection order and overlap equations are those of the original
pushouts. [Arithmetic system gluing](../Approximation/FinitePresentationEnvelope/README.md)
and [finite-presentation descent](../Descent/FinitePresentation/README.md)
consume these maps.

[OpenUnionPushout](OpenUnionPushout.lean), imported as
`Aglib.AlgebraicGeometry.Gluing.OpenUnionPushout`, proves
`Scheme.isPushout_of_isPullback_of_openCover`: a cartesian overlap of two open
immersions whose ranges cover the target is a scheme pushout.
`isPushout_opens_of_sup_eq_top` specializes to actual opens `U ⊔ V = ⊤`.

[SchematicDensity](SchematicDensity.lean), imported as
`Aglib.AlgebraicGeometry.Gluing.SchematicDensity`, gives
`Scheme.Cover.glueMorphismsOfSchemeTheoreticallyDominant`. For an open cover
of `X`, compatible maps over `S` to a separated `Y ⟶ S` agree on overlaps
when they agree after a quasi-compact schematically dominant `j : U ⟶ X`.
The constructed map retains each chart map, its composite with `j`, and its
map to `S`. Quasi-compactness of `j`, schematic dominance and relative
separatedness are explicit hypotheses. This is the map-gluing input used
in the finite-cover [compactification construction](../Compactification/README.md).
