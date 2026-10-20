# Gluing on actual scheme covers

[OpenImmersion](OpenImmersion.lean) proves coverage, overlap equality, the
cartesian overlap square, compactness and separatedness criteria for Mathlib's
actual open-immersion pushout. Its declarations belong to `Scheme`,
`Scheme.OpenNormalizationGluing` and `Scheme.SeparatedGluing`. The normalization
map API starts from a supplied map of one chart and its actual overlap equation;
its finiteness conclusion also requires the displayed inverse-image equality.
[Coproduct](Coproduct.lean) compares a doubled open pushout with the coproduct
of its pushouts and proves properness of the coproduct of a proper map.

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
