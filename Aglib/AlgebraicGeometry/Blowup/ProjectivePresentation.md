# Tautological coordinates after arbitrary blowup base change

[ProjectivePresentation.lean](ProjectivePresentation.lean) works with the
original `B : BlowupDatum I` and the literal fibre product `B.Y ×[X] W`
for an arbitrary morphism `f : W ⟶ X`.

`tautologicalQuotient` is the canonical epimorphism from the full module
pullback of the original ideal to its invertible image ideal on `B.Y`.
`pulledTautologicalQuotient` pulls this epimorphism through the original
cartesian square. Its target is the pulled-back invertible module. Its
source is the pullback of `degreeOneModule`, which is the full module
`f*I`, including its possible torsion.

When `X` is locally Noetherian and `W` has an actual closed embedding into
finite-coordinate projective space over a commutative ring, the existing
coherent presentation theorem supplies a finite common-negative-twist
quotient of `f*I`. The module's finite-type hypothesis is proved.
`exists_commonTwistQuotient` pulls this quotient to the fibre product;
`exists_finite_twistedTautologicalFamily` uses the existing native
`FromSections.LineSource` construction to cancel the common invertible
source and produce an epimorphic finite family of actual global sections.
`coordinateMap` is the native `LineSource.mapOfFamily` for the original
coproduct row of the supplied quotient. `commonTwistQuotient` retains its
construction from the original base presentation, and
`coordinateMapOfPresentation` applies the coordinate map to that exact
quotient. This retains every original coordinate and the native
twisting-pullback comparison. `exists_projectiveCoordinates` returns the
original epimorphic base presentation together with the exact structural
triangle of its canonical coordinate map.

No flatness is assumed. The literal fibre product is not identified with
the blowup of the image ideal on `W`, and that image ideal is not asserted
to remain Cartier. This distinction is necessary for the Chow modification
consumer in proper-surface projectivity.

The missing geometric step is to prove that the coordinate graph over
`W`, for the family arising from the full degree-one presentation, is a
closed immersion. The present leaf does not prove this step or a finite
standard projective embedding of the fibre product. It does not prove
projectivity of a point-blowup chain over the final affine base.

The intended mathematical comparison is the Rees degree-one quotient in
[Stacks 02NS](https://stacks.math.columbia.edu/tag/02NS). The formal results
above concern the constructed module maps and their stated hypotheses;
this reference does not discharge the remaining closed-immersion proof.
