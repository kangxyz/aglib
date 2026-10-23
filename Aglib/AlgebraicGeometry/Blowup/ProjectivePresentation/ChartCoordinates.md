# The original projective map on scalar blowup charts

[ChartCoordinates.lean](ChartCoordinates.lean) combines three actual
producers: the scalar chart and original projections in `ScalarChart`,
the original framed-row coefficient formula in `RowCoordinates`, and the
native graded augmentation chart in `DegreeOneAugmentationChart`.

The original row frame is constructed from the same `ChartTriangleEq`
provided by the scalar chart. Its equation is consumed in a generic frame
constructor and coefficient theorem before concrete scalar specialization.
The native augmentation comparison uses the chart witness's proved original
arrow equation through a generic composition helper.

The concrete S-linear scalar ratio map satisfies the proved pure-tensor
formula. Thus the original finite quotient row has the same coefficients
as its polynomial Rees presentation. The actual original denominator is a
linear combination of the same full tensor generators. Adding that
coordinate gives a closed augmentation retaining all original coordinates.
The native chart equations identify the two morphisms after augmentation;
monicity and the derived original denominator cover prove
`OriginalRowRestriction.mapOfFramedPresentation_eq_embedding`.
The same original map is closed and retains its original Spec S triangle.

No flatness, domain, reducedness, or image-ideal blowup identity is assumed.
`Embedding.lean` uses this exact original-map equality to prove the relative
coordinate graph closed and construct the finite projective embedding.
