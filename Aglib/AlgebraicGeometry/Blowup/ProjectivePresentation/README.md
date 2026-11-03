# Projective presentations of the original blowup

[AffineCoordinates](AffineCoordinates.lean),
[AffineRow](AffineRow.lean) and [RowCoordinates](RowCoordinates.lean)
retain the actual blowup datum, its ideal quotient and original sections.
The affine comparison uses the full module `S ⊗[R] I`, including torsion;
its section formula sends `b ∈ I` to `1 ⊗ b`. A framed presentation row
keeps the supplied line frame and original quotient map.

[ChartCoordinates](ChartCoordinates.lean) identifies the projective map
on the same saturated scalar charts using the original ratio coefficients
and graded augmentation comparison.

[OriginalEmbedding](OriginalEmbedding.lean) constructs a finite-coordinate
projective embedding of the same blowup source from a supplied
finite-coordinate projective embedding of a locally Noetherian scheme.
The original structural triangle is part of the conclusion.
No Noetherian hypothesis on the base ring, integrality, normality or
dimension bound is added. Projective-stage and finite-domination
constructions use this embedding.

Present consumers include [Canonical coefficients on embedded normal surfaces](../../Cohomology/Duality/Projective/Relative/NormalSurface/README.md), [Original point blowups of rational surface stalks](../../Surfaces/RationalSingularities/Blowup/README.md).
