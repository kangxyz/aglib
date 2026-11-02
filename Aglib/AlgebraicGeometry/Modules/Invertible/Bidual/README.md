# Bidual evaluation, naturality and restriction

[Map](Map.lean) defines `doubleDualMap` from the original internal-Hom
precomposition twice and proves naturality of bidual evaluation.
A map into an actual line extends through its bidual by
`extendToBidualLine`. [Naturality](Naturality.lean) proves composition and
pre/postcomposition laws for these same maps on arbitrary module sheaves.

[AffineGlobalSections](AffineGlobalSections.lean) compares bidual sections
with the algebraic double dual when the coefficient and its sheaf dual
are quasicoherent. [AffineNaturality](AffineNaturality.lean) and
[AffineGlobalNaturality](AffineGlobalNaturality.lean) retain the original
coefficient morphisms.

[OpenRestriction](OpenRestriction.lean) and
[OpenNaturality](OpenNaturality.lean) give evaluation and naturality on the
same affine open. Their explicit quasicoherence inputs cover the
coefficient, its dual and bidual, and the corresponding affine duals.
[CoherentOpenRestriction](CoherentOpenRestriction.lean) supplies that
comparison for an affine-locally finite-type coefficient on a locally
Noetherian scheme. Relative-form and one-pole consumers use these original
evaluation squares.

Present consumers include [Relative forms on saturated regular-pair charts](../../../Blowup/Differentials/RegularPair/README.md), [Relative differentials over arbitrary scheme bases](../../Differentials/Relative/README.md).
