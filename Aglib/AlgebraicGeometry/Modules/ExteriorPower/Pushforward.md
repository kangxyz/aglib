# Exterior coefficients under pushforward

Source: [Pushforward.lean](Pushforward.lean).

For any scheme morphism g : X → Y and ordinary coefficient arrow
φ : M → g_*N, `exteriorCoefficientMap g φ n` is the actual morphism
∧ⁿM → g_*(∧ⁿN). Its defining alternating family wedges the original
section images on each inverse-image open. Scalar compatibility uses g.app,
not a replacement scalar action. Neither flatness nor local freeness nor an
open-immersion hypothesis is imposed.

This module is the sole implementation extracted from the existing private
generic block of `Cohomology/Duality/Projective/DifferentialTrace/Restriction`.
The original consumer imports this owner, with the proof bodies and maps
unchanged. The integral differential trace needs the same exterior coefficient
construction for non-open proper birational maps; this extraction avoids a
second implementation or importing the full projective differential trace.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/DifferentialTrace/Restriction](../../Cohomology/Duality/Projective/DifferentialTrace/Restriction.lean), [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorAffineRestriction](../Differentials/Relative/ExteriorAffineRestriction.md), [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficient](../Differentials/Relative/ExteriorCoefficient.md).
