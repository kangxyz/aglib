# Coefficient descent on the actual rational blowup

Source: [ExceptionalCoefficientVanishing.lean](ExceptionalCoefficientVanishing.lean).

For the original ordinary blowup T of a rational normal Nagata local surface S,
let M be an actual finitely presented coefficient module. Retain monicity of its
actual Cartier tensor section and an actual restriction isomorphism
`i* M ≅ Ω_(E,V) ⊗ L`, with the full exceptional curve, original projective
embedding and O(1) comparison, and finite rank-one coefficient V.

Native Serre vanishing on T/S supplies the high-degree start. The original
Cartier row, tensor comparisons, projection formula and positive coefficient-
canonical curve vanishing supply one finite descent, proving H1 of every
nonnegative original ideal power tensored with M vanishes. The final theorem
proves section lifting through the literal original adjunction unit.

There is no vanishing premise, no choice V≅κ, and no R or finite R S requirement.
The geometric coefficient restriction and Cartier monicity are genuine inputs,
not inferred for an arbitrary M. In particular a later-stalk application must
construct them for the actual pullback of the original global canonical object.

This is the unique descent/section-lifting proof body; the original initial
ExceptionalCanonicalVanishing statements are wrappers deriving their unchanged
actual canonical inputs.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalizedExceptionalCanonicalVanishing](LocalizedExceptionalCanonicalVanishing.md).
