# The exceptional generator in the normalized-point stalk

Source: [ExceptionalGenerator.lean](ExceptionalGenerator.lean).

For integral `X` and a closed nongeneric point `x`,
`pointIdeal_isLocallyRankOne_normalizedPointBlowup` proves that the literal
normalized point blowup makes the inverse image of the full point ideal
`(X.fromSpecResidueField x).ker` locally rank one.

At a point `y` above `x`, `normalizedPoint_stalkGenerator` gives a nonzero
nonunit `d` in the actual new stalk. The maximal ideal of the original
target stalk extends under the original blowdown stalk map to `Ideal.span {d}`.
`pointCentre_stalkIdeal` and `stalkIdeal_comap` identify the ideals and map.

For two original maximal-ideal elements, `normalizedPoint_stalk_factor_pair`
constructs factorizations by this same `d` and retains both stalk-map
equations. The proof uses the ordinary blowup's Cartier ideal and its
dominant pullback to normalization. Regularity and finite normalization
are unnecessary for these local statements.

Present consumers: [SelectedStep](SelectedStep.md).
