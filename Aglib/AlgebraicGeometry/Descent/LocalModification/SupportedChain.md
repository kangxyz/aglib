# Serial globalization of the prescribed local point chain

Source: [SupportedChain.lean](SupportedChain.lean).

`globalize_normalizedChain_from_model` inducts on the actual supplied native
chain. The induction retains the original base `X`, closed nongeneric
support point, a proper normal integral intermediate global model isomorphic
off that point, its actual original-base localization square, and properness
plus punctured isomorphy of the *same actual total terminal local map*.

Each centre is the image of the prescribed local centre. `PointLocalization`
proves it closed and over the original support point. The full point ideals
and both ordinary/normalized blowups are compared by the original
localization maps. `FactorNormalization` forces finiteness of the next literal
global normalization from the terminal local factor. `NormalizationAway`
preserves the unchanged complement. The recursive output is a native chain,
not a product of terminal models. It retains exact length and the actual
terminal cartesian square and equation over the previous global model.

`exists_supported_normalizedChain_of_punctured` starts the induction at the
identity global model. It requires the actual proper supplied local chain
and punctured-isomorphism property, and produces the actual supported global
chain of the same length with the original terminal square. For surface
consumers the already proved proper-birational punctured-spectrum theorem
can discharge that punctured hypothesis; it is not an algebraization oracle.

[SurfaceChain](SurfaceChain.md) specializes the construction to the
normal Noetherian surface setting and derives punctured isomorphy.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/SurfaceChain](SurfaceChain.md).
