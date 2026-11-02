# The original stalk map at a surviving curve

Source: [CurveStalk.lean](CurveStalk.lean).

`Hom.isIso_stalkMap_of_mem_targetIsomorphismLocus` proves that the original
stalk map is invertible at any point mapping into the target isomorphism
locus, using the restriction-stalk comparison.

For a proper dominant birational map of integral schemes to a normal locally
Noetherian target of dimension at most two,
`isIso_stalkMap_genericPoint_of_not_subsingleton_image` gives this conclusion
at the generic point of any irreducible closed subset with nonsubsingleton
image. This is the map used to compare the old and new selected-curve DVRs.

Present consumers: [CurveSurvival](CurveSurvival.md).
