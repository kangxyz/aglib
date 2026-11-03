# Intrinsic self-injective dimension gives an actual canonical frame

Let `q:R→S` be a finite homomorphism, with `R` regular local of specified
finite dimension and `S` Noetherian local. Suppose the original ambient
Ext from the restricted regular `S` module to `R` is concentrated in degree
`n`. Keep `K` equal to the degree-`n` homology of the installed derived
coinduction of the original regular `R` module.

`coinducedHomologyLinearEquivOfSelfInjectiveDimension` constructs an actual
`S`-linear equivalence `K ≃ S` from a native finite self-injective-dimension
bound for `S`. The proof uses the previously proved finite projective
dimension of `K`, its positive self-Ext vanishing, and top-Ext detection to
obtain projectivity. Native finite local freeness and the original scalar
homothety `S ≃ End(K)` give `rank(K)^2=1`; native rank-one classification
then chooses a frame. This frame is not claimed to have a preferred
normalization.

The `OfIso` variant first transports an actual ambient coefficient-line
frame through the same original derived-coinduction and homology functors.
No second canonical module or substitute scalar action is introduced.

The statement retains the selected ambient Ext and both derived-category
sizes. It assumes neither a complete target nor target projectivity over
the ambient ring. Finite generation, homothety, duality, projectivity and a
canonical trivialization are not premises. There is no new Gorenstein
predicate: the input is intrinsic native finite self-injective dimension.
Normal-quotient concentration, the reverse implication, and geometric
canonical-stalk comparisons are separate interfaces.
