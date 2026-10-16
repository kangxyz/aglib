# Native scheme limits

[FiniteProducts](FiniteProducts.lean) supplies `Scheme.finiteProductOver` for a
family `Fin n → Over S`. The empty case is exactly `Over.mk (𝟙 S)`; each
successor is the actual binary product in `Over S`. The native
`Over.prodLeftIsoPullback` gives its original scheme pullback and structural-map
formula. This construction has no Noetherian or projective hypothesis.

`finiteProductOverπ`, `finiteProductOverLift`, and `finiteProductOverMap` are
assembled from the original binary projections, lifts and componentwise maps.
The projection equations and `finiteProductOver_hom_ext` retain their universal
property. `isProper_finiteProductOver`, `surjective_finiteProductOver`, and
`isIso_finiteProductOver` concern the actual structure map. The theorem
`isClosedImmersion_finiteProductOverMap` concerns the original product map of
closed component immersions.

The immediate consumers are finite products of proper graph closures and
finite towers of actual projective projections. No alternative scheme, Proj,
or cohomology object is introduced.

[FiniteProducts.BaseChange](FiniteProducts/BaseChange.lean) compares this same
fold with the original `Over.pullback f`. `finiteProductOverPullbackIso` is
assembled from the native limit-preserving binary product comparisons; its
empty-family map is exactly `pullback.snd (𝟙 S) f`. The forward and inverse
projection equations, actual new-base structure equation, and original
pullback-first-projection formula are public. No flatness, finiteness,
Noetherianity or projectivity hypothesis is imposed on `f`.
