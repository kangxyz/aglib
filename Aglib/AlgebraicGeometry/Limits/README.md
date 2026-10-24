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

[Monomorphisms](Monomorphisms.lean): factorization through a monomorphism is
local on the source (`Scheme.exists_lift_of_mono_of_forall_exists`); a point of
a coproduct `∐ X` lies in the image of one component (`Scheme.exists_sigmaι_eq`);
and `∐ X ⟶ S` induced by monomorphisms with pairwise disjoint images is a
monomorphism (`Scheme.mono_sigmaDesc_of_pairwise_disjoint`). The statements use
points, opens and covers of schemes. The flattening stratification
(`FlatteningStratification/Flatness`) consumes them.

[OpenImmersionIntersection](OpenImmersionIntersection.lean) proves that specified open-chart factorizations
with actual image intersection form a cartesian square.

[FibreProductBaseChange](FibreProductBaseChange.lean) proves `Scheme.isPullback_pullbackMap_snd`:
for `p : X ⟶ S` and `f : T' ⟶ T` with `f ≫ g = g'`, the map
`pullback.map p g' p g (𝟙 X) f (𝟙 S)` (the map of `RelativePicard.familyScheme p`) and the second
projections form a cartesian square over `f`. No hypothesis on the morphisms is used. The
[immersed Hilbert functor](../HilbertScheme/Immersed/Functor.lean) consumes it, and the base change
of relative effective Cartier divisors on `X ×_S T` (F14) is its next consumer.
