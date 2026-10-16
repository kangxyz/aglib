# Finite native projective products

`Derived` proves
`Scheme.Cohomology.finiteProjectiveProduct_derived_bounded_coherent`.
The product is exactly `Scheme.finiteProductOver P`, built from native
binary products in `Over S`. Each displayed component comes with its
original Cartesian square to polynomial projective space over `Spec R`
and a coordinate equivalence `ι i ≃ Fin (d i + 1)`.

Over a locally Noetherian base `S`, the original structure morphism's
installed derived pushforward preserves the sole shared
`coherentHomologyObjects` property on every cohomologically bounded input.
It sends bounds `[l,b]` to `[l,b + ∑ i, d i]`. The original ring `R` need
not be Noetherian; no relative-flatness or representative-term condition
is imposed. The source's locally Noetherian guard forms the shared input
property and follows from properness of this finite product.

The successor step uses the original over-product projections and
`Over.isPullback_of_binaryFan_isLimit`, then the proved
[relative projection](../Projection/README.md) theorem and original
`derivedPushforwardPlusCompIso`. The empty family is the actual identity
of `S`, compared through the original pushforward identity and installed
derived-identity comparison. No second product object, Segre embedding,
Chow theorem or general proper-finiteness family is introduced.

`BaseChange.projectiveProductProjection_derived_bounded_coherent` now gives
the same result for the original first projection of the actual fibre
product with any locally Noetherian base over `Spec R`. Its comparison is
the original `productBaseChangeIso`; the exact base projection equation and
native derived composition preserve the displayed morphism. The sole
finite-image theorem applies to that geometric isomorphism with amplitude
zero. The source's locally Noetherian guard is supplied by the proved
`ProjectiveSpace.isLocallyNoetherian_productPullback`.

`Finite.finiteOverProjectiveProduct_derived_bounded_coherent` composes this
same result with the sole finite-image theorem. It accepts an actual finite
map `i` into the original fibre product and a separately specified original
map `p` to the base, retaining the exact equation `i ≫ pullback.fst = p`.
Its single-coefficient version constructs source local Noetherianity
internally and works for every integer placement with the same uniform
product bound. Closed graph-product embeddings are included through the
native finite-morphism instance; finite pushforward on arbitrary module
sheaves is not assumed exact.

`Finiteness.moduleCohomology_finite_of_finiteToProjectiveProduct` proves
finite unchanged `Sheaf.H` in every natural degree for an actual finite
map into the original finite projective product over any Noetherian ring.
The scalar action is exactly the structural action of the independently
specified map `f`, with its original displayed factorization through the
product. The actual derived-single theorem in the same leaf retains
coherent homology and the uniform sum-of-dimensions bound in every integer
placement. The proof uses the sole affine section comparison once to
return from the installed direct image to the original cohomology.

These results supply both cohomology inputs for the actual
proper-modification cone, without importing general proper finiteness.
The [proper Chow consumer](../../Proper/Chow/README.md) now constructs the
modification internally and applies these same results uniformly to every
coherent coefficient, with one coefficient-independent product bound.
