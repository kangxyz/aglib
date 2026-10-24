# Units and square-zero quotients of ring sheaves

The objects are native `Sheaf J CommRingCat` and `Sheaf J AddCommGrpCat`, on an
arbitrary site. Ring sections and their original maps are retained. The
current consumer is square-zero line-bundle lifting in the Picard step of
etale proper base change.

[Units](Units.lean) defines `CommRingCat.unitsAddFunctor` using the native
right adjoint on commutative monoids and the native additive-group equivalence.
`Sheaf.units`, `unitsMap`, `additive` and `additiveMap` are applications of
Mathlib's existing `sheafCompose`, without a new sheafification construction.
Additive forgetting records `UnivLE.{max u v,w}` for a site in object/Hom
universes `u,v` and coefficient universe `w`.

[SquareZeroUnits](SquareZeroUnits.lean) proves
`Sheaf.unitsMap_isLocallySurjective`. Its hypotheses are actual local
surjectivity of the ring-sheaf map and square-zero section kernels. A unit and
its inverse lift on the intersection of their two covering sieves; there is
no surjectivity premise on all sections over every object.

[SquareZeroKernel](SquareZeroKernel.lean) and
[SquareZeroKernelIso](SquareZeroKernelIso.lean) construct the actual maps
`1+x` and `u-1` between the native additive and unit kernel sheaves.
`oneAddUnitsKernelIso` is an isomorphism with the original kernel inclusions,
not just an objectwise group correspondence.

[SquareZeroSequence](SquareZeroSequence.lean) gives
`squareZeroUnitsComplex_shortExact` in the actual abelian-sheaf category.
It uses the native additive kernel, original one-plus inclusion and original
map on units. This layer retains `HasSheafify J AddCommGrpCat`.

[SquareZeroCohomology](SquareZeroCohomology.lean) uses original `Sheaf.H`,
`H.map` and `H.δ`. It defines `squareZeroUnitsObstruction`, proves lifting of
classes with zero obstruction, and proves surjectivity when the next additive-
kernel cohomology group is a subsingleton. `HasExt` and its size are explicit.
The application at degree one still requires Picard classification and the
actual coherent-kernel H2 vanishing; those conclusions are not supplied here.

The lower ring-only inputs are
[square-zero units](../../../../RingTheory/Ideal/SquareZeroUnits.lean) and
[ideal-power quotient kernels](../../../../RingTheory/Ideal/PowerQuotientSquareZero.lean).
No flatness, Noetherianity or invertible-order hypothesis enters these generic
unit-sequence results.

[SquareZeroSplitting](SquareZeroSplitting.lean) adds a ring section `s` with `s ≫ f = 𝟙`.
Then `f` is locally surjective (`isLocallySurjective_of_section`), `squareZeroUnitsSplitting`
splits the original unit sequence with section literally `unitsMap s`, and in every degree
`squareZeroUnitsCohomologyEquiv : H^n(R^*) ≃+ H^n(I) × H^n(S^*)` and
`squareZeroUnitsCohomologyKerEquiv : ker H^n(unitsMap f) ≃+ H^n(I)` (through the one-plus
map). The generic statements for split short complexes of abelian sheaves are in
[CategoryTheory/Sites/SheafCohomology/Splitting](../../../../CategoryTheory/Sites/SheafCohomology/Splitting.lean).
The consumer is the Picard tangent space.
