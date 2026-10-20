# Universal property of the original affine Rees Proj

`AffineUniversalProperty.lean` proves `Scheme.Blowup.affineProjMap_universal`:
for every commutative ring `A`, ideal `I`, scheme `T`, actual map
`f : T ⟶ Spec A` and original premise
`cartierPullback (affineCenter A I) f`, there is exactly one
`g : T ⟶ affineProj I` with `g ≫ affineProjMap I = f`.

Both `affineProj I` and `affineProjMap I` are the unchanged native Rees Proj
and its published base map. No desired cover or factorization is a premise.
There is no Noetherian, finite-generation, regularity, reducedness, separation
or affineness assumption on the test scheme.

The proof first constructs the actual affine pivot cover in
`AffineLiftingCover.lean`. A map into any native chart lands in a regular
pivot chart because the original fraction equation and regular cancellation
make the overlap ratio a unit (`affineChartHom_range_pivot`). Applying this
on an affine refinement of the pulled-back native Proj cover proves
`affineProjHom_range_pivot`; flatness of open immersions preserves pivot
regularity. The saturated-chart uniqueness theorem then gives affine
uniqueness, and the produced source cover gives `affineProjHom_ext` for
arbitrary test schemes.

The actual image-ideal comparison along open immersions transports the
Cartier premise to source overlaps. Uniqueness proves compatibility of the
local maps on literal pullbacks. Native `glueMorphisms` constructs
`affineProjLift`; `affineProjLift_map` is its original base triangle.

`affineProjBlowupDatum I` realizes the existing interface with these exact
objects, the previously proved Cartier property and the new universal
property. Properness over a Noetherian base remains the separate existing
theorem. Blowups over arbitrary nonaffine bases and their global flat-base-change
theorem are outside this affine construction.

The focused client is `AglibTest.AffineBlowupUniversalProperty`, including
the original arbitrary-test statement, exact object/map identities, the
nonreduced ring `ZMod 4` and the zero-centre empty-test boundary. Compilation
receipts are maintained separately from this mathematical guide.
