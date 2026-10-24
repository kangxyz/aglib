# Structure direct images of an actual regular point blowup

`Scheme.Cohomology.isZero_higherDirectImage_structure_of_regular_point`
proves vanishing of every positive higher direct image of the canonical
structure module on the original blowup of a closed point. The original
source is locally Noetherian with regular stalks, and the actual local
ring at the point has dimension two.

The centre is the full kernel ideal of `X.fromSpecResidueField x` and the
blowup is exactly its native `blowupDatum`. A private lower construction
embeds any actual two-generated affine blowup in
`ProjectiveSpace A (ULift (Fin 2))`, with the native common geometric
universe and the original equivalence to `Fin 2`.
The full ideal generators give the original degree-one Rees evaluation;
the generator-induced closed immersion and the canonical comparison of
blowup data preserve the original structural map. The ClosedLine theorem
then kills positive cohomology of the actual affine blowup's structure
module, without a normality or flatness premise.

Higher direct images are checked on their actual module stalks using
`moduleHigherDirectImageStalkLinearEquiv`. Its target is cohomology on
the literal pullback along `X.fromSpecStalk y`. The original coefficient
module there is identified with the canonical unit by
`Scheme.Modules.pullbackUnitIso`.

At the centre, `Blowup.RegularPoint.stalkBlowupIso` identifies that actual
pullback with the maximal-ideal blowup of the original local ring. The
native regular parameters generate its full maximal ideal. At every
other point the pulled centre ideal is the unit ideal, so the actual
pullback projection is an isomorphism and affine acyclicity applies.
Only the local-spectrum maps are used as flat maps.

For integral original `X`,
`isIso_structureModuleMap_of_regular_point` identifies the ordinary
original structural unit as an isomorphism. The literal one-step point
chain supplies integrality, dominance and the original birational field
map; regularity supplies normal stalks of `X`, and the constructed blowup
is proper. The existing proper-birational-normal unit theorem applies to
these derived conditions.

No Nagata, completeness, general resolution, flat blowdown, supplied
acyclicity or replacement model is a premise. The
[regular-local universal vanishing theorem](../../Surfaces/RationalSingularities/Regular.md)
uses this result in point-chain cohomology induction and then applies the
[original birational H1 injection](../Proper/BirationalFirstCohomology.md)
to each supplied normal proper birational model.
