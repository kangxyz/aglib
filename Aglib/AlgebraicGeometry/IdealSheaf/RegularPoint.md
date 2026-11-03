# Actual affine regular-pair neighbourhoods of the point ideal

`RegularPoint.lean` uses the original affine section rings and the original
residue-point kernel ideal throughout. `Scheme.exists_regularPair_basicOpen`
starts with an actual affine open U containing x, Noetherianity of its section
ring, and a regular original stalk of dimension two. It produces one native
principal open D(f) containing x and two actual sections a,b there. Their
span equals exactly `(X.fromSpecResidueField x).ker.ideal (X.affineBasicOpen f)`.
The ideal is proper, a is regular on the section ring, and b is regular on
the quotient by the principal ideal of a.

The native germ algebra identifies the actual stalk with the canonical
localization at the original chart prime. Regularity and dimension pass
through the native localization algebra equivalence. The existing complete
`IsRegularLocalRing.exists_regularPair_away` produces the pair on one Away
ring. Its single native localization equivalence to the actual section ring
uses precisely the original principal-open restriction algebra. Exact ideal
transport uses the algebra-map equation and `ResiduePoint`'s basic-open law.
One native `Ideal.quotientEquiv` transports the second regularity witness.
There is no copied colon-clearing or regular-parameter implementation.

Properness follows from the point surviving in D(f) and the exact original
chart prime there; it is not inferred from weak regularity alone. No domain,
closed-point, globally local section-ring, J2, excellence, finite-type, or
field-of-definition hypothesis is added. The core requires Noetherianity
only of the supplied original affine section ring. The scheme, opens, germs,
restriction maps, quotient carriers, and scalar actions retain their native
universe and identities.

`Scheme.exists_regularPair_affineOpen` is a thin locally Noetherian consumer.
Given any original open W containing x, it chooses an actual affine U inside
W, derives its section-ring Noetherianity, and applies the same construction.
Its output V is an affine open of the SAME X, with x in V and V contained in
W, not an arbitrary equivalent affine scheme.

The first normal whole-owner check of source `aa85c584` (`reupload-own-197`)
returned four ordinary proof-view errors in 3.5 s leaf time / 5.7508 s total,
with exit 1 and no aggregate guard. The current source repairs only native
preimage membership, the original algebra-equivalence projection values, and
separately typed source/target quotient scalar laws. Those failed checks
were not acceptance of the geometric bridge, nor was the separate acceptance
of its original algebraic Away and exact point-ideal suppliers. The follow-up normal check of `811f1a62`
(`reupload-own-200`, 3.7 s leaf / 6.256 s total) returned only three ordinary
projection-view errors, with exit 1 and no aggregate guard. The current
repair inserts the native explicit-projection equations before the same
coercion value laws, retaining the entire original quotient equality chain.
The resulting complete source `a16e7f83` then passed normal native
`reupload-own-202` in 3.6 s leaf / 6.0478 s total (2762 jobs), exit 0, no
aggregate guard, and owned group gone. Both the exact basic-open construction
and the thin actual affine-neighbourhood corollary are included in this pass.
This does not prove global one-pole gluing or trace. Reverse orientation requires
the genuine domain hypothesis at its original geometric consumer; under
integrality, the surviving point supplies nonemptiness of the section ring's
open before using the existing proper-pair swap theorem. A two-open cover
by V and the centre complement requires a closed point. Neither that cover,
its actual blowup comparison, nor global one-pole gluing is constructed here.
