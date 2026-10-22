# Actual exceptional normal at a closed scheme point

This file transports the local regular-point geometry to the literal exceptional
fibre of an actual closed point on an arbitrary scheme. The assumptions are precisely
`hx : IsClosed ({x} : Set X)`, `[IsRegularLocalRing (X.presheaf.stalk x)]`, and
`hd : ringKrullDim (X.presheaf.stalk x) = 2`. It adds no global locally Noetherian, regular,
integral, excellent, Henselian or completeness hypothesis.

## Literal schemes, ideals and structure maps

`pointBlowupDatum X x` is the original
`blowupDatum (X.fromSpecResidueField x).ker`. `pointBlowup X x` and `pointBlowdown X x`
are its scheme and morphism. `pointExceptionalFibre X x` is literally
`pullback (pointBlowdown X x) (X.fromSpecResidueField x)`. Its original first and second
projections are `pointExceptionalι` and `pointExceptionalStructureMap`.

The residue field is the original `X.residueField x`, whose native definition is the residue
field of `X.presheaf.stalk x`; no field extension is introduced. The inverse-image-centre
and literal-fibre comparison preserves the original immersion. `pointIdealLine` has value
EXACTLY `idealModule (pointExceptionalι X x)`, with its actual rank-one property transported
from the original blowup Cartier ideal. `pointIdealCentreIso_hom_inclusion` retains the
original inclusion. `pointExceptionalι_isClosedImmersion` gives the closed immersion.
`pointConormalLine` is pullback of this actual kernel ideal; `pointNormalLine` is pullback
of its actual dual by the original exceptional immersion.

## Canonical local-to-global comparison

The existing `stalkBlowupComparison_isPullback` is an actual flat base-change square.
Pasting with the original local residue-fibre square produces `stalkExceptionalIso`.
The equations `stalkExceptionalIso_hom_ι` and `stalkExceptionalIso_hom_over` keep both
literal projections. Composing with the original local centre/fibre isomorphism produces
`stalkCentreFibreIso`, with the corresponding actual immersion and residue-field triangles.

The stalk comparison is flat and a monomorphism. Its square of original exceptional
immersions is therefore Cartesian. The native `idealPullbackMap_isIso_of_flat` applies:
the original exceptional immersion is closed, hence affine, and the comparison between
blowups is flat. It needs neither flatness of the exceptional quotient nor a global integral
model. `stalkPointIdealIso_hom_inclusion` retains the exact canonical ideal map, original
inclusions and native unit. The map inverted here is along the flat stalk comparison;
the blowdown is used to form the original inverse-image centre.

Canonical pullback associators and equality comparisons give `stalkPointConormalIso`.
Its forward formula preserves those actual components. The checked local O(1) comparison
is transported through the actual fibre isomorphism using the native pullback unit and
composition maps; `pointConormalTwistingIso_inv_formula` records this exact transport.
No local cocycle theorem is duplicated and no desired global comparison is a premise.

## Global endpoint interfaces

`pointExceptionalOverIsoProjectiveP1 X x hx hd` identifies the literal exceptional fibre
with native polynomial P1 over the SAME original residue field. Its forward structural
triangle and the comparison with the original local P1 map are explicit.
`pointNativeComparison_projectiveP1` identifies the native twisting coordinates with that
same actual Over-P1 map followed by canonical finUlift coordinates.

`pointConormalProjectiveP1Iso` identifies pullback of native O(1) with the actual conormal.
`pointNormalProjectiveP1Iso` identifies the actual restricted dual with pullback of native
O(-1). The latter uses the actual conormal/normal evaluation and native multiplication of
positive and negative twists; `pointNormalTwistingIso_tensor_hom` retains the exact original
evaluation equation. These are actual module isomorphisms, not only numerical degrees or
Picard-class equalities. Native invariants can be transported through the displayed actual
Scheme isomorphism; separate counting, dimension and contraction interfaces have other owners.

Numerical self-intersection and contraction have separate interfaces.
