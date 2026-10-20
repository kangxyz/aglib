# Actual global universal blowups

`Construction.lean` constructs `Scheme.Blowup.blowupDatum I` for the actual ideal
sheaf `I` of a scheme. It proves the original Cartier image-ideal condition and
the final-object property for every test scheme. The exact original
`NoetherianBlowupExistence` family is supplied by
`noetherianBlowupExistence`; its original locally Noetherian binder remains in
that interface. The construction itself requires no added Noetherian or
finite-generation premise.

For every actual affine base open `U`, `Construction.localDatum I U` is the
proved affine Rees Proj datum, transported through the canonical spectrum
isomorphism, for the literal centre `I.comap U.ι`. Inclusions of affine opens
give the existing canonical `BaseChange.map`. The proved flat-base-change
theorem makes these actual maps cartesian open immersions. Universal uniqueness
gives the identity and composition laws.

The diagram is locally directed: a point lying in two local images has a base
point in their intersection; an affine neighbourhood there supplies a common
smaller local datum. The actual cartesian transition squares lift the point to
that datum. Native `Scheme.IsLocallyDirected` gluing constructs the colimit and
its open cover. The structural maps form the original base cocone and induce
`Construction.map I`.

`map_preimage` identifies the inverse image of every affine base open with its
local chart in the colimit. `local_isPullback` proves the literal local
cartesian square. The actual ideal comparison along the chart open immersions
transports the local Cartier property to the glued scheme.

For an arbitrary test map with the original Cartier inverse-image centre,
these local pullback squares and the local universal properties prove global
homomorphism uniqueness. The local universal lifts over the pulled-back affine
base cover agree on literal overlaps by that uniqueness. Native
`glueMorphisms` gives the global lift and its original base triangle. These
proved fields assemble `blowupDatum I`; no cover, gluing, factorization or
existence theorem-family input is introduced.

`AglibTest.BlowupGlobal` consumes all four original family types on one coherent
basis and checks arbitrary-test finality, actual local pullback charts,
properness of the constructed datum over a locally Noetherian base, and the
original saturated chart triangles and overlaps. Existing flat-base-change,
affine, Rees and universal-property sources remain unchanged. Compilation
receipts and source hashes are maintained separately.
