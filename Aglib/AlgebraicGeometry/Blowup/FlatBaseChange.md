# Flat base change of given universal blowups

`FlatBaseChange.lean` proves the exact existing family
`Scheme.Blowup.BlowupFlatBaseChange` through its supplier
`Scheme.Blowup.blowupFlatBaseChange`. For arbitrary schemes `X`, `X'`, a flat
map `f : X' ⟶ X`, an actual ideal sheaf `I` and given universal blowup data
`B` for `I` and `B'` for `I.comap f`, the actual canonical map
`BaseChange.map f rfl B B'` is cartesian with `B'.map`, `B.map` and `f`.
`BaseChange.isPullback_of_flat` also accepts an exact centre equality
`I.comap f = I'` and a given datum for `I'`.

No Noetherian, finite-generation, reducedness, regularity or separation
hypothesis is added. Existence of the given blowup data remains part of the
original question; this theorem constructs no nonaffine-base existence family.

The lower leaf `IdealSheaf/Cartier/FlatComap.lean` proves
`Scheme.IdealSheafData.isLocallyRankOne_comap_of_flat`. It starts from local
rank one of the actual module `idealModule I.subschemeι`. Native affine
regular-generator neighbourhoods and the exact formula
`(I.comap f).ideal V = (I.ideal U).map (f.appLE U V h).hom`
show that the image ideal is locally principal with a regular generator:
flatness preserves that generator's regularity. The native affine ideal-module
comparison and open restriction then give local rank one of the actual comap
ideal. No flatness of the quotient is assumed. This lower theorem has no
blowup import.

`flatPullbackDatum B f` has exactly `pullback B.map f` as its scheme and
`pullback.snd B.map f` as its map. Flatness of the first projection and the
literal pullback triangle give its Cartier property. Its universal map pairs
the given map to `X'` with the unique lift supplied by `B.universal`;
uniqueness follows from that same universal property and pullback uniqueness.

`flatComparisonIso B f B'` is the existing comparison isomorphism from `B'`
to this constructed datum. Its second projection is `B'.map`. Its first
projection is the original `BaseChange.map`, by `BaseChange.map_unique`.
These two equations prove the actual cartesian square and the exact quantified
family. Neither flat stability nor the desired comparison is supplied as an
extra theorem-family input.

The focused client `AglibTest.BlowupFlatBaseChange` checks the exact family,
canonical cartesian square, both projection equations, definitional pullback
objects and maps, the lower image-ideal supplier, and an existing conditional
native consumer using the new proved family. Compilation receipts are separate
from this mathematical guide.
