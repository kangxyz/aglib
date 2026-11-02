# Original singular prefixes under flat preimmersion base change

For a flat preimmersion `j : U -> X` and a root `x : U` whose image is globally
closed, `singularPrefixEquiv` identifies the accepted finite prefix types
with the literal nonregular-stalk eligibility predicate. There is no abstract
eligibility-invariance assumption or alternative prefix implementation.

At every step the original point-centre pullback theorem supplies the exact
ideal equality. `pointBaseChangeMap` is the existing `BaseChange.map` on the
native `blowupDatum` sources; its square is the existing flat-base-change
square. The accepted `ClosedFiber` theorem supplies the actual globally
closed singular-child equivalence. Global image-root closedness is retained
at each recursive step through `point_closed` on the target prefix.

A single dependent comparison stage stores the equivalence of these existing
prefixes and actual maps between their endpoint schemes. It does not store
new schemes, ideals, blowups, local rings or paths. The successor equivalence
uses native `Equiv.sigmaCongr`. The zero, successor, parent and full truncation
laws expose the original recursive construction.

`singularPrefixMap_isPullback` and both `isoPullback_hom_fst` / `_snd` laws
retain the exact endpoint comparison and original blowdown. The same maps
are open immersions when `j` is open. `singularPrefixStalkMapIso` is the
existing native original stalk-arrow comparison for this square; its right
component is explicitly the original `Arc.pointLocalRingMap`.

No Noetherianity, normality, dimension, completeness, finiteness, marking,
height or termination is assumed or concluded. In particular, this leaf does
not claim that distinct point blowups commute globally. Later away-from-a-
centre applications must use the actual native away isomorphism.
