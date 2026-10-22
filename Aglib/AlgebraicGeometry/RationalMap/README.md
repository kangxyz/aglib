# Rational coordinates and graph closures

[Graph](Graph.lean), in `Scheme`, constructs the literal graph map from an open
of a field scheme into a fibre product and then takes its actual schematic
image. It retains both projections and their triangles. Properness of each
projection has its own properness hypothesis on the opposite field scheme.
Image integrality, dominance, Noetherianity and the isomorphism over the
original open retain their separate displayed assumptions.

This is a graph-closure construction over a field. It does not construct a
common regular domination or a graph closure over an arithmetic trait. The
native curve projectivity constructions use this exact field graph.

The proof reuses the actual schematic-image integrality and the open-section
restriction theorem from their lower native owners.

## Quasi-domination on target opens

In `Scheme.QuasiDomination`,
[TargetOpen.Modification](QuasiDomination/TargetOpen/Modification.lean)
proves `exists_targetOpen_modification` for Noetherian `X`, a quasi-compact
locally finite-type `f : Y ⟶ X`, opens `U ≤ V`, and an actual section
`g : U.toScheme ⟶ Y` with `g ≫ f = U.ι`. The image of this section's
graph is assumed closed over `V`. For each affine open `O` of `Y`, it
constructs a `V`-admissible sequence `β : B ⟶ X`, an immersion
`d : D ⟶ B`, and a map `h : D ⟶ O.toScheme`. The original restriction of
`g` lifts through `D`, and the induced map `D ⟶ B ×[X] O` is a closed
immersion, with the original projection triangles.

[FiniteTargetCover](QuasiDomination/FiniteTargetCover.lean) proves
`exists_locallyQuasiFinite_graphImage_modification` under the same
hypotheses on `X`, `f`, `U`, `V`, `g`, and its graph. It constructs a
`V`-admissible sequence `β : B ⟶ X` for which the actual map from the
schematic image of `modifiedGraph U f g hg β` to `B` is locally
quasi-finite.

## Denominator and base ideals

[BaseIdeal](BaseIdeal.md), in `Scheme.RationalCoordinates`, starts with a finite
family in the original function field of an integral scheme. Its actual
denominator ideal and kernel module retain the simultaneous denominator and
numerator equations. The base ideal is the image of the original numerator
row, and its coordinate maps from the denominator module form an epimorphic
row with the same index. On nonempty affine opens and actual stalks, the
comparisons use the original fractional-coordinate span and its integral
product with the denominator ideal. They do not replace nonaffine section
ideals by affine quotient formulas.

The lower [finite fractional denominators](../../RingTheory/FractionalIdeal/Denominator.md)
supply the original common-denominator and numerator maps. Over a GCD domain,
a finite coordinate family containing one has a nonzero principal denominator;
this retains the actual coefficient map and specified coordinates.

If an original coordinate is one, the base ideal is nonzero and contains the
denominator ideal. On a locally Noetherian integral scheme with regular
actual stalks, `denominatorModule_isLocallyRankOne` makes the actual denominator
kernel module a line module, with no dimension bound. On a globally Noetherian
regular integral scheme with actual stalk dimensions at most two,
`baseIdeal_isArtinian_subscheme` makes the original base-ideal quotient
Artinian; finite local colength is derived from regularity and primitivity.
These endpoints construct the coordinate ideals and maps used by the
projective extension below.

## Extension after point blowups

[ProjectiveExtension](ProjectiveExtension.md), in `Scheme.RationalCoordinates`,
supplies `exists_pointBlowupChain_projectiveExtension` for an integral
Noetherian scheme `X` with regular stalks and topological dimension at most
two. It starts with an actual `p : X ⟶ Spec R`, finite coordinate type `I`,
and original `gη : Spec K(X) ⟶ ProjectiveSpace R I` satisfying the original
base triangle. A finite point-blowup chain `β : Y ⟶ X` gives a proper
birational map, regular integral source of local dimension at most two,
and an actual extension `h`. Its structural triangle is
`h ≫ toSpec = β ≫ p`; its generic triangle uses exactly
`Scheme.functionFieldMap β` and the original `gη`. Dominance of `gη` is
unnecessary.

The original denominator line is pulled back literally; the pulled
coordinate row maps canonically onto the actual inverse-image base ideal.
[Point principalization](../Surfaces/Resolution/README.md) makes that ideal
Cartier, and the native line-source projective constructor retains the
original indexed coordinates. The
[common-domination consumer](../Surfaces/Birational/CommonDomination.md)
combines these extensions for finite projective products and an actual
proper integral target. Resolution of an initially singular source remains
separate.
