# Conditional resolution from original full quadratic cones

[NormalizedResolution](NormalizedResolution.lean) takes a commutative
Noetherian Nagata local domain `R` of dimension two satisfying
`NormalModificationH1Vanishing R` and a proper dominant map
`f : X → Spec R` with integral normal `X` and invertible original
function-field map.

At each original singular stalk, `hcones` supplies a triple generating its
maximal ideal and a nonzero homogeneous quadratic over its original
residue field which generates the entire `CaseOne.canonicalConeMap` kernel.
A commutative local domain `A` is maximal-adically complete and
two-dimensional, with an actual local injective `A → R` whose original
residue-field map is finite. No Noetherianity of this earlier `A` is added.

[OriginalPathCones](OriginalPathCones.lean) derives later cones from the
supplied initial cone. The Case-I successor and Case-II entry/continuation
interfaces retain original stalk maps, exceptional ideals and residue
maps. [OriginalMixedPath](OriginalMixedPath.lean) constructs a marked tail,
distinguishing a second-entry ratio parameter from its previous
exceptional denominator.

[FinitePrefixGeometry](FinitePrefixGeometry.lean) proves finite branching;
[FiniteHeight](FiniteHeight.lean) combines native König with the earlier
complete-base contradiction.
[PointHeight](PointHeight.lean), [HeightMultiset](HeightMultiset.lean) and
[FiniteResolution](FiniteResolution.lean) serialize the original blowups
with proved normal stages and preserve every original regular open.
The normalized presentation keeps an explicit terminal isomorphism.
The result is a proper dominant birational normalized-point chain with
integral regular terminal under exactly these supplied inputs.

Initial full cones are not derived from arbitrary rational or
rational-Gorenstein data. This conditional family does not close the full
RDP/Gorenstein reduction, RES or RES-QE.

Present consumers include [Rational surface singularities](../../RationalSingularities/README.md), [Surface principalization and resolution prerequisites](../README.md).
