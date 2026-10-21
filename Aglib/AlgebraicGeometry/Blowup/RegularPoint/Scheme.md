# Actual point blowups on regular schemes

`AlgebraicGeometry.Scheme.Blowup.RegularPoint.regularStalks_pointBlowup`
proves regularity of every actual stalk of
`(blowupDatum (X.fromSpecResidueField x).ker).Y`. Its hypotheses are a
scheme `X` with `Scheme.RegularStalks X`, a closed point `x`, and
`ringKrullDim (X.presheaf.stalk x) = 2`. The dimension condition is only
on that original stalk. No local Noetherianity hypothesis on `X` is needed.

The proof uses the canonical map `X.fromSpecStalk x` from the spectrum of
the original local ring. The existing `Scheme.fromSpecStalk_flat` theorem
proves its flatness; Mathlib supplies its preimmersion and monomorphism
properties.

`pointCentre_comap_fromSpecStalk` identifies the pullback of the original
centre `(X.fromSpecResidueField x).ker` with the actual maximal-ideal centre
on the local spectrum. The original residue-field map factors as the
spectrum of the residue quotient followed by `X.fromSpecStalk x`. Since
the second map is a monomorphism, this factorization gives a Cartesian
square with the identity on the original residue-field spectrum. Closedness
of `x` makes its original residue-field map a closed immersion, so the
actual kernel comap formula gives the centre equality.

`stalkBlowupComparison` is the original `BaseChange.map` for this exact
centre equality. `stalkBlowupComparison_isPullback` uses the proved flat
base-change supplier. `stalkBlowupIso` therefore identifies the actual
maximal-ideal blowup of the original local ring with the literal pullback
of the original point blowup. Its two projection theorems retain both the
canonical comparison to the original blowup and the original local blowdown.

`stalkBlowupProjection_isIso_stalkMap` proves that every actual stalk map
of the pullback's first projection is an isomorphism. That projection is
the base change of the original flat preimmersion, and the existing flat
surjective-on-stalks theorem applies to its own stalk maps.

For a point of the actual blowup mapping to `x`, the literal pullback range
identity supplies a lift because `x` is in the image of its local spectrum.
The frozen `RegularPoint.regularStalks` theorem makes the local-ring blowup
regular. The actual blowup comparison and the projection's own stalk
isomorphism transport this regularity to the original blowup stalk.
Outside the original point, `blowup_regular_away` supplies regularity from
`Scheme.RegularStalks X`.

The local mathematical input is the regularity slice of [Stacks Lemma
54.3.2, tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR), through the
existing native local theorem. All centre equalities, maps, Cartesian
squares and stalk transports used in the extension are proved in Lean.
No excellence, Henselian, completeness, trait, coefficient-field or global
dimension premise is imposed. This leaf adds no projective-line or
normal-bundle construction.
