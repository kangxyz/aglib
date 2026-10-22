# Projective morphisms from finite generating sections

The native owner is `Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections`.

`mapOfFiniteFamily p M hM s` constructs an actual morphism
`X ⟶ ProjectiveSpace R I` from the original structural map `p : X ⟶ Spec R`, an
actual locally rank-one module sheaf `M`, and an original finite family
`s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)` whose original coproduct map
`Sigma.desc s` is an epimorphism. `mapOfFiniteFamily_toSpec` proves the structural
triangle. The original coordinate index and section family are retained by
`generatingSectionsOfFamily_section`.

No quasi-compactness, Noetherian, coherence, field, normality, finite-type or
properness premise is needed. The source scheme and base ring are arbitrary.
The scheme, base ring and coordinate index lie in the same universe, as in the
native polynomial projective-space owner.

## Construction

The epimorphism is locally surjective. On an actual line-module chart, lift its
original generator locally through the actual finite free module sheaf. Expand
the lift in the native finite basis of its section module. The resulting finite
linear combination of original section coefficients is one. In the local stalk
ring, one original coefficient is therefore a unit. Its original basic open is a
neighbourhood of the point. `normalizedFrame` rescales the original frame there,
so that this original section is the actual frame generator.

`framesOfGeneratingSections` assembles this actual covering. Its lower interface,
`SectionFrames`, allows the source cover to refine the original coordinate index.
Each frame is an actual over-site isomorphism of the original module, and its
selected original section has coefficient one. It assumes neither a projective
morphism nor a comparison with a pullback.

On each frame chart, the original coefficients evaluate the native homogeneous
localization chart ring. The actual change-of-frame unit gives the projective
rescaling law. The chart maps therefore agree on source overlaps and glue to
`SectionFrames.map`.

## Coordinate opens and sections

For the generated frame cover `F` and original coordinate `i`, the nonvanishing
open is

```text
F.nonvanishingOpen i = ⋃ k, X.basicOpen (F.coefficientOn k le_rfl i).
```

The coefficient is that of the original section in the displayed original frame.
`mapOfFiniteFamily_preimage` and `mapOfGeneratingSections_preimage` identify this
open with the exact preimage of the native target coordinate open.
`SectionFrames.chartMap_preimage` gives the same identity on every source subopen.
`SectionFrames.selected_eq_generator` retains the actual original section as the
chosen local generator; `chartRingHom_ratio` retains every original normalized
coordinate coefficient.

## Pullback of the twisting module

`twistingPullbackIsoOfFiniteFamily p M hM s` constructs an actual isomorphism
from `(Scheme.Modules.pullback (mapOfFiniteFamily p M hM s)).obj
(twistingSheaf R I 1)` to the original module `M`, under the same hypotheses.

`pulledCoordinateMapOfFiniteFamily_comp` proves that each pulled native
coordinate-section map, followed by this isomorphism, is exactly the originally
prescribed map `s i`. The pulled coordinate maps are defined from the actual
native homogeneous coordinate sections through the pullback adjunction unit
and the original unit-module/global-section equivalence. Their definition is
independent of the comparison.

The section-level chart-ring identity `SectionFrames.map_chartRingHom` and its
ratio specialization `map_coordinateRatioSection` first identify the actual
pullback of every native chart ratio with the original section coefficient.
The original sections consequently satisfy the pullback of the native `O(1)`
unit cocycle. They glue into an actual module morphism, which is an isomorphism
in every original source frame. `twistingPullbackIso_hom_coordinate` checks every
global coordinate section on every source frame, including the complement of
that coordinate's own nonvanishing open. Thus the section-map equality is global.
