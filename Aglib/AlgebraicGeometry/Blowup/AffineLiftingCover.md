# Affine pivot cover of an actual Cartier image ideal

`AffineLiftingCover.lean` proves `Scheme.Blowup.exists_affine_pivot` for an
arbitrary commutative ring `A`, ideal `I`, scheme `T` and actual map
`f : T ⟶ Spec A`. The sole geometric premise is the existing
`cartierPullback (affineCenter A I) f`: the actual module of the inverse-image
ideal is locally rank one. No Noetherian, finite-generation, reducedness or
affineness condition on `T` is needed.

On each affine open `U`, `affineBaseMap f U` is the composite of the original
`ΓSpecIso.inv` and `f.appLE ⊤ U`. `affineCenter_comap_ideal` identifies the
original inverse-image ideal on `U` with `I.map (affineBaseMap f U)`.

The native local-unit theorem gives a regular generator `r` of this actual
image ideal. Write each original image as `r * q b`. Ideal-span induction and
regular cancellation show that the `q b` generate the unit ideal. Their basic
opens cover `U`; on the basic open of one `q a`, the image of the original
`a : I` is regular and divides all original images. This argument does not
require a finite generating set of `I`.

`affineLiftingCover` is the resulting actual affine open cover.
`affineLiftingCoverLift` composes the proved saturated-chart ring lift with
the original `affineProjChart I a`; `affineLiftingCoverLift_map` states its
literal base triangle. The common chart object remains the existing subalgebra
of `A[1/a]`. This file supplies a cover and local maps; their gluing and the
final-object theorem are proved in `AffineUniversalProperty.lean`.
