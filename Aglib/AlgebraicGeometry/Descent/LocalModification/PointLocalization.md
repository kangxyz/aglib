# Closed centres on localized models

Source: [PointLocalization.lean](PointLocalization.lean).

`localizationClosedPoint_data` starts with the actual cartesian model square
`IsPullback a p f (X.fromSpecStalk x)`, a closed point `x` of the original
base, a proper local structural morphism `p`, and a closed point `y` of the
local model. It proves that `a y` is closed on the global model and that
`f (a y) = x`. No properness of `f`, dimension, Noetherian or separatedness
hypothesis is needed for this point statement.

Properness of `p` puts `y` over the unique closed point of its local base.
Any specialization of `a y` stays in the fibre over closed `x`. It lifts to
the local model in the original cartesian square; the embedding underlying
the localization reflects specialization. Closedness of `y` then forces
that specialization to equal `a y`.

`point_isPullback_of_flat_preimmersion` retains the original residue-field
arrow. Flatness plus preimmersion makes the original stalk map invertible,
hence its induced residue-field map invertible. The full point square is
cartesian, not merely a bijection of supports. The read-only point-centre
supplier then yields `pointCentre_comap_of_flat_preimmersion` for the full
reduced point ideals.

These are prerequisites for prescribed local-chain globalization, not that
entire construction.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/NormalizedPointLocalization](NormalizedPointLocalization.md).
