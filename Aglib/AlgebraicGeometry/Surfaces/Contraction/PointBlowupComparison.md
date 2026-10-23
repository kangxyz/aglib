# Projective presentations through an original point blowup

`Surfaces.Contraction.exists_projective_embedding_of_pointBlowup` descends a
finite projective embedding of the original point blowup to its original target.
Its inputs are an integral regular Noetherian scheme `Z`, a closed point `x`
whose original stalk has Krull dimension two, a Noetherian ring `A`, an actual
map `q : Z ⟶ Spec A`, and a closed immersion of the native point blowup into
finite projective space over `A`. The embedding must have structural map
`pointBlowdown Z x ≫ q`. The result is a closed immersion of `Z` into finite
projective space over the same `A`, with structural map exactly `q`.

The proof uses the original exceptional fibre over `κ(x)`. The canonical
point-blowup comparison identifies it with the native projective line and
identifies its conormal with `O(1)`. Restricting the supplied embedding gives
an actual `O(d)` comparison for `d > 0` by
`ProjectiveSpace.Line.exists_positiveTwist_of_isClosedImmersion_over_ring`.
This step retains `κ(x)` without identifying it with a residue field of `A`.
The projective contraction theorem then constructs a projective target `T`
for that same exceptional curve.

`Surfaces.Contraction.exists_pointBlowup_target_iso` compares this target with
the original `Z`. Its second contraction is proper and surjective, has a
closed field-valued point of local dimension two, and is identified with the
blowup of that full point ideal by its canonical Cartier lift. Equality of
the two pulled-back full point ideals gives equality of the exceptional
point fibres. Each blowup is injective outside its centre. These facts prove
pointwise constancy in both directions on the fibres of the actual maps.

The proper birational structure-sheaf theorem applies because both targets
are regular and integral. On the second target the canonical blowup lift
supplies the original birational function-field map; no comparison
isomorphism is assumed. Native proper fibre descent constructs `Z ⟶ T` and
`T ⟶ Z`. Uniqueness proves their inverse equations and then the equality of
their actual maps to `Spec A`. Composition with the constructed embedding
of `T` gives the embedding of the unchanged original `Z`.

This is the one-step P5–P6 implication for reverse induction through actual
closed-point blowups. It does not prove projectivity of an arbitrary proper
surface without a projective presentation of its blowup. It imposes no
positive-genus, trait, excellence, coefficient-field or perfectness premise.
The comparison theorem only needs local Noetherianity of `Z`; the embedding
theorem records the Noetherian hypotheses of its intended finite-chain consumer.

The mathematical route is Section 3, P0/P1/P5/P6, of the accepted
`general-contraction-research.md` and its ordinary
`proper-modification-v1-review.md`. The native source dependencies are
`Blowup.RegularPoint.Normal.Scheme`, `Surfaces.Contraction.Projective`,
`ProjectiveSpace.Line.RelativePositiveTwist`, and the proper birational
structure-sheaf and fibre-descent modules. Compilation is coordinated with
the consuming contraction graph; the source text itself is not compiler
evidence or an established-status decision.
