# Projective sections near an exceptional Cartier curve

[ProjectiveSections.lean](ProjectiveSections.lean) uses an actual closed embedding
`p : X -> ProjectiveSpace A iota` over a commutative Noetherian ring, with the
specified finite coordinate labeling `iota ≃ Fin (r + 1)`. A specified
isomorphism `H ≅ p^* O(1)` is the very ample data. The curve is a closed immersion
from the native projective line, with its original invertible kernel ideal `I_E`.
The conormal and coefficient comparisons are actual module-sheaf isomorphisms
`i^* I_E ≅ O(1)` and `i^* H ≅ O(d)`.

The generic `embeddedTensorTwist` and `embeddedTensorTwist_serreVanishing`
implementations live in [Cohomology/Projective/SerreVanishing/ClosedImmersion](../../Cohomology/Projective/SerreVanishing/ClosedImmersion.md).
The names in this file are transparent adapters with the same objects and statements.
The proof uses the native projective Serre theorem, closed-immersion projection
formula, and original projective-embedding cohomology map. No relative flatness is assumed.

`conormalDualRestrictionIso`, `tensorPowerRestrictionIso`, and
`projectivePowerIso` construct the needed dual and power comparisons from the
single supplied line-bundle comparisons. `cartierTwistRestrictionIso` then gives
the restriction `O(nd-j)` of the actual coefficient representing `nH+jE`.

`cartierStepSequence` constructs

`M -> M(E) -> i_* i^* M(E)`.

It tensors the original structure-module kernel sequence by the actual
invertible coefficient and uses the native evaluation, braiding, associator,
unit, and projection-formula isomorphisms. `cartierStepSequence_shortExact`
proves exactness. `cartierPowerTwist` retains these actual tensor objects.

`exists_cartier_vanishing_and_section_lifts` proves that one Serre bound works
for every `n` above it and every `0 <= j <= nd+1`. First cohomology vanishes
throughout that range, and every original quotient section map lifts through
all its steps. The compactness and separatedness used by the cohomology
comparison follow from the projective embedding. No desired vanishing,
section-lifting, presentation, or contraction premise is supplied.

For `nd >= 2`, the last two relevant restrictions are `O(1)` on
`H^n((nd-1)E)` and `O` on `H^n(ndE)`. Thus the theorem supplies the section lifts
used for a nonvanishing section along the curve and for first-order ideal
generators.

`exists_cartier_finite_section_families` constructs finite actual section
families with epimorphic free maps for every stage through `H^n(ndE)`. It starts
with native nonnegative projective-twist generators, retains them under the
original pullback and closed direct-image maps, and lifts quotient generators
through each proved Cartier sequence. `cartierPowerInclusion` is the original
common Cartier multiplier on sections of the initial projective coefficient.

These are sheaf-generating families. For an actual birational image construction,
retain mixed degree-n coordinates as well as coordinate powers, and retain
enough global sections to preserve the contraction point's full residue field.
The augmentation lemma permits prescribed finite section families to be kept
verbatim. Constructing the actual image and proving contraction/target regularity
remain further steps; no contraction or general proper Grothendieck-existence
theorem is asserted here.

For a future contraction `f : X -> Y` with image point `z`, one must prove the
actual ideal identity `m_z O_X = I_E`. Besides sections retaining the full residue
field, keep original lifts of the two coordinate generators of `O_E(1)` through
`L_n(-E) -> L_n(-E)|E`. For `nd >= 2`, the proved vanishing of `H^1(L_n(-2E))`
supplies these lifts. Identifying the pulled-back maximal ideal, its powers, and
the target's associated graded ring remains a separate obligation. Finite sheaf
generation and a set-theoretically contracted curve do not establish that
identity. No identification with a power-series ring over the residue field is
asserted in mixed characteristic.

An ample bundle without specified projective embedding data requires the
additional passage to a very ample power. Extracting a positive `d` from very
ampleness is separate from the theorem with the stated restriction comparison.
