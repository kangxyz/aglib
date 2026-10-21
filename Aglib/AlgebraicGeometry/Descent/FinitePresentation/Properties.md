# Property suppliers for finite-stage curve models

[Properties.lean](Properties.lean) supplies the property constructions used by
`R-LIMIT-PROPERTIES` and the finite-base curve producer.

The native scheme-theoretic image of a quasi-compact map receives a
schematically dominant map from its original source. Flat base change preserves
this dominance. If the changed original map is a closed immersion, its map
to the changed image is both a closed immersion and schematically dominant,
hence an isomorphism. `imageModelBaseChangeIso` keeps the two original
cartesian squares and both structural triangles, and identifies the literal
pullback of the closed-image model with the original fibre in the over
category. Its `of_schematicFactor` variant permits a schematically dense
piece of the original closed fibre, rather than requiring the original piece
itself to be closed. A closed image in a proper target is proper; over a
locally Noetherian base its structural map is finitely presented.

`exists_standardSmooth_affine_model_above` constructs a standard-smooth affine
model in the original relative dimension over a finitely generated integer
subalgebra containing any prescribed finitely generated integer subalgebra.
It uses the native standard-smooth coefficient model, retaining its actual
tensor equivalence and converting it to a literal `Over.pullback` comparison.
The intermediate coefficient rings are genuine subalgebras of the given field.

`exists_finite_standardSmooth_affine_atlas` extracts a finite standard-smooth
atlas in the same relative dimension, retaining each original structural
triangle. `isPullback_affineModelMap` makes the canonical tensor model's
structural square cartesian.

`exists_open_smooth_of_isProper_of_flat_preimmersion` uses the actual
localization stalk isomorphisms to locate the changed fibre in the original
smooth locus. Properness then removes the closed image of the nonsmooth
locus. `smoothOfRelativeDimension_of_dominant_fieldBaseChange` proves that the
relative dimension of a smooth family is detected by one dominant field
point: every nonempty standard-smooth chart meets that fibre, where the
native field-dimension theorems determine its dimension.

[SpreadingOut](../../Morphisms/SpreadingOut.lean) assembles these suppliers
into an actual finite-base curve family using the equations of one original
affine projective chart. Its
`Scheme.exists_curve_properties_on_later_baseChange` transfers properness,
smooth relative dimension one and geometric integrality to the literal later
pullback of any given finitely presented qcqs stage model with the specified
original curve as its field-limit pullback. The constructed finite integer
algebra is finitely presented, so its original map to the field factors
through a ring stage. Actual common-stage isomorphism descent then identifies
the two models. The final field comparison uses canonical pullback pasting
followed by the original supplied comparison. The filtered-ring maps may be
noninjective and nonflat.

Primary comparison locators are Stacks
[Lemma 32.8.5, eventual closed immersion](https://stacks.math.columbia.edu/tag/01ZP)
and [Lemma 32.8.9, eventual smoothness](https://stacks.math.columbia.edu/tag/0C0C);
[Lemma 32.13.1, eventual properness](https://stacks.math.columbia.edu/tag/081F)
is a different result and uses Chow's lemma. The present curve route uses the
existing actual projective embedding of the original smooth proper curve and
the explicit image argument, rather than importing the full Chow-based theorem.
Object and Hom descent are compared with
[Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM).

Assignment basis: `AGLIB_PROOF_TASKS.json`, task `R-LIMIT-PROPERTIES`, from
`aglib-full-independent-agent-20261021.zip`; implementation base Aglib
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1. Source applicability
and compiled coverage remain distinct.
