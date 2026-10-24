# Normalized point blowups after completion

Import `Aglib.AlgebraicGeometry.Descent.CompletionPointBlowup`.
Point and blowup declarations belong to `AlgebraicGeometry.Scheme.Blowup`.

Let `A` be a Noetherian local ring, let `f : X → Spec A`, and let `β` be the
original projection from the literal completion pullback to `X`.
`completionPoint_isPullback` treats a point `y` for which the original maximal
ideal is contained in the prime ideal of `f (β y)`. It proves the cartesian
square of the two original residue-spectrum inclusions. Its horizontal field
arrow is exactly `Spec.map (β.residueFieldMap y)`.

The proof uses the actual scalar map from `A` to the residue field of `β y`.
The original maximal ideal annihilates this coefficient algebra. The proved
nilpotent tensor equivalence therefore makes its completion pullback unchanged,
through the original tensor inclusion. The canonical point comparison into
that fibre is a surjective closed immersion into a reduced field spectrum,
and hence an isomorphism. No rational-point, separability, normality or
properness hypothesis is needed for this point-square theorem.

For a closed lower point, `completionPointCentre_comap` derives equality of
the full point ideal sheaves. `pointCentre_comap_of_isPullback` records the
general kernel calculation from the actual cartesian point square.

`pointBlowupBaseChangeIso` applies the proved universal flat-base-change
theorem to those exact centres. Its two projection theorems retain the
original upper blowdown and the existing canonical `BaseChange.map`.

`completionClosedPoint_data` proves that a specified closed point of the
completed proper model lies on the original closed fibre and has closed image
in the original model. It uses the actual closed-fibre comparison and both
closed-fibre inclusions. `completionPoint_isPullback_of_iso` retains the original
residue map when the given upper stage is identified with the literal pullback
by an actual scheme isomorphism.

`Scheme.genericNormalizationIsoOfIso` transports the two original generic
normalizations along an actual isomorphism of integral schemes. Its map is
constructed by `normalizationDesc` from the original induced function-field
map. The structural and generic projection equations are retained explicitly.
The inverse is proved by the same normalization universal property. No normality,
normalization finiteness or chosen replacement function field is an input to
this transport.

`exists_normalizedPointCompletion` supplies one complete descent step. Its
inputs are a proper dominant integral model over a Noetherian local domain of
dimension two, invertibility of its original function-field map, a domain
completion, an actual comparison of the given integral upper model with the
literal completion pullback, normal stalks on that upper model, and its
specified closed nongeneric point.

The theorem derives the lower closed nongeneric point and full point-ideal
equality. Actual flat blowup base change identifies the ordinary upper blowup
with the literal completion of the ordinary lower blowup. Normality away from
the upper centre supplies the off-closed-fibre hypothesis of
`CompletionNormalization.finite_normalization_and_isIso_completionComparison`.
That theorem derives finite lower normalization and the canonical completion
comparison. Transport along the ordinary blowup isomorphism then identifies
the prescribed upper normalization. The output retains the original projection
to the completed base and the original projection to the ordinary lower
blowup, through `BaseChange.map`.

No finite normalization or desired normalization comparison is an input to
this step. No excellence, G-ring or Nagata condition is imposed on the original
ring. The finite-chain consumer retains normal completion: it supplies normality
of the initial upper spectrum and of every later literal normalized stage.
Construction of a resolving upper chain and global spreading are separate.

The coefficient and centre argument corresponds to the prescribed-chain proof
in [Stacks Lemma 54.11.7, tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA).
The ordinary blowup comparison is the actual flat-base-change construction of
[Stacks Lemma 31.33.3, tag 0805](https://stacks.math.columbia.edu/tag/0805).
