# Actual finite-base models of the original field curve

[SpreadingOut.lean](SpreadingOut.lean) constructs the literal comparison between
the pullback of `f ∣_ U` along a specified factorization through `U` and the
pullback of the original `f`. The isomorphism lives in the over category and
its underlying map retains the original projection to the total space.

A dominant field point of an irreducible scheme maps to the actual generic
point. `liftDominantFieldPoint` therefore factors that same point through
every generic open. `restrictModelComparison` composes the resulting canonical
pullback comparison with a supplied original model comparison. It changes
neither the specified original field scheme nor its structural morphism.

`Curve.Properties.exists_finite_base_model` constructs one finitely generated
integer subalgebra `A` of the original field `K`, an actual scheme `X` and
map `f : X ⟶ Spec A`, with properness, smooth relative dimension one,
geometric integrality, flatness, local finite presentation, quasi-compactness
and quasi-separatedness. Its literal pullback along the inclusion `A → K`
is isomorphic to the original field curve in `Over (Spec K)`. An arbitrary
prescribed finite set of original field constants lies in `A`. The input
is the original `Curve.Properties`, not a supplied family or projectivity
datum. The genus and characteristic are unrestricted.

The existing projective-embedding producer supplies an actual finite
projective embedding. One standard chart meeting the integral curve gives
a schematically dense affine closed chart. Its particular polynomial
generators and finite relations descend through
`exists_closed_chart_model`; the closed chart is retained over the finite
coefficient ring. The scheme-theoretic image in the same finite projective
space is proper. Flat base change and the original schematic-density
factorization identify its whole field fibre with the original curve.
The lower `exists_proper_model_of_dense_closed_chart` also retains an actual
finitely presented affine open in that proper model and the original affine
fibre comparison.

Smoothness descends first from `K` to the fraction field. The proper smooth
locus construction gives a generic open, and the fixed-dimension theorem
recovers relative dimension one there. Field-extension reflection and the
generic geometric-integrality theorem give the further open. Adjoining
one inverse to a finite integer subalgebra realizes each needed generic
open over another finite integer subalgebra. Native pullback pasting retains
the original comparison throughout.

`Scheme.exists_curve_properties_on_later_baseChange` starts from an arbitrary
filtered diagram of commutative rings whose specified colimit is the field,
an actual finitely presented qcqs model at a prescribed stage, and its
specified literal field-pullback isomorphism to the original curve. It
constructs a later stage where the literal pullback of that given model is
proper, smooth of relative dimension one, geometrically integral and flat.
The finite integer algebra of the constructed curve family factors through a
stage above the prescribed one. The actual stage-isomorphism theorem then
transfers the properties. The original comparison is retained by canonical
pullback pasting. This argument imposes no flatness or injectivity on the
filtered-ring maps and does not require a general scheme-object producer.

This closes the generic finite-base family core of `R-SPREAD-FAMILY` with
prescribed finite base constants. Consumer-specific finite chart/function,
certificate, point, and symbol/model assemblies remain downstream and use
their separate actual finite-data descent interfaces. The general arbitrary
scheme-object theorem is a separate obligation; it is not an input hidden
inside this curve producer.

Assignment basis: `AGLIB_PROOF_TASKS.json`, task `R-SPREAD-FAMILY`, from
`aglib-full-independent-agent-20261021.zip`; implementation base Aglib
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1. Compilation evidence
is reported separately with the corresponding source identity.
