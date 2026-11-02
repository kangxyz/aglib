# Closed parameters and field extension

Source: [FieldExtension.lean](FieldExtension.lean).

The original coefficient-curve hypothesis says that every closed stalk has a
regular element in its maximal ideal whose principal ideal has that maximal
ideal as radical. The first stage derives the full dimension bound from this
hypothesis on any compact locally Noetherian scheme. The proof uses actual
closed specializations and Krull's principal ideal theorem; no reducedness,
Jacobson, separability, perfection or algebraic-closure assumption is added.

`ringKrullDim_le_one_of_primary_parameter` only needs the primary principal
ideal. `dimension_le_one_of_closed_parameters` retains the original stronger
regular-parameter input required by the coefficient Serre theorem.

`dimension_le_of_integralHom` uses the actual pulled-back affine cover and
integral section maps, with prime incomparability. It never assumes that a
localized stalk map is finite or integral. The original flat stalk map
preserves the regular parameter. A regular nonunit on a Noetherian local
ring of dimension at most one has Artinian quotient and hence generates a
maximal-primary ideal. Integral morphisms map closed points to closed points.

`closed_parameters_of_flat_integral` combines these facts: for an integral
flat morphism `Y → X`, both schemes locally Noetherian and `X` compact, the
original closed-parameter condition on `X` implies that on `Y`, with no extra
dimension premise. This is the generic transporter for the actual algebraic
field-extension curve projection. The caller still derives integralness,
flatness and locally Noetherianity for that original square; this leaf does
not replace them by assumptions on the final curve-generation theorem.

## Actual projective field-extension specialization

`closed_parameters_projective_algebraic_field_extension` uses the literal
curve `pullback j (ProjectiveSpace.map (algebraMap k K) ι)` and its original
projections. Algebraicity makes the spectrum map integral; the original
projective Cartesian square makes its projective map integral. Flatness
comes from the actual field extension. Compactness and local Noetherianity
are derived from the two original closed projective embeddings. No new
dimension, separability, perfection, or reducedness premise is used.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Generation/Hyperplane](Generation/Hyperplane.md).
