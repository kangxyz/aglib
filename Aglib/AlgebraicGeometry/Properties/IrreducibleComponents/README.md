# Actual component selection and transport

[DenseComponent](DenseComponent.lean) proves that the closure of a nonempty
irreducible open is an actual irreducible component. A map to an irreducible
space with the displayed open-image hypotheses has exactly one component with
dense image. Its scheme corollaries retain the actual restriction isomorphism
and require an integral target, without a Noetherian hypothesis.

[PointComponent](PointComponent.lean), in `Scheme.OverField`, constructs the
actual open irreducible component through a point of a smooth field scheme,
its finite etale inclusion and the factorization of a given field-valued point.
The source API retains the explicit `SmoothFieldNormality` and
`NormalComponentsOpen` arguments. Their native suppliers are
`Scheme.smoothFieldNormality` and `Scheme.normalComponentsOpen`; these facts
are already proved in the smooth-normality and normal-component providers.

[Transport](Transport.lean) supplies `Scheme.componentsEquiv` for an actual
scheme isomorphism and `Scheme.fibreEquivOfTargetIso` for the literal point
fibres of a morphism after transporting its target. It assumes no branch
cardinality or normalization theorem.

The existing [component provider](../IrreducibleComponents.lean) remains the
owner of domain-stalk uniqueness and component openness. The new curve/model
constructions use these selection and transport lemmas.
