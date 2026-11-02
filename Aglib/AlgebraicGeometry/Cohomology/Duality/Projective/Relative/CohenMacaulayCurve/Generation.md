# Coefficient canonical input to generation

`Generation.lean` connects the actual coefficient-valued Serre parent to
`Enlargement.lean`. It retains an arbitrary field, the chosen finite closed
projective embedding, ambient dimension at least one, the genuine closed-stalk
regular-parameter condition, and the finite rank-one coefficient module V.

`cmCurveCoefficientHomH1Equiv` is the degree-zero Serre equivalence after
native `Ext.homEquiv₀`, not a newly supplied duality. Its forward equation
is precisely trace composed with the original H1 morphism.
`cmCurveCoefficientCanonical_no_finiteSupport_subobject` derives purity
against coherent finite-closed-support subobjects by finite-support H1
vanishing and this same equivalence. No structural H0 condition is needed
for this purity statement, and V is not identified with the field.

`cmCurveCoefficientCanonical_tensor_no_finiteSupport_subobject` also proves
purity after tensoring by any invertible line: apply its actual dual-tensor
equivalence to a subobject, retain finite support through the original tensor
stalk comparison, and reflect the resulting zero object back.

These are the actual comparison inputs used by the finite-support mechanism
in Stacks [0B5E](https://stacks.math.columbia.edu/tag/0B5E) and
[0B5F](https://stacks.math.columbia.edu/tag/0B5F). They do not alone establish
global generation. The regular-section construction through each point,
the actual quotient dimension bound, and the local Nakayama argument remain to be assembled. Over arbitrary fields
the hyperplane route additionally needs its genuine base-change/descent
comparisons; no algebraic closure assumption is inserted.

Native status: authored for the principal's incremental batch; no successful
compilation, lint, test or axiom-audit coverage is asserted yet.
