# Normalization forced finite by a proper birational normal model

`ProperBirational.lean` starts with an actual proper dominant morphism
between integral schemes, normal stalks on the source, locally Noetherian
target, and an isomorphism on the original `Scheme.functionFieldMap`.
It proves that the literal normalization of the target's original generic
inclusion is finite. Neither dimension nor a Nagata or excellence property
is assumed.

On each nonempty affine target open, proper H0 finiteness applies to the
original section map. The section algebra is identified with the integral
closure in the original target function field. Its forward-value theorem
is the original source germ followed by the inverse original function-field
map. Normality is used through integral closedness in the source function
field; no fraction-field-of-sections hypothesis is imposed on the
nonaffine source open.

The next comparison uses `functionFieldSectionsIso`,
`normalizationObjIso`, and `fromNormalization_app` to identify actual source
sections with actual sections of the literal normalization. Its coefficient
triangle is stated explicitly. Finiteness transfers through this original
comparison and is assembled on all affine opens, including the empty case.

`genericNormalizationLift` is the actual factor through that same
normalization. Its construction uses the existing trivial normalization of
the normal source's generic inclusion and the universal property of an
integral pullback. It retains both the original structural triangle and the
original generic arrow. Properness and the original function-field
isomorphism then pass to this factor. The factor construction itself needs
only dominance and a normal integral source.

The [Necessity](../Surfaces/Resolution/Necessity.md) consumer starts with a
supplied proper birational regular surface model. It uses this finiteness
and factorization, then derives the finite singular-set and normal-domain
completion conditions. None of these implications constructs a resolution.
