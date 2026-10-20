# Function fields of literal Dedekind-base generic fibres

[DedekindGenericFiber](DedekindGenericFiber.lean) works with
`Scheme.LocalRing.GenericFiber.scheme A F p`, the actual pullback of
`p : Y ⟶ Spec A` along the supplied fraction-field algebra map. For a Dedekind
domain `A`, an integral `Y` and dominant `p`, `genericLift` lifts the actual
generic-point arrow and `projection_isDominant` proves dominance of the
projection. Neither result assumes the pullback integral.

Once integrality of that same pullback is available, `functionFieldRingEquiv`
has the actual `Scheme.functionFieldMap` of its projection as forward map.
`structuralConstants` is the preimage under the fully faithful `Spec` functor
of the literal generic-point structural arrow. The constants equation compares
this map with `Scheme.DedekindBase.constantToFunctionField F p`, including
forward and inverse element equations. `projection_generic_triangle` delegates
the native generic-point naturality theorem.

[DedekindGenericFiberIntegral](DedekindGenericFiberIntegral.lean) supplies
`integral_genericFiber` for that pullback from exactly the Dedekind, supplied
fraction-field, model-integrality and dominance assumptions. It uses projection
dominance, preimmersion and the actual stalk equivalences. The preceding
`irreducible_of_dominant_preimmersion` theorem has only its arbitrary-scheme
preimmersion, dominance and irreducible-target hypotheses. No regularity,
local Noetherianity, properness, smoothness or characteristic premise is added.

These declarations live in
`AlgebraicGeometry.Scheme.FunctionField.DedekindGenericFiber`. They concern a
different pullback from the finite-dominant morphism result in
[GenericFiber](GenericFiber.lean). The focused interface consumer is
[DedekindGenericFiber](../../../AglibTest/DedekindGenericFiber.lean).

Sources are `FunctionField/GenericFiber.lean` and
`FunctionField/IntegralGenericFiber.lean` under
`R5Lab/Aglib/AlgebraicGeometry`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. Complete source hashes and ranges
are in the module headers. Native maps replace source namespace wrappers;
the original hypotheses, scalars and literal structural triangles are retained.
