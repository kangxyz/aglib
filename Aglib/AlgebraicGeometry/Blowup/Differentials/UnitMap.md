# The ordinary one-pole unit map

For a coefficient from the original affine relative exterior forms to an actual line, `pairIdeal_onePoleUnitMap` pulls the coefficient to the canonical blowup and inserts the original dual ideal section through the existing tensor unit and braiding. The section is exactly `InternalHom.transpose` of the original center ideal inclusion.

`pairIdeal_onePoleUnitMap_pullback` retains the native tensor and structural-unit comparison for every scheme morphism into that same blowup. The coefficient ring, arbitrary ideal, exterior degree, line and scalar actions are unchanged. No derived-category input is used by these constructions.
