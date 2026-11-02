# Identity of the original exterior coefficient

Source: [PushforwardIdentity.lean](PushforwardIdentity.lean).

exteriorCoefficientMap_id says that exterior coefficient construction applied
to the native identity-pushforward inverse gives the native inverse on exterior
powers. Both maps and the sheaf exterior construction are unchanged. The proof
uses exteriorPower_hom_ext and exteriorPowerDesc_mk on original wedges, whose
identity coefficient and pushforward comparison evaluate literally to identity.
The original arbitrary module and exterior degree are retained.

Direct consumers: [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficientCoherence](../Differentials/Relative/ExteriorCoefficientCoherence.md).
