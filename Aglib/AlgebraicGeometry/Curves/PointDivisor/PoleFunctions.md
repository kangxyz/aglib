# Original point poles and fractional sections

[PoleFunctions.lean](PoleFunctions.lean) compares the actual positive point
module of the original smooth proper geometrically connected genus-one
curve with the existing divisor sheaf at its original rational point. The
curve has no chosen group law and no representing Picard scheme is used.
The original field is arbitrary.

`closedPoint` retains the actual section and closed image; `pointDivisor n`
is the existing finitely supported divisor there with coefficient `n`.
`idealDivisor` is the native map divisor of the original point ideal and
its original inclusion. `idealDivisor_eq_pointDivisor` identifies that
actual divisor with the point. At the point, a native local ideal
generator spans the kernel of the original stalk map to the actual field
stalk. The quotient is simple of length one, so its order is one.
Outside the original image, the native ideal-support theorem makes every
coefficient zero. This uses actual local generators and stalk maps; the
global point ideal may have no nonzero global sections.

`exists_positive_divisorSheafIso` first obtains an actual module-sheaf
isomorphism from the proved divisor and native divisor/class comparison.
The intrinsic one-dimensional section space from [Sections](Sections.lean)
then normalizes that sheaf isomorphism by an actual nonzero constant
scalar. `positiveDivisorIso` sends the original section one to literal
rational one. `positiveSection_comp_positiveDivisorIso` is equality of
the actual sheaf maps from the structure module, so the normalization
holds on every open, not just on global ideal sections.
`poleDivisorIso` extends the same normalized sheaf comparison to the
original tensor powers. The zero power uses the native unit comparison,
the first power uses `firstPowerIso`, and higher powers use the native
divisor tensor multiplication. `sectionsFractionalEquiv` is the resulting
linear equivalence from actual global sections to the existing fractional
sections at every bound. Its final comparison uses the native
`explicitSheafSectionsEquiv`, whose actual forward map is rational value;
the divisor sheaf, fractional module and structural scalar maps remain
the original objects. Its value on the original first `oneSection` is
literal rational one. `sectionsFractionalEquiv_inclusion_value` proves
that every original n-to-n+1 inclusion preserves the actual rational
value, including the native zero power.

`fractionalPoleSectionsModule` uses the original structural map for its
field action. `fractionalSections_smul_val` identifies this with the
original `functionFieldConstants` map. `sectionsToFunctionField` is the
actual injective field-linear section map for that same algebra, and
`mem_range_sectionsToFunctionField_iff` identifies its range with the
literal existing fractional-section condition. This permits consumers to
use the actual pole submodule in the original function field without
choosing a vector-space model or assuming a scalar tower.

The fractional comparison uses the native integral, Noetherian and
closed-stalk DVR structures required by the existing function-field
objects. They follow from the given curve properties;
`isIntegral_of_properties`, `isDiscreteValuationRing_stalk` and the native
`curveProperties_isNoetherian` supply them. No added field hypothesis is
used.

[Products](Products.lean) proves the arbitrary-bound comparison of the
native power-addition maps with multiplication in the same original
function field. Its `sectionsToFunctionField_tensor` theorem retains the
actual section maps and includes the zero powers; the same multiplication
compatibility holds on every original open.
