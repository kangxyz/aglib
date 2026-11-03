# The original derived structure unit from genuine R1 vanishing

Source: [Surface.lean](Surface.lean).

For a proper dominant birational integral surface map, retain the actual
function-field isomorphism, normal locally Noetherian target, source dimension
at most two, and actual vanishing of R1 of the original structure module.
The higher-image fibre theorem proves all degrees above one vanish. Native
AcyclicSingle then makes the original single comparison invertible; the
existing proper-birational theorem makes the original ordinary structure unit
invertible. Their composite is precisely `moduleDerivedPushforwardUnit`.

R1 is an intermediate vanishing input, not the final rationality theorem.
The upper rational/maximal-model consumer must prove it and the source dimension
from the actual models. No later stalk completeness or finite-base assumption
is added.

Direct consumers: [AlgebraicGeometry/Cohomology/Proper/DerivedStructure/Supported](Supported.md).
