# Supported globalization of a prescribed local modification

[SurfaceChain](SurfaceChain.lean) starts with an integral normal Noetherian
scheme `X` of dimension at most two, a closed nongeneric `x` and a
supplied proper `NormalizedPointBlowupChain` over `Spec O_(X,x)`.
It constructs a global native chain of the same length, its actual
Cartesian terminal square and an isomorphism off `x`.
Punctured isomorphy of the supplied chain is derived. If its terminal and
the unchanged complement are regular, the global terminal is regular,
integral and normal, with both original stalk projection equations
and the original birational function-field map.

[SupportedChain](SupportedChain.lean) supplies the induction from a proper
local total map and punctured comparison. [ChainProperness](ChainProperness.lean)
derives finite first normalization and properness of the first step and tail
from properness of that actual total map.
[PointLocalization](PointLocalization.lean) and
[NormalizedPointLocalization](NormalizedPointLocalization.lean) retain full
point ideals, residue maps and both blowup projections.
[FactorReplacement](FactorReplacement.lean) and
[FactorNormalization](FactorNormalization.lean) construct the required
proper factor and finite normalization. [NormalizationAway](NormalizationAway.lean)
preserves the original complement.

[ChainTransport](ChainTransport.lean) transports the same prescribed chain
through an actual base isomorphism, retaining length and terminal triangle.
[ProjectiveSurfaceChain](ProjectiveSurfaceChain.lean) also preserves the
original finite-coordinate projective setting and dimension bound, given
the actual local-terminal bound. [Dimension](Dimension.lean) supplies the
general dimension transport through the same supported stalk square.
These theorems globalize supplied local chains; they do not construct
resolving local chains from arbitrary singular input.

Present consumers include [Actual stages of a supplied normalized-point chain](../../Surfaces/Resolution/NormalizedPointBlowupChain/README.md), [Normal stages and normalized presentation of ordinary chains](../../Surfaces/Resolution/PointBlowupChain/README.md).
