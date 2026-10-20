# Rational sections and their actual local rings

[Basic](Basic.lean) defines `Scheme.RationalPoint F X` by an actual structure
map and section. Its selected point, stalk, evaluation and constants use those
maps. The constructed residue equivalence is induced by the section, and
reduction retracts constants, including on units. For integral `X`, the actual
generic stalk is the fraction field of this local ring. Regularity and Krull
dimension one imply the stalk is a DVR; they remain explicit hypotheses of
that implication.

[Completion](Completion.lean) constructs the maximal-ideal completion of that
actual rational-point stalk and its fraction field when `X` is integral and
the stalk is a DVR. It reuses the canonical `AdicCompletion` algebra, residue
and fraction-map suppliers. Its scalar and residue triangles retain the
original section's constants and evaluation. Characteristic zero is propagated
only when the original rational-point field has characteristic zero.

The finite-etale specialization is
[Adic.RationalPointCompletion](../Morphisms/FiniteEtale/Adic/RationalPointCompletion.lean).
[SmoothCurve](SmoothCurve.lean), in `Scheme.RationalPoint`, proves closedness
of the section and its selected point. Local finite type supplies local
Noetherianity and a Noetherian actual stalk. Smooth relative dimension `n`
gives a standard-smooth affine neighbourhood, a free differential module of
rank `n`, and actual cotangent-space dimension `n`. In relative dimension one,
the explicit domain hypothesis on the actual stalk gives its DVR,
dimension-one and regularity conclusions. Integrality of the actual scheme
supplies that domain hypothesis. General smooth field normality remains the
native stronger supplier of the historical `SmoothNormal` source.
General generic-section constructions live in
[Stalk.GenericSection](../Stalk/GenericSection.lean).

The source identities are recorded in each leaf against the frozen R5 packet
at `f8a3314ddecffcada2ec721d26d56a937bed9690`. These are ordinary scheme and
local-ring interfaces; no arithmetic-model existence is assumed or proved.
