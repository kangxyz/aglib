# The original derived structure unit on surface models

[FiniteLength](FiniteLength.lean) proves finite length of the original
structural derived H1 for a proper dominant birational integral model
over a normal Noetherian local domain of dimension two. Its scalar map
is the actual structural section map. Source normality, completeness,
Nagata and a projective embedding are unnecessary for this result.

[Supported](Supported.lean) uses a qcqs morphism which is an isomorphism
off one closed point. Vanishing of the same local-model structure H1
under its actual stalk pullback square gives vanishing of the original
R1; this supported step needs no surface or properness hypothesis.

[Surface](Surface.lean) makes the original derived structure unit invertible
for a proper dominant birational integral surface map with normal locally
Noetherian target, source dimension at most two and original R1 vanishing.
The higher-image fibre bound kills the remaining degrees.
R1 is an explicit input to this implication; maximal-model and rationality
consumers must prove it on their actual models.

Present consumers include [Proper cohomology with original structural coefficients](../README.md), [Original point blowups of rational surface stalks](../../../Surfaces/RationalSingularities/Blowup/README.md).
