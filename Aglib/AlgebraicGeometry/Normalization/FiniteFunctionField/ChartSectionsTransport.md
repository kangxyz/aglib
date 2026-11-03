# Shared original normalization-chart transport

Source: [ChartSectionsTransport.lean](ChartSectionsTransport.lean).

Fix an integral scheme `X`, the SAME specified native field `F` with its
original `X.functionField`-algebra, an actual map `f : Spec F -> X`, and the
original equality `hf : f = genericMap X F`. The normalization construction
uses the original `QuasiCompact f` and `QuasiSeparated f` witnesses.
No alternative normalization or generic map is chosen.

`chartFieldIsoOfEq` names the original generic-section field comparison
transported by `hf.symm`. It needs only a nonempty open, not an affine-open
witness or the normalization's quasi-compactness/quasi-separatedness data.
`normalizationSectionsEquivOfEq` names the original affine normalization
section equivalence transported by the SAME equality. Its motive retains
the original QC/QS witnesses and the original `fromNormalization.app U`
source algebra. Each `Eq.ndrec` construction is implemented once.

For an independent-universe commutative ring `G` with its actual chart
algebra and a genuine chart algebra equivalence `E : F ~= G`,
`normalizationSectionsEquivMapOfEq` composes that SAME section equivalence
with native `E.mapIntegralClosure`. It does not create a spectrum of `G`,
a new chart action, an intermediate normalization or another closure map.

The original coefficient law is the algebra equivalence's native commutes
law. The whole ambient RingHom law transports the existing normalization
whole-map law and composes native closure values before any section is
evaluated. It retains the original `toNormalization.appLE` and the SAME
transported generic-chart field iso.

The pointwise `normalizationSectionsEquivMapOfEq_val` derives and evaluates
that same whole law before specialization. It consumes a genuine identity of
the chart algebra equivalence's field function with its specified original
function view. This is not a supplied ambient section equation. The actual
Cover consumer proves the function identity from its original field upgrade,
then receives the literal value of the SAME transported mapped constructor.
There is no second equality-transport or normalization-value implementation.

The unmapped affine-restriction law transports the existing normalization
restriction law. The complete mapped law then uses native closure
naturality. Its genuine input data are the original scalar tower on `G`
and equality of the underlying RingHoms of the two chart upgrades. These
are not the desired section-restriction square. In actual original-field
Cover applications, both are proved from the existing chart-restriction
and original field-comparison laws, not added as public assumptions.

The principal-localization law transports the original normalization's
actual section localization. It does not need `G`, `E` or a nonempty ambient
open; the principal subopen may also be empty. It asserts no field or domain
structure on an empty open's zero section ring.

No finite extension, Nagata, Noetherian, normality of `X`, regularity,
dimension, characteristic, differential basis or scalar bound is assumed.
The separately supplied target field remains universe-independent. Later
trace constructions must retain their original fields/maps and prove their
own gluing, canonical comparison and uniform image bound.

Direct consumers: [AlgebraicGeometry/Surfaces/Birational/NormalizedBlowupCover/ChartSections](../../Surfaces/Birational/NormalizedBlowupCover/ChartSections.md).
