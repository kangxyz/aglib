# Approximation by finitely presented schemes

This family constructs inverse systems and closed envelopes using the actual
schemes, structural morphisms, and limit projections. The two principal
interfaces serve different consumers:

| Interface | Hypotheses and result |
| --- | --- |
| [Arithmetic systems](FinitePresentationEnvelope/README.md), import `Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Absolute` | Every `X : Scheme.{u}` with `CompactSpace X` and `QuasiSeparatedSpace X` admits `Scheme.FinitePresentationEnvelope.System X`: finite-type arithmetic stages with affine transitions and original cone point `X`. |
| [Proper fixed-base systems](Proper/README.md), import `Aglib.AlgebraicGeometry.Approximation.Proper.FiniteType` | For proper `f : X ⟶ S` with affine `S`, `Scheme.Approximation.nonempty_properFinitePresentationSystem f` constructs proper finitely presented stages over the unchanged `S`, with closed transitions and projections. |

The arithmetic system produces the separated closed
[finite-presentation hull](../Morphisms/FiniteType/README.md) and supplies both
systems used in [qcqs compactification](../Compactification/QCQS.md). The
proper fixed-base system supplies the
[proper henselian finite-étale comparison](../Morphisms/FiniteEtale/ProperHenselian/README.md).
Neither public existence theorem takes an approximation system as an extra
premise.

[ClosedSubscheme/FiniteType](ClosedSubscheme/FiniteType.lean), imported as
`Aglib.AlgebraicGeometry.Approximation.ClosedSubscheme.FiniteType`, lifts
finite-type kernel ideals to an actual diagram in `Over Y`.
In `AlgebraicGeometry.Approximation.ClosedSubscheme`,
`finitePresentationCone f` has point `Over.mk f` by
`finitePresentationCone_pt`. For a closed immersion into qcqs `Y`,
`isLimitFinitePresentationCone f` proves the over-category limit and
`isLimitFinitePresentationSchemeCone f` proves its scheme-valued form.
Transitions and projections are closed immersions, and stage structure maps
are locally finitely presented. The stages are closed superschemes of the
original source; no nilpotent-thickening or equal-support assertion is part
of this approximation.

The underlying [ideal approximation](../IdealSheaf/README.md) and
[closed-immersion diagrams](../Morphisms/ClosedImmersion/README.md) remain
reusable lower interfaces. [Finite-type descent](../Descent/FiniteType/README.md)
owns eventual closedness and separatedness, while
[finite-presentation descent](../Descent/FinitePresentation/README.md) owns
actual stage models and common-stage maps.
