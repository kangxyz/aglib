# Continuity on the small-etale site

This family owns continuity for original small-etale cohomology and the
canonical sections and coefficient maps used in scheme-limit comparisons.
Its namespace is `AlgebraicGeometry.Scheme.EtaleCohomology.Continuity`.

[CohomologyTransfers](CohomologyTransfers.lean) retains the original transfer
and constructs the actual constant-integer source system from native inverse
image and constant-sheaf comparison maps. [DiagramCohomology](DiagramCohomology.lean)
specializes the [general represented Ext diagram](../../../CategoryTheory/Sites/SheafCohomology/Continuity/RepresentedDiagram.lean),
with whole original-map equality and the same independent Ext universe.
Geometric section-colimit and injective-acyclicity suppliers remain in this
family and provide the continuity hypotheses used below.

The original Arrow and cone section maps specialize the complete
[section calculus](../../../CategoryTheory/Sites/SheafCohomology/Continuity/InjectiveDiagram/SectionArrows.lean)
and [coefficient-cone constructors](../../../CategoryTheory/Sites/SheafCohomology/Continuity/InjectiveDiagram/Cone.lean).
Their inputs are the actual scheme adjunctions, global sections and pullback
maps. Native object and map values are retained.

The varying and fixed-source systems use the complete generic
[system constructors](../../../CategoryTheory/Filtered/SystemConstructions.lean).
[DiagramLimitSections](DiagramLimitSections.lean),
[DiagramSmallIndex](DiagramSmallIndex.lean) and
[DiagramRawConeSections](DiagramRawConeSections.lean) evaluate one shared
[coefficient-section functor](../../../CategoryTheory/Filtered/CoefficientSections.lean).
The test Arrow row and its canonical Tail cocone specialize the whole
[indexed cone comparison](../../../CategoryTheory/Filtered/IndexedConeSections.lean),
with the original pullback and chart-comparison component values. The geometric
colimit hypotheses remain in their native suppliers.

[DiagramCohomologyCocone](DiagramCohomologyCocone.lean) specializes the complete
[source-system transfer and cocone construction](../../../CategoryTheory/Sites/SheafCohomology/Continuity/InjectiveDiagram/CohomologyCocone.lean).
The original coefficient functor has the same colimit, and every leg is the
original stage pullback followed by its coefficient insertion. Only the actual
stage and apex Ext instances are needed. Source cartesianness stays explicit;
no cohomology-comparison invertibility or scheme-limit continuity premise is
introduced.

## Filtered coefficients on a fixed qcqs scheme

Let `S : Scheme.{u}` be quasi-compact and quasi-separated, let
`I : Type (u + 1)` be a small filtered category, and let
`G : I ⥤ AbelianSheaf.{u,u+1} S`. For every natural degree `n`,
[QcqsCoefficientContinuity](QcqsCoefficientContinuity.lean) proves
`isIso_qcqsCoefficientColimitComparison G n` for the actual map

```lean
Sheaf.H.coefficientColimitComparison G n :
  colimit (G ⋙ Sheaf.functorH S.smallEtaleTopology n) ⟶
    (Sheaf.functorH S.smallEtaleTopology n).obj (colimit G)
```

The theorem retains `HasExt.{e} (AbelianSheaf.{u,u+1} S)` and
`HasColimitsOfShape I AddCommGrpCat.{e}`. In particular, the Ext universe
`e` is independent of `u`.
`qcqsCoefficientFilteredColimitIso` has exactly this comparison as its forward
map, and `ι_qcqsCoefficientFilteredColimitIso` identifies its composite with
each colimit injection with the original cohomology map of the coefficient
injection.

[QcqsSections](QcqsSections.lean) supplies section-colimit preservation on
qcqs étale objects, and [QcqsAcyclic](QcqsAcyclic.lean) supplies acyclicity of
filtered colimits of actual injective coefficients. Their lower
[generic site providers](../../../CategoryTheory/Sites/SheafCohomology/README.md)
use finite hypercovers, exact filtered colimits and original connecting maps.
No torsion condition is imposed on the coefficient diagram.

A focused import is:

```lean
import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsCoefficientContinuity
```

## Sections on scheme limits

| Source | Actual interface and conditions |
| --- | --- |
| [SchemeLimitSections](SchemeLimitSections.lean) | For a cofiltered diagram in `Over S` with qcqs stages and affine transition maps, a locally finitely presented `Y : Over S` has its relative Hom set on the supplied underlying scheme limit as the filtered colimit of the stage Hom sets. Every cocone leg is composition with the original cone projection. |
| [PullbackEtaleEvaluation](PullbackEtaleEvaluation.lean) and [PullbackEtaleNaturality](PullbackEtaleNaturality.lean) | Étale-chart evaluation of actual inverse-image coefficients, with coefficient and chart naturality. |
| [PullbackSectionsBase](PullbackSectionsBase.lean) | The original relative sections form a bifunctor in the relative scheme and coefficient sheaf. Its whole base-change comparison, evaluated only after naturality is proved, identifies the restriction to the actual small-etale site with the original inverse-image sheaf. No section-continuity premise is used. |
| [PullbackRestrictionSections](PullbackRestrictionSections.lean) | Original restriction maps, followed by the chart-evaluation inverse and original inverse-image composition, agree with the literal relative-section pullback maps. |
| [DiagramPullbacks](DiagramPullbacks.lean) and [DiagramLimitSections](DiagramLimitSections.lean) | Compatible systems use the actual pulled-back stage coefficients. Fixed qcqs coefficient continuity makes the outer section cocone a colimit when the cone point is qcqs. |
| [DiagramTailCocones](DiagramTailCocones.lean) | Relative tail cocones and compatible-system tail cocones agree under the actual diagram transport. `isColimitCompatibleTailOfNative` transports a supplied native `IsColimit` certificate. |
| [DiagramInjectives](DiagramInjectives.lean) and [PullbackCohomologySystem](PullbackCohomologySystem.lean) | Actual compatible coefficient and cohomology systems retain the original direct/inverse-image adjunctions, composition maps and injective envelopes. |
| [DiagramH0Sections](DiagramH0Sections.lean) | A supplied colimit certificate for the original compatible-section cocone gives a colimit certificate for the original degree-zero cohomology cocone, preserving all native legs. For a `u`-small scheme index, sections take values in `Ab.{u + 1}` and original cohomology in independent `Ab.{e}`. Only the section universe lift preserves a colimit; the fully faithful cohomology lift reflects it, so no `e`-smallness of the index or target colimit premise is introduced. |
| [DiagramNativeCocone](DiagramNativeCocone.lean) | Native cohomology cocones retain the actual inverse-image units, composition and coefficient transports. |
| [DiagramEtaleSections](DiagramEtaleSections.lean) | Étale-test section comparisons retain the original compatible cocones and their displayed colimit inputs; the matching section producers supply those certificates. |
| [SectionComparison](SectionComparison.lean) | Original unit, chart evaluation and coefficient-square transformations define whole section-comparison families. Whole coefficient coherence gives their square before any higher-direct-image specialization; component laws preserve the raw original maps. No exchange invertibility or continuity premise is added. |
| [DiagramShortExact](DiagramShortExact.lean), [DiagramCohomologyExact](DiagramCohomologyExact.lean) | Actual compatible injective replacements and pointwise cokernels give the original cohomology exact sequences and connecting squares. |
| [InjectiveLimitAcyclic](InjectiveLimitAcyclic.lean) | Descended finite-family cochains give positive original cohomology vanishing for the actual injective limit once its qcqs evaluated right-tail cocones are colimiting. |

[AffineLimitSections](AffineLimitSections.lean) proves the actual relative
section cocone is colimiting on affine inverse limits using real finite local
representatives, matching, original-stage gluing and eventual equality.
Its final presheaf criterion is the
[general filtered-colimit argument](../../../CategoryTheory/Limits/Preserves/PresheafSections.lean),
applied to the same original cocone and legs.
[QcqsLimitSections](QcqsLimitSections.lean) extends this to qcqs stages with
affine transitions using one finite affine one-hypercover at a fixed stage.
It also proves `isColimitCompatibleSectionsOfQcqsStages` for the original
varying-system section cocone. Neither endpoint assumes section continuity.
[DiagramTestRightTailColimit](DiagramTestRightTailColimit.lean) gives the literal
original right-tail cocone evaluated on a qcqs stage test, using the genuine
fixed-coefficient rows, original outer coefficient colimit and diagonal.

## All-degree cohomology on qcqs inverse scheme limits

[SchemeLimit](SchemeLimit.lean) proves
`isIso_schemeLimitCohomologyComparison X c hc n F` for every natural degree
`n` and compatible coefficient system `F`. Here `I : Type u` has
`Category.{u} I` and `IsFiltered I`, `X : I ⥤ Scheme.{u}ᵒᵖ`, and
`hc : IsColimit c` specifies the actual inverse scheme limit. Every stage is
qcqs and every transition is affine. Coefficients remain the original
`AbelianSheaf.{u,u+1}` objects.

The original cohomology universe `e` is independent of `u`: retain
`HasExt.{e}` for the original sheaf categories at all stages and the limit,
and `HasColimitsOfShape I AddCommGrpCat.{e}`. There is no equality of universes
or requirement that `I` be `e`-small. No geometric section-colimit,
injective-pullback, higher-vanishing or comparison-isomorphism premise is
assumed. No torsion, Noetherian or cohomological-dimension restriction is used.

`isColimitDiagramCohomologyOfQcqsStages X c hc F n` is the certificate for the
original cohomology cocone. `schemeLimitCohomologyIso X c hc F n` has exactly
the original comparison as its forward map. Its
`ι_schemeLimitCohomologyIso_hom` formula retains each original stage pullback
followed by the coefficient-colimit insertion. The higher induction uses the
original compatible injective replacement, pointwise cokernel and connecting
squares. The genuine qcqs section producer, evaluated right-tail assembler
and final all-degree consumer were accepted in graphs 260, 264 and 265,
respectively.

The [finite family](../Finite/README.md) owns the constructed strict-local
neighborhood model, its finite local decomposition and the resulting finite
direct-image results. The marked strict-local higher-cohomology comparison is supplied in the
[stalk family](../Stalk/README.md), with actual pointed germs, coefficient
naturality and original degree-zero normalization. The
[proper family](../Proper/README.md) uses these inputs for the original locally
torsion higher and D+ exchange; properness and torsion remain conditions of
those endpoints.
