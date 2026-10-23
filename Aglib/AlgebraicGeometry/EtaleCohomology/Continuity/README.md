# Continuity on the small-etale site

This family owns continuity for original small-etale cohomology and the
canonical sections and coefficient maps used in scheme-limit comparisons.
Its namespace is `AlgebraicGeometry.Scheme.EtaleCohomology.Continuity`.

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
| [PullbackRestrictionSections](PullbackRestrictionSections.lean) | Original restriction maps, followed by the chart-evaluation inverse and original inverse-image composition, agree with the literal relative-section pullback maps. |
| [DiagramPullbacks](DiagramPullbacks.lean) and [DiagramLimitSections](DiagramLimitSections.lean) | Compatible systems use the actual pulled-back stage coefficients. Fixed qcqs coefficient continuity makes the outer section cocone a colimit when the cone point is qcqs. |
| [DiagramTailCocones](DiagramTailCocones.lean) | Relative tail cocones and compatible-system tail cocones agree under the actual diagram transport. `isColimitCompatibleTailOfNative` transports a supplied native `IsColimit` certificate. |
| [DiagramInjectives](DiagramInjectives.lean) and [PullbackCohomologySystem](PullbackCohomologySystem.lean) | Actual compatible coefficient and cohomology systems retain the original direct/inverse-image adjunctions, composition maps and injective envelopes. |

Represented-section descent and the fixed-site coefficient theorem are inputs
to varying-scheme continuity. General inverse-image section gluing and the
higher-degree varying-scheme theorem remain open; the native tail
`IsColimit` premise above is still supplied by the caller.

The [finite family](../Finite/README.md) owns the constructed strict-local
neighborhood model, its finite local decomposition and the resulting finite
direct-image results. The final strict-local higher-cohomology comparison
remains open.
