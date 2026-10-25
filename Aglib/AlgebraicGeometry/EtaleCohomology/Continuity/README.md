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

## Sections and compatible systems

| Source | Actual interface |
| --- | --- |
| [SchemeLimitSections](SchemeLimitSections.lean) | Locally finitely presented relative represented objects commute with cofiltered qcqs affine-transition scheme limits, using original projection-composition maps. |
| [PullbackRestrictionSections](PullbackRestrictionSections.lean), [DiagramNativeCocone](DiagramNativeCocone.lean) | Original inverse-image restrictions and native cohomology cocones retain actual units, composition and coefficient transports. |
| [DiagramH0Sections](DiagramH0Sections.lean), [DiagramEtaleSections](DiagramEtaleSections.lean) | Degree-zero and étale-test section comparisons use the original section cocones. These normalizations are distinct from producing their missing colimit certificates. |
| [SectionComparison](SectionComparison.lean) | Original unit, chart evaluation and coefficient-square transformations define whole section-comparison families. Whole coefficient coherence gives their square before any higher-direct-image specialization; component laws preserve the raw original maps. No exchange invertibility or continuity premise is added. |
| [DiagramShortExact](DiagramShortExact.lean), [DiagramCohomologyExact](DiagramCohomologyExact.lean) | Actual compatible injective replacements and pointwise cokernels give the original cohomology exact sequences and connecting squares. |
| [InjectiveLimitAcyclic](InjectiveLimitAcyclic.lean) | Descended finite-family cochains give positive original cohomology vanishing for the actual injective limit once its qcqs evaluated right-tail cocones are colimiting. |

## Higher continuity from two degree-zero inputs

[SchemeLimitHigher](SchemeLimitHigher.lean) proves
`isIso_schemeLimitCohomologyComparison_of_sectionCocones` for the literal
`schemeLimitCohomologyComparison X c F n`. Its legs are original pullback
followed by original coefficient-colimit maps.

Here `I : Type u` has `Category.{u} I` and is filtered,
`X : I ⥤ Scheme.{u}ᵒᵖ`, and `c` is an actual colimit cocone.
All stages are qcqs and all transition scheme maps are affine. The theorem
retains one independent Ext universe `e` at every stage and the limit,
and `HasColimitsOfShape I AddCommGrpCat.{e}`.

Two inputs remain explicit:

- `hzero`: for every actual compatible coefficient system, the original
  degree-zero `diagramCohomologyCocone` is colimiting.
- `hqcqsSectionCocones`: for every objectwise-injective compatible system,
  every stage and every qcqs étale test there, evaluation of the original
  `diagramRightTailCocone` is colimiting.

Under these hypotheses the original comparison is invertible in every natural
degree, by the constructed injective system, actual cokernel and original
dimension shift. This closes the higher reduction. The geometric degree-zero
and cone assembly needed to discharge both inputs remain open; no
unconditional varying-scheme theorem is claimed.

The [stalk family](../Stalk/README.md) now identifies the original geometric
neighborhood-cohomology colimit with the native higher-image stalk. Identifying
that colimit with cohomology of the strict-local limit still requires the
remaining continuity assembly.
[Finite/Cohomology](../Finite/Cohomology.lean) supplies the original finite
direct-image cohomology equivalence and its actual pullback/counit/base-change
normalization; it does not make arbitrary global pullback invertible.
