# Etale cohomology

This family owns scheme-specific cohomology of the actual small-etale site.
Its principal declaration namespace is
`AlgebraicGeometry.Scheme.EtaleCohomology`. It is a sibling of the
[Zariski/module-cohomology family](../Cohomology/README.md).

| Subfamily | Existing objects, maps and conditions |
| --- | --- |
| [H1](H1/README.md) | Actual `Sheaf.H L 1`, coefficient maps, exact inverse image, direct image, canonical transports, torsors and finite-etale representation |
| [FiniteLocallyConstant](FiniteLocallyConstant/CoefficientSquare.lean) | Coefficient, section and pullback comparisons with the original local-trivialization and comparison premises |
| [Kummer](Kummer/Coefficients.lean) | Actual root coefficients, power-fibre torsors and field/stalk comparison maps with their stated level and representation hypotheses |

Use focused imports, for example:

```lean
import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback

open AlgebraicGeometry.Scheme.EtaleCohomology
```

`AbelianSheaf` uses the actual small-etale topology and `H1Etale` is original
Mathlib `Sheaf.H` in degree one. Keep displayed `HasSheafify`/`HasExt`
universes, markings, point data and theorem-family premises. General torsor
classification and finite representation do not impose an invertible group
order; the separate finite-coefficient package retains its positive globally
invertible level. Kummer and field-comparison leaves keep their own hypotheses.

Generic site, Ext and derived-category constructions remain in their lower
mathematical owners. Finite-etale cover geometry remains in
`AlgebraicGeometry/Morphisms/FiniteEtale`. The Kummer leaves that extend
`GroupCohomology.Kummer` keep that native object namespace; the directory
change does not duplicate their group-cohomological objects.

The [migration guide](../../../docs/ETALE_COHOMOLOGY_MIGRATION.md) gives exact
old/new modules and the scheme-namespace change. This relocation preserves
mathematical statements and maps; it does not add higher-degree etale
base-change or proper base change. Downstream dependency updates are separate
work and are not included in this migration.
