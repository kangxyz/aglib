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
| [Derived cohomology](Derived/BaseChange.lean) | Original all-degree pullback and bounded-below `D+` comparison maps with their actual adjunction, mates and degree-zero normalization; normalized H1 action is supplied, while pullback-square compatibility and full scheme pasting remain open |

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

The [older migration guide](../../../docs/ETALE_COHOMOLOGY_MIGRATION.md) records
the module relocation and namespace change. The [2026-10-23 foundation note](../../../docs/migration/etale-foundations-2026-10-23.md)
describes the admitted generic and derived providers. The canonical exchange maps are constructed, with their degree-zero
normalization. Their invertibility is not asserted here. Under the stated
`HasExt` hypotheses on both abelian-sheaf categories,
`derivedBaseChangeMap_h1_normalized` identifies the actual canonical mate
action on an original `H1Etale` representative with `h1Pullback`, after the
constant-sheaf, adjunction, shift and single comparisons. This does not prove
the original pullback-square compatibility or identify sections of `R¹` with
fibre `H¹`; full ordinary/derived/all-degree pasting remains open.

The new bounded-below sources are [DirectImage](DirectImage.lean),
[Pullback](Pullback.lean), [PullbackComposition](PullbackComposition.lean),
[BaseChangeMap](BaseChangeMap.lean), and [Derived base change](Derived/BaseChange.lean).
They retain the original maps and the actual canonical comparison data; their
stated boundaries are not a proper-base-change theorem.
