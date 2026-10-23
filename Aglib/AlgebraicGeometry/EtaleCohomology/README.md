# Etale cohomology

This family owns scheme-specific cohomology of the actual small-etale site.
Its principal declaration namespace is
`AlgebraicGeometry.Scheme.EtaleCohomology`. It is a sibling of the
[Zariski/module-cohomology family](../Cohomology/README.md).

| Subfamily | Existing objects, maps and conditions |
| --- | --- |
| [H1](H1/README.md) | Actual `Sheaf.H L 1`, coefficient maps, exact inverse image, direct image, canonical transports, torsors and finite-etale representation |
| [H0 proper henselian](H0/README.md) | Original constant-finite sections and `Sheaf.H` degree-zero pullbacks are bijective over any proper henselian local base; sections extend to actual finite locally constant coefficients. |
| [H1 finite constant](H1/ConstantFinite/README.md) | Original `H1Etale` closed-residue pullback is bijective for every finite constant additive group, with no order-invertibility or Noetherian premise; the result extends to actual finite locally constant abelian sheaves. |
| [FiniteLocallyConstant](FiniteLocallyConstant/CoefficientSquare.lean) | Coefficient, section and pullback comparisons with the original local-trivialization and comparison premises |
| [Kummer](Kummer/Coefficients.lean) | Actual root coefficients, power-fibre torsors and field/stalk comparison maps with their stated level and representation hypotheses |
| [Derived cohomology](Derived/BaseChange.lean) | Original all-degree pullback and bounded-below `D+` comparison maps. The D source supplies the original H1 square and ordinary, derived, and all-degree identity/pasting equations through native comparisons; exchange invertibility, proper base change, and unbounded scope remain open. |
| [Fibrewise-closed geometric points](GeometricPoints/FibrewiseClosed/README.md) | Under only `LocallyOfFiniteType p`, genuine geometric-point lifts detect covers on every object of the actual small-etale site; the resulting `Point.{u+1}` family detects isomorphisms of `AbelianSheaf.{u,u+1}`. No Ext or proper-base-change theorem is asserted. |
| [Original geometric stalks](GeometricPoints/FibrewiseClosed/README.md) | The canonical larger-point to original `pointSmallEtale` stalk comparison applies to every `AbelianSheaf.{u,u+1}`; only the separate isomorphism-detection consumer needs `LocallyOfFiniteType p`. |

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
describes the admitted generic and derived providers. The canonical exchange maps retain their degree-zero normalization. The D
continuation adds the original square equations: `h1Pullback_square` uses the
four displayed `HasExt` universes, while `derivedBaseChangeMap_h1_square`
normalizes the actual derived mate through the constant-sheaf, adjunction, shift,
and single comparisons.

The ordinary `baseChangeMap_hComp`, `_vComp`, and `_vId` equations use the
original inverse-image and direct-image composition maps. The derived
`derivedBaseChangeMap_hComp`, `_vComp`, and `_vId` equations use the native
`D+` adjunctions and comparisons under their displayed derived-category
instances. For each natural degree `q`, `higherBaseChangeMap_hComp`, `_vComp`,
and `_vId` state the corresponding equations using the actual source/target
higher-image comparisons and homology of the actual composite derived images.
The higher vertical identity retains its native comparison; it does not identify
the positive-degree derived image of an identity with the identity functor.

These equations are compatibility statements for the canonical maps. They do
not assert exchange-map invertibility, proper base change, or an unbounded
derived theorem. The independent `derived_archive_review` accepted the selected D sources,
and the principal-owned incremental compilation and selected native checks
passed. The general proper-base-change theorem remains a separate target.

The new bounded-below sources are [DirectImage](DirectImage.lean),
[Pullback](Pullback.lean), [PullbackComposition](PullbackComposition.lean),
[BaseChangeMap](BaseChangeMap.lean), and [Derived base change](Derived/BaseChange.lean).
They retain the original maps and the actual canonical comparison data; their
stated boundaries are not a proper-base-change theorem.

## Further small-etale inputs

| Input | Scope and owner |
| --- | --- |
| [Strictly local](StrictlyLocal/README.md) | For henselian local rings with separably closed residue field: arbitrary jointly surjective étale families split, terminal covering sieves are maximal, and original positive-degree `Sheaf.H` vanishes for arbitrary value and Ext universes under native existence assumptions. These are suppliers, not a proper-base-change theorem. |
| [Artin–Schreier](ArtinSchreier/README.md) | Actual finite étale surjective root covers for global sections when the prime maps to zero; the lower finite/free root algebra is owned by [RingTheory/Etale](../../RingTheory/Etale/README.md). The full additive sheaf sequence remains open. |
| [Binary-form product](../ProjectiveSpace/BinaryFormProduct/README.md) | The actual finite surjective map to projective space has a cartesian coefficient-map square under every commutative-ring map and every degree `n`, including zero. This is an available projective geometric input, not a proper-base-change theorem. |

## Original geometric stalks at the standard value universe

[StalkUniverse](GeometricPoints/StalkUniverse.lean) constructs
the canonical natural isomorphism from `FibrewiseClosed.largePoint η` to the
original `pointSmallEtale η` sheaf fibre for every actual
`AbelianSheaf.{u,u+1} T`. Its germ formula sends the lifted witness
`ULift.up x` to the same original geometric Hom witness `x`; the map is natural
for every coefficient morphism. The comparison itself has no FLC, `HasExt`, or
`LocallyOfFiniteType` premise.

The separate `isIso_of_original_geometricStalks` consumer uses the original
small-etale stalks and assumes only `[LocallyOfFiniteType p]`; it is not a
proper-base-change theorem. General inverse-image `stalkUnit` bijectivity
remains a separate open question.
