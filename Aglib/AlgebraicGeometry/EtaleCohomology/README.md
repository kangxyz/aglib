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
| [Original stalks](GeometricPoints/FibrewiseClosed/README.md) and [inverse image](GeometricPoints/InverseImage/README.md) | The canonical `pointSmallEtale` stalk comparison and original inverse-image `stalkUnit` isomorphism hold for every standard-value abelian sheaf; only the separate fibrewise-closed detection consumer needs `LocallyOfFiniteType p`. |

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
| [Artin–Schreier](ArtinSchreier/README.md) | The actual additive small-etale short exact sequence and original constant-prime-field/native-kernel isomorphism are supplied for every scheme `X : Scheme.{u}` when `p` is prime and `(p : Γ(X, ⊤)) = 0`, including empty schemes, with coefficients in `AddCommGrpCat.{u+1}` and no extra affine, Noetherian, exact-characteristic or Ext premise. The finite-etale root cover and its lower finite/free algebra remain linked inputs. This is not affine-etale acyclicity or proper base change. |
| [Binary-form product](../ProjectiveSpace/BinaryFormProduct/README.md) | The actual finite surjective map to projective space has a cartesian coefficient-map square under every commutative-ring map and every degree `n`, including zero. This is an available projective geometric input, not a proper-base-change theorem. |
| [Amitsur module complex](../../Algebra/Homology/Amitsur/README.md) | Under faithfully flat scalar extension, the actual augmented module Amitsur complex is exact in every degree and the unaugmented complex has zero positive homology for arbitrary coefficient modules. This is algebraic module exactness, not étale-sheaf acyclicity. |

## Original geometric stalks and inverse images

[StalkUniverse](GeometricPoints/StalkUniverse.lean) compares the canonical
`FibrewiseClosed.largePoint η` sheaf fibre with the original
`pointSmallEtale η` fibre for every actual `AbelianSheaf.{u,u+1}`. The
isomorphism uses the literal lifted Hom witness and is natural for every
coefficient morphism. The comparison itself requires no finite-local-constant,
Ext, or `LocallyOfFiniteType` premise.

[InverseImage](GeometricPoints/InverseImage/README.md) proves that for every
morphism `f : S ⟶ X`, geometric point `η : Spec Ω ⟶ S`, and actual
`L : AbelianSheaf.{u,u+1} X`, the original `stalkUnit f η L` is an isomorphism.
Its natural-isomorphism component is definitionally that original map, and the
germ formula retains the original section and `pulledBackPoint`. It is natural
in coefficient maps and agrees with the existing represented-coefficient
isomorphism when a representation is supplied. No FLC, Ext, or
`LocallyOfFiniteType` condition is required for this stalk comparison. General
inverse-image stalk-unit bijectivity at wider coefficient universes remains
outside scope; no proper-base-change theorem is asserted.

The separate detection consumer
`isIso_of_original_geometricStalks` continues to require
`[LocallyOfFiniteType p]`. That geometric condition belongs to the
isomorphism-detection theorem, not to the stalk-unit comparison.
