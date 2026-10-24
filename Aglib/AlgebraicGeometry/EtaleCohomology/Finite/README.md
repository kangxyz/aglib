# Finite direct image and base change

This family studies an arbitrary finite morphism `f : X ⟶ S` of schemes
in `Scheme.{u}`, using the actual small-etale sites and coefficients
`AbelianSheaf.{u,u+1}`. Its principal namespace is
`AlgebraicGeometry.Scheme.EtaleCohomology.Finite`.

## Exact direct image

[FiniteDirectImageExactness](FiniteDirectImageExactness.lean) supplies
`finiteDirectImage_preservesEpimorphisms` for the original `directImage f`.
[HigherVanishing](HigherVanishing.lean) supplies
`finiteDirectImage_preservesHomology` and
`finiteDirectImage_preservesFiniteColimits`. These results hold over arbitrary
base schemes, with arbitrary coefficients in the displayed sheaf category;
they impose no Noetherian, finite-presentation or torsion premise.

For every such coefficient `F` and every `q > 0`,
`isZero_higherDirectImage_obj_of_isFinite` gives
`IsZero ((higherDirectImage f q).obj F)`. It retains independent
`HasDerivedCategory.{wX} (AbelianSheaf.{u,u+1} X)` and
`HasDerivedCategory.{wS} (AbelianSheaf.{u,u+1} S)` inputs.

## Canonical base change

Consider morphisms `f : X ⟶ S`, `f' : X' ⟶ S'`,
`g : S' ⟶ S` and `g' : X' ⟶ X`, with `f` finite and
`h : IsPullback g' f' f g`.
[OrdinaryBaseChange](ExactImageComparison/OrdinaryBaseChange.lean) proves
`finiteBaseChange_app_isIso` for every
`F : AbelianSheaf.{u,u+1} X`, and `finiteBaseChange_isIso` for the entire
original natural transformation

```lean
baseChangeMap f f' g g' h.w.symm
```

There is no affine-base, Noetherian, finite-presentation or coefficient-torsion
restriction. Finiteness of `f'` follows from the actual cartesian square.
The [two-affine-base result](ExactImageComparison/AffineOrdinaryBaseChangeIso.lean)
is the earlier specialization using the same canonical map.

[DerivedBaseChange](DerivedBaseChange.lean) proves
`finiteDerivedBaseChange_isIso` for the original bounded-below
`derivedBaseChangeMap`, and `finiteHigherBaseChange_isIso q` for the original
`higherBaseChangeMap` in every natural degree. The four
`HasDerivedCategory` inputs for `X`, `S`, `X'` and `S'` retain
independent universes `wX`, `wS`, `wX'` and `wS'`. Finite geometry
supplies exactness and ordinary exchange; neither remains an additional
comparison hypothesis.

Focused imports are:

```lean
import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DerivedBaseChange
```

## Original finite direct-image cohomology

[Cohomology](Cohomology.lean) defines
`finiteCohomologyDirectImageAddEquiv f F q` for every natural `q`:

```lean
Sheaf.H.{wS} ((directImage f).obj F) q ≃+ Sheaf.H.{wX} F q
```

The source and target `HasExt` universes `wS,wX` are independent.
Its value at an original class `a` is exactly

```lean
Sheaf.H.map ((inverseImageAdjunction f).counit.app F) q
  (cohomologyPullback f ((directImage f).obj F) q a)
```

Coefficient naturality uses the original cohomology maps.
`finiteCohomologyDirectImageAddEquiv_baseChange` normalizes the actual
cartesian square: original pullback along `g`, followed by cohomology of
the original ordinary exchange and the finite equivalence upstairs, equals
original pullback along `g'` after the finite equivalence downstairs.
All four Ext universes remain independent. This is the finite export;
arbitrary global-cohomology pullback need not be invertible.

## Local geometry and original stalks

| Source | Canonical construction and conditions |
| --- | --- |
| [GeometricNeighborhoodLimit](GeometricNeighborhoodLimit.lean) | Spectra of the actual filtered geometric-neighborhood ring colimit form a limiting scheme cone. Its projections and specified field-valued point use the literal stage ring maps. The lower [strict-henselization family](../../../RingTheory/Henselian/StrictHenselization/LocalRing.lean) supplies the local and Henselian properties, with [separably closed residue](../../../RingTheory/Henselian/StrictHenselization/SeparablyClosedResidue.lean) when the chosen geometric field is separably closed. |
| [GeometricNeighborhoodCofinal](GeometricNeighborhoodCofinal.lean) and [GeometricNeighborhoodStalk](GeometricNeighborhoodStalk.lean) | For a separably closed geometric field, the actual algebra-presentation index is initial in the original pointed étale category. Its opposite computes the original geometric stalk, and the colimit comparison sends every stage section to its literal original germ. |
| [LocalDecomposition](LocalDecomposition.lean) | For a finite algebra over a Henselian local ring, the coproduct of spectra of its maximal localizations maps isomorphically to its spectrum by the actual localization maps. |
| [StrictLocalComponents](StrictLocalComponents.lean) | Finite local algebras over a Henselian local ring with separably closed residue have zero positive original `Sheaf.H`. Base, algebra and Ext universes remain independent, and the displayed sheafification and Ext existence assumptions are retained. |
| [GlobalEvaluationIso](ExactImageComparison/GlobalEvaluationIso.lean) and [PointedEvaluationBaseChange](ExactImageComparison/PointedEvaluationBaseChange.lean) | At an algebraically closed geometric point, the original finite direct-image stalk is compared with its actual geometric-fibre tuple, and the canonical exchange is normalized by the original pointed unit/counit evaluation formula. |

The [marked strict-local comparison](../Stalk/README.md) now identifies the
actual higher-image stalk with original limit-scheme cohomology, with its
explicit chart/Ext/colimit premises and original germ/degree-zero equations.
General proper base change and unbounded derived scope remain open.
No arbitrary global-cohomology pullback is asserted to be invertible.

## Module-linear finite comparison and trace

[EtaleTrace](EtaleTrace.lean) and [EtaleModuleTrace](EtaleModuleTrace.lean)
retain the original finite-etale unit/rank equation and coefficient
naturality. Coprime annihilators give actual retractions preserved by further
functors. The [module-coefficient comparison](../ModuleCoefficients/FiniteDirectImage.lean)
is linear over the original coefficient ring and preserves the original
finite direct-image cohomology map, with independent Ext universes. This
does not prove constructibility for arbitrary finite direct image.

`Exceptional/Derived/FiniteBaseChange` also proves finite base change for the
original genuine constant-ring module D+ exchange over arbitrary rings. It
uses the proved scalar-forgetting exchange square and conservative exact
derived forgetting; its eight derived-model universes remain independent.
