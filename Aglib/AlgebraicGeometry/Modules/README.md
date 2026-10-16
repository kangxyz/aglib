# Actual structure-module sheaves

Objects are Mathlib's actual `X.Modules` on a scheme's Zariski site. Native `Scheme.Modules` functors carry the structure-ring scalar maps. Project extensions use `AlgebraicGeometry.Scheme.Modules` and mathematical subnamespaces.

[Stalk](Stalk/Basic.lean) constructs `moduleStalk`, `moduleStalkMap` and the actual stalk/skyscraper adjunction; `moduleStalkExactFunctor` is the genuine module-valued stalk exact functor. [Support](Support.lean) defines support through nonzero stalks, gives `isZero_iff_stalks` and compares support with actual open restriction. [Exact](Exact.lean) supplies `sheafExactStructure`, exact open restriction and the supported-away property. [Epimorphisms](../../Algebra/Category/ModuleCat/Sheaf/Epimorphisms.lean) proves actual sheaf epimorphisms are locally surjective. [IsomorphismFunctors](IsomorphismFunctors.lean) gives pullback/direct-image equivalences for scheme isomorphisms.

[Ext](Ext.lean) gives the standard `Type (u + 1)` native Ext universe for
`X.Modules`, including its unfolded `SheafOfModules` form. It specializes
the lower ringed-site theorem without a resizing or geometric finiteness
hypothesis.

[Linear](Linear.lean) defines `globalScalarCenter` and
`globalScalarEndomorphism` by original global-function multiplication on
each open. On the structure module this is the original `unitMul`.
`moduleCategoryLinearOfHom X α` is the native `Linear R X.Modules` structure
for a specified map to global functions; it remains explicit to distinguish
different structural maps. Its sectionwise formulas retain the original
restriction and module action. Ring and scheme universes may differ.

[Stalk](Stalk/Basic.lean) constructs `moduleStalk`, `moduleStalkMap` and the actual stalk/skyscraper adjunction; `moduleStalkExactFunctor` is the genuine module-valued stalk exact functor. [Support](Support.lean) defines support through nonzero stalks, gives `isZero_iff_stalks` and compares support with actual open restriction. [Exact](Exact.lean) supplies `sheafExactStructure`, exact open restriction and the supported-away property. [Epimorphisms](Epimorphisms.lean) proves actual sheaf epimorphisms are locally surjective. [IsomorphismFunctors](IsomorphismFunctors.lean) gives pullback/direct-image equivalences for scheme isomorphisms.

[InternalHom](InternalHom.lean) is the generic `Scheme.Modules.InternalHom` of actual structure-linear maps between restrictions. Its `sectionHomEquiv` identifies sections with the actual restricted module-sheaf morphisms. It lies below invertible sheaves and has no rank-one hypothesis. The
[restriction and gluing guide](InternalHom/README.md) gives literal native
open-restriction comparisons and unique global module morphisms from
compatible arrows on jointly covering open immersions. It needs no
quasicoherence or finiteness, allows independent cover-index universes and
includes empty covers on empty schemes. Euler maps and higher-direct-image
base-change maps share this lower interface.

| Subfamily | Objects and principal results |
| --- | --- |
| [Generators](Generators/README.md) and [Locality](Locality/README.md) | Actual open-free generators, finite local lifts and stalk/open-cover detection |
| [Restriction](Restriction/README.md), [Pullback](Pullback/README.md), [Pushforward](Pushforward/README.md) | Canonical geometric functors, units/counits, extension by zero and scalar comparisons |
| [Complex](Complex/README.md) | Ordinary integer complexes, geometric restriction, flat pullback, tensor and acyclicity on specified opens |
| [PerfectComplexes](PerfectComplexes/README.md) | Strict term-bounded finite locally free complexes, their inherited exact structure, locally strict derived models and open restriction |
| [StructureSheaf](StructureSheaf/README.md) and [BaseChange](BaseChange/README.md) | Actual direct image of the unit and the adjunction-mate base-change map |
| [QuasiCoherent](QuasiCoherent/README.md) | Affine module comparison, local/limit closure, finite-type objects and scalar-localization results |
| [FinitePresentation](FinitePresentation/README.md) | Actual finite generators/relations, transport and open-locality without a coherent-category dependency |
| [Flat](Flat/README.md) | Genuine stalkwise-flat objects and arbitrary pullback exactness for flat quotients |
| [LocallyFree](LocallyFree/README.md) | Canonical finite-local-basis class, exact arbitrary pullback and conditional fibre/rank results |
| [Coherent](Coherent/README.md) | Locally Noetherian abelian/exact specialization and coherent direct image |
| [Invertible](Invertible/README.md) and [Differentials](Differentials/README.md) | Ordinary Picard tensor/dual/pullback and actual universal differentials/etale comparison |

The main consumers are the more specific object-property categories and [scheme cohomology](../Cohomology/README.md). Scheme/object/coefficient universes remain those of the source statement, including the sheaf-object universe when a small model is used.

The latest general surface adds [Tensor](Tensor/README.md), [Stalk](Stalk/README.md), [ProjectionFormula](ProjectionFormula/README.md), coefficient/cartesian base change and the affine/tensor subfamilies of finite locally free sheaves. All tensors delegate to one site construction. The arbitrary-morphism projection formula requires finite local freeness of its target coefficient; the closed-immersion module formula permits arbitrary coefficients.

The perfect-complex family uses these same ordinary sheaf complexes. `Scheme.Modules.Complex.StrictPerfect X` and `Perfect X` are full subcategories of the chain-map category; the latter's local-model predicate uses the canonical `DerivedCategory.Q`. The [family guide](PerfectComplexes/README.md) separates term bounds, local derived representatives and the exact structures actually supplied. Its definitions and restriction results hold on arbitrary schemes, without global quasi-compactness, Noetherianity or projectivity assumptions.
