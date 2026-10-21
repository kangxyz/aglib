# Descent for schemes

This family collects descent statements for objects over schemes, in the
organization of the Stacks project's descent chapter. The objects keep their
native namespaces (`Scheme.Modules`, `Scheme.IdealSheafData`); only the import
paths group them here. Stack statements use Mathlib's
`Pseudofunctor.IsPrestack`, `Pseudofunctor.IsStack` and
`Pseudofunctor.IsStackFor` (`Mathlib/CategoryTheory/Sites/Descent/`).

| Family | Content |
| --- | --- |
| [FinitePresentation](FinitePresentation/README.md) | Actual stage models and finite diagrams of finitely presented qcqs schemes over filtered ring colimits, with canonical pullback comparisons, common-stage maps and equations, and model-property suppliers for finite-base curves. |
| [Modules](Modules/README.md) | The pullback pseudofunctor of module sheaves on `Scheme`, its quasi-coherent and line-bundle full subpseudofunctors, and unconditional stack instances for `Scheme.zariskiTopology`; in [Fppf](Modules/Fppf/README.md), effective descent of quasi-coherent sheaves along a faithfully flat ring map, and unconditional stack instances of quasi-coherent sheaves for `Scheme.fpqcTopology` and `Scheme.fppfTopology` and of line bundles for `Scheme.fppfTopology` |
| [IdealSheaf](IdealSheaf/README.md) | Faithfully flat descent of ideal sheaves and closed subschemes along flat, surjective, quasi-compact morphisms (Nitsure, Lemma 6.7(2)) |
| [Opens](Opens.lean) | Open subschemes: `Scheme.opensPresheaf` (`X ↦ X.Opens`, preimages) is a sheaf for `Scheme.fppfTopology`, and descent of opens along jointly surjective families of open morphisms and along one flat surjective morphism locally of finite presentation (Stacks, Tag 03N0, in its fppf form); focused consumer [AglibTest/AlgebraicGeometry/Descent/Opens.lean](../../../AglibTest/AlgebraicGeometry/Descent/Opens.lean) |

The affine and ring-level inputs stay with their algebraic owners:
[RingTheory/Descent](../../RingTheory/Descent/README.md) descends algebras and,
along faithfully flat ring maps, finite presentation, invertibility and ideals;
[ModuleCat/Descent](../../Algebra/Category/ModuleCat/Descent/README.md) proves
effective descent of modules along faithfully flat ring maps, as `IsStackFor`
for the extension-of-scalars pseudofunctor on `CommRingCatᵒᵖ`.
