# Descent for schemes

This family collects descent statements for objects over schemes, in the
organization of the Stacks project's descent chapter. The objects keep their
native namespaces (`Scheme.Modules`, `Scheme.IdealSheafData`); only the import
paths group them here. Stack statements use Mathlib's
`Pseudofunctor.IsPrestack`, `Pseudofunctor.IsStack` and
`Pseudofunctor.IsStackFor` (`Mathlib/CategoryTheory/Sites/Descent/`).

| Family | Content |
| --- | --- |
| [Modules](Modules/README.md) | The pullback pseudofunctor of module sheaves on `Scheme`, its quasi-coherent and line-bundle full subpseudofunctors, and unconditional stack instances for `Scheme.zariskiTopology`; in [Fppf](Modules/Fppf/README.md), effective descent of quasi-coherent sheaves along a faithfully flat ring map |
| [IdealSheaf](IdealSheaf/README.md) | Faithfully flat descent of ideal sheaves and closed subschemes along flat, surjective, quasi-compact morphisms (Nitsure, Lemma 6.7(2)) |

The affine and ring-level inputs stay with their algebraic owners:
[RingTheory/Descent](../../RingTheory/Descent/README.md) descends algebras and,
along faithfully flat ring maps, finite presentation, invertibility and ideals;
[ModuleCat/Descent](../../Algebra/Category/ModuleCat/Descent/README.md) proves
effective descent of modules along faithfully flat ring maps, as `IsStackFor`
for the extension-of-scalars pseudofunctor on `CommRingCatᵒᵖ`.
