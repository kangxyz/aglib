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
| [FiniteType](FiniteType/README.md) | Eventual closedness and separatedness along actual affine-transition limits, with conditional closed finite-presentation hulls and an unconditional compact-source specialization. |
| [Modules](Modules/README.md) | The pullback pseudofunctor of module sheaves on `Scheme`, its quasi-coherent and line-bundle full subpseudofunctors, and unconditional stack instances for `Scheme.zariskiTopology`; in [Fppf](Modules/Fppf/README.md), effective descent of quasi-coherent sheaves along a faithfully flat ring map, and unconditional stack instances of quasi-coherent sheaves for `Scheme.fpqcTopology` and `Scheme.fppfTopology` and of line bundles for `Scheme.fppfTopology` |
| [IdealSheaf](IdealSheaf/README.md) | Faithfully flat descent of ideal sheaves and closed subschemes along flat, surjective, quasi-compact morphisms (Nitsure, Lemma 6.7(2)) |
| [Opens](Opens.lean) | Open subschemes: `Scheme.opensPresheaf` (`X ↦ X.Opens`, preimages) is a sheaf for `Scheme.fppfTopology`, and descent of opens along jointly surjective families of open morphisms and along one flat surjective morphism locally of finite presentation (Stacks, Tag 03N0, in its fppf form); focused consumer [AglibTest/AlgebraicGeometry/Descent/Opens.lean](../../../AglibTest/AlgebraicGeometry/Descent/Opens.lean) |

The affine and ring-level inputs stay with their algebraic owners:
[RingTheory/Descent](../../RingTheory/Descent/README.md) descends algebras and,
along faithfully flat ring maps, finite presentation, invertibility and ideals;
[ModuleCat/Descent](../../Algebra/Category/ModuleCat/Descent/README.md) proves
effective descent of modules along faithfully flat ring maps, as `IsStackFor`
for the extension-of-scalars pseudofunctor on `CommRingCatᵒᵖ`.

[CompletionNormalization](CompletionNormalization.md) proves finiteness and
the actual normalization/completion comparison for a proper birational
integral model over a Noetherian local domain of dimension two, assuming
the actual completion is a domain, the pullback is integral and its stalks
are normal off the original closed fibre. The completion and structural
maps are retained. These conditional descent interfaces do not construct
a normalized resolving chain or assert arbitrary completion base change.

[CompletionPointBlowup](CompletionPointBlowup.md) proves the actual
residue-point cartesian square over the original closed fibre, full
point-centre equality and ordinary flat blowup base change. Its one-step
`exists_normalizedPointCompletion` retains a proper birational integral
model over a Noetherian local domain of dimension two, domain completion,
an actual isomorphism of the integral upper model with the literal pullback,
normal upper stalks and a specified closed nongeneric upper point. It derives
finite lower normalization and the original normalized-blowup comparison;
neither is assumed. The supplied-chain consumer retains normal completion.
No Nagata premise is added to this step, and no resolving upper chain or
global descent capstone is constructed here.
