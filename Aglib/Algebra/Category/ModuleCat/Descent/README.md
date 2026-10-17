# Faithfully flat descent of modules

This family extends Mathlib's `Mathlib/Algebra/Category/ModuleCat/Descent.lean`, which proves
that extension of scalars along a faithfully flat ring map is comonadic and leaves effectivity
of descent as a TODO. Statements use Mathlib's actual pseudofunctor and descent-data objects.

## Objects

- `CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp :
  Pseudofunctor (LocallyDiscrete CommRingCat.{u}ᵒᵖᵒᵖ) Cat` is, by definition, the composite
  `(unopUnop CommRingCat).toPseudofunctor.comp CommRingCat.moduleCatExtendScalarsPseudofunctor`.
  It has the shape `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` for the site category `C = CommRingCatᵒᵖ`
  required by `Pseudofunctor.IsStackFor` and `Pseudofunctor.IsStack`. Its value on
  `g.op.op.toLoc` is literally `ModuleCat.extendScalars g.hom` (`rfl`).
- `CommRingCat.ExtendScalarsDescent.Data f` abbreviates Mathlib's
  `Pseudofunctor.DescentData` of this pseudofunctor for the family `fun _ : PUnit ↦ f.op`.

## Results

[Coalgebra](Coalgebra.lean), for an arbitrary ring map `f : A ⟶ B` (no flatness):

- `coalgebraFunctor f : Data f ⥤ (extendRestrictScalarsAdj f.hom).toComonad.Coalgebra`
  sends a descent datum to its module with the coaction `N ⟶ B ⊗_A N`, the descent morphism
  over the categorical pushout `B ⊗_A B` evaluated on `1 ⊗ n` and transported by Aglib's
  `ModuleCat.baseChangeMap`. Counit and coassociativity are the diagonal and cocycle axioms
  (the latter over `pushout f (f ≫ pushout.inl f f)`).
- `fullyFaithfulCoalgebraFunctor f : (coalgebraFunctor f).FullyFaithful`.
- `toDescentDataCompCoalgebraFunctorIso f : toDescentData ⋙ coalgebraFunctor f ≅
  Comonad.comparison (extendRestrictScalarsAdj f.hom)`.

[FaithfullyFlat](FaithfullyFlat.lean), for `hf : f.hom.FaithfullyFlat`:

- `CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton f hf :
  moduleCatExtendScalarsPseudofunctorOpOp.IsStackFor (Presieve.singleton f.op)`. It encodes
  Stacks Project, Tag 023N (1)–(2), and Vistoli, arXiv:math/0412512v4, Theorem 4.21, with
  Mathlib's `Pseudofunctor.DescentData` in place of the cocycle category of Stacks 023G or
  Vistoli's `Mod_{A→B}`; the description of the inverse by `H⁰` in 023N (3) is not encoded.
  Modules are `ModuleCat.{u}` over rings in `CommRingCat.{u}`;
- `ExtendScalarsDescent.isEquivalence_toDescentData f hf` (the same statement for the
  `PUnit`-indexed family) and `ExtendScalarsDescent.isEquivalence_coalgebraFunctor f hf`.

The proof feeds Mathlib's `ModuleCat.comonadicExtendScalars` through the fully faithful
`coalgebraFunctor`.

## Helpers with other intended owners

`ModuleCat.extendScalarsComp'`, `ModuleCat.ExtendScalars.oneTmul` and their pure-tensor
lemmas, `ModuleCat.baseChangeMap_oneTmul` (a restatement of
`ModuleCat.baseChangeMap_unit_apply`) and the `mapComp'` bridges of
`moduleCatExtendScalarsPseudofunctorOpOp` live in [Coalgebra](Coalgebra.lean). Their natural
owners are `Algebra/Category/ModuleCat/ChangeOfRings` and
`Algebra/Category/ModuleCat/BaseChange`; they were placed here to leave existing leaves
unchanged.

## Consumers

Plan row F6 (`doc/PICARD_PLAN.md`) is the intended consumer: fppf stacks of quasi-coherent
sheaves reduce one faithfully flat morphism of affine schemes to this statement. Two inputs
remain open for F6 and are not in this family:

- the comparison of quasi-coherent sheaves on affine schemes with this `ModuleCat`
  pseudofunctor, a pseudonatural equivalence through the tilde construction compatible with
  pullback along `Spec.map`;
- the transfer of `IsStackFor` from the site `CommRingCatᵒᵖ` to `Scheme`. Over `Scheme`,
  Mathlib's `Pseudofunctor.DescentData` ranges over all test schemes, not only affine ones.

The focused test is `AglibTest/Algebra/Category/ModuleCat/Descent/FaithfullyFlat.lean`.
