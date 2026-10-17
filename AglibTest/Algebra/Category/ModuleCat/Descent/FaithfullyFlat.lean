/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Descent.FaithfullyFlat

/-! Focused consumer of effective faithfully flat descent of modules. The stack
statement is Mathlib's `Pseudofunctor.IsStackFor` for Mathlib's extension-of-scalars
pseudofunctor, reindexed to the site `CommRingCatᵒᵖ` by the literal composite with
`unopUnop`, and the singleton presieve of `f.op`; the reindexed functoriality is literally
`ModuleCat.extendScalars`, as functors (`rfl`). -/

@[expose] public section

noncomputable section
open CategoryTheory Opposite

universe u

example : CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.{u} =
    (unopUnop CommRingCat.{u}).toPseudofunctor.comp
      CommRingCat.moduleCatExtendScalarsPseudofunctor.{u} :=
  rfl

example {R S : CommRingCat.{u}} (g : R ⟶ S) :
    (CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.map g.op.op.toLoc).toFunctor =
      ModuleCat.extendScalars g.hom :=
  rfl

example {R S : CommRingCat.{u}} (g : R ⟶ S) (M : ModuleCat.{u} R) :
    (CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.map g.op.op.toLoc).toFunctor.obj M =
      (ModuleCat.extendScalars g.hom).obj M :=
  rfl

example {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.IsStackFor (Presieve.singleton f.op) :=
  CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton f hf

example {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    ((CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
      (fun (_ : PUnit.{1}) ↦ f.op)).IsEquivalence :=
  CommRingCat.ExtendScalarsDescent.isEquivalence_toDescentData f hf

example {A B : CommRingCat.{u}} (f : A ⟶ B) :
    (CommRingCat.ExtendScalarsDescent.coalgebraFunctor f).FullyFaithful :=
  CommRingCat.ExtendScalarsDescent.fullyFaithfulCoalgebraFunctor f

example {A B : CommRingCat.{u}} (f : A ⟶ B) :
    (CommRingCat.moduleCatExtendScalarsPseudofunctorOpOp.{u}).toDescentData
        (fun (_ : PUnit.{1}) ↦ f.op) ⋙ CommRingCat.ExtendScalarsDescent.coalgebraFunctor f ≅
      Comonad.comparison (ModuleCat.extendRestrictScalarsAdj f.hom) :=
  CommRingCat.ExtendScalarsDescent.toDescentDataCompCoalgebraFunctorIso f

/--
info: 'CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CommRingCat.isStackFor_moduleCatExtendScalarsPseudofunctorOpOp_singleton

/--
info: 'CommRingCat.ExtendScalarsDescent.isEquivalence_coalgebraFunctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CommRingCat.ExtendScalarsDescent.isEquivalence_coalgebraFunctor

/--
info: 'CommRingCat.ExtendScalarsDescent.fullyFaithfulCoalgebraFunctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CommRingCat.ExtendScalarsDescent.fullyFaithfulCoalgebraFunctor
