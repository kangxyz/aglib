/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.AffineStack

/-! Focused consumer of the affine descent transfer: the generic transfer lemmas of
`Aglib.CategoryTheory.Sites.Descent.{Transfer,SiteChange}` instantiated at `Spec`, and the affine
stack statement conditional on the comparison transformation. Universes: `CommRingCat.{u}`,
`Scheme.{u}`. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules CommRingCat

universe u

variable {A B : CommRingCat.{u}} (f : A ⟶ B)

example (X : CommRingCat.{u}ᵒᵖ) : (specTransApp.{u} X).IsEquivalence := inferInstance

example (X : CommRingCat.{u}ᵒᵖ) :
    specQuasicoherentPseudofunctor.{u}.obj (.mk (Opposite.op X)) =
      quasicoherentPseudofunctor.{u}.obj (.mk (Opposite.op (Spec X.unop))) := rfl

example {X Y : CommRingCat.{u}ᵒᵖ} (g : Y ⟶ X) (N : ModuleCat.{u} X.unop) :
    ((specTransNat g).hom.app N).hom = (tildePullbackIso g.unop).inv.app N := rfl

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isStackFor_quasicoherentPseudofunctor_singleton_specMap_of_compTransAlong

/--
info: 'CategoryTheory.Pseudofunctor.CompTrans.isStackFor_of_isStackFor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.CompTrans.isStackFor_of_isStackFor

/--
info: 'CategoryTheory.Pseudofunctor.isStackFor_ofArrows_map_of_restrictAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.isStackFor_ofArrows_map_of_restrictAlong

/--
info: 'CategoryTheory.Pseudofunctor.CompTrans.pullHom_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.CompTrans.pullHom_conj

/--
info: 'CategoryTheory.Pseudofunctor.CompTransAlong.toCompTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.CompTransAlong.toCompTrans
