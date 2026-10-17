/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.LocalIso

/-! Focused consumer of the monoidal class of local isomorphisms of module presheaves. The
class is `GrothendieckTopology.W` of the Zariski topology pulled back along Mathlib's
`PresheafOfModules.toPresheaf`, on Mathlib's monoidal category
`PresheafOfModulesOfCommRing X.sheaf.obj`, for an arbitrary scheme. The consumer abbreviation
`W` below repeats the body used by the monoidal-structure layer; the instance is found for it.
The last two examples are the two comparison isomorphisms of the general associator for
arbitrary module sheaves. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme.Modules

universe u

variable (X : Scheme.{u})

/-- The consumer spelling of the class. -/
abbrev W : MorphismProperty (PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :=
  (Opens.grothendieckTopology X).W.inverseImage (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

example : W X = presheafLocalIso X := rfl

example : (W X).IsMonoidal := inferInstance

example : (presheafLocalIso X).IsMonoidal := inferInstance

example : (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).IsLocalization (presheafLocalIso X) :=
  inferInstance

example {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q) :
    W X f ↔ IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f) :=
  presheafLocalIso_iff f

example (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    W X ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P) :=
  presheafLocalIso_unit P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q) :
    W X f ↔ ∀ N : X.Modules, Function.Bijective (fun g : Q ⟶ N.val => f ≫ g) :=
  presheafLocalIso_iff_bijective f

example (M N O : X.Modules) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N) ▷
        (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj O)) :=
  (presheafLocalIso_iff _).1 ((W X).whiskerRight_mem _ (presheafLocalIso_unit _) _)

example (M N O : X.Modules) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ◁
        (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj O))) :=
  (presheafLocalIso_iff _).1 ((W X).whiskerLeft_mem _ _ (presheafLocalIso_unit _))

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_unit

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_iff_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_iff_bijective

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_whiskerLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_whiskerLeft

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_whiskerRight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_whiskerRight

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_isMonoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_isMonoidal

/--
info: 'AlgebraicGeometry.Scheme.Modules.presheafLocalIso_isMultiplicative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms presheafLocalIso_isMultiplicative
