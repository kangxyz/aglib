/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Multiplication

/-! Focused consumer of multiplication by global twist sections as whiskering: the general
coherence lemmas for `unitMultiply`, the bridge for `twistingMultiplyGlobal`, and the outer and
inner multiplication laws. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (ι : Type u)

example {a : ℤ} (s : Γ(twistingSheaf R ι a, ⊤)) (F : (ProjectiveSpace R ι).Modules) :
    unitMultiply (twistingSectionUnitHom s) F = (λ_ F).inv ≫ twistingSectionUnitHom s ▷ F :=
  rfl

example (a b : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤)) :
    twistingMultiplyGlobal R ι a b s =
      (λ_ (twistingSheaf R ι b)).inv ≫ twistingSectionUnitHom s ▷ twistingSheaf R ι b ≫
        Functor.LaxMonoidal.μ (twistingFunctor R ι) ⟨a⟩ ⟨b⟩ :=
  twistingMultiplyGlobal_eq R ι a b s

example (a : ℤ) (s : Γ(twistingSheaf R ι a, ⊤)) :
    (twistingGlobalSectionsUnitHomEquiv R ι a).symm (twistingSectionUnitHom s) = s :=
  (twistingGlobalSectionsUnitHomEquiv R ι a).symm_apply_apply s


/--
info: 'CategoryTheory.MonoidalCategory.unitMultiply_naturality' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MonoidalCategory.unitMultiply_naturality

/--
info: 'CategoryTheory.MonoidalCategory.unitMultiply_whiskerRight_associator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MonoidalCategory.unitMultiply_whiskerRight_associator

/--
info: 'CategoryTheory.MonoidalCategory.whiskerLeft_unitMultiply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MonoidalCategory.whiskerLeft_unitMultiply

/--
info: 'CategoryTheory.Functor.LaxMonoidal.unitMultiply_μ_whiskerRight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.LaxMonoidal.unitMultiply_μ_whiskerRight

/--
info: 'CategoryTheory.Functor.LaxBraided.whiskerLeft_unitMultiply_μ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.LaxBraided.whiskerLeft_unitMultiply_μ

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSectionUnitHom_app_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSectionUnitHom_app_one

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_eq_unitMultiply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_eq_unitMultiply

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_eq

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingGlobalSectionsHomAddEquiv_apply_eq_unitMultiply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingGlobalSectionsHomAddEquiv_apply_eq_unitMultiply

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_whiskerRight_tensorMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingMultiplyGlobal_whiskerRight_tensorMap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.whiskerLeft_twistingMultiplyGlobal_tensorMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.whiskerLeft_twistingMultiplyGlobal_tensorMap
