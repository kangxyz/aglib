/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekExt

/-!
# Tests for extension by zero on Ext groups of module sheaves

The examples take an open immersion `j : U ⟶ X` and `Λ = ULift (ZMod n)`, with the standard
Ext universes, and guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityLowerShriekExt

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

/-- `j_!` on Ext groups preserves Yoneda composition. -/
example {A B C : ModuleSheaf U (ULift.{u + 1} (ZMod n))} {a b : ℕ}
    (α : Ext.{u + 2} A B a) (β : Ext.{u + 2} B C b) :
    moduleLowerShriekExt j _ A C (a + b) (α.comp β rfl) =
      (moduleLowerShriekExt j _ A B a α).comp (moduleLowerShriekExt j _ B C b β) rfl :=
  moduleLowerShriekExt_comp j _ α β rfl

/-- `j_!` sends extension classes to extension classes. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact) :
    moduleLowerShriekExt j _ S.X₃ S.X₁ 1 hS.extClass =
      (shortExact_moduleLowerShriek j _ hS).extClass :=
  moduleLowerShriekExt_extClass j _ hS

/-- The adjunction `j_! ⊣ j^*` on Ext groups. -/
example (A : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (B : ModuleSheaf X (ULift.{u + 1} (ZMod n)))
    (q : ℕ) :
    Ext.{u + 2} ((moduleLowerShriek j _).obj A) B q ≃+
      Ext.{u + 2} A ((moduleInverseImage j _).obj B) q :=
  moduleLowerShriekExtEquiv j _ A B q

/-- The Ext adjunction is compatible with Yoneda composition in the source. -/
example {A₁ A₂ : ModuleSheaf U (ULift.{u + 1} (ZMod n))}
    {B : ModuleSheaf X (ULift.{u + 1} (ZMod n))} {a b : ℕ} (e : Ext.{u + 2} A₁ A₂ a)
    (e' : Ext.{u + 2} ((moduleLowerShriek j _).obj A₂) B b) :
    moduleLowerShriekExtEquiv j _ A₁ B (a + b)
        ((moduleLowerShriekExt j _ A₁ A₂ a e).comp e' rfl) =
      e.comp (moduleLowerShriekExtEquiv j _ A₂ B b e') rfl :=
  moduleLowerShriekExtEquiv_comp_left j _ e e' rfl

/-- The Ext adjunction is compatible with Yoneda composition in the target. -/
example {A : ModuleSheaf U (ULift.{u + 1} (ZMod n))}
    {B₁ B₂ : ModuleSheaf X (ULift.{u + 1} (ZMod n))} {a b : ℕ}
    (e : Ext.{u + 2} ((moduleLowerShriek j _).obj A) B₁ a) (e' : Ext.{u + 2} B₁ B₂ b) :
    moduleLowerShriekExtEquiv j _ A B₂ (a + b) (e.comp e' rfl) =
      (moduleLowerShriekExtEquiv j _ A B₁ a e).comp
        (e'.mapExactFunctor (moduleInverseImage j _)) rfl :=
  moduleLowerShriekExtEquiv_comp_right j _ e e' rfl

end AglibTest.EtaleDualityLowerShriekExt

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExt

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExt_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExt_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExt_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExt_comp

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExt_mk₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExt_mk₀

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExt_extClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExt_extClass

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv_symm_apply

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_mk₀' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv_mk₀

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_comp_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv_comp_left

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_comp_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleLowerShriekExtEquiv_comp_right
