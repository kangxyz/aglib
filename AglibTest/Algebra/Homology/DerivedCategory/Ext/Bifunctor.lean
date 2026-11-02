/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor

/-!
The original three independent HasExt worlds and actual partial exactness
suffice for signed interchange and both native source-connecting laws.
No EnoughInjectives, EnoughProjectives, derived model or sign datum is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

example {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) (h : p + q = n) :
    F.extBifunctor x y h = ((-1 : ℤ) ^ (p * q)) •
      (y.mapExactFunctor (F.obj X₀)).comp
        (x.mapExactFunctor (F.flip.obj Y₁)) ((Nat.add_comm q p).trans h) :=
  F.extBifunctor_comm x y h

example {X₀ X₁ : C} {Y₀ Y₁ : D} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) :
    F.extBifunctor (Ext.mk₀ f) (Ext.mk₀ g) (zero_add 0) =
      Ext.mk₀ ((F.map f).app Y₀ ≫ (F.obj X₁).map g) :=
  F.extBifunctor_mk₀_mk₀ f g

example {S : ShortComplex C} (hS : S.ShortExact)
    {X₁ : C} {Y₀ Y₁ : D} {p p' q n n' : ℕ}
    (x : Ext.{w₁} S.X₁ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q)
    (hp : p + 1 = p') (h : p + q = n) (h' : p' + q = n') :
    F.extBifunctor (Ext.δ hS p p' hp x) y h' = ((-1 : ℤ) ^ q) •
      Ext.δ (hS.map_of_exact (F.flip.obj Y₀)) n n' (by omega) (F.extBifunctor x y h) :=
  F.extBifunctor_δ_left hS x y hp h h'

example {T : ShortComplex D} (hT : T.ShortExact)
    {X₀ X₁ : C} {Y₁ : D} {p q q' n n' : ℕ}
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} T.X₁ Y₁ q)
    (hq : q + 1 = q') (h : p + q = n) (h' : p + q' = n') :
    F.extBifunctor x (Ext.δ hT q q' hq y) h' =
      Ext.δ (hT.map_of_exact (F.obj X₀)) n n' (by omega) (F.extBifunctor x y h) :=
  F.extBifunctor_δ_right hT x y hq h h'

end

/--
info: 'CategoryTheory.Functor.extBifunctor_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extBifunctor_comm

/--
info: 'CategoryTheory.Functor.extBifunctor_δ_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extBifunctor_δ_left

/--
info: 'CategoryTheory.Functor.extBifunctor_δ_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.extBifunctor_δ_right
