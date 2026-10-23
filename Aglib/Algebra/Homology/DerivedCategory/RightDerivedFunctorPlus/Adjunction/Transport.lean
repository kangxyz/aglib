/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison

/-! # Equality transport for the installed bounded-below derived comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w'
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] {G : A ⥤ B} [G.Additive]

/-- Equality transport is sent to equality transport, not to an independently chosen
isomorphism of the installed derived functors. -/
@[simp]
theorem rightDerivedFunctorPlusIso_eqToIso (h : F = G) :
    F.rightDerivedFunctorPlusIso (eqToIso h) =
      eqToIso (show F.rightDerivedFunctorPlus = G.rightDerivedFunctorPlus by cases h; rfl) := by
  cases h
  simpa only [eqToIso_refl] using rightDerivedFunctorPlusIso_refl F

end CategoryTheory.Functor
