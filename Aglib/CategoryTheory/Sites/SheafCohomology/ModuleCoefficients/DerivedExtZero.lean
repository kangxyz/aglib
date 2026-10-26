/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.ExtZero
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExtNormalization

/-!
# Original degree-zero normalization of represented derived sections

This uses the single public native resolution-Ext zero supplier, rather than
copying the previous geometric private implementation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- The identity forgetful functor on additive commutative groups. -/
local instance derivedExtZeroHasForget₂ : HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} where
  forget₂ := 𝟭 _

local instance derivedExtZeroForget₂Additive :
    (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
  inferInstanceAs (Functor.Additive (𝟭 AddCommGrpCat.{v}))

local instance derivedExtZeroForget₂PreservesHomology :
    (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
  inferInstanceAs (Functor.PreservesHomology (𝟭 AddCommGrpCat.{v}))

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] {X Y : C}

/-- The actual represented Ext comparison sends `Ext.mk₀` to the native derived-functor unit. -/
lemma extRightDerivedRepresentedAddEquiv_mk₀ (f : X ⟶ Y) :
    extRightDerivedRepresentedAddEquiv X Y 0 (Ext.mk₀ f) =
      (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app Y f :=
  CategoryTheory.Abelian.extRightDerivedRepresentedAddEquiv_mk₀ f

end CategoryTheory.Sheaf.ModuleCoefficients
