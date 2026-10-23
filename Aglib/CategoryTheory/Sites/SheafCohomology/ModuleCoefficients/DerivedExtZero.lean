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
      (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app Y f := by
  let I := injectiveResolution Y
  let G := preadditiveCoyoneda.obj (op X)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hf : (f ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    erw [Category.assoc, I.ι.comm 0 1]
    simp
  have hp : I.toRightDerivedZero' G f = K.cyclesMk (f ≫ I.ι.f 0) 1 (by simp) hf := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
    have hi : K.iCycles 0 (K.cyclesMk (f ≫ I.ι.f 0) 1 (by simp) hf) = f ≫ I.ι.f 0 :=
      K.i_cyclesMk _ _ _ _
    rw [hi]
    exact ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles G) f
  rw [← I.extMk_ι_zero f, extRightDerivedRepresentedAddEquiv_extMk,
    I.toRightDerivedZero_eq G]
  change (I.isoRightDerivedObj G 0).inv (K.homologyπ 0
      (K.cyclesMk (f ≫ I.ι.f 0) 1 (by simp) hf)) =
    (I.isoRightDerivedObj G 0).inv (K.homologyπ 0 (I.toRightDerivedZero' G f))
  rw [hp]

end CategoryTheory.Sheaf.ModuleCoefficients
