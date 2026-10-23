/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExtNormalization

/-!
# Coefficient naturality of the native represented Ext comparison

The coefficient map is original Yoneda postcomposition with `Ext.mk₀`, and
its derived counterpart is the native right-derived functor map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- The identity forgetful functor on additive commutative groups. -/
local instance derivedExtNaturalityHasForget₂ :
    HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} where
  forget₂ := 𝟭 _

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
  inferInstanceAs (Functor.Additive (𝟭 AddCommGrpCat.{v}))

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
  inferInstanceAs (Functor.PreservesHomology (𝟭 AddCommGrpCat.{v}))

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] {X Y Y' : C}

/-- The actual Ext comparison commutes with the original coefficient morphism. -/
lemma extRightDerivedRepresentedAddEquiv_naturality
    (f : Y ⟶ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extRightDerivedRepresentedAddEquiv X Y' n (x.comp (Ext.mk₀ f) (add_zero _)) =
      ((preadditiveCoyoneda.obj (op X)).rightDerived n).map f
        (extRightDerivedRepresentedAddEquiv X Y n x) := by
  let I := injectiveResolution Y
  let I' := injectiveResolution Y'
  let G := preadditiveCoyoneda.obj (op X)
  let φ : I.Hom I' f :=
    { hom := InjectiveResolution.desc f I' I
      ι_f_zero_comp_hom_f_zero := by
        rw [CochainComplex.single₀_map_f_zero]
        exact InjectiveResolution.desc_commutes_zero f I' I }
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  rw [InjectiveResolution.extMk_comp_mk₀ a (n + 1) rfl ha φ,
    extRightDerivedRepresentedAddEquiv_extMk,
    extRightDerivedRepresentedAddEquiv_extMk]
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h := ConcreteCategory.congr_hom
    (InjectiveResolution.isoRightDerivedObj_inv_naturality f I I' φ.hom
      (by
        have hφ := φ.ι_f_zero_comp_hom_f_zero
        rw [CochainComplex.single₀_map_f_zero] at hφ
        exact hφ) G n)
    (K.homologyπ n (K.cyclesMk a (n + 1) (by simp) ha))
  change (G.rightDerived n).map f ((I.isoRightDerivedObj G n).inv
      (K.homologyπ n (K.cyclesMk a (n + 1) (by simp) ha))) =
    (I'.isoRightDerivedObj G n).inv
    (HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℕ)).map φ.hom) n
      (K.homologyπ n (K.cyclesMk a (n + 1) (by simp) ha))) at h
  erw [homologyMap_cyclesMk] at h
  exact h.symm

end CategoryTheory.Sheaf.ModuleCoefficients
