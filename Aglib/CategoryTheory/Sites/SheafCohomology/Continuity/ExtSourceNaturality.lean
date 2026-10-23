/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CocycleComparison

/-!
# Source naturality of the original Ext comparison

The actual comparison from original Ext to native right-derived additive Hom
commutes with precomposition in its representing object. The proof uses the
existing resolution cocycle formula and native derived natural transformations.
The Ext universe is independent of the morphism universe.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Abelian HomologicalComplex Opposite

universe u v w

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (X : C) {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
  (α : preadditiveCoyoneda.obj (op X) ⟶ G)
  {Y : C} (I : InjectiveResolution Y) (n : ℕ)

/-- The native cocycle formula, stated directly for the original natural-degree
Ext constructor rather than its integer-resolution presentation. -/
theorem extRightDerivedAddEquiv_extMk_natTrans
    (a : X ⟶ I.cocomplex.X n) (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.isoRightDerivedObjCochain G n).hom
      ((α.rightDerived n).app Y
        (I.extRightDerivedAddEquiv X n (I.extMk a (n + 1) rfl ha))) =
      let H := (G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      let b := a ≫ (I.cochainComplexXIso n n rfl).inv
      addCommGrpCycleClass H (n : ℤ) (α.app _ b) (by
        have hb : b ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
          dsimp only [b]
          rw [I.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
        have he := ConcreteCategory.congr_hom
          (α.naturality (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) b
        change α.app _ (b ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
          H.d (n : ℤ) ((n : ℤ) + 1) (α.app _ b) at he
        rw [hb, map_zero] at he
        exact he.symm) := by
  have hb : (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫
      I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
    rw [I.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% ha, zero_comp]
  simpa only [extMk, Nat.cast_add, Nat.cast_one] using
    extRightDerivedAddEquiv_cocycle_natTrans X α I n
      (a ≫ (I.cochainComplexXIso n n rfl).inv) hb

/-- Precomposition of original Ext classes agrees with the native derived
precomposition transformation. -/
theorem extRightDerivedAddEquiv_naturality_left
    {X' : C} (f : X' ⟶ X) (x : Ext.{w} X Y n) :
    I.extRightDerivedAddEquiv X' n ((Ext.mk₀ f).comp x (zero_add n)) =
      ((preadditiveCoyoneda.map f.op).rightDerived n).app Y
        (I.extRightDerivedAddEquiv X n x) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  rw [I.mk₀_comp_extMk]
  let G := preadditiveCoyoneda.obj (op X')
  apply (I.isoRightDerivedObjCochain G n).addCommGroupIsoToAddEquiv.injective
  have hL := extRightDerivedAddEquiv_extMk_natTrans X' (𝟙 G) I n
    (f ≫ a) (by simp [ha])
  have hR := extRightDerivedAddEquiv_extMk_natTrans X
    (preadditiveCoyoneda.map f.op) I n a ha
  erw [NatTrans.rightDerived_id G n, NatTrans.id_app] at hL
  change (I.isoRightDerivedObjCochain G n).hom
      (I.extRightDerivedAddEquiv X' n (I.extMk (f ≫ a) (n + 1) rfl _)) =
    addCommGrpCycleClass ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
      (n : ℤ) ((f ≫ a) ≫ (I.cochainComplexXIso n n rfl).inv) _ at hL
  change (I.isoRightDerivedObjCochain G n).hom
      (((preadditiveCoyoneda.map f.op).rightDerived n).app Y
        (I.extRightDerivedAddEquiv X n (I.extMk a (n + 1) rfl ha))) =
    addCommGrpCycleClass ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
      (n : ℤ) (f ≫ (a ≫ (I.cochainComplexXIso n n rfl).inv)) _ at hR
  change (I.isoRightDerivedObjCochain G n).hom _ =
    (I.isoRightDerivedObjCochain G n).hom _
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  exact Category.assoc f a (I.cochainComplexXIso n n rfl).inv

end CategoryTheory.InjectiveResolution
