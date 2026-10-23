/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedScalarSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedGammaZero
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedExtZero

/-!
# Abstract normalization packet for native derived sections

The complete degree-zero calculation is performed before specializing the
abelian category to module sheaves. This keeps native resolution instances opaque.
-/

@[expose] public noncomputable section

universe u v u₁ v₁ w r s t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]

/-- The original unit under a represented exact-postcomposition normalization. -/
lemma representedPostcomp_unit (F : C ⥤ D) (G : D ⥤ AddCommGrpCat.{v})
    [F.Additive] [G.Additive] [G.PreservesHomology] (X : C)
    (α : preadditiveCoyoneda.obj (op X) ≅ F ⋙ G) (M : C) :
    G.map (F.toRightDerivedZero.app M) ≫
        ((rightDerivedPostcompIso F G 0).symm ≪≫
          rightDerivedNatIso α.symm 0).hom.app M =
      α.inv.app M ≫ (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app M := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, rightDerivedNatIso]
  rw [← toRightDerivedZero_postcomp F G M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact toRightDerivedZero_naturality α.inv M

/-- Original Ext degree zero, for the full abstract represented comparison. -/
lemma representedPostcomp_ext_zero [HasExt.{w} C]
    (F : C ⥤ D) (G : D ⥤ AddCommGrpCat.{v})
    [F.Additive] [G.Additive] [G.PreservesHomology] (X : C)
    (α : preadditiveCoyoneda.obj (op X) ≅ F ⋙ G) (M : C) (x : G.obj (F.obj M)) :
    (((((rightDerivedPostcompIso F G 0).symm ≪≫
        rightDerivedNatIso α.symm 0).app M).addCommGroupIsoToAddEquiv).trans
      (extRightDerivedRepresentedAddEquiv X M 0).symm)
        (G.map (F.toRightDerivedZero.app M) x) = Ext.mk₀ (α.inv.app M x) := by
  let f : X ⟶ M := α.inv.app M x
  change (extRightDerivedRepresentedAddEquiv X M 0).symm
    (((rightDerivedPostcompIso F G 0).symm ≪≫
      rightDerivedNatIso α.symm 0).hom.app M (G.map (F.toRightDerivedZero.app M) x)) =
    Ext.mk₀ f
  apply (AddEquiv.symm_apply_eq _).mpr
  have h := ConcreteCategory.congr_hom (representedPostcomp_unit F G X α M) x
  change ((rightDerivedPostcompIso F G 0).symm ≪≫
      rightDerivedNatIso α.symm 0).hom.app M (G.map (F.toRightDerivedZero.app M) x) =
    (preadditiveCoyoneda.obj (op X)).toRightDerivedZero.app M f at h
  exact h.trans (extRightDerivedRepresentedAddEquiv_mk₀ f).symm


/-- Module-valued version with the original section and its original morphism
specified before any concrete sheaf specialization. -/
lemma moduleRepresentedPostcomp_ext_zero [HasExt.{w} C]
    {B : Type r} [Ring B] (F : C ⥤ ModuleCat.{v} B) [F.Additive] (X : C)
    (α : preadditiveCoyoneda.obj (op X) ≅ F ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat)
    (β : F.rightDerived 0 ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat ≅
      (preadditiveCoyoneda.obj (op X)).rightDerived 0)
    (hβ : β =
      (rightDerivedPostcompIso F (forget₂ (ModuleCat.{v} B) AddCommGrpCat) 0).symm ≪≫
        rightDerivedNatIso α.symm 0)
    (M : C) (x : F.obj M) (f : X ⟶ M) (hx : α.inv.app M x = f) :
    representedDerivedModuleAddEquiv X (F.rightDerived 0) 0 β M
      (F.toRightDerivedZero.app M x) = Ext.mk₀ f := by
  subst β
  have h := representedPostcomp_ext_zero F
    (forget₂ (ModuleCat.{v} B) AddCommGrpCat) X α M x
  exact h.trans (congrArg (fun a : X ⟶ M => Ext.mk₀ a) hx)


/-- Keep the complete comparison, original unit value, and output class opaque
when instantiating the represented degree-zero normalization. -/
lemma moduleRepresentedPostcomp_ext_zero_of_eq [HasExt.{w} C]
    {B : Type r} [Ring B] (F : C ⥤ ModuleCat.{v} B) [F.Additive] (X : C)
    (α : preadditiveCoyoneda.obj (op X) ≅ F ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat)
    (β : F.rightDerived 0 ⋙ forget₂ (ModuleCat.{v} B) AddCommGrpCat ≅
      (preadditiveCoyoneda.obj (op X)).rightDerived 0)
    (hβ : β =
      (rightDerivedPostcompIso F (forget₂ (ModuleCat.{v} B) AddCommGrpCat) 0).symm ≪≫
        rightDerivedNatIso α.symm 0)
    (M : C) (x : F.obj M) (f : X ⟶ M) (hx : α.inv.app M x = f)
    (E : (F.rightDerived 0).obj M ≃+ Ext.{w} X M 0)
    (hE : E = representedDerivedModuleAddEquiv X (F.rightDerived 0) 0 β M)
    (y : (F.rightDerived 0).obj M) (hy : y = F.toRightDerivedZero.app M x)
    (z : Ext.{w} X M 0) (hz : z = Ext.mk₀ f) : E y = z := by
  rw [hE, hy, hz]
  exact moduleRepresentedPostcomp_ext_zero F X α β hβ M x f hx


section Scalar

variable {B : Type r} [Ring B] {Λ : Type s} [Ring Λ]
  (F : C ⥤ ModuleCat.{t} B) [F.Additive] (α : Λ →+* B)
  [(ModuleCat.restrictScalars.{t} α).PreservesHomology]

/-- Restriction of scalars retains the native degree-zero section for every
subsequent additive identification, without unfolding that identification. -/
lemma scalarPostcomp_addEquiv_zero (M : C) {Z : Type*} [AddCommGroup Z]
    (e : ((F.rightDerived 0).obj M) ≃+ Z) (x : F.obj M) :
    scalarDerivedModuleAddEquiv (F.rightDerived 0)
      ((F ⋙ ModuleCat.restrictScalars α).rightDerived 0) α
      (rightDerivedPostcompIso F (ModuleCat.restrictScalars.{t} α) 0) M e
        ((F ⋙ ModuleCat.restrictScalars α).toRightDerivedZero.app M x) =
      e (F.toRightDerivedZero.app M x) := by
  have h := ConcreteCategory.congr_hom
    (toRightDerivedZero_postcomp F (ModuleCat.restrictScalars.{t} α) M) x
  change (rightDerivedPostcompIso F (ModuleCat.restrictScalars.{t} α) 0).hom.app M
      ((F ⋙ ModuleCat.restrictScalars α).toRightDerivedZero.app M x) =
    F.toRightDerivedZero.app M x at h
  exact congrArg e h

end Scalar

end CategoryTheory.Sheaf.ModuleCoefficients
