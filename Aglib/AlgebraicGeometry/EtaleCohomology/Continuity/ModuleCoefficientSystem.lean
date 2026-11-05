/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleImageCoherence
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Reindex

/-! # Original fixed-ring coefficient systems

The generic adjoint-system construction uses the original module-valued
images over the unchanged ring. Reindexing retains actual scheme maps and
all original identity and composition comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R]

/-- Original étale images, indexed in the coefficient-transition direction. -/
def schemeAdjunctionData :
    InjectiveSystem.AdjunctionData
      (fun X : Scheme.{u}ᵒᵖ => Coefficient R X.unop) where
  left a := inverseImage R a.unop
  right a := directImage R a.unop
  adj a := imageAdjunction R a.unop
  left_preservesMonomorphisms _ := inferInstance
  idIso X := directImageIdIso R X.unop
  compIso a b := (directImageCompIso R a.unop b.unop).symm

private theorem directImageCompIso_inverse_associativity {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (directImageCompIso R (g ≫ f) h).symm ≪≫
        Functor.isoWhiskerLeft (directImage R h) (directImageCompIso R f g).symm =
      eqToIso (congrArg (fun k : V ⟶ X => directImage R k) (Category.assoc h g f).symm) ≪≫
        (directImageCompIso R f (h ≫ g)).symm ≪≫
        Functor.isoWhiskerRight (directImageCompIso R g h).symm (directImage R f) ≪≫
        Functor.associator (directImage R h) (directImage R g) (directImage R f) := by
  apply Iso.symm_bijective.injective
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    Category.assoc, Functor.comp_obj] using (directImageCompIso_assoc_app R f g h K).symm

/-- The generic original-comparison laws hold for the actual étale images.
These are supplied by native scheme-image coherence, not new assumptions. -/
theorem schemeAdjunctionData_coherent : (schemeAdjunctionData R).Coherent where
  id_comp := by
    intro i j a F
    change (directImageCompIso R (𝟙 i.unop) a.unop).inv.app F ≫
      (directImageIdIso R i.unop).hom.app ((directImage R a.unop).obj F) =
        eqToHom (congrArg (fun f => (directImage R f).obj F) (Category.comp_id a.unop))
    have h := congrArg (fun e => e.hom.app F) (directImageCompIso_id_comp R a.unop)
    change (directImageCompIso R (𝟙 i.unop) a.unop).inv.app F ≫
      ((directImageIdIso R i.unop).hom.app ((directImage R a.unop).obj F) ≫ 𝟙 _) = _ at h
    simpa only [Category.comp_id, eqToIso.hom, eqToHom_app] using h
  comp_id := by
    intro i j a F
    change (directImageCompIso R a.unop (𝟙 j.unop)).inv.app F ≫
      (directImage R a.unop).map ((directImageIdIso R j.unop).hom.app F) =
        eqToHom (congrArg (fun f => (directImage R f).obj F) (Category.id_comp a.unop))
    have h := congrArg (fun e => e.hom.app F) (directImageCompIso_comp_id R a.unop)
    change (directImageCompIso R a.unop (𝟙 j.unop)).inv.app F ≫
      ((directImage R a.unop).map ((directImageIdIso R j.unop).hom.app F) ≫ 𝟙 _) = _ at h
    simpa only [Category.comp_id, eqToIso.hom, eqToHom_app] using h
  assoc := by
    intro i j k l a b c F
    change (directImageCompIso R (b.unop ≫ a.unop) c.unop).inv.app F ≫
      (directImageCompIso R a.unop b.unop).inv.app ((directImage R c.unop).obj F) =
      eqToHom (congrArg (fun f => (directImage R f).obj F)
        (Category.assoc c.unop b.unop a.unop).symm) ≫
      (directImageCompIso R a.unop (c.unop ≫ b.unop)).inv.app F ≫
        (directImage R a.unop).map ((directImageCompIso R b.unop c.unop).inv.app F)
    have h := congrArg (fun e => e.hom.app F)
      (directImageCompIso_inverse_associativity R a.unop b.unop c.unop)
    simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, eqToIso.hom, eqToHom_app, Functor.comp_obj] using h


/-- Native systems over precisely the specified inverse scheme diagram. -/
abbrev diagramAdjunctionData {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) := (schemeAdjunctionData R).reindex X

/-- Reindexing preserves the original image coherence. -/
theorem diagramAdjunctionData_coherent {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) : (diagramAdjunctionData R X).Coherent :=
  InjectiveSystem.AdjunctionData.Coherent.reindex _ X (schemeAdjunctionData_coherent R)

/-- Coefficients and transition maps are native module-valued sheaves. -/
abbrev DiagramCoefficientSystem {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) := InjectiveSystem.System (diagramAdjunctionData R X)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
