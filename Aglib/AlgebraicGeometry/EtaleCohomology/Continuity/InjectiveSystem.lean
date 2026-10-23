/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SystemCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage

/-! # Original étale-image data for injective coefficient systems

The varying-category construction is supplied with the original inverse and
direct images, their actual adjunctions, and the already proved identity and
composition comparisons. Coefficients remain `AbelianSheaf.{u,u+1}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- Original étale images, indexed in the coefficient-transition direction. -/
def schemeAdjunctionData :
    InjectiveSystem.AdjunctionData
      (fun X : Scheme.{u}ᵒᵖ => AbelianSheaf.{u, u + 1} X.unop) where
  left a := inverseImage a.unop
  right a := directImage a.unop
  adj a := inverseImageAdjunction a.unop
  left_preservesMonomorphisms _ := inferInstance
  idIso X := directImageIdIso X.unop
  compIso a b := (directImageCompIso a.unop b.unop).symm

private theorem directImageCompIso_inverse_associativity {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (directImageCompIso (g ≫ f) h).symm ≪≫
        Functor.isoWhiskerLeft (directImage h) (directImageCompIso f g).symm =
      eqToIso (congrArg (fun k : V ⟶ X => directImage k) (Category.assoc h g f).symm) ≪≫
        (directImageCompIso f (h ≫ g)).symm ≪≫
        Functor.isoWhiskerRight (directImageCompIso g h).symm (directImage f) ≪≫
        Functor.associator (directImage h) (directImage g) (directImage f) := by
  apply Iso.symm_bijective.injective
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    Category.assoc, Functor.comp_obj] using (directImageCompIso_assoc_app f g h K).symm

/-- The generic original-comparison laws hold for the actual étale images.
These are supplied by native scheme-image coherence, not new assumptions. -/
theorem schemeAdjunctionData_coherent : schemeAdjunctionData.{u}.Coherent where
  id_comp := by
    intro i j a F
    change (directImageCompIso (𝟙 i.unop) a.unop).inv.app F ≫
      (directImageIdIso i.unop).hom.app ((directImage a.unop).obj F) =
        eqToHom (congrArg (fun f => (directImage f).obj F) (Category.comp_id a.unop))
    have h := congrArg (fun e => e.hom.app F) (directImageCompIso_id_comp a.unop)
    change (directImageCompIso (𝟙 i.unop) a.unop).inv.app F ≫
      ((directImageIdIso i.unop).hom.app ((directImage a.unop).obj F) ≫ 𝟙 _) = _ at h
    simpa only [Category.comp_id, eqToIso.hom, eqToHom_app] using h
  comp_id := by
    intro i j a F
    change (directImageCompIso a.unop (𝟙 j.unop)).inv.app F ≫
      (directImage a.unop).map ((directImageIdIso j.unop).hom.app F) =
        eqToHom (congrArg (fun f => (directImage f).obj F) (Category.id_comp a.unop))
    have h := congrArg (fun e => e.hom.app F) (directImageCompIso_comp_id a.unop)
    change (directImageCompIso a.unop (𝟙 j.unop)).inv.app F ≫
      ((directImage a.unop).map ((directImageIdIso j.unop).hom.app F) ≫ 𝟙 _) = _ at h
    simpa only [Category.comp_id, eqToIso.hom, eqToHom_app] using h
  assoc := by
    intro i j k l a b c F
    change (directImageCompIso (b.unop ≫ a.unop) c.unop).inv.app F ≫
      (directImageCompIso a.unop b.unop).inv.app ((directImage c.unop).obj F) =
      eqToHom (congrArg (fun f => (directImage f).obj F)
        (Category.assoc c.unop b.unop a.unop).symm) ≫
      (directImageCompIso a.unop (c.unop ≫ b.unop)).inv.app F ≫
        (directImage a.unop).map ((directImageCompIso b.unop c.unop).inv.app F)
    have h := congrArg (fun e => e.hom.app F)
      (directImageCompIso_inverse_associativity a.unop b.unop c.unop)
    simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, eqToIso.hom, eqToHom_app, Functor.comp_obj] using h

/-- A system on schemes, written using its original direct-image adjoints. -/
abbrev SchemeCoefficientSystem := InjectiveSystem.System schemeAdjunctionData.{u}

/-- The original scheme-image system has an actual objectwise injective
replacement. Reindexing to a chosen inverse system is a separate construction. -/
def schemeInjectiveReplacement (F : SchemeCoefficientSystem.{u}) : SchemeCoefficientSystem.{u} :=
  InjectiveSystem.replacement schemeAdjunctionData schemeAdjunctionData_coherent F

/-- The compatible embedding is the product construction, with no replacement
of the original étale-image comparisons. -/
def schemeInjectiveEmbedding (F : SchemeCoefficientSystem.{u}) :
    InjectiveSystem.System.Hom schemeAdjunctionData F (schemeInjectiveReplacement F) :=
  InjectiveSystem.replacementEmbedding schemeAdjunctionData schemeAdjunctionData_coherent F

instance schemeInjectiveReplacement_injective (F : SchemeCoefficientSystem.{u})
    (X : Scheme.{u}ᵒᵖ) : Injective ((schemeInjectiveReplacement F).obj X) :=
  InjectiveSystem.replacement_obj_injective _ _ _ _

instance schemeInjectiveEmbedding_mono (F : SchemeCoefficientSystem.{u})
    (X : Scheme.{u}ᵒᵖ) : Mono ((schemeInjectiveEmbedding F).app X) :=
  InjectiveSystem.replacementEmbedding_mono _ _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
