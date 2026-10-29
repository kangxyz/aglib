/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareSections

/-! # Identity-square normalization for original relative section maps -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- Normalize the whole original inverse-image square before evaluating coefficients. -/
lemma inverseImageSquareIso_base_id {X S Y : Scheme.{u}}
    (f : X ⟶ S) (p : Y ⟶ S) (h : Y ⟶ X) (e : h ≫ f = p) :
    (inverseImageSquareIso f p (𝟙 S) h ((Category.comp_id p).trans e.symm)).symm ≪≫
        Functor.isoWhiskerRight (inverseImageId S) (inverseImage p) ≪≫
        Functor.leftUnitor (inverseImage p) = (pullbackTriangleIso p f h e).symm := by
  have hu := inverseImageComp_id_comp p
  have ht := congrArg
    (fun z : inverseImage (p ≫ 𝟙 S) ≅ inverseImage p =>
      (inverseImageComp f h).symm ≪≫
        (eqToIso (congrArg (fun k : Y ⟶ S => inverseImage k)
          ((Category.comp_id p).trans e.symm))).symm ≪≫ z) hu
  apply Iso.ext
  have hth := congrArg Iso.hom ht
  simpa only [inverseImageSquareIso, pullbackTriangleIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc, eqToIso.hom, eqToIso.inv, eqToHom_trans]
    using hth

/-- A base-identity square has exactly the original triangle coefficient comparison. -/
lemma squareCoefficientMap_base_id {X S Y : Scheme.{u}}
    (f : X ⟶ S) (p : Y ⟶ S) (h : Y ⟶ X) (e : h ≫ f = p)
    (F : AbelianSheaf.{u, u + 1} S) :
    squareCoefficientMap f p (𝟙 S) h ((Category.comp_id p).trans e.symm)
      ((inverseImageId S).hom.app F) = (pullbackTriangleIso p f h e).inv.app F := by
  have hc := congrArg (fun z => z.hom.app F) (inverseImageSquareIso_base_id f p h e)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hc
  let m : (inverseImage p).obj ((inverseImage (𝟙 S)).obj F) ⟶
      (inverseImage p).obj F := (inverseImage p).map ((inverseImageId S).hom.app F)
  change (inverseImageSquareIso f p (𝟙 S) h _).inv.app F ≫ m ≫
    𝟙 ((inverseImage p).obj F) = _ at hc
  exact (congrArg
    (fun k : (inverseImage p).obj ((inverseImage (𝟙 S)).obj F) ⟶
        (inverseImage p).obj F =>
      (inverseImageSquareIso f p (𝟙 S) h ((Category.comp_id p).trans e.symm)).inv.app F ≫ k)
    (Category.comp_id m)).symm.trans hc

/-- The base-identity section square is the original relative pullback on sections. -/
lemma squareSectionsMap_base_id {S : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} S)
    {Y Z : Over S} (a : Y ⟶ Z) :
    squareSectionsMap Z.hom Y.hom (𝟙 S) a.left
      ((Category.comp_id Y.hom).trans a.w.symm) ((inverseImageId S).hom.app F) =
        pullbackSectionsMap F a := by
  exact congrArg
    (fun k : (inverseImage a.left).obj ((inverseImage Z.hom).obj F) ⟶
        (inverseImage Y.hom).obj F =>
      globalSectionsPullback a.left ((inverseImage Z.hom).obj F) ≫
        (globalSections Y.left).map k)
    (squareCoefficientMap_base_id Z.hom Y.hom a.left a.w F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
