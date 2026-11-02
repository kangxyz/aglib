/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients

/-! # Top-identity normalization for the cone coefficient diagram -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma inverseImageSquareIso_top_id {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : X ⟶ T) (g : T ⟶ S) (e : p ≫ g = f) :
    (Functor.rightUnitor (inverseImage f)).symm ≪≫
        Functor.isoWhiskerLeft (inverseImage f) (inverseImageId X).symm ≪≫
        (inverseImageSquareIso f p g (𝟙 X) (e.trans (Category.id_comp f).symm)).symm =
      pullbackTriangleIso f g p e := by
  have hu := congrArg Iso.symm (inverseImageComp_comp_id f)
  have ht := congrArg
    (fun z : inverseImage f ≅ inverseImage (𝟙 X ≫ f) =>
      z ≪≫ (eqToIso (congrArg (fun k : X ⟶ S => inverseImage k)
        (e.trans (Category.id_comp f).symm))).symm ≪≫ inverseImageComp g p) hu
  apply Iso.ext
  have hth := congrArg Iso.hom ht
  simpa only [inverseImageSquareIso, pullbackTriangleIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Category.assoc, eqToIso.hom, eqToIso.inv, eqToHom_trans_assoc] using hth

lemma squareCoefficientMap_top_id {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : X ⟶ T) (g : T ⟶ S) (e : p ≫ g = f)
    {F : AbelianSheaf.{u, u + 1} S} {G : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage g).obj F ⟶ G) :
    (inverseImageId X).inv.app ((inverseImage f).obj F) ≫
      squareCoefficientMap f p g (𝟙 X) (e.trans (Category.id_comp f).symm) φ =
        triangleCoefficientMap g f p e φ := by
  have hc := congrArg (fun z => z.hom.app F) (inverseImageSquareIso_top_id f p g e)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hc
  let m : (inverseImage f).obj F ⟶ (inverseImage p).obj ((inverseImage g).obj F) :=
    (inverseImageId X).inv.app ((inverseImage f).obj F) ≫
      (inverseImageSquareIso f p g (𝟙 X) (e.trans (Category.id_comp f).symm)).inv.app F
  change 𝟙 ((inverseImage f).obj F) ≫ m = _ at hc
  have hc' := (Category.id_comp m).symm.trans hc
  have ht := congrArg
    (fun k : (inverseImage f).obj F ⟶ (inverseImage p).obj ((inverseImage g).obj F) =>
      k ≫ (inverseImage p).map φ) hc'
  simpa only [squareCoefficientMap, triangleCoefficientMap, Category.assoc, m] using ht

private lemma globalSectionsPullback_id_inverse (X : Scheme.{u})
    (F : AbelianSheaf.{u, u + 1} X) :
    globalSectionsPullback (𝟙 X) F = (globalSections X).map ((inverseImageId X).inv.app F) := by
  let e := (globalSections X).mapIso ((inverseImageId X).app F)
  have h : globalSectionsPullback (𝟙 X) F = 𝟙 ((globalSections X).obj F) ≫ e.inv :=
    e.eq_comp_inv.mpr (globalSectionsPullback_id X F)
  exact h.trans (Category.id_comp e.inv)

lemma squareSectionsMap_top_id {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : X ⟶ T) (g : T ⟶ S) (e : p ≫ g = f)
    {F : AbelianSheaf.{u, u + 1} S} {G : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f p g (𝟙 X) (e.trans (Category.id_comp f).symm) φ =
      (globalSections X).map (triangleCoefficientMap g f p e φ) := by
  let q := squareCoefficientMap f p g (𝟙 X) (e.trans (Category.id_comp f).symm) φ
  have h₁ := congrArg
    (fun k : (globalSections X).obj ((inverseImage f).obj F) ⟶
        (globalSections X).obj ((inverseImage (𝟙 X)).obj ((inverseImage f).obj F)) =>
      k ≫ (globalSections X).map q)
    (globalSectionsPullback_id_inverse X ((inverseImage f).obj F))
  have h₂ := ((globalSections X).map_comp
    ((inverseImageId X).inv.app ((inverseImage f).obj F)) q).symm
  have h₃ := congrArg
    (fun k : (inverseImage f).obj F ⟶ (inverseImage p).obj G =>
      (globalSections X).map k) (squareCoefficientMap_top_id f p g e φ)
  exact h₁.trans (h₂.trans h₃)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
