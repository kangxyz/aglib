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
  simpa only [schemeSquareIso_eq_inverseImageSquareIso, schemeLeftIdIso_eq_inverseImageId,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    unop_id, Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareIso_top_id schemeAdjunctionData_coherent
      f.op p.op g.op (congrArg Quiver.Hom.op e)

lemma squareCoefficientMap_top_id {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : X ⟶ T) (g : T ⟶ S) (e : p ≫ g = f)
    {F : AbelianSheaf.{u, u + 1} S} {G : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage g).obj F ⟶ G) :
    (inverseImageId X).inv.app ((inverseImage f).obj F) ≫
      squareCoefficientMap f p g (𝟙 X) (e.trans (Category.id_comp f).symm) φ =
        triangleCoefficientMap g f p e φ := by
  exact Adjunction.CoefficientSquares.coefficient_top_id (inverseImageId X)
    (inverseImageSquareIso f p g (𝟙 X) (e.trans (Category.id_comp f).symm))
    (pullbackTriangleIso f g p e) (inverseImageSquareIso_top_id f p g e) φ

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
