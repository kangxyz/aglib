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
  simpa only [schemeSquareIso_eq_inverseImageSquareIso, schemeLeftIdIso_eq_inverseImageId,
    schemeTriangleIso_eq_pullbackTriangleIso, schemeLeft_eq_inverseImage,
    unop_id, Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareIso_base_id schemeAdjunctionData_coherent
      f.op p.op h.op (congrArg Quiver.Hom.op e)

/-- A base-identity square has exactly the original triangle coefficient comparison. -/
lemma squareCoefficientMap_base_id {X S Y : Scheme.{u}}
    (f : X ⟶ S) (p : Y ⟶ S) (h : Y ⟶ X) (e : h ≫ f = p)
    (F : AbelianSheaf.{u, u + 1} S) :
    squareCoefficientMap f p (𝟙 S) h ((Category.comp_id p).trans e.symm)
      ((inverseImageId S).hom.app F) = (pullbackTriangleIso p f h e).inv.app F := by
  exact Adjunction.CoefficientSquares.coefficient_base_id (inverseImageId S)
    (inverseImageSquareIso f p (𝟙 S) h ((Category.comp_id p).trans e.symm))
    (pullbackTriangleIso p f h e) (inverseImageSquareIso_base_id f p h e) F

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
