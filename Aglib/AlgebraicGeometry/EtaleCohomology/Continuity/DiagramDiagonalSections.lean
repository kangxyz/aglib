/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSectionTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramArrowSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SchemeSystemColimits

/-! # Identification of the diagonal with the original compatible section system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

lemma squareCoefficientMap_vertical_id {X Y : Scheme.{u}} (g : Y ⟶ X)
    (e : 𝟙 Y ≫ g = g ≫ 𝟙 X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareCoefficientMap (𝟙 X) (𝟙 Y) g g e φ ≫ (inverseImageId Y).hom.app G =
      (inverseImage g).map ((inverseImageId X).hom.app F) ≫ φ := by
  have hs := inverseImageSquareIso_vId g e F
  change (inverseImageId Y).hom.app ((inverseImage g).obj F) =
    (inverseImageSquareIso (𝟙 X) (𝟙 Y) g g e).hom.app F ≫
      (inverseImage g).map ((inverseImageId X).hom.app F) at hs
  have hi := congrArg
    (fun k => (inverseImageSquareIso (𝟙 X) (𝟙 Y) g g e).inv.app F ≫ k) hs
  have hc : (inverseImageSquareIso (𝟙 X) (𝟙 Y) g g e).inv.app F ≫
      (inverseImageId Y).hom.app ((inverseImage g).obj F) =
        (inverseImage g).map ((inverseImageId X).hom.app F) := by
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using hi
  have hn := (inverseImageId Y).hom.naturality φ
  change (inverseImage (𝟙 Y)).map φ ≫ (inverseImageId Y).hom.app G =
    (inverseImageId Y).hom.app ((inverseImage g).obj F) ≫ φ at hn
  dsimp only [squareCoefficientMap]
  rw [Category.assoc, hn, ← Category.assoc, hc]

lemma squareSectionsMap_vertical_id {X Y : Scheme.{u}} (g : Y ⟶ X)
    (e : 𝟙 Y ≫ g = g ≫ 𝟙 X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap (𝟙 X) (𝟙 Y) g g e φ ≫
        (globalSections Y).map ((inverseImageId Y).hom.app G) =
      (globalSections X).map ((inverseImageId X).hom.app F) ≫ sectionTransfer g φ := by
  dsimp only [squareSectionsMap, sectionTransfer]
  simp only [Category.assoc]
  rw [← Functor.map_comp, squareCoefficientMap_vertical_id]
  simp only [Functor.map_comp]
  rw [← globalSectionsPullback_naturality_assoc]

lemma squareSectionsMap_vertical_identity_transport {X Y : Scheme.{u}}
    (f₀ : X ⟶ X) (f₁ : Y ⟶ Y) (e₀ : f₀ = 𝟙 X) (e₁ : f₁ = 𝟙 Y)
    (g : Y ⟶ X) (e : f₁ ≫ g = g ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f₀ f₁ g g e φ ≫
        (globalSections Y).map (eqToHom (congrArg (fun f : Y ⟶ Y => (inverseImage f).obj G) e₁) ≫
          (inverseImageId Y).hom.app G) =
      (globalSections X).map (eqToHom (congrArg (fun f : X ⟶ X => (inverseImage f).obj F) e₀) ≫
        (inverseImageId X).hom.app F) ≫ sectionTransfer g φ := by
  subst f₀
  subst f₁
  simpa only [eqToHom_refl, Category.id_comp] using squareSectionsMap_vertical_id g e φ

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

lemma diagonalSectionsNaturality {i j : I} (a : i ⟶ j) :
    arrowSectionsMap X F (SchemeSystemColimits.diagonal.map a) ≫
        (globalSections (X.obj j).unop).map ((diagramInverseImageId X j).hom.app (F.obj j)) =
      (globalSections (X.obj i).unop).map ((diagramInverseImageId X i).hom.app (F.obj i)) ≫
        diagramSectionsMap X F a := by
  dsimp only [arrowSectionsMap, diagramSectionsMap]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  exact squareSectionsMap_vertical_identity_transport
    (X.map (𝟙 i)).unop (X.map (𝟙 j)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i))
    (congrArg (fun f : X.obj j ⟶ X.obj j => f.unop) (X.map_id j))
    (X.map a).unop (arrowSectionsSquare X ((SchemeSystemColimits.diagonal).map a))
    (diagramInverseTransition X F a)

/-- The original identity comparison at each stage. -/
def diagonalSectionsIso :
    SchemeSystemColimits.diagonal ⋙ arrowSectionsFunctor X F ≅ diagramSectionsFunctor X F :=
  NatIso.ofComponents
    (fun i => (globalSections (X.obj i).unop).mapIso ((diagramInverseImageId X i).app (F.obj i)))
    (fun a => diagonalSectionsNaturality X F a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
