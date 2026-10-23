/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Original section transitions of a compatible coefficient system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Original pullback of sections, followed by the given inverse-image coefficient map. -/
def sectionTransfer {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) : (globalSections X).obj F ⟶ (globalSections Y).obj G :=
  globalSectionsPullback f F ≫ (globalSections Y).map φ

lemma sectionTransfer_transport {X Y : Scheme.{u}} (f f' : Y ⟶ X) (e : f' = f)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) :
    sectionTransfer f' (eqToHom (congrArg (fun g : Y ⟶ X => (inverseImage g).obj F) e) ≫ φ) =
      sectionTransfer f φ := by
  subst f'
  simp only [eqToHom_refl, Category.id_comp]

lemma sectionTransfer_id (X : Scheme.{u}) (F : AbelianSheaf.{u, u + 1} X) :
    sectionTransfer (𝟙 X) ((inverseImageId X).hom.app F) = 𝟙 _ :=
  globalSectionsPullback_id X F

lemma sectionTransfer_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) :
    sectionTransfer f φ ≫ sectionTransfer g ψ =
      sectionTransfer (g ≫ f) ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) := by
  dsimp only [sectionTransfer]
  simp only [Category.assoc]
  rw [globalSectionsPullback_naturality_assoc, ← globalSectionsPullback_comp_assoc]
  simp only [Functor.map_comp]

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- The original sections at a stage, without an identity-twisted coefficient. -/
abbrev diagramSectionsObj (i : I) : AddCommGrpCat.{u + 1} :=
  (globalSections (X.obj i).unop).obj (F.obj i)

/-- The actual transition prescribed by the compatible coefficient system. -/
def diagramSectionsMap {i j : I} (a : i ⟶ j) :
    diagramSectionsObj X F i ⟶ diagramSectionsObj X F j :=
  sectionTransfer (X.map a).unop (diagramInverseTransition X F a)

lemma diagramSectionsMap_id (i : I) : diagramSectionsMap X F (𝟙 i) = 𝟙 _ := by
  dsimp only [diagramSectionsMap]
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  exact (sectionTransfer_transport (𝟙 _) (X.map (𝟙 i)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i))
    ((inverseImageId (X.obj i).unop).hom.app (F.obj i))).trans (sectionTransfer_id _ _)

lemma diagramSectionsMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramSectionsMap X F (a ≫ b) = diagramSectionsMap X F a ≫ diagramSectionsMap X F b := by
  dsimp only [diagramSectionsMap]
  rw [diagramInverseTransition_comp]
  simp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  let φ : (inverseImage ((X.map b).unop ≫ (X.map a).unop)).obj (F.obj i) ⟶ F.obj k :=
    (inverseImageComp (X.map a).unop (X.map b).unop).hom.app (F.obj i) ≫
      (inverseImage (X.map b).unop).map (diagramInverseTransition X F a) ≫
        diagramInverseTransition X F b
  have ht := sectionTransfer_transport ((X.map b).unop ≫ (X.map a).unop)
    (X.map (a ≫ b)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj k => f.unop) (X.map_comp a b)) φ
  exact ht.trans (sectionTransfer_comp (X.map a).unop (X.map b).unop
    (diagramInverseTransition X F a) (diagramInverseTransition X F b)).symm

/-- The native source diagram for compatible-system degree-zero continuity. -/
def diagramSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} where
  obj := diagramSectionsObj X F
  map := diagramSectionsMap X F
  map_id := diagramSectionsMap_id X F
  map_comp := diagramSectionsMap_comp X F

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
