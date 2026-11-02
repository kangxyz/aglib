/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.RepresentedDiagram.Hom

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

/-- The original constant-integer Hom/global-sections additive equivalence. -/
def sectionIntegerHomEquiv (X : Scheme.{u}) (F : AbelianSheaf.{u, u + 1} X) :
    ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) ≃+ (globalSections X).obj F :=
  ((constantAdjunction X).homAddEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj F))

lemma sectionIntegerHomEquiv_apply (X : Scheme.{u}) (F : AbelianSheaf.{u, u + 1} X)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    sectionIntegerHomEquiv X F a =
      AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj F)
        ((constantAdjunction X).homEquiv _ F a) := rfl

/-- Coefficient naturality uses the same original adjunction and section values. -/
lemma sectionIntegerHomEquiv_naturality {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (q : F ⟶ G)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    sectionIntegerHomEquiv X G (a ≫ q) =
      (globalSections X).map q (sectionIntegerHomEquiv X F a) := by
  simp only [sectionIntegerHomEquiv_apply]
  rw [(constantAdjunction X).homEquiv_naturality_right]
  rfl

/-- The literal original section transfer has the original constant-source Hom value. -/
lemma sectionTransfer_homEquiv {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    sectionIntegerHomEquiv Y G
        (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage f).map a ≫ φ) =
      sectionTransfer f φ (sectionIntegerHomEquiv X F a) := by
  let A : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have h : (constantAdjunction Y).homEquiv A G
      (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a ≫ φ) =
      (constantAdjunction X).homEquiv A F a ≫ sectionTransfer f φ := by
    rw [← Category.assoc, (constantAdjunction Y).homEquiv_naturality_right,
      constantTransport_homEquiv]
    simp only [sectionTransfer, Category.assoc]
  exact congrArg
    (fun q : A ⟶ (globalSections Y).obj G =>
      AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections Y).obj G) q) h

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

local instance sectionDiagramLeftAdditive :
    ∀ {i j : I} (a : i ⟶ j), ((diagramAdjunctionData X).left a).Additive := by
  intro i j a
  change (inverseImage (X.map a).unop).Additive
  infer_instance

local instance sectionDiagramIntegerCartesian :
    ∀ {i j : I} (a : i ⟶ j),
      IsIso ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) := by
  intro i j a
  exact diagramIntegerSystem_leftMap_isIso X a

/-- The original sections at a stage, without an identity-twisted coefficient. -/
abbrev diagramSectionsObj (i : I) : AddCommGrpCat.{u + 1} :=
  (globalSections (X.obj i).unop).obj (F.obj i)

/-- The actual transition prescribed by the compatible coefficient system. -/
def diagramSectionsMap {i j : I} (a : i ⟶ j) :
    diagramSectionsObj X F i ⟶ diagramSectionsObj X F j :=
  sectionTransfer (X.map a).unop (diagramInverseTransition X F a)

/-- The same integer-source equivalence, typed at the actual representing system. -/
abbrev diagramSectionsHomEquiv (i : I) :
    ((diagramIntegerSystem X).obj i ⟶ F.obj i) ≃+ diagramSectionsObj X F i := by
  dsimp only [diagramIntegerSystem, InjectiveSystem.System.ofLeft]
  exact sectionIntegerHomEquiv (X.obj i).unop (F.obj i)

/-- The actual original map, after the same representing equivalence, is plain Hom transport. -/
lemma diagramSectionsMap_homEquiv {i j : I} (a : i ⟶ j)
    (f : (diagramIntegerSystem X).obj i ⟶ F.obj i) :
    diagramSectionsHomEquiv X F j
        (InjectiveSystem.representedHomMap (diagramAdjunctionData X)
          (diagramIntegerSystem X) F a f) =
      diagramSectionsMap X F a (diagramSectionsHomEquiv X F i f) := by
  let sourceTransportIso :
      IsIso ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) :=
    diagramIntegerSystem_leftMap_isIso X a
  have hcomp : (diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a ≫
      ((inverseImageConstantIso (X.map a).unop).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv =
        𝟙 (((diagramAdjunctionData X).left a).obj ((diagramIntegerSystem X).obj i)) :=
    (congrArg
      (fun q : ((diagramAdjunctionData X).left a).obj ((diagramIntegerSystem X).obj i) ⟶
          (diagramIntegerSystem X).obj j =>
        q ≫ ((inverseImageConstantIso (X.map a).unop).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
      (diagramIntegerSystem_leftMap X a)).trans
        (Iso.hom_inv_id ((inverseImageConstantIso (X.map a).unop).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  have hinv : inv ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a)
      (I := sourceTransportIso) =
        ((inverseImageConstantIso (X.map a).unop).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv :=
    @IsIso.inv_eq_of_hom_inv_id _ _ _ _ _ sourceTransportIso _ hcomp
  have hHom : InjectiveSystem.representedHomMap (diagramAdjunctionData X)
      (diagramIntegerSystem X) F a f =
        ((inverseImageConstantIso (X.map a).unop).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (inverseImage (X.map a).unop).map f ≫ diagramInverseTransition X F a :=
    congrArg
      (fun q : (diagramIntegerSystem X).obj j ⟶
          ((diagramAdjunctionData X).left a).obj ((diagramIntegerSystem X).obj i) =>
        q ≫ (inverseImage (X.map a).unop).map f ≫ diagramInverseTransition X F a) hinv
  exact (congrArg (diagramSectionsHomEquiv X F j) hHom).trans
    (sectionTransfer_homEquiv (X := (X.obj i).unop) (Y := (X.obj j).unop)
      (F := F.obj i) (G := F.obj j) (X.map a).unop (diagramInverseTransition X F a) f)

lemma diagramSectionsMap_id (i : I) : diagramSectionsMap X F (𝟙 i) = 𝟙 _ :=
  InjectiveSystem.representedHomValuesMap_id (diagramAdjunctionData X)
    (diagramIntegerSystem X) F (diagramSectionsObj X F) (diagramSectionsMap X F)
    (diagramSectionsHomEquiv X F) (diagramSectionsMap_homEquiv X F) i

lemma diagramSectionsMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramSectionsMap X F (a ≫ b) = diagramSectionsMap X F a ≫ diagramSectionsMap X F b :=
  InjectiveSystem.representedHomValuesMap_comp (diagramAdjunctionData X)
    (diagramIntegerSystem X) F (diagramSectionsObj X F) (diagramSectionsMap X F)
    (diagramSectionsHomEquiv X F) (diagramSectionsMap_homEquiv X F) a b

/-- The one original section diagram: its original maps with the shared plain-Hom laws. -/
abbrev diagramSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  InjectiveSystem.representedHomValuesFunctor (diagramAdjunctionData X)
    (diagramIntegerSystem X) F (diagramSectionsObj X F) (diagramSectionsMap X F)
    (diagramSectionsHomEquiv X F) (diagramSectionsMap_homEquiv X F)

/-- The whole actual section map is retained, not merely its source and target. -/
lemma diagramSectionsFunctor_map {i j : I} (a : i ⟶ j) :
    (diagramSectionsFunctor X F).map a =
      sectionTransfer (X.map a).unop (diagramInverseTransition X F a) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
