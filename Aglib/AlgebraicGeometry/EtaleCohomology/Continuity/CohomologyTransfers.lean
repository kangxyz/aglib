/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.RepresentedDiagram

/-! # Original cohomology transport with compatible coefficients

The Ext universe is independent of the scheme and coefficient universes.
All maps below are the original cohomological pullback followed by the original
coefficient map; no continuity or invertibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge

section IntegerSource

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)

/-- The exact native constant-integer object representing stage sheaf cohomology. -/
abbrev diagramIntegerObj (i : I) : AbelianSheaf.{u, u + 1} (X.obj i).unop :=
  (constantSheaf (Scheme.smallEtaleTopology (X.obj i).unop) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The original inverse-image constant transport on the actual integer source. -/
def diagramIntegerLeftMap {i j : I} (a : i ⟶ j) :
    (inverseImage (X.map a).unop).obj (diagramIntegerObj X i) ⟶ diagramIntegerObj X j :=
  (inverseImageConstantIso (X.map a).unop).hom.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private lemma integerTransport_eq {S T : Scheme.{u}} (f f' : T ⟶ S) (h : f' = f) :
    eqToHom (congrArg (fun k : T ⟶ S => (inverseImage k).obj
      ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) h) ≫
      (inverseImageConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
        (inverseImageConstantIso f').hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  subst f'
  simp only [eqToHom_refl, Category.id_comp]

lemma diagramIntegerLeftMap_id (i : I) :
    diagramIntegerLeftMap X (𝟙 i) =
      ((diagramAdjunctionData X).leftIdIso i).hom.app (diagramIntegerObj X i) := by
  rw [leftIdIso_eq_diagramInverseImageId]
  simp only [diagramIntegerLeftMap, diagramInverseImageId, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rw [inverseImageId_constant]
  exact (integerTransport_eq (𝟙 (X.obj i).unop) (X.map (𝟙 i)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i))).symm

lemma diagramIntegerLeftMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramIntegerLeftMap X (a ≫ b) =
      ((diagramAdjunctionData X).leftCompIso a b).hom.app (diagramIntegerObj X i) ≫
        (inverseImage (X.map b).unop).map (diagramIntegerLeftMap X a) ≫
          diagramIntegerLeftMap X b := by
  rw [leftCompIso_eq_diagramInverseImageComp]
  change (inverseImageConstantIso (X.map (a ≫ b)).unop).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (diagramInverseImageComp X a b).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology (X.obj i).unop)
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (inverseImage (X.map b).unop).map
        ((inverseImageConstantIso (X.map a).unop).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
        (inverseImageConstantIso (X.map b).unop).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  simp only [diagramInverseImageComp, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc]
  rw [inverseImageComp_constant]
  exact (integerTransport_eq ((X.map b).unop ≫ (X.map a).unop) (X.map (a ≫ b)).unop
    (congrArg (fun f : X.obj i ⟶ X.obj k => f.unop) (X.map_comp a b))).symm

/-- The actual cartesian integer-source system, with its original adjunction mates. -/
def diagramIntegerSystem : DiagramCoefficientSystem X :=
  InjectiveSystem.System.ofLeft (diagramAdjunctionData X) (diagramIntegerObj X)
    (diagramIntegerLeftMap X) (diagramIntegerLeftMap_id X) (diagramIntegerLeftMap_comp X)

/-- The constructed source retains the original constant-integer transport exactly. -/
@[simp]
lemma diagramIntegerSystem_leftMap {i j : I} (a : i ⟶ j) :
    (diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a =
      (inverseImageConstantIso (X.map a).unop).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  InjectiveSystem.System.ofLeft_leftMap (diagramAdjunctionData X) (diagramIntegerObj X)
    (diagramIntegerLeftMap X) (diagramIntegerLeftMap_id X) (diagramIntegerLeftMap_comp X) a

instance diagramIntegerSystem_leftMap_isIso {i j : I} (a : i ⟶ j) :
    IsIso ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) := by
  rw [diagramIntegerSystem_leftMap]
  exact ((inverseImageConstantIso (X.map a).unop).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).isIso_hom

end IntegerSource

variable {X Y Z : Scheme.{u}}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]

/-- Original pullback followed by the given inverse-image coefficient morphism. -/
def cohomologyTransfer (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{e} F n) ⟶ AddCommGrpCat.of (Sheaf.H.{e} G n) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map φ n).comp (cohomologyPullback f F n))

lemma cohomologyTransfer_transport (f f' : Y ⟶ X) (h : f' = f)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    cohomologyTransfer f'
        (eqToHom (congrArg (fun k : Y ⟶ X => (inverseImage k).obj F) h) ≫ φ) n =
      cohomologyTransfer f φ n := by
  subst f'
  simp only [eqToHom_refl, Category.id_comp]

lemma cohomologyTransfer_id (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    cohomologyTransfer (𝟙 X) ((inverseImageId X).hom.app F) n = 𝟙 _ := by
  ext x
  exact cohomologyPullback_id X F n x

lemma cohomologyTransfer_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) (n : ℕ) :
    cohomologyTransfer f φ n ≫ cohomologyTransfer g ψ n =
      cohomologyTransfer (g ≫ f)
        ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) n := by
  ext x
  change Sheaf.H.map ψ n (cohomologyPullback g G n
    (Sheaf.H.map φ n (cohomologyPullback f F n x))) =
      Sheaf.H.map ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) n
        (cohomologyPullback (g ≫ f) F n x)
  simp only [Sheaf.H.map_comp_apply]
  rw [cohomologyPullback_coefficientMap, cohomologyPullback_comp]

lemma cohomologyTransfer_naturality (f : Y ⟶ X)
    {F F' : AbelianSheaf.{u, u + 1} X} {G G' : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage f).obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : (inverseImage f).map a ≫ ψ = φ ≫ b) (n : ℕ) :
    cohomologyTransfer f φ n ≫ AddCommGrpCat.ofHom (Sheaf.H.map b n) =
      AddCommGrpCat.ofHom (Sheaf.H.map a n) ≫ cohomologyTransfer f ψ n := by
  ext x
  change Sheaf.H.map b n (Sheaf.H.map φ n (cohomologyPullback f F n x)) =
    Sheaf.H.map ψ n (cohomologyPullback f F' n (Sheaf.H.map a n x))
  rw [cohomologyPullback_coefficientMap, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply, h]

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
