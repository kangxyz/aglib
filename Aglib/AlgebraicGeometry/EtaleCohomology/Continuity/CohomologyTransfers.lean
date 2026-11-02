/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CohomologyCocone
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.RepresentedDiagram

/-! # Original cohomology transport with compatible coefficients

The Ext universe is independent of the scheme and coefficient universes.
All maps below are the original cohomological pullback followed by the original
coefficient map; no continuity or invertibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
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

/-- Select the original global constant-integer source once, with its actual
inverse-image comparison and the already proved ordinary constant laws. -/
def schemeIntegerSystem : InjectiveSystem.System schemeAdjunctionData :=
  InjectiveSystem.System.ofLeft schemeAdjunctionData
    (fun S => (constantSheaf (Scheme.smallEtaleTopology S.unop) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (fun a => (inverseImageConstantIso a.unop).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (fun S => by
      rw [schemeLeftIdIso_eq_inverseImageId]
      exact (inverseImageId_constant S.unop (AddCommGrpCat.of (ULift.{u + 1} ℤ))).symm)
    (fun a b => by
      rw [schemeLeftCompIso_eq_inverseImageComp]
      exact (inverseImageComp_constant a.unop b.unop
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).symm)

/-- The selected source is the original constant-integer sheaf itself. -/
lemma schemeIntegerSystem_obj (S : Scheme.{u}ᵒᵖ) :
    schemeIntegerSystem.obj S =
      (constantSheaf (Scheme.smallEtaleTopology S.unop) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := rfl

/-- The selected global source retains the whole original constant transport. -/
lemma schemeIntegerSystem_leftMap {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T) :
    schemeIntegerSystem.leftMap schemeAdjunctionData a =
      (inverseImageConstantIso a.unop).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  dsimp only [schemeIntegerSystem]
  apply InjectiveSystem.System.ofLeft_leftMap

instance schemeIntegerSystem_leftMap_isIso {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T) :
    IsIso (schemeIntegerSystem.leftMap schemeAdjunctionData a) := by
  rw [schemeIntegerSystem_leftMap]
  infer_instance

/-- The inverse source arrow is the same original inverse constant comparison. -/
lemma schemeIntegerSystem_leftMap_inv {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T) :
    inv (schemeIntegerSystem.leftMap schemeAdjunctionData a) =
      (inverseImageConstantIso a.unop).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [schemeIntegerSystem_leftMap]
  exact Iso.hom_inv_id_app _ _

lemma diagramIntegerLeftMap_id (i : I) :
    diagramIntegerLeftMap X (𝟙 i) =
      ((diagramAdjunctionData X).leftIdIso i).hom.app (diagramIntegerObj X i) := by
  dsimp only [diagramIntegerLeftMap]
  rw [← schemeIntegerSystem_leftMap (X.map (𝟙 i))]
  change (schemeIntegerSystem.reindex schemeAdjunctionData X).leftMap
      (diagramAdjunctionData X) (𝟙 i) =
    ((diagramAdjunctionData X).leftIdIso i).hom.app
      ((schemeIntegerSystem.reindex schemeAdjunctionData X).obj i)
  exact InjectiveSystem.System.leftMap_id (diagramAdjunctionData X)
    (schemeIntegerSystem.reindex schemeAdjunctionData X) i

lemma diagramIntegerLeftMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramIntegerLeftMap X (a ≫ b) =
      ((diagramAdjunctionData X).leftCompIso a b).hom.app (diagramIntegerObj X i) ≫
        (inverseImage (X.map b).unop).map (diagramIntegerLeftMap X a) ≫
          diagramIntegerLeftMap X b := by
  dsimp only [diagramIntegerLeftMap]
  rw [← schemeIntegerSystem_leftMap (X.map (a ≫ b)),
    ← schemeIntegerSystem_leftMap (X.map a), ← schemeIntegerSystem_leftMap (X.map b)]
  change (schemeIntegerSystem.reindex schemeAdjunctionData X).leftMap
      (diagramAdjunctionData X) (a ≫ b) =
    ((diagramAdjunctionData X).leftCompIso a b).hom.app
        ((schemeIntegerSystem.reindex schemeAdjunctionData X).obj i) ≫
      ((diagramAdjunctionData X).left b).map
        ((schemeIntegerSystem.reindex schemeAdjunctionData X).leftMap (diagramAdjunctionData X) a) ≫
      (schemeIntegerSystem.reindex schemeAdjunctionData X).leftMap (diagramAdjunctionData X) b
  exact InjectiveSystem.System.leftMap_comp (diagramAdjunctionData X)
    (schemeIntegerSystem.reindex schemeAdjunctionData X) a b

/-- The actual cartesian integer-source system, with its original adjunction mates. -/
def diagramIntegerSystem : DiagramCoefficientSystem X :=
  schemeIntegerSystem.reindex schemeAdjunctionData X

/-- Restriction stores the same original adjunction mate as the original source system. -/
lemma diagramIntegerSystem_map {i j : I} (a : i ⟶ j) :
    (diagramIntegerSystem X).map a =
      (inverseImageAdjunction (X.map a).unop).homEquiv _ _ (diagramIntegerLeftMap X a) := rfl

/-- The constructed source retains the original constant-integer transport exactly. -/
@[simp]
lemma diagramIntegerSystem_leftMap {i j : I} (a : i ⟶ j) :
    (diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a =
      (inverseImageConstantIso (X.map a).unop).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (InjectiveSystem.System.reindex_leftMap schemeAdjunctionData X schemeIntegerSystem a).trans
    (schemeIntegerSystem_leftMap (X.map a))

instance diagramIntegerSystem_leftMap_isIso {i j : I} (a : i ⟶ j) :
    IsIso ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) := by
  rw [diagramIntegerSystem_leftMap]
  exact ((inverseImageConstantIso (X.map a).unop).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).isIso_hom

end IntegerSource

local instance schemeTransferLeftAdditive :
    ∀ {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T), (schemeAdjunctionData.left a).Additive := by
  intro S T a
  change (inverseImage a.unop).Additive
  infer_instance

local instance schemeTransferLeftLimits :
    ∀ {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T), PreservesFiniteLimits (schemeAdjunctionData.left a) := by
  intro S T a
  change PreservesFiniteLimits (inverseImage a.unop)
  infer_instance

local instance schemeTransferLeftColimits :
    ∀ {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T), PreservesFiniteColimits (schemeAdjunctionData.left a) := by
  intro S T a
  change PreservesFiniteColimits (inverseImage a.unop)
  infer_instance

local instance schemeTransferSourceCartesian :
    ∀ {S T : Scheme.{u}ᵒᵖ} (a : S ⟶ T),
      IsIso (schemeIntegerSystem.leftMap schemeAdjunctionData a) := by
  intro S T a
  exact schemeIntegerSystem_leftMap_isIso a

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

/-- The whole original native transfer is the single operational raw Ext transfer. -/
lemma cohomologyTransfer_eq_extCoefficientTransfer (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    cohomologyTransfer f φ n =
      AddCommGrpCat.ofHom ((inverseImage f).extCoefficientTransfer
        ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) φ n) := rfl

/-- The single original integer source gives the whole native cohomology transfer. -/
lemma schemeIntegerSystem_extTransfer_eq_cohomologyTransfer
    {S T : Scheme.{u}ᵒᵖ}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} S.unop)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} T.unop)]
    (a : S ⟶ T) {F : AbelianSheaf.{u, u + 1} S.unop}
    {G : AbelianSheaf.{u, u + 1} T.unop} (φ : (inverseImage a.unop).obj F ⟶ G) (n : ℕ) :
    schemeIntegerSystem.extTransfer schemeAdjunctionData a φ n = cohomologyTransfer a.unop φ n := by
  ext x
  change (((schemeAdjunctionData.left a).extPrecompMap
      (inv (schemeIntegerSystem.leftMap schemeAdjunctionData a)) F n x).comp
        (Abelian.Ext.mk₀ φ) (add_zero n)) =
    Sheaf.H.map φ n (cohomologyPullback a.unop F n x)
  rw [schemeIntegerSystem_leftMap_inv]
  rfl

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
  have hs : (inverseImageConstantIso (𝟙 X)).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (inverseImageId X).hom.app
          ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) = 𝟙 _ := by
    rw [inverseImageId_constant]
    exact Iso.inv_hom_id_app _ _
  have h := Functor.extCoefficientTransfer_id (inverseImage (𝟙 X)) (inverseImageId X)
    ((inverseImageConstantIso (𝟙 X)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) hs F n
  ext x
  exact DFunLike.congr_fun h x

lemma cohomologyTransfer_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) (n : ℕ) :
    cohomologyTransfer f φ n ≫ cohomologyTransfer g ψ n =
      cohomologyTransfer (g ≫ f)
        ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) n := by
  have h := Functor.extCoefficientTransfer_comp
    (inverseImage f) (inverseImage g) (inverseImage (g ≫ f)) (inverseImageComp f g)
    ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso (g ≫ f)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageComp_constant_inv f g (AddCommGrpCat.of (ULift.{u + 1} ℤ))) φ ψ n
  ext x
  exact DFunLike.congr_fun h x

lemma cohomologyTransfer_naturality (f : Y ⟶ X)
    {F F' : AbelianSheaf.{u, u + 1} X} {G G' : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage f).obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : (inverseImage f).map a ≫ ψ = φ ≫ b) (n : ℕ) :
    cohomologyTransfer f φ n ≫ AddCommGrpCat.ofHom (Sheaf.H.map b n) =
      AddCommGrpCat.ofHom (Sheaf.H.map a n) ≫ cohomologyTransfer f ψ n := by
  have hn := Functor.extCoefficientTransfer_naturality (inverseImage f)
    ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) φ ψ a b h n
  ext x
  exact DFunLike.congr_fun hn x

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
