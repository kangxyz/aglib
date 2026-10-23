/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCoefficientSystem

/-! # Pulling back a varying coefficient system along an actual diagram map

No cartesian square or continuity assertion is required: the transitions are
formed using the original inverse-image square comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I]
  (X Y : I ⥤ Scheme.{u}ᵒᵖ) (τ : X ⟶ Y) (F : DiagramCoefficientSystem X)

/-- The actual square transition of the coefficient pulled to the second diagram. -/
def diagramPullbackTransition {i j : I} (a : i ⟶ j) :
    (inverseImage (Y.map a).unop).obj ((inverseImage (τ.app i).unop).obj (F.obj i)) ⟶
      (inverseImage (τ.app j).unop).obj (F.obj j) :=
  squareCoefficientMap (τ.app i).unop (τ.app j).unop (X.map a).unop (Y.map a).unop
    (congrArg Quiver.Hom.unop (τ.naturality a)) (diagramInverseTransition X F a)

lemma diagramPullbackTransition_id (i : I) :
    diagramPullbackTransition X Y τ F (𝟙 i) =
      (diagramInverseImageId Y i).hom.app ((inverseImage (τ.app i).unop).obj (F.obj i)) := by
  have ht := squareCoefficientMap_transport (τ.app i).unop (τ.app i).unop
    (𝟙 (X.obj i).unop) (X.map (𝟙 i)).unop
    (𝟙 (Y.obj i).unop) (Y.map (𝟙 i)).unop
    (congrArg Quiver.Hom.unop (X.map_id i))
    (congrArg Quiver.Hom.unop (Y.map_id i))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (congrArg Quiver.Hom.unop (τ.naturality (𝟙 i)))
    ((inverseImageId (X.obj i).unop).hom.app (F.obj i))
  rw [squareCoefficientMap_id] at ht
  dsimp only [diagramPullbackTransition]
  rw [diagramInverseTransition_id]
  simpa only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app] using ht

lemma diagramPullbackTransition_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramPullbackTransition X Y τ F (a ≫ b) =
      (diagramInverseImageComp Y a b).hom.app ((inverseImage (τ.app i).unop).obj
        (F.obj i)) ≫
        (inverseImage (Y.map b).unop).map (diagramPullbackTransition X Y τ F a) ≫
          diagramPullbackTransition X Y τ F b := by
  let e₁ : (τ.app j).unop ≫ (X.map a).unop =
      (Y.map a).unop ≫ (τ.app i).unop :=
    congrArg Quiver.Hom.unop (τ.naturality a)
  let e₂ : (τ.app k).unop ≫ (X.map b).unop =
      (Y.map b).unop ≫ (τ.app j).unop :=
    congrArg Quiver.Hom.unop (τ.naturality b)
  let e : (τ.app k).unop ≫ ((X.map b).unop ≫ (X.map a).unop) =
      ((Y.map b).unop ≫ (Y.map a).unop) ≫ (τ.app i).unop := by
    rw [← Category.assoc, e₂, Category.assoc, e₁, ← Category.assoc]
  let φ := (inverseImageComp (X.map a).unop (X.map b).unop).hom.app (F.obj i) ≫
    (inverseImage (X.map b).unop).map (diagramInverseTransition X F a) ≫
      diagramInverseTransition X F b
  have ht := squareCoefficientMap_transport (τ.app i).unop (τ.app k).unop
    ((X.map b).unop ≫ (X.map a).unop) (X.map (a ≫ b)).unop
    ((Y.map b).unop ≫ (Y.map a).unop) (Y.map (a ≫ b)).unop
    (congrArg Quiver.Hom.unop (X.map_comp a b))
    (congrArg Quiver.Hom.unop (Y.map_comp a b)) e
    (congrArg Quiver.Hom.unop (τ.naturality (a ≫ b))) φ
  have hp := squareCoefficientMap_hComp (τ.app i).unop (τ.app j).unop (τ.app k).unop
    (X.map a).unop (X.map b).unop (Y.map a).unop (Y.map b).unop e₁ e₂ e
    (diagramInverseTransition X F a) (diagramInverseTransition X F b)
  have hp' := congrArg
    (fun z => eqToHom (congrArg
      (fun h => (inverseImage h).obj ((inverseImage (τ.app i).unop).obj (F.obj i)))
      (congrArg Quiver.Hom.unop (Y.map_comp a b))) ≫ z) hp.symm
  dsimp only [diagramPullbackTransition]
  rw [diagramInverseTransition_comp]
  simpa only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc, φ] using ht.trans hp'

/-- A genuine compatible system, not a class containing a continuity hypothesis. -/
def diagramPullbackSystem : DiagramCoefficientSystem Y :=
  InjectiveSystem.System.ofLeftMapsWithComparisons (diagramAdjunctionData Y)
    (diagramInverseImageId Y) (diagramInverseImageComp Y)
    (leftIdIso_eq_diagramInverseImageId Y) (leftCompIso_eq_diagramInverseImageComp Y)
    (fun i => (inverseImage (τ.app i).unop).obj (F.obj i))
    (diagramPullbackTransition X Y τ F)
    (diagramPullbackTransition_id X Y τ F) (diagramPullbackTransition_comp X Y τ F)

/-- The system's transpose is exactly its original square coefficient transition. -/
lemma diagramInverseTransition_pullbackSystem {i j : I} (a : i ⟶ j) :
    diagramInverseTransition Y (diagramPullbackSystem X Y τ F) a =
      diagramPullbackTransition X Y τ F a :=
  ((inverseImageAdjunction (Y.map a).unop).homEquiv _ _).symm_apply_apply _

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
