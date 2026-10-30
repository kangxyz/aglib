/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.CategoryTheory.Filtered.SystemConstructions

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

/-- The native square is the actual selected generic square transition. -/
lemma diagramPullbackTransition_eq_generic {i j : I} (a : i ⟶ j) :
    diagramPullbackTransition X Y τ F a =
      InjectiveSystem.System.pullbackTransition schemeAdjunctionData X Y τ F a := by
  exact (schemeSquareCoefficientMap_eq_squareCoefficientMap
    (τ.app i) (τ.app j) (X.map a) (Y.map a) (τ.naturality a)
    (diagramInverseTransition X F a)).symm

lemma diagramPullbackTransition_id (i : I) :
    diagramPullbackTransition X Y τ F (𝟙 i) =
      (diagramInverseImageId Y i).hom.app ((inverseImage (τ.app i).unop).obj (F.obj i)) := by
  rw [diagramPullbackTransition_eq_generic, ← leftIdIso_eq_diagramInverseImageId Y i]
  exact InjectiveSystem.System.pullbackTransition_id
    schemeAdjunctionData X Y τ F schemeAdjunctionData_coherent i

lemma diagramPullbackTransition_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramPullbackTransition X Y τ F (a ≫ b) =
      (diagramInverseImageComp Y a b).hom.app ((inverseImage (τ.app i).unop).obj
        (F.obj i)) ≫
        (inverseImage (Y.map b).unop).map (diagramPullbackTransition X Y τ F a) ≫
          diagramPullbackTransition X Y τ F b := by
  have h := InjectiveSystem.System.pullbackTransition_comp
    schemeAdjunctionData X Y τ F schemeAdjunctionData_coherent a b
  simp only [← diagramPullbackTransition_eq_generic,
    leftCompIso_eq_diagramInverseImageComp, schemeLeft_eq_inverseImage] at h
  exact h

/-- A genuine compatible system, not a class containing a continuity hypothesis. -/
def diagramPullbackSystem : DiagramCoefficientSystem Y :=
  InjectiveSystem.System.pullback schemeAdjunctionData X Y τ F schemeAdjunctionData_coherent

/-- The system's transpose is exactly its original square coefficient transition. -/
lemma diagramInverseTransition_pullbackSystem {i j : I} (a : i ⟶ j) :
    diagramInverseTransition Y (diagramPullbackSystem X Y τ F) a =
      diagramPullbackTransition X Y τ F a := by
  exact (InjectiveSystem.System.pullback_leftMap
    schemeAdjunctionData X Y τ F schemeAdjunctionData_coherent a).trans
      (diagramPullbackTransition_eq_generic X Y τ F a).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
