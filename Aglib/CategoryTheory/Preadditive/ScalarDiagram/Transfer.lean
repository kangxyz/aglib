/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.ScalarDiagram
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Scalar transfer of the original coefficient diagram

A coefficient-compatible transformation between the original additive diagrams
produces its module transformation and its scalar-adjunction mate. All index
maps, scalar actions and the adjunction unit belong to these same constructions.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ChangeOfRings TensorProduct

universe u v u' v' i j k l r w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]
  (H : C ⥤ I ⥤ AddCommGrpCat.{max r w}) [H.Additive]
  (K : D ⥤ J ⥤ AddCommGrpCat.{max r w}) [K.Additive]
  {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
  (A : C) (B : D) (ρ : R →+* End A) (τ : S →+* End B)
  (P : I ⥤ J) (η : H.obj A ⟶ P ⋙ K.obj B)
  (hη : ∀ a : R, H.map (ρ a) ≫ η = η ≫ whiskerLeft P (K.map (τ (σ a))))

/-- The original transfer, linear over the original coefficient actions. -/
def coefficientModuleDiagramMap :
    H.coefficientModuleDiagram A ρ ⟶
      (P ⋙ K.coefficientModuleDiagram B τ) ⋙ ModuleCat.restrictScalars σ where
  app i := by
    letI := H.coefficientModule A ρ i
    letI := K.coefficientModule B τ (P.obj i)
    refine ModuleCat.ofHom
      (X := (H.coefficientModuleDiagram A ρ).obj i)
      (Y := (ModuleCat.restrictScalars σ).obj
        ((K.coefficientModuleDiagram B τ).obj (P.obj i)))
      { __ := (η.app i).hom, map_smul' := ?_ }
    intro a x
    change η.app i ((H.map (ρ a)).app i x) =
      (K.map (τ (σ a))).app (P.obj i) (η.app i x)
    have hi : (H.map (ρ a)).app i ≫ η.app i =
        η.app i ≫ (K.map (τ (σ a))).app (P.obj i) :=
      congrArg (fun t => t.app i) (hη a)
    exact ConcreteCategory.congr_hom hi x
  naturality i j f := by
    apply (forget₂ (ModuleCat.{max r w} R) AddCommGrpCat.{max r w}).map_injective
    exact η.naturality f

/-- The underlying transfer at every index is the original additive map. -/
theorem coefficientModuleDiagramMap_apply (i : I) (x : (H.obj A).obj i) :
    (H.coefficientModuleDiagramMap K σ A B ρ τ P η hη).app i x = η.app i x := rfl

/-- Transpose the same original module transformation, without a new mate. -/
def coefficientTensorDiagramMap :
    H.coefficientModuleDiagram A ρ ⋙ ModuleCat.extendScalars σ ⟶
      P ⋙ K.coefficientModuleDiagram B τ :=
  (((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).whiskerRight I).homEquiv
    (H.coefficientModuleDiagram A ρ) (P ⋙ K.coefficientModuleDiagram B τ)).symm
      (H.coefficientModuleDiagramMap K σ A B ρ τ P η hη)

/-- The original adjunction unit recovers the same whole module transfer. -/
theorem coefficientTensorDiagramMap_unit :
    ((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).whiskerRight I).unit.app
        (H.coefficientModuleDiagram A ρ) ≫
      whiskerRight (H.coefficientTensorDiagramMap K σ A B ρ τ P η hη)
        (ModuleCat.restrictScalars σ) =
      H.coefficientModuleDiagramMap K σ A B ρ τ P η hη :=
  (((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).whiskerRight I).homEquiv
    (H.coefficientModuleDiagram A ρ) (P ⋙ K.coefficientModuleDiagram B τ)).apply_symm_apply _

/-- On an original pure tensor the mate is the original transfer. -/
theorem coefficientTensorDiagramMap_one_tmul (i : I) (x : (H.obj A).obj i) :
    letI := H.coefficientModule A ρ i
    (H.coefficientTensorDiagramMap K σ A B ρ τ P η hη).app i
      ((1 : S) ⊗ₜ[R,σ] x) = η.app i x := by
  have hi := congrArg (fun t => t.app i)
    (H.coefficientTensorDiagramMap_unit K σ A B ρ τ P η hη)
  exact congrArg (fun f => f x) hi

end CategoryTheory.Functor
