/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence
public import Aglib.CategoryTheory.Adjunction.OpenRefinementNormalization
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageSquareComparison

/-! # Original identity normalizations for module derived exchange maps -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wIdS wIdS'

variable (Λ : Type (u + 1)) [Ring Λ]

section HorizontalIdentity
variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The actual inverse-image square over identity horizontal maps is normalized by the
original inverse-image identity comparisons. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f) :
    moduleUnboundedDerivedInverseImageSquareIso Λ f f (𝟙 S) (𝟙 X) e ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
          (moduleUnboundedDerivedInverseImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleUnboundedDerivedInverseImage Λ f) =
      Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ S)
        (moduleUnboundedDerivedInverseImage Λ f) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedInverseImage Λ f) := by
  rw [moduleUnboundedDerivedInverseImageSquareIso_eq_comp]
  exact sourceSquareIso_unit_normalization
    (moduleUnboundedDerivedInverseImageCompIso Λ (𝟙 S) f)
    (moduleUnboundedDerivedInverseImageCompIso Λ f (𝟙 X))
    (Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedDerivedInverseImage Λ f) ≪≫ Functor.leftUnitor _)
    (Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
      (moduleUnboundedDerivedInverseImageIdIso Λ X) ≪≫ Functor.rightUnitor _)
    (congrArg (fun k : X ⟶ S => moduleUnboundedDerivedInverseImage Λ k) (Category.comp_id f))
    (congrArg (fun k : X ⟶ S => moduleUnboundedDerivedInverseImage Λ k) (Category.id_comp f))
    (congrArg (fun k : X ⟶ S => moduleUnboundedDerivedInverseImage Λ k) e)
    (moduleUnboundedDerivedInverseImageCompIso_id_comp Λ f)
    (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ f)

/-- The canonical exchange for identity horizontal maps is the identity after the
original inverse-image identity comparisons, not a newly chosen exchange. -/
@[reassoc]
theorem moduleUnboundedDerivedBaseChangeMap_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (F : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedDerivedBaseChangeMap Λ f f (𝟙 S) (𝟙 X) e).app F ≫
        (moduleUnboundedDerivedDirectImage Λ f).map
          ((moduleUnboundedDerivedInverseImageIdIso Λ X).hom.app F) =
      (moduleUnboundedDerivedInverseImageIdIso Λ S).hom.app
          ((moduleUnboundedDerivedDirectImage Λ f).obj F) := by
  exact originalMate_horizontal_identity (moduleUnboundedDerivedAdjunction Λ f)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f (𝟙 S) (𝟙 X) e)
    (moduleUnboundedDerivedInverseImageIdIso Λ S) (moduleUnboundedDerivedInverseImageIdIso Λ X)
    (moduleUnboundedDerivedBaseChangeMap Λ f f (𝟙 S) (𝟙 X) e) rfl
    (moduleUnboundedDerivedInverseImageSquareIso_id Λ f e) F


end HorizontalIdentity

/-- The inverse-image square over vertical identities has its original normalization. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory (ModuleSheaf S Λ)) :
    IdentitySquareEquation
      (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
      (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedDerivedInverseImageIdIso Λ S') A := by
  change (moduleUnboundedDerivedInverseImageIdIso Λ S').hom.app
      ((moduleUnboundedDerivedInverseImage Λ g).obj A) =
    (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom.app A ≫
      (moduleUnboundedDerivedInverseImage Λ g).map
        ((moduleUnboundedDerivedInverseImageIdIso Λ S).hom.app A)
  exact originalSquare_transpose_identity
    (moduleUnboundedDerivedInverseImageSquareIso Λ g g (𝟙 S) (𝟙 S') e.symm)
    (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e)
    (moduleUnboundedDerivedInverseImageIdIso Λ S) (moduleUnboundedDerivedInverseImageIdIso Λ S')
    (moduleUnboundedDerivedInverseImageSquareIso_transpose Λ g g (𝟙 S) (𝟙 S') e.symm)
    (moduleUnboundedDerivedInverseImageSquareIso_id Λ g e.symm) A

/-- The actual derived exchange over vertical identities uses the native identity maps. -/
theorem moduleUnboundedDerivedBaseChangeMap_vId_mate {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory (ModuleSheaf S Λ)) :
    IdentityMateEquation
      (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
      (moduleUnboundedDerivedDirectImageIdIso Λ S) (moduleUnboundedDerivedDirectImageIdIso Λ S')
      (moduleUnboundedDerivedAdjunction Λ (𝟙 S))
      (moduleUnboundedDerivedAdjunction Λ (𝟙 S')) A :=
  identityMateEquation
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
    (moduleUnboundedDerivedInverseImageIdIso Λ S) (moduleUnboundedDerivedInverseImageIdIso Λ S')
    (moduleUnboundedDerivedDirectImageIdIso Λ S) (moduleUnboundedDerivedDirectImageIdIso Λ S')
    (moduleUnboundedDerivedAdjunction Λ (𝟙 S)) (moduleUnboundedDerivedAdjunction Λ (𝟙 S'))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ S)
      (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ S')
    (moduleUnboundedDerivedInverseImageSquareIso_vId Λ g e) A

/-- The actual exchange over vertical identities uses the original direct-image units. -/
theorem moduleUnboundedDerivedBaseChangeMap_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory (ModuleSheaf S Λ)) :
    (moduleUnboundedDerivedInverseImage Λ g).map
          ((moduleUnboundedDerivedDirectImageIdIso Λ S).hom.app A) =
      (moduleUnboundedDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e).app A ≫
        (moduleUnboundedDerivedDirectImageIdIso Λ S').hom.app
          ((moduleUnboundedDerivedInverseImage Λ g).obj A) := by
  apply actualIdentityMateEquation_eq
    (moduleUnboundedDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e)
    (moduleUnboundedDerivedDirectImageIdIso Λ S).hom
    (moduleUnboundedDerivedDirectImageIdIso Λ S').hom A
  exact actualIdentityMateEquation_of_mate
    (moduleUnboundedDerivedAdjunction Λ (𝟙 S)) (moduleUnboundedDerivedAdjunction Λ (𝟙 S'))
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
    (moduleUnboundedDerivedDirectImageIdIso Λ S) (moduleUnboundedDerivedDirectImageIdIso Λ S')
    (moduleUnboundedDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e)
    rfl A (moduleUnboundedDerivedBaseChangeMap_vId_mate Λ g e A)


end AlgebraicGeometry.Scheme.EtaleCohomology
