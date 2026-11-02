/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.OpenRefinementNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageIdentityCoherence

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
theorem moduleDerivedInverseImageSquareIso_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f) :
    moduleDerivedInverseImageSquareIso Λ f f (𝟙 S) (𝟙 X) e ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImage Λ f)
          (moduleDerivedInverseImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleDerivedInverseImage Λ f) =
      Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ S)
        (moduleDerivedInverseImage Λ f) ≪≫
        Functor.leftUnitor (moduleDerivedInverseImage Λ f) := by
  unfold moduleDerivedInverseImageSquareIso
  exact sourceSquareIso_unit_normalization
    (moduleDerivedInverseImageCompIso Λ (𝟙 S) f)
    (moduleDerivedInverseImageCompIso Λ f (𝟙 X))
    (Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ S)
      (moduleDerivedInverseImage Λ f) ≪≫ Functor.leftUnitor _)
    (Functor.isoWhiskerLeft (moduleDerivedInverseImage Λ f)
      (moduleDerivedInverseImageIdIso Λ X) ≪≫ Functor.rightUnitor _)
    (congrArg (fun k : X ⟶ S => moduleDerivedInverseImage Λ k) (Category.comp_id f))
    (congrArg (fun k : X ⟶ S => moduleDerivedInverseImage Λ k) (Category.id_comp f))
    (congrArg (fun k : X ⟶ S => moduleDerivedInverseImage Λ k) e)
    (moduleDerivedInverseImageCompIso_id_comp Λ f)
    (moduleDerivedInverseImageCompIso_comp_id Λ f)

/-- The canonical exchange for identity horizontal maps is the identity after the
original inverse-image identity comparisons, not a newly chosen exchange. -/
@[reassoc]
theorem moduleDerivedBaseChangeMap_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (F : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedBaseChangeMap Λ f f (𝟙 S) (𝟙 X) e).app F ≫
        (moduleDerivedDirectImage Λ f).map ((moduleDerivedInverseImageIdIso Λ X).hom.app F) =
      (moduleDerivedInverseImageIdIso Λ S).hom.app ((moduleDerivedDirectImage Λ f).obj F) := by
  exact originalMate_horizontal_identity (moduleDerivedAdjunction Λ f)
    (moduleDerivedInverseImageSquareIso Λ f f (𝟙 S) (𝟙 X) e)
    (moduleDerivedInverseImageIdIso Λ S) (moduleDerivedInverseImageIdIso Λ X)
    (moduleDerivedBaseChangeMap Λ f f (𝟙 S) (𝟙 X) e) rfl
    (moduleDerivedInverseImageSquareIso_id Λ f e) F

end HorizontalIdentity

/-- The inverse-image square over vertical identities has its original normalization. -/
theorem moduleDerivedInverseImageSquareIso_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (ModuleSheaf S Λ)) :
    IdentitySquareEquation
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
      (moduleDerivedInverseImageIdIso Λ S) (moduleDerivedInverseImageIdIso Λ S') A := by
  change (moduleDerivedInverseImageIdIso Λ S').hom.app
      ((moduleDerivedInverseImage Λ g).obj A) =
    (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom.app A ≫
      (moduleDerivedInverseImage Λ g).map ((moduleDerivedInverseImageIdIso Λ S).hom.app A)
  exact originalSquare_transpose_identity
    (moduleDerivedInverseImageSquareIso Λ g g (𝟙 S) (𝟙 S') e.symm)
    (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e)
    (moduleDerivedInverseImageIdIso Λ S) (moduleDerivedInverseImageIdIso Λ S')
    (moduleDerivedInverseImageSquareIso_transpose Λ g g (𝟙 S) (𝟙 S') e.symm)
    (moduleDerivedInverseImageSquareIso_id Λ g e.symm) A

/-- The actual derived exchange over vertical identities uses the native identity maps. -/
theorem moduleDerivedBaseChangeMap_vId_mate {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (ModuleSheaf S Λ)) :
    IdentityMateEquation
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
      (moduleDerivedDirectImageIdIso Λ S) (moduleDerivedDirectImageIdIso Λ S')
      (moduleDerivedAdjunction Λ (𝟙 S)) (moduleDerivedAdjunction Λ (𝟙 S')) A :=
  identityMateEquation
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
    (moduleDerivedInverseImageIdIso Λ S) (moduleDerivedInverseImageIdIso Λ S')
    (moduleDerivedDirectImageIdIso Λ S) (moduleDerivedDirectImageIdIso Λ S')
    (moduleDerivedAdjunction Λ (𝟙 S)) (moduleDerivedAdjunction Λ (𝟙 S'))
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ S)
      (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ S')
    (moduleDerivedInverseImageSquareIso_vId Λ g e) A

/-- The actual exchange over vertical identities uses the original direct-image units. -/
theorem moduleDerivedBaseChangeMap_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wIdS'} (ModuleSheaf S' Λ)] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (ModuleSheaf S Λ)) :
    (moduleDerivedInverseImage Λ g).map ((moduleDerivedDirectImageIdIso Λ S).hom.app A) =
      (moduleDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e).app A ≫
        (moduleDerivedDirectImageIdIso Λ S').hom.app ((moduleDerivedInverseImage Λ g).obj A) := by
  apply actualIdentityMateEquation_eq
    (moduleDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e)
    (moduleDerivedDirectImageIdIso Λ S).hom (moduleDerivedDirectImageIdIso Λ S').hom A
  exact actualIdentityMateEquation_of_mate
    (moduleDerivedAdjunction Λ (𝟙 S)) (moduleDerivedAdjunction Λ (𝟙 S'))
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ (𝟙 S) (𝟙 S') g g e).hom)
    (moduleDerivedDirectImageIdIso Λ S) (moduleDerivedDirectImageIdIso Λ S')
    (moduleDerivedBaseChangeMap Λ (𝟙 S) (𝟙 S') g g e)
    rfl A (moduleDerivedBaseChangeMap_vId_mate Λ g e A)


end AlgebraicGeometry.Scheme.EtaleCohomology
