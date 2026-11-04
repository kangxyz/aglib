/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Shift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange

/-! The original bounded-below module exchange commutes with the installed shifts. -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ]

private theorem moduleInverseImageComp_commShift {X S T : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf T Λ)]
    (f : S ⟶ X) (g : T ⟶ S) :
    NatTrans.CommShift (moduleDerivedInverseImageCompIso Λ f g).hom ℤ := by
  have := Functor.rightDerivedFunctorPlusIso_commShift
    (moduleInverseImage (g ≫ f) Λ) (moduleInverseImageCompIso Λ f g)
  have := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_commShift
    (moduleInverseImage f Λ) (moduleInverseImage g Λ)
  change NatTrans.CommShift
    (((moduleInverseImage (g ≫ f) Λ).rightDerivedFunctorPlusIso
      (moduleInverseImageCompIso Λ f g)).hom ≫
        (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
          (moduleInverseImage f Λ) (moduleInverseImage g Λ)).hom) ℤ
  infer_instance

private theorem moduleInverseImageEquality_commShift {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] {a b : S ⟶ X} (h : a = b) :
    NatTrans.CommShift
      (eqToIso (congrArg (fun f : S ⟶ X => moduleDerivedInverseImage Λ f) h)).hom ℤ := by
  subst h
  change NatTrans.CommShift (𝟙 (moduleDerivedInverseImage Λ a)) ℤ
  infer_instance

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The genuine module exchange commutes with shifts, using its original
inverse-image square and the shift-compatible derived adjunctions. -/
theorem moduleDerivedBaseChangeMap_commShift :
    NatTrans.CommShift (moduleDerivedBaseChangeMap Λ f f' g g' h) ℤ := by
  have : (moduleDerivedAdjunction Λ f).CommShift ℤ :=
    Adjunction.rightDerivedFunctorPlus_commShift (moduleInverseImageAdjunction f Λ)
  have : (moduleDerivedAdjunction Λ f').CommShift ℤ :=
    Adjunction.rightDerivedFunctorPlus_commShift (moduleInverseImageAdjunction f' Λ)
  have := moduleInverseImageComp_commShift Λ g f'
  have := moduleInverseImageComp_commShift Λ f g'
  have := moduleInverseImageEquality_commShift Λ h
  have : NatTrans.CommShift (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom ℤ := by
    change NatTrans.CommShift
      ((moduleDerivedInverseImageCompIso Λ g f').inv ≫
        (eqToIso (congrArg (fun k : X' ⟶ S => moduleDerivedInverseImage Λ k) h)).hom ≫
        (moduleDerivedInverseImageCompIso Λ f g').hom) ℤ
    infer_instance
  exact mateEquiv_commShift (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)


universe wY

/-- The original module inverse-image identity commutes with the installed shift. -/
theorem moduleDerivedInverseImageIdIso_commShift
    (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    NatTrans.CommShift (moduleDerivedInverseImageIdIso Λ X).hom ℤ := by
  have := Functor.rightDerivedFunctorPlusIso_commShift
    (moduleInverseImage (𝟙 X) Λ) (moduleInverseImageIdIso Λ X)
  have := Functor.rightDerivedFunctorPlusIdIso_commShift (ModuleSheaf X Λ)
  change NatTrans.CommShift
    (((moduleInverseImage (𝟙 X) Λ).rightDerivedFunctorPlusIso
      (moduleInverseImageIdIso Λ X)).hom ≫
        (Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)).hom) ℤ
  infer_instance

/-- The original section comparison of derived inverse image commutes with shifts. -/
theorem moduleDerivedInverseImageSectionIso_commShift {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    (p : Y ⟶ X) (o : X ⟶ Y) (ho : o ≫ p = 𝟙 X) :
    NatTrans.CommShift ((moduleDerivedInverseImageCompIso Λ p o).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => moduleDerivedInverseImage Λ f) ho) ≪≫
      moduleDerivedInverseImageIdIso Λ X).hom ℤ := by
  have := Functor.rightDerivedFunctorPlusIso_commShift
    (moduleInverseImage (o ≫ p) Λ) (moduleInverseImageCompIso Λ p o)
  have := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_commShift
    (moduleInverseImage p Λ) (moduleInverseImage o Λ)
  have : NatTrans.CommShift (moduleDerivedInverseImageCompIso Λ p o).hom ℤ := by
    change NatTrans.CommShift
      (((moduleInverseImage (o ≫ p) Λ).rightDerivedFunctorPlusIso
        (moduleInverseImageCompIso Λ p o)).hom ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
            (moduleInverseImage p Λ) (moduleInverseImage o Λ)).hom) ℤ
    infer_instance
  have := moduleDerivedInverseImageIdIso_commShift Λ X
  have := moduleInverseImageEquality_commShift Λ ho
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
