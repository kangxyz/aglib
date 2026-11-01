/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.CategoryTheory.Adjunction.MatePastingIdentification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualPasting
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactPasting

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactIsoCube
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquareSymmetry

/-! # Pasting of the actual unbounded module base-change maps -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wb0 wb1 wb2 wb3 wb4 wb5

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original unbounded inverse-image square retains its exact localization factors. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_pastingExactFactor
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wb1} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wb2} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wb3} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (K : CochainComplex (ModuleSheaf S Λ) ℤ) :
    ExactFactorSquareEquation
      (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
      (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)
      K :=
  mapDerivedCategorySquareIso_exactFactor
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    rfl K

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wb0} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wb1} (ModuleSheaf S₀ Λ)]
  [HasDerivedCategory.{wb2} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wb3} (ModuleSheaf S₁ Λ)]
  [HasDerivedCategory.{wb4} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wb5} (ModuleSheaf S₂ Λ)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Original horizontal inverse-image square pasting survives native exact deriving. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_hComp
    (K : DerivedCategory (ModuleSheaf S₀ Λ)) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ h₁ h₂).hom K := by
  exact mapDerivedCategory_exactHorizontalPasting
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleInverseImageCompIso Λ g₁ g₂) (moduleInverseImageCompIso Λ h₁ h₂)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleUnboundedDerivedInverseImageSquareIso_pastingExactFactor Λ f₀ f₁ g₁ h₁ e₁)
      (moduleUnboundedDerivedInverseImageSquareIso_pastingExactFactor Λ f₁ f₂ g₂ h₂ e₂)
      (moduleUnboundedDerivedInverseImageSquareIso_pastingExactFactor Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
      (moduleInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K

end Horizontal

/-- Transposing the commuting square inverts its canonical inverse-image comparison. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wb1} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wb2} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wb3} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    moduleUnboundedDerivedInverseImageSquareIso Λ g g' f f' e.symm =
      (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' e).symm := by
  exact Functor.mapDerivedCategorySquareIso_transpose
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' e)
    (moduleInverseImageSquareIso Λ g g' f f' e.symm)
    (moduleInverseImageSquareIso_transpose Λ f f' g g' e)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' e)
    (moduleUnboundedDerivedInverseImageSquareIso Λ g g' f f' e.symm) rfl rfl

/-- The vertical square-coherence law follows from transposed horizontal coherence. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_vComp {S X Y S' X' Y' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wb1} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wb2} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wb3} (ModuleSheaf S' Λ)]
    [HasDerivedCategory.{wb4} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wb5} (ModuleSheaf Y' Λ)]
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
    (ef : f' ≫ g = g' ≫ f) (ek : k' ≫ g' = g'' ≫ k)
    (e : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (A : DerivedCategory (ModuleSheaf S Λ)) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' ef).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ k k' g' g'' ek).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom)
      (moduleUnboundedDerivedInverseImageCompIso Λ f k)
        (moduleUnboundedDerivedInverseImageCompIso Λ f' k') A := by
  apply inverse_vertical_of_forward_horizontal
    (moduleUnboundedDerivedInverseImageSquareIso Λ k k' g' g'' ek).symm
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' ef).symm
    (moduleUnboundedDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).symm
    (moduleUnboundedDerivedInverseImageCompIso Λ f k)
    (moduleUnboundedDerivedInverseImageCompIso Λ f' k') _ A
  intro K
  simpa only [moduleUnboundedDerivedInverseImageSquareIso_transpose Λ f f' g g' ef,
    moduleUnboundedDerivedInverseImageSquareIso_transpose Λ k k' g' g'' ek,
    moduleUnboundedDerivedInverseImageSquareIso_transpose Λ (k ≫ f) (k' ≫ f') g g'' e]
    using moduleUnboundedDerivedInverseImageSquareIso_hComp Λ g g' g'' f k f' k'
      ef.symm ek.symm e.symm K


section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wb0} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wb1} (ModuleSheaf S₀ Λ)]
  [HasDerivedCategory.{wb2} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wb3} (ModuleSheaf S₁ Λ)]
  [HasDerivedCategory.{wb4} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wb5} (ModuleSheaf S₂ Λ)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Horizontal pasting for the actual derived exchange maps, with native comparisons. -/
theorem moduleUnboundedDerivedBaseChangeMap_hComp
    (K : DerivedCategory (ModuleSheaf X₀ Λ)) :
    (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂).hom.app
      ((moduleUnboundedDerivedDirectImage Λ f₀).obj K) ≫
        (moduleUnboundedDerivedInverseImage Λ g₂).map ((moduleUnboundedDerivedBaseChangeMap Λ
          f₀ f₁ g₁ h₁ e₁).app K) ≫
        (moduleUnboundedDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂).app
          ((moduleUnboundedDerivedInverseImage Λ h₁).obj K) =
      (moduleUnboundedDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app K ≫
        (moduleUnboundedDerivedDirectImage Λ f₂).map
          ((moduleUnboundedDerivedInverseImageCompIso Λ h₁ h₂).hom.app K) := by
  apply actualHorizontalMateEquation_eq
    (moduleUnboundedDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleUnboundedDerivedBaseChangeMap
      Λ f₁ f₂ g₂ h₂ e₂)
    (moduleUnboundedDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂).hom
    (moduleUnboundedDerivedInverseImageCompIso Λ h₁ h₂).hom K
  exact actualHorizontalMateEquation_of_mates
    (moduleUnboundedDerivedAdjunction Λ f₀) (moduleUnboundedDerivedAdjunction Λ f₁)
    (moduleUnboundedDerivedAdjunction Λ f₂)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
    (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂).hom
    (moduleUnboundedDerivedInverseImageCompIso Λ h₁ h₂).hom
    (moduleUnboundedDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleUnboundedDerivedBaseChangeMap
      Λ f₁ f₂ g₂ h₂ e₂)
    (moduleUnboundedDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    rfl
    rfl
    rfl K
    (horizontalMateEquation _ _ _ _ _
      (moduleUnboundedDerivedAdjunction Λ f₀) (moduleUnboundedDerivedAdjunction Λ f₁)
    (moduleUnboundedDerivedAdjunction Λ f₂)
      (moduleUnboundedDerivedInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K)

end Horizontal

section VerticalPasting
universe w₁ w₂ w₃ w₄ w₅ w₆
variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{w₁} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₃} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{w₄} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{w₅} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{w₆} (ModuleSheaf Y' Λ)]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))

/-- Actual vertical derived exchange pasting, normalized by the native comparisons. -/
theorem moduleUnboundedDerivedBaseChangeMap_vComp_mate
    (K : DerivedCategory (ModuleSheaf Y Λ)) :
    VerticalMateEquation
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
      (moduleUnboundedDerivedDirectImageCompIso Λ f k)
        (moduleUnboundedDerivedDirectImageCompIso Λ f' k')
      (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
      (moduleUnboundedDerivedAdjunction Λ k) (moduleUnboundedDerivedAdjunction Λ k')
      (moduleUnboundedDerivedAdjunction Λ (k ≫ f)) (moduleUnboundedDerivedAdjunction Λ (k' ≫
        f')) K :=
  verticalMateEquation
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
    (moduleUnboundedDerivedInverseImageCompIso Λ f k)
      (moduleUnboundedDerivedInverseImageCompIso Λ f' k')
    (moduleUnboundedDerivedDirectImageCompIso Λ f k) (moduleUnboundedDerivedDirectImageCompIso
      Λ f' k')
    (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (moduleUnboundedDerivedAdjunction Λ k) (moduleUnboundedDerivedAdjunction Λ k')
    (moduleUnboundedDerivedAdjunction Λ (k ≫ f)) (moduleUnboundedDerivedAdjunction Λ (k' ≫ f'))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f k)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f' k')
    (moduleUnboundedDerivedInverseImageSquareIso_vComp Λ f k f' k' g g' g'' h₁ h₂ h) K

/-- Vertical pasting of the actual exchange maps under the native direct-image comparisons. -/
theorem moduleUnboundedDerivedBaseChangeMap_vComp
    (K : DerivedCategory (ModuleSheaf Y Λ)) :
    (moduleUnboundedDerivedInverseImage Λ g).map ((moduleUnboundedDerivedDirectImageCompIso Λ f
      k).hom.app K) ≫
        (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h₁).app
          ((moduleUnboundedDerivedDirectImage Λ k).obj K) ≫
        (moduleUnboundedDerivedDirectImage Λ f').map ((moduleUnboundedDerivedBaseChangeMap Λ k
          k' g' g'' h₂).app K) =
      (moduleUnboundedDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h).app K ≫
        (moduleUnboundedDerivedDirectImageCompIso Λ f' k').hom.app
          ((moduleUnboundedDerivedInverseImage Λ g'').obj K) := by
  apply actualVerticalMateEquation_eq
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h₁) (moduleUnboundedDerivedBaseChangeMap Λ
      k k' g' g'' h₂)
    (moduleUnboundedDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    (moduleUnboundedDerivedDirectImageCompIso Λ f k).hom
      (moduleUnboundedDerivedDirectImageCompIso Λ f' k').hom K
  exact actualVerticalMateEquation_of_mates
    (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (moduleUnboundedDerivedAdjunction Λ k) (moduleUnboundedDerivedAdjunction Λ k')
    (moduleUnboundedDerivedAdjunction Λ (k ≫ f)) (moduleUnboundedDerivedAdjunction Λ (k' ≫ f'))
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _ (moduleUnboundedDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g
      g'' h).hom)
    (moduleUnboundedDerivedDirectImageCompIso Λ f k) (moduleUnboundedDerivedDirectImageCompIso
      Λ f' k')
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h₁) (moduleUnboundedDerivedBaseChangeMap Λ
      k k' g' g'' h₂)
    (moduleUnboundedDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    rfl rfl
    rfl K
    (moduleUnboundedDerivedBaseChangeMap_vComp_mate Λ f k f' k' g g' g'' h₁ h₂ h K)

end VerticalPasting


end AlgebraicGeometry.Scheme.EtaleCohomology
