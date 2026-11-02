/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactPasting

/-! # Pasting of the actual native module derived base-change maps -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wb0 wb1 wb2 wb3 wb4 wb5

variable (Λ : Type (u + 1)) [Ring Λ]

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
theorem moduleDerivedInverseImageSquareIso_hComp
    (K : DerivedCategory.Plus (ModuleSheaf S₀ Λ)) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom
      (moduleDerivedInverseImageCompIso Λ h₁ h₂).hom K := by
  simpa only [moduleDerivedInverseImageCompIso] using
    rightDerivedFunctorPlus_exactHorizontalPasting
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleInverseImageCompIso Λ g₁ g₂) (moduleInverseImageCompIso Λ h₁ h₂)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (moduleDerivedInverseImageSquareIso_exactComparison Λ f₀ f₁ g₁ h₁ e₁)
      (moduleDerivedInverseImageSquareIso_exactComparison Λ f₁ f₂ g₂ h₂ e₂)
      (moduleDerivedInverseImageSquareIso_exactComparison Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
      (moduleInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K

end Horizontal

/-- Transposing the commuting square inverts its canonical inverse-image comparison. -/
theorem moduleDerivedInverseImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wb1} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wb2} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wb3} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    moduleDerivedInverseImageSquareIso Λ g g' f f' e.symm =
      (moduleDerivedInverseImageSquareIso Λ f f' g g' e).symm := by
  simp only [moduleDerivedInverseImageSquareIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

/-- The vertical square-coherence law follows from transposed horizontal coherence. -/
theorem moduleDerivedInverseImageSquareIso_vComp {S X Y S' X' Y' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wb1} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wb2} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wb3} (ModuleSheaf S' Λ)]
    [HasDerivedCategory.{wb4} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wb5} (ModuleSheaf Y' Λ)]
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
    (ef : f' ≫ g = g' ≫ f) (ek : k' ≫ g' = g'' ≫ k)
    (e : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (A : DerivedCategory.Plus (ModuleSheaf S Λ)) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' ef).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ k k' g' g'' ek).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom)
      (moduleDerivedInverseImageCompIso Λ f k) (moduleDerivedInverseImageCompIso Λ f' k') A := by
  change (moduleDerivedInverseImageCompIso Λ f' k').hom.app
    ((moduleDerivedInverseImage Λ g).obj A) ≫
        (moduleDerivedInverseImage Λ k').map
          ((moduleDerivedInverseImageSquareIso Λ f f' g g' ef).hom.app A) ≫
        (moduleDerivedInverseImageSquareIso Λ k k' g' g'' ek).hom.app
          ((moduleDerivedInverseImage Λ f).obj A) =
      (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫
        (moduleDerivedInverseImage Λ g'').map ((moduleDerivedInverseImageCompIso Λ f k).hom.app A)
  have hp := moduleDerivedInverseImageSquareIso_hComp Λ g g' g'' f k f' k' ef.symm ek.symm e.symm A
  dsimp only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans] at hp
  rw [moduleDerivedInverseImageSquareIso_transpose Λ f f' g g' ef,
    moduleDerivedInverseImageSquareIso_transpose Λ k k' g' g'' ek,
    moduleDerivedInverseImageSquareIso_transpose Λ (k ≫ f) (k' ≫ f') g g'' e] at hp
  have hr := congrArg (fun z =>
    (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫ z ≫
      (moduleDerivedInverseImage Λ k').map
        ((moduleDerivedInverseImageSquareIso Λ f f' g g' ef).hom.app A) ≫
      (moduleDerivedInverseImageSquareIso Λ k k' g' g'' ek).hom.app
        ((moduleDerivedInverseImage Λ f).obj A)) hp
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app] at hr
  rw [(moduleDerivedInverseImage Λ k').map_id
    ((moduleDerivedInverseImage Λ f ⋙ moduleDerivedInverseImage Λ g').obj A)] at hr
  simpa only [CategoryTheory.Functor.comp_obj, CategoryTheory.Category.id_comp,
    Iso.inv_hom_id_app, CategoryTheory.Category.comp_id] using hr.symm


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
theorem moduleDerivedBaseChangeMap_hComp
    (K : DerivedCategory.Plus (ModuleSheaf X₀ Λ)) :
    (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom.app ((moduleDerivedDirectImage Λ f₀).obj K) ≫
        (moduleDerivedInverseImage Λ g₂).map ((moduleDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁).app K) ≫
        (moduleDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂).app ((moduleDerivedInverseImage Λ h₁).obj K) =
      (moduleDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app K ≫
        (moduleDerivedDirectImage Λ f₂).map
          ((moduleDerivedInverseImageCompIso Λ h₁ h₂).hom.app K) := by
  apply actualHorizontalMateEquation_eq
    (moduleDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
    (moduleDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom
    (moduleDerivedInverseImageCompIso Λ h₁ h₂).hom K
  exact actualHorizontalMateEquation_of_mates
    (moduleDerivedAdjunction Λ f₀) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₂)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₀ f₁ g₁ h₁ e₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f₁ f₂ g₂ h₂ e₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
    (moduleDerivedInverseImageCompIso Λ g₁ g₂).hom
    (moduleDerivedInverseImageCompIso Λ h₁ h₂).hom
    (moduleDerivedBaseChangeMap Λ f₀ f₁ g₁ h₁ e₁) (moduleDerivedBaseChangeMap Λ f₁ f₂ g₂ h₂ e₂)
    (moduleDerivedBaseChangeMap Λ f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    rfl
    rfl
    rfl K
    (horizontalMateEquation _ _ _ _ _
      (moduleDerivedAdjunction Λ f₀) (moduleDerivedAdjunction Λ f₁)
    (moduleDerivedAdjunction Λ f₂)
      (moduleDerivedInverseImageSquareIso_hComp Λ f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K)

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
theorem moduleDerivedBaseChangeMap_vComp_mate
    (K : DerivedCategory.Plus (ModuleSheaf Y Λ)) :
    VerticalMateEquation
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
      (moduleDerivedDirectImageCompIso Λ f k) (moduleDerivedDirectImageCompIso Λ f' k')
      (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
      (moduleDerivedAdjunction Λ k) (moduleDerivedAdjunction Λ k')
      (moduleDerivedAdjunction Λ (k ≫ f)) (moduleDerivedAdjunction Λ (k' ≫ f')) K :=
  verticalMateEquation
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
    (moduleDerivedInverseImageCompIso Λ f k) (moduleDerivedInverseImageCompIso Λ f' k')
    (moduleDerivedDirectImageCompIso Λ f k) (moduleDerivedDirectImageCompIso Λ f' k')
    (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (moduleDerivedAdjunction Λ k) (moduleDerivedAdjunction Λ k')
    (moduleDerivedAdjunction Λ (k ≫ f)) (moduleDerivedAdjunction Λ (k' ≫ f'))
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ f k)
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ f' k')
    (moduleDerivedInverseImageSquareIso_vComp Λ f k f' k' g g' g'' h₁ h₂ h) K

/-- Vertical pasting of the actual exchange maps under the native direct-image comparisons. -/
theorem moduleDerivedBaseChangeMap_vComp
    (K : DerivedCategory.Plus (ModuleSheaf Y Λ)) :
    (moduleDerivedInverseImage Λ g).map ((moduleDerivedDirectImageCompIso Λ f k).hom.app K) ≫
        (moduleDerivedBaseChangeMap Λ f f' g g' h₁).app ((moduleDerivedDirectImage Λ k).obj K) ≫
        (moduleDerivedDirectImage Λ f').map ((moduleDerivedBaseChangeMap Λ k k' g' g'' h₂).app K) =
      (moduleDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h).app K ≫
        (moduleDerivedDirectImageCompIso Λ f' k').hom.app
          ((moduleDerivedInverseImage Λ g'').obj K) := by
  apply actualVerticalMateEquation_eq
    (moduleDerivedBaseChangeMap Λ f f' g g' h₁) (moduleDerivedBaseChangeMap Λ k k' g' g'' h₂)
    (moduleDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    (moduleDerivedDirectImageCompIso Λ f k).hom (moduleDerivedDirectImageCompIso Λ f' k').hom K
  exact actualVerticalMateEquation_of_mates
    (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (moduleDerivedAdjunction Λ k) (moduleDerivedAdjunction Λ k')
    (moduleDerivedAdjunction Λ (k ≫ f)) (moduleDerivedAdjunction Λ (k' ≫ f'))
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ (k ≫ f) (k' ≫ f') g g'' h).hom)
    (moduleDerivedDirectImageCompIso Λ f k) (moduleDerivedDirectImageCompIso Λ f' k')
    (moduleDerivedBaseChangeMap Λ f f' g g' h₁) (moduleDerivedBaseChangeMap Λ k k' g' g'' h₂)
    (moduleDerivedBaseChangeMap Λ (k ≫ f) (k' ≫ f') g g'' h)
    rfl rfl
    rfl K
    (moduleDerivedBaseChangeMap_vComp_mate Λ f k f' k' g g' g'' h₁ h₂ h K)

end VerticalPasting


end AlgebraicGeometry.Scheme.EtaleCohomology
