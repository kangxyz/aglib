/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.MateNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Coherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionPreservation

/-! # Original proper/open coherence on the native torsion source

The global original mate is the previously constructed comparison, not a
replacement isomorphism. Intermediate proper direct images stay in the same
internal torsion full subcategory by the proved qcqs preservation theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wV wX wY wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable (Λ : Type (u + 1)) [Ring Λ]

section Comparison

variable {V U X Y : Scheme.{u}} (p : X ⟶ Y) (p' : V ⟶ U)
  (j : U ⟶ Y) (j' : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : IsPullback j' p' p j)
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]

/-- Component specialization of the accepted equality of original transformations. -/
theorem moduleProperOpenComparison_eq_mate_app
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    (moduleProperOpenComparison Λ p p' j j' sq).app K =
      (moduleProperOpenMate Λ j j' p' p sq.flip).app K.obj := by
  have h := congrArg (fun t => t.app K)
    (moduleProperOpenComparison_eq_mixedMate Λ p p' j j' sq)
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.comp_obj, ObjectProperty.ι_obj, Category.id_comp] using h

/-- Proper/torsion invertibility applies to the literal original global mate. -/
theorem moduleProperOpenMate_isIso_app_of_torsion [IsProper p]
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    IsIso ((moduleProperOpenMate Λ j j' p' p sq.flip).app K.obj) := by
  rw [← moduleProperOpenComparison_eq_mate_app Λ p p' j j' sq K]
  let := moduleProperOpenComparison_isIso Λ p p' j j' sq
  exact NatIso.isIso_app_of_isIso (moduleProperOpenComparison Λ p p' j j' sq) K

/-- The unchanged proper direct-image object, with its proved internal torsion property. -/
def moduleProperOpenTorsionImage [IsProper p]
    (K : (moduleTorsionCohomologyPlus V Λ).FullSubcategory) :
    (moduleTorsionCohomologyPlus U Λ).FullSubcategory := by
  have : IsProper p' := MorphismProperty.of_isPullback sq (inferInstance : IsProper p)
  exact ⟨(moduleDerivedDirectImage Λ p').obj K.obj,
    moduleDerivedDirectImage_preservesTorsionCohomology p' Λ K.obj K.property⟩

end Comparison

section Vertical

variable {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
  (g₁ : U₁ ⟶ U₀) (g₂ : U₂ ⟶ U₁) (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
  [IsProper f₁] [IsProper f₂]
  (h₁ : IsPullback g₁ j₁ j₀ f₁) (h₂ : IsPullback g₂ j₂ j₁ f₂)
  (ht : IsPullback (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁))
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

omit [IsProper f₁] in
/-- Vertical pasting for the previously constructed canonical torsion comparison.
The intermediate coefficient is the actual proper direct image, not an assumed
object in the torsion category. -/
theorem moduleProperOpenComparison_vComp
    (K : (moduleTorsionCohomologyPlus U₂ Λ).FullSubcategory) :
    (moduleDerivedLowerShriek j₀ Λ).map
        ((moduleDerivedDirectImageCompIso Λ g₁ g₂).hom.app K.obj) ≫
      (moduleProperOpenComparison Λ f₁ g₁ j₀ j₁ h₁.flip).app
        (moduleProperOpenTorsionImage Λ f₂ g₂ j₁ j₂ h₂.flip K) ≫
      (moduleDerivedDirectImage Λ f₁).map
        ((moduleProperOpenComparison Λ f₂ g₂ j₁ j₂ h₂.flip).app K) =
    (moduleProperOpenComparison Λ (f₂ ≫ f₁) (g₂ ≫ g₁) j₀ j₂ ht.flip).app K ≫
      (moduleDerivedDirectImageCompIso Λ f₁ f₂).hom.app
        ((moduleDerivedLowerShriek j₂ Λ).obj K.obj) := by
  simp only [moduleProperOpenComparison_eq_mate_app]
  exact moduleProperOpenMate_vComp Λ j₀ j₁ j₂ g₁ g₂ f₁ f₂ h₁ h₂ ht K.obj

end Vertical

/-- Identity normalization for the original canonical torsion comparison. -/
theorem moduleProperOpenComparison_identity
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : IsPullback (𝟙 U) j j (𝟙 X))
    [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    (K : (moduleTorsionCohomologyPlus U Λ).FullSubcategory) :
    (moduleDerivedLowerShriek j Λ).map
        ((moduleDerivedDirectImageIdIso Λ U).hom.app K.obj) =
      (moduleProperOpenComparison Λ (𝟙 X) (𝟙 U) j j h.flip).app K ≫
        (moduleDerivedDirectImageIdIso Λ X).hom.app
          ((moduleDerivedLowerShriek j Λ).obj K.obj) := by
  rw [moduleProperOpenComparison_eq_mate_app]
  exact moduleProperOpenMate_identity Λ j h K.obj

end AlgebraicGeometry.Scheme.EtaleCohomology
