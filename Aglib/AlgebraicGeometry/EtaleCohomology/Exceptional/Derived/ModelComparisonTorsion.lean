/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ModelComparisonCoherence

/-! # Native model comparison on the original internal-torsion range -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
universe u d₀ d₁
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The original torsion-cohomology property in the explicitly specified model. -/
abbrev moduleTorsionCohomologyPlusModel
    (h : HasDerivedCategory.{d₀} (ModuleSheaf X Λ)) :
    ObjectProperty (@DerivedCategory.Plus _ _ _ h) :=
  @moduleTorsionCohomologyPlus X Λ _ h

variable (h₀ : HasDerivedCategory.{d₀} (ModuleSheaf X Λ))
  (h₁ : HasDerivedCategory.{d₁} (ModuleSheaf X Λ))

/-- Canonical model transport preserves internal torsion via the original homology comparison. -/
theorem moduleModelComparison_preservesTorsion (K : (@DerivedCategory.Plus _ _ _ h₀))
    (hK : moduleTorsionCohomologyPlusModel X Λ h₀ K) :
    moduleTorsionCohomologyPlusModel X Λ h₁ ((canonicalEquivalence h₀ h₁).functor.obj K) := by
  intro n
  exact moduleIsTorsion_of_iso X Λ ((canonicalEquivalenceHomologyIso h₀ h₁ n).app K) (hK n)

/-- The native localization comparison restricted to the original torsion full subcategories. -/
def moduleModelComparisonTorsion :
    (moduleTorsionCohomologyPlusModel X Λ h₀).FullSubcategory ⥤
      (moduleTorsionCohomologyPlusModel X Λ h₁).FullSubcategory :=
  (moduleTorsionCohomologyPlusModel X Λ h₁).lift
    ((moduleTorsionCohomologyPlusModel X Λ h₀).ι ⋙ (canonicalEquivalence h₀ h₁).functor)
    (fun K => moduleModelComparison_preservesTorsion X Λ h₀ h₁ K.obj K.property)

/-- Forgetting torsion recovers the exact original comparison, on objects and maps. -/
def moduleModelComparisonTorsionForgetIso :
    moduleModelComparisonTorsion X Λ h₀ h₁ ⋙ (moduleTorsionCohomologyPlusModel X Λ h₁).ι ≅
      (moduleTorsionCohomologyPlusModel X Λ h₀).ι ⋙ (canonicalEquivalence h₀ h₁).functor :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
