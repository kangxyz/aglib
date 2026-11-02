/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelMaps
public import Aglib.CategoryTheory.Functor.ImageUnitCompositionFormula

/-! # The actual left-unit tower map contracts to its original mixed identity transition

The source is expanded by the original lower-shriek identity compositor. All
three ambient families remain independent. Turning this normalized supplied
triangle into the chosen exceptional unit law also requires the original
identity-factorization contraction and canonical model-family comparison.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

/-- The local derived-category model on `ModuleSheaf (Hom.CompactifiedComposition.leftUnit
C).first.Xbar Λ`. -/
local instance leftUnitImageFirstModel : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ) :=
  firstModels (Hom.CompactifiedComposition.leftUnit C).first
/-- The local derived-category model on `ModuleSheaf C.Xbar Λ`. -/
local instance leftUnitImageTargetModel : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ) :=
  targetModels C
/-- The local derived-category model on `ModuleSheaf C.Xbar Λ`. -/
local instance leftUnitImageTotalModel : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ) :=
  compositeModels (Hom.CompactifiedComposition.leftUnit C).composite

/-- The category structure for the specified derived-category model. -/
local instance leftUnitImageTotalCategory : Category.{wB}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)
/-- The category structure for the specified derived-category model. -/
local instance leftUnitImageTargetCategory : Category.{wD}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)

/-- The literal original first-refinement unit, with its endpoint model fixed explicitly. -/
abbrev moduleUnboundedLeftUnitFirstDelta :=
  @moduleUnboundedDerivedProperRefinementComparison X
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
    (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X) _ _
    (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitTowerSourceSquare C)
    Λ _ hX (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX

/-- The original mixed-model identity unit on the total ambient. -/
abbrev moduleUnboundedLeftUnitTotalDelta :=
  @moduleUnboundedDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
    (𝟙 C.Xbar) (unboundedLeftUnitTowerTotalSquare C) Λ _ hX
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)

/-- The exact original central exchange of the left-unit tower. -/
abbrev moduleUnboundedLeftUnitCentralMate :=
  @moduleUnboundedProperOpenMate
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
    (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitMiddleOpen C)
    C.j (𝟙 C.Xbar) _ _
    (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen.flip Λ _
    (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C)

/-- The original image compositor, with the independent middle ambient retained. -/
abbrev moduleUnboundedLeftUnitImageContraction :=
  (@moduleUnboundedDerivedDirectImageCompIso Λ _ Y C.Xbar C.Xbar C.p (𝟙 C.Xbar) hY
    (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)).symm

omit hY targetModels in
/-- The inverse expansion is exactly the original supplied-tower open compositor. -/
theorem moduleUnboundedLeftUnitSourceExpansion_symm :
    (moduleUnboundedLeftUnitSourceExpansion C Λ hX
      (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)).symm =
    moduleUnboundedCompactifiedCompositionOpenIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C) := by
  apply Iso.ext
  rfl

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual supplied-tower map, not a replacement map, has the original unit-image formula. -/
theorem moduleUnboundedLeftUnitCompositionFormula :
    ImageUnitHorizontalFormula
      (J' := @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit
        C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (L' := @moduleUnboundedDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        C.Xbar (unboundedLeftUnitMiddleOpen C) _ Λ _
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (R := @moduleUnboundedDerivedDirectImage Λ _ X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleUnboundedDerivedDirectImage Λ _ C.Xbar C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar C.p hY (targetModels C))
      (P' := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (moduleUnboundedLeftUnitCentralMate f Λ C)
      (moduleUnboundedLeftUnitSourceExpansion C Λ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (moduleUnboundedLeftUnitImageContraction f Λ C)
      (moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C) N hN hΛ).hom := by
  refine imageUnitHorizontalFormula_of_composition
      (J' := @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit
        C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (L' := @moduleUnboundedDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        C.Xbar (unboundedLeftUnitMiddleOpen C) _ Λ _
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (R := @moduleUnboundedDerivedDirectImage Λ _ X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleUnboundedDerivedDirectImage Λ _ C.Xbar C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar C.p hY (targetModels C))
      (P' := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
    (moduleUnboundedLeftUnitCentralMate f Λ C)
    (moduleUnboundedCompactifiedCompositionOpenIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C))
    (moduleUnboundedLeftUnitSourceExpansion C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
    (moduleUnboundedLeftUnitImageContraction f Λ C)
    (moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C) N hN hΛ).hom ?_ ?_
  · exact (moduleUnboundedLeftUnitSourceExpansion_symm f Λ C).symm
  · exact moduleUnboundedCompactifiedCompositionIso_formula (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C) N hN hΛ


/-- The actual normalized left-unit tower triangle is its original mixed identity transition. -/
theorem moduleUnboundedLeftUnitCompositionImageEquation :
    ImageUnitHorizontalEquation
      (J := @moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit
        C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (T' := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
          (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (L := @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (targetModels C))
      (R := @moduleUnboundedDerivedDirectImage Λ _ X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (S := @moduleUnboundedDerivedDirectImage Λ _ C.Xbar C.Xbar (𝟙 C.Xbar)
        (targetModels C) (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (P := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar C.p hY (targetModels C))
      (P' := @moduleUnboundedDerivedDirectImage Λ _ Y C.Xbar ((𝟙 C.Xbar) ≫ C.p) hY
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite))
      (moduleUnboundedLeftUnitFirstDelta f Λ C)
      (moduleUnboundedLeftUnitTotalDelta f Λ C)
      (moduleUnboundedLeftUnitTargetExpansion C Λ hX (targetModels C))
      (moduleUnboundedLeftUnitImageContraction f Λ C)
      (moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C) N hN hΛ).hom :=
  imageUnitHorizontalEquation _ _ (moduleUnboundedLeftUnitCentralMate f Λ C) _
    (moduleUnboundedLeftUnitSourceExpansion C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
        (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)) _ _
    (moduleUnboundedLeftUnitTowerTotalOpenEquation C Λ hX
      (firstModels (Hom.CompactifiedComposition.leftUnit C).first)
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C))
    (moduleUnboundedLeftUnitCompositionFormula f Λ C N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
