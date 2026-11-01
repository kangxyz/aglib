/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitImage
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LeftUnitSourceRestriction
public import Aglib.CategoryTheory.Functor.ImageLeftUnitEquation

/-! # The original source-contracted left-unit supplied-tower triangle -/

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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The category structure for the specified derived-category model. -/
local instance suppliedLeftUnitTotalCategory : Category.{wB}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance
    (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)
/-- The category structure for the specified derived-category model. -/
local instance suppliedLeftUnitTargetCategory : Category.{wD}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance (targetModels C)

/-- The actual supplied composition and actual first transition contract to the total transition.
The identity model here is the endpoint model; other ambient models remain independent. -/
theorem moduleUnboundedLeftUnitSuppliedEquation :
    ImageLeftUnitEquation
      (V := (𝟭 (DerivedCategory (ModuleSheaf X Λ))))
      (I := @moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hX)
      (J := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
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
      (Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
        (moduleUnboundedLeftUnitTotalDelta f Λ C))
      (moduleUnboundedLeftUnitImageContraction f Λ C)
      (moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C) N hN hΛ).hom
      (moduleUnboundedLeftUnitRestrictedContraction Λ hX)
      (moduleUnboundedLeftUnitRestrictedFirstComparison C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first)) := by
  exact imageLeftUnitEquation
      (V := (𝟭 (DerivedCategory (ModuleSheaf X Λ))))
      (I := @moduleUnboundedDerivedDirectImage Λ _ X X (𝟙 X) hX hX)
      (J := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (J' := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
          (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX
          (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (T' := (𝟭 (DerivedCategory (ModuleSheaf X Λ))) ⋙
        @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX
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
      (Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
        (moduleUnboundedLeftUnitFirstDelta f Λ C))
      (Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
        (moduleUnboundedLeftUnitTotalDelta f Λ C))
      (Functor.isoWhiskerLeft (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
        (moduleUnboundedLeftUnitTargetExpansion C Λ hX (targetModels C)))
      (moduleUnboundedLeftUnitImageContraction f Λ C)
      (moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
        (Hom.CompactifiedComposition.leftUnit C) N hN hΛ).hom
      (moduleUnboundedLeftUnitRestrictedContraction Λ hX)
      (moduleUnboundedLeftUnitRestrictedImageIdentity Λ hX)
      (moduleUnboundedLeftUnitRestrictedFirstComparison C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (moduleUnboundedLeftUnitRestrictedExpansion C Λ hX (targetModels C))
      (moduleUnboundedLeftUnitRestrictedFirstComparison_eq C Λ hX
        (firstModels (Hom.CompactifiedComposition.leftUnit C).first))
      (moduleUnboundedLeftUnitCompositionImageEquation f Λ C N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
