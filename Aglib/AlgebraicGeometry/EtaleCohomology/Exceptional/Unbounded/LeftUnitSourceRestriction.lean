/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LeftUnitSourceExpansion
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitSource
public import Aglib.CategoryTheory.Functor.IdentitySourceRestriction

/-! # Original identity-source restriction of the left-unit contraction -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

universe u wX wA wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y}
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The category structure for the specified derived-category model. -/
local instance sourceRestrictionEndpointCategory : Category.{wX}
    (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX) :=
  @instCategoryDerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX
/-- The category structure for the specified derived-category model. -/
local instance sourceRestrictionAmbientCategory : Category.{wD}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance hD) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance hD

/-- The actual source contraction, including the identity-source unitor. -/
abbrev moduleUnboundedLeftUnitRestrictedContraction :=
  Functor.isoWhiskerLeft (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
    (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ) ≪≫
    Functor.rightUnitor (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))

/-- The original identity proper-image contraction inside the source. -/
abbrev moduleUnboundedLeftUnitRestrictedImageIdentity :=
  Functor.isoWhiskerLeft (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
    (Functor.isoWhiskerLeft (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX) ≪≫
      Functor.rightUnitor (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))

/-- The proved source-expansion equality is retained as a whole equation under inclusion. -/
theorem moduleUnboundedLeftUnitRestrictedExpansion :
    Functor.isoWhiskerRight (moduleUnboundedLeftUnitRestrictedContraction Λ hX)
        (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      Functor.isoWhiskerLeft (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
        (moduleUnboundedLeftUnitTargetExpansion C Λ hX hD) =
    Functor.isoWhiskerRight (moduleUnboundedLeftUnitRestrictedImageIdentity Λ hX)
      (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) :=
  identitySourceExpansion_whiskerLeft
    (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
    (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ)
    (Functor.isoWhiskerLeft (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX) ≪≫
      Functor.rightUnitor (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))
    (moduleUnboundedLeftUnitTargetExpansion C Λ hX hD)
    (moduleUnboundedLeftUnitSourceExpansion_normalize C Λ hX hD)

variable [QuasiCompact f]
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))

/-- The category structure for the specified derived-category model. -/
local instance sourceRestrictionIdentityCategory : Category.{wX}
    (@DerivedCategory
      (ModuleSheaf (Hom.DenseCompactification.ofProper (𝟙 X)).Xbar Λ)
      inferInstance inferInstance hX) :=
  @instCategoryDerivedCategory
    (ModuleSheaf (Hom.DenseCompactification.ofProper (𝟙 X)).Xbar Λ)
    inferInstance inferInstance hX

/-- This is the original first-refinement map, not a map chosen from the unit law. -/
abbrev moduleUnboundedLeftUnitRestrictedFirstComparison :=
  Functor.whiskerLeft (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
    (CategoryTheory.imageComparison
      (@moduleUnboundedDerivedRefinementComparison X X (𝟙 X) _
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX)
      (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X X (𝟙 X) hX
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) hA hX))

/-- Its normalization is inherited from the original proper compositor and original unit. -/
theorem moduleUnboundedLeftUnitRestrictedFirstComparison_eq :
    moduleUnboundedLeftUnitRestrictedFirstComparison C Λ hX hA =
      (moduleUnboundedLeftUnitRestrictedImageIdentity Λ hX).hom ≫
        Functor.whiskerLeft (𝟭 (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX))
          (@moduleUnboundedDerivedRefinementComparison X X (𝟙 X) _
            (Hom.CompactifiedComposition.leftUnit C).first
            (Hom.DenseCompactification.ofProper (𝟙 X))
            (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX) := by
  apply NatTrans.ext
  funext K
  have h := congrArg (fun τ => τ.app K)
    (moduleUnboundedLeftUnitFirstComparison_identityTarget (hX := hX) (hA := hA) Λ C)
  let a := Functor.whiskerLeft (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
    (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX).hom
  let b := (Functor.rightUnitor
    (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)).hom
  let δ := @moduleUnboundedDerivedRefinementComparison X X (𝟙 X) _
    (Hom.CompactifiedComposition.leftUnit C).first
    (Hom.DenseCompactification.ofProper (𝟙 X))
    (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX
  change _ = a.app K ≫ b.app K ≫ δ.app K at h
  change _ = (a.app K ≫ b.app K) ≫ δ.app K
  exact h.trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
