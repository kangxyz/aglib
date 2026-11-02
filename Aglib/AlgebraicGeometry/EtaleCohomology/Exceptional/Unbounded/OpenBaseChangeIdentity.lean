/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquareIdentity
public import Aglib.CategoryTheory.Adjunction.IdentitySourceMate

/-! # Original source-identity normalization of the unbounded mixed mate -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wC wD
variable {X C D : Scheme.{u}} (jC : X ⟶ C) (jD : X ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD] (a : C ⟶ D)
  (h : IsPullback jC (𝟙 X) a jD) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]

/-- The original exact source-identity contraction holds on every unbounded object. -/
theorem moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_identity_source :
    moduleUnboundedDerivedProperRefinementPullbackIso jC jD a h Λ =
      moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) jC jD a h.flip Λ ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X)
          (moduleUnboundedDerivedLowerShriek jC Λ) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedLowerShriek jC Λ) :=
  Functor.mapDerivedCategorySquareIso_source_identity
    (moduleLowerShriek jD Λ) (moduleInverseImage a Λ) (moduleLowerShriek jC Λ)
    (moduleInverseImage (𝟙 X) Λ)
    (moduleLowerShriekCartesianBaseChangeIso (𝟙 X) jC jD a h.flip Λ)
    (moduleInverseImageIdIso Λ X) (moduleLowerShriekCartesianIdentityIso jC jD a h.flip Λ) rfl

/-- The actual refinement unit is the same mixed mate contracted by the original identity. -/
theorem moduleUnboundedDerivedProperRefinementComparison_identitySourceMate :
    IdentitySourceMateEquation
      (moduleUnboundedDerivedAdjunction Λ (𝟙 X)) (moduleUnboundedDerivedAdjunction Λ a)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) jC jD a h.flip Λ).hom)
      (moduleUnboundedDerivedDirectImageIdIso Λ X)
      (moduleUnboundedDerivedProperRefinementComparison jC jD a h Λ) := by
  apply identitySourceMateEquation
    (moduleUnboundedDerivedAdjunction Λ (𝟙 X)) (moduleUnboundedDerivedAdjunction Λ a)
    (moduleUnboundedDerivedInverseImageIdIso Λ X) (moduleUnboundedDerivedDirectImageIdIso Λ X)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ X)
    _ (moduleUnboundedDerivedProperRefinementPullbackIso jC jD a h Λ).hom _
  · intro K
    have hp := congrArg (fun e => e.hom.app K)
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_identity_source jC jD a h Λ)
    change _ = _ ≫ _ ≫ 𝟙 _ at hp
    rw [Category.comp_id] at hp
    exact hp
  · exact moduleUnboundedDerivedProperRefinementComparison_app jC jD a h Λ
end AlgebraicGeometry.Scheme.EtaleCohomology
