/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.TargetModelDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ModelComparisonTorsion

/-! # Canonical target-model comparison of the chosen exceptional direct image -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS₀ wS₁ wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The chosen ambient exceptional functor commutes with canonical native target transport. -/
def moduleExceptionalTargetComparison :
    (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₀ (models
      (moduleExceptionalSuppliedCompactification f))) ⋙
        (canonicalEquivalence hS₀ hS₁).functor ≅
      (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₁ (models
        (moduleExceptionalSuppliedCompactification f))) :=
  moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models
    (moduleExceptionalSuppliedCompactification f)

/-- This same chosen target transport is computed through every original compactification. -/
theorem moduleExceptionalTargetComparison_model (C : Hom.DenseCompactification f) :
    moduleExceptionalTargetComparison f Λ hX hS₀ hS₁ models ≪≫
        @moduleExceptionalDirectImagePlusOfNonemptyIso X S f _ _ Λ _ hX hS₁ models C =
      Functor.isoWhiskerRight
        (@moduleExceptionalDirectImagePlusOfNonemptyIso X S f _ _ Λ _ hX hS₀ models C)
          (canonicalEquivalence hS₀ hS₁).functor ≪≫
        moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models C :=
  moduleCompactificationTargetComparison_canonical f Λ hX hS₀ hS₁ models
    (moduleExceptionalSuppliedCompactification f) C

/-- The same original target transport, lifted without changing its components. -/
def moduleExceptionalTorsionTargetComparison :
    (@moduleExceptionalDirectImagePlusTorsionOfNonempty X S f _ Λ _ hX hS₀ (models
      (moduleExceptionalSuppliedCompactification f))) ⋙
        moduleModelComparisonTorsion S Λ hS₀ hS₁ ≅
      (@moduleExceptionalDirectImagePlusTorsionOfNonempty X S f _ Λ _ hX hS₁ (models
        (moduleExceptionalSuppliedCompactification f))) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk (@moduleTorsionCohomologyPlus S Λ _ hS₁)
      ((moduleExceptionalTargetComparison f Λ hX hS₀ hS₁ models).app K))
    (by
      intro K L a
      apply ObjectProperty.hom_ext
      exact (moduleExceptionalTargetComparison f Λ hX hS₀ hS₁ models).hom.naturality a)

omit [QuasiCompact f] in
/-- Forgetting torsion retains the actual canonical target-model comparison component. -/
theorem moduleExceptionalTorsionTargetComparison_hom_app
    (K : (@moduleTorsionCohomologyPlus X Λ _ hX).FullSubcategory) :
    ((moduleExceptionalTorsionTargetComparison f Λ hX hS₀ hS₁ models).hom.app K).hom =
      (moduleExceptionalTargetComparison f Λ hX hS₀ hS₁ models).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
