/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FamilyModelComparison

public import Aglib.CategoryTheory.Functor.IsoSquarePostcompose

/-! # Original global family transport commutes with a single supplied value -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wC
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))
  (C : Hom.DenseCompactification f)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))

/-- This is the original three-model identity cocycle at the supplied compactification. -/
theorem moduleCompactificationSingleModelIso_family :
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C ≪≫
      (@moduleCompactificationSingleModelIso X S f _ Λ _ hX hS models₁ C hC) =
    @moduleCompactificationSingleModelIso X S f _ Λ _ hX hS models₀ C hC := by
  apply Iso.ext
  have hc := @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C C (𝟙 C) hC (models₁ C) C (𝟙 C) (models₀ C)
  simp only [Category.id_comp] at hc
  exact hc.symm

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The ambient chosen comparison is natural in the original middle-family transport. -/
theorem moduleExceptionalSingleValueIso_family :
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁
        (moduleExceptionalCompactification f) ≪≫
      (@moduleExceptionalSingleValueIso X S f _ Λ _ hX hS models₁ _ _ _ _ C hC) =
    @moduleExceptionalSingleValueIso X S f _ Λ _ hX hS models₀ _ _ _ _ C hC := by
  exact isoSquarePostcompose
    (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁
      (moduleExceptionalCompactification f))
    (@moduleCompactificationComparison X S f _ Λ _ hX hS models₁
      (moduleExceptionalCompactification f) C)
    (@moduleCompactificationComparison X S f _ Λ _ hX hS models₀
      (moduleExceptionalCompactification f) C)
    (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C)
    (@moduleCompactificationSingleModelIso X S f _ Λ _ hX hS models₁ C hC)
    (@moduleCompactificationSingleModelIso X S f _ Λ _ hX hS models₀ C hC)
    (moduleCompactificationFamilyComparison_canonical f Λ hX hS models₀ models₁
      (moduleExceptionalCompactification f) C)
    (moduleCompactificationSingleModelIso_family f Λ hX hS models₀ models₁ C hC)

/-- The same original square is retained by the native torsion lift. -/
theorem moduleExceptionalSingleTorsionValueIso_family :
    moduleExceptionalDirectImagePlusTorsionFamilyComparison f Λ hX hS models₀ models₁ ≪≫
      (moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
        (models := models₁) f Λ C hC) =
    moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
      (models := models₀) f Λ C hC := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun e => e.hom.app K)
    (moduleExceptionalSingleValueIso_family f Λ hX hS models₀ models₁ C hC)

end AlgebraicGeometry.Scheme.EtaleCohomology
