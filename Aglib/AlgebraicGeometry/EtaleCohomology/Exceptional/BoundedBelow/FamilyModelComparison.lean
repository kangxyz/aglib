/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.FamilyModelDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion

/-! # Coherent original family transport for the torsion-valued exceptional functor

The map is the original mixed-model identity refinement transition. The native
full-subcategory lift changes neither its carrier nor its components. Actual
canonical compactification comparisons commute with this same map.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wM₂
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))

/-- The original coherent family comparison in the native torsion subcategory. -/
def moduleCompactificationTorsionFamilyComparison (C : Hom.DenseCompactification f) :
    (@moduleCompactificationTorsionFunctor X S f Λ _ hX hS C (models₀ C)) ≅
      (@moduleCompactificationTorsionFunctor X S f Λ _ hX hS C (models₁ C)) :=
  (@moduleTorsionCohomologyPlus S Λ _ hS).liftFunctorIso _ _
    (@moduleCompactificationFunctor_torsion X S f Λ _ hX hS C (models₀ C))
    (@moduleCompactificationFunctor_torsion X S f Λ _ hX hS C (models₁ C))
    (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C)

/-- The torsion lift retains the literal original mixed-model refinement component. -/
theorem moduleCompactificationTorsionFamilyComparison_hom_app
    (C : Hom.DenseCompactification f)
    (K : (@moduleTorsionCohomologyPlus X Λ _ hX).FullSubcategory) :
    ((moduleCompactificationTorsionFamilyComparison f Λ hX hS models₀ models₁ C).hom.app K).hom =
      (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C).hom.app K := rfl

/-- The lifted original family comparison retains the canonical compactification square. -/
theorem moduleCompactificationTorsionFamilyComparison_canonical
    (C D : Hom.DenseCompactification f) :
    moduleCompactificationTorsionFamilyComparison f Λ hX hS models₀ models₁ C ≪≫
        (@moduleCompactificationTorsionComparison X S f _ Λ _ hX hS models₁ C D) =
      (@moduleCompactificationTorsionComparison X S f _ Λ _ hX hS models₀ C D) ≪≫
        moduleCompactificationTorsionFamilyComparison f Λ hX hS models₀ models₁ D := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun e => e.hom.app K)
    (moduleCompactificationFamilyComparison_canonical f Λ hX hS models₀ models₁ C D)

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The original chosen exceptional functor changes middle families by the coherent
identity refinement, not by a newly chosen isomorphism. -/
def moduleExceptionalDirectImagePlusTorsionFamilyComparison :
    (@moduleExceptionalDirectImagePlusTorsion X S f _ Λ _ hX hS
      _ _ _ _ (models₀ (moduleExceptionalCompactification f))) ≅
      (@moduleExceptionalDirectImagePlusTorsion X S f _ Λ _ hX hS
      _ _ _ _ (models₁ (moduleExceptionalCompactification f))) :=
  moduleCompactificationTorsionFamilyComparison f Λ hX hS models₀ models₁
    (moduleExceptionalCompactification f)

/-- Every specified compactification computes the same original chosen-family comparison. -/
theorem moduleExceptionalDirectImagePlusTorsionFamilyComparison_model
    (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusTorsionFamilyComparison f Λ hX hS models₀ models₁ ≪≫
        (@moduleExceptionalDirectImagePlusTorsionIso X S f _ Λ _ hX hS _ _ _ _ models₁ C) =
      (@moduleExceptionalDirectImagePlusTorsionIso X S f _ Λ _ hX hS _ _ _ _ models₀ C) ≪≫
        moduleCompactificationTorsionFamilyComparison f Λ hX hS models₀ models₁ C :=
  moduleCompactificationTorsionFamilyComparison_canonical f Λ hX hS models₀ models₁
    (moduleExceptionalCompactification f) C

end AlgebraicGeometry.Scheme.EtaleCohomology
