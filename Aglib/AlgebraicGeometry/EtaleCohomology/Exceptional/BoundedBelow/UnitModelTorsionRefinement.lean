/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion

/-! # Original mixed refinement transitions between individual torsion-valued models -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))

/-- The same original mixed refinement isomorphism with only torsion properties recorded. -/
def moduleCompactificationSingleTorsionTransition :
    moduleCompactificationSingleTorsionValue Λ D hD ≅
      moduleCompactificationSingleTorsionValue Λ C hC :=
  (moduleTorsionCohomologyPlus S Λ).liftFunctorIso _ _
    (moduleCompactificationSingleValue_torsion Λ D hD)
    (moduleCompactificationSingleValue_torsion Λ C hC)
    (@asIso _ _ _ _
      (@moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD)
      (@moduleCompactificationMixedTransition_isIso X S f _ Λ _ hX hS C D a hC hD))

/-- The native lift keeps the exact original refinement morphism. -/
theorem moduleCompactificationSingleTorsionTransition_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactificationSingleTorsionTransition Λ a hC hD).hom.app K).hom =
      (@moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD).app K := rfl

variable (f)
  [models : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf E.Xbar Λ)]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The original chosen comparison satisfies the actual single-model refinement square. -/
theorem moduleExceptionalSingleTorsionValueIso_refinement :
    moduleExceptionalSingleTorsionValueIso f Λ D hD ≪≫
      moduleCompactificationSingleTorsionTransition Λ a hC hD =
    moduleExceptionalSingleTorsionValueIso f Λ C hC := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun τ => τ.app K)
    (moduleExceptionalSingleValueIso_refinement f Λ a hC hD)

end AlgebraicGeometry.Scheme.EtaleCohomology
