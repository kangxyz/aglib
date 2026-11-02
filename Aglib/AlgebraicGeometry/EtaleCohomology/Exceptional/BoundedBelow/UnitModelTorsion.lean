/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion

/-! # The original single-model comparison in the native torsion subcategory -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  (C : Hom.DenseCompactification f)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))

/-- Torsion output follows from the original preservation laws. -/
theorem moduleCompactificationSingleValue_torsion
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    moduleTorsionCohomologyPlus S Λ
      ((@moduleCompactificationValue X S f Λ _ hX hS C hC).obj K) := by
  let : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ) := hC
  exact moduleDerivedDirectImage_preservesTorsionCohomology C.p Λ
    ((moduleDerivedLowerShriek C.j Λ).obj K.obj)
    (moduleDerivedLowerShriek_preservesTorsionCohomology C.j Λ K.property)

/-- The unchanged original value with only its target property recorded. -/
def moduleCompactificationSingleTorsionValue :=
  (moduleTorsionCohomologyPlus S Λ).lift
    (@moduleCompactificationValue X S f Λ _ hX hS C hC)
    (moduleCompactificationSingleValue_torsion Λ C hC)

variable (f) [QuasiCompact f]
  [models : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf E.Xbar Λ)]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The canonical single-value comparison retains its original components after native lifting. -/
def moduleExceptionalSingleTorsionValueIso :
    @moduleExceptionalDirectImagePlusTorsion X S f _ Λ _ hX hS _ _ _ _
        (models (moduleExceptionalCompactification f)) ≅
      moduleCompactificationSingleTorsionValue Λ C hC :=
  NatIso.ofComponents (fun K => (moduleTorsionCohomologyPlus S Λ).isoMk
    ((moduleExceptionalSingleValueIso f Λ C hC).app K)) (by
      intro K K' a
      apply ObjectProperty.hom_ext
      exact (moduleExceptionalSingleValueIso f Λ C hC).hom.naturality a)

/-- No new morphism is introduced by recording the torsion property. -/
theorem moduleExceptionalSingleTorsionValueIso_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleExceptionalSingleTorsionValueIso f Λ C hC).hom.app K).hom =
      (moduleExceptionalSingleValueIso f Λ C hC).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
