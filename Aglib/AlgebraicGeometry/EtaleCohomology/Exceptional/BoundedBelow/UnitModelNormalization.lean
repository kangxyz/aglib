/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsionRefinement

/-! # The single-model comparison specializes to the unchanged canonical comparison -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- With the original model, the original mixed identity transition is the identity. -/
theorem moduleCompactificationSingleModelIso_self (C : Hom.DenseCompactification f) :
    moduleCompactificationSingleModelIso f Λ C (models C) = Iso.refl _ := by
  apply Iso.ext
  exact @moduleCompactificationTransition_id X S f _ Λ _ hX hS models C

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The ambient single-value comparison specializes to the original chosen comparison. -/
theorem moduleExceptionalSingleValueIso_self (C : Hom.DenseCompactification f) :
    moduleExceptionalSingleValueIso f Λ C (models C) =
      moduleExceptionalDirectImagePlusIso f Λ C := by
  rw [moduleExceptionalSingleValueIso, moduleCompactificationSingleModelIso_self]
  exact Iso.trans_refl (moduleExceptionalDirectImagePlusIso f Λ C)

/-- The native torsion lift also retains the unchanged canonical comparison. -/
theorem moduleExceptionalSingleTorsionValueIso_self (C : Hom.DenseCompactification f) :
    moduleExceptionalSingleTorsionValueIso f Λ C (models C) =
      moduleExceptionalDirectImagePlusTorsionIso f Λ C := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun e => e.hom.app K) (moduleExceptionalSingleValueIso_self f Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
