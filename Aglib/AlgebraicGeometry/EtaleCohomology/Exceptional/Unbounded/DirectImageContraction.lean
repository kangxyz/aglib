/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.OpenCompositionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence

/-! # The original direct-image triple contraction with actual associativity transport -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB wC
variable (Λ : Type (u + 1)) [Ring Λ]
  {X A B C : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]

/-- Direct-image contraction is the inverse of the original proved compositor associativity. -/
theorem moduleUnboundedDerivedDirectImageContraction_assoc
    (k : X ⟶ A) (m : A ⟶ B) (n : B ⟶ C) :
    OpenCompositionEquation
      (moduleUnboundedDerivedDirectImageCompIso Λ m k).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ n (k ≫ m)).symm
      ((moduleUnboundedDerivedDirectImageCompIso Λ (m ≫ n) k).symm ≪≫
        eqToIso (congrArg (fun q : X ⟶ C => moduleUnboundedDerivedDirectImage Λ q)
          (Category.assoc k m n).symm))
      (moduleUnboundedDerivedDirectImageCompIso Λ n m).symm := by
  exact openCompositionEquation_of_associates
    (eqToIso (congrArg (fun q : X ⟶ C => moduleUnboundedDerivedDirectImage Λ q)
      (Category.assoc k m n).symm))
    (moduleUnboundedDerivedDirectImageCompIso Λ (m ≫ n) k)
    (moduleUnboundedDerivedDirectImageCompIso Λ n m)
    (moduleUnboundedDerivedDirectImageCompIso Λ n (k ≫ m))
    (moduleUnboundedDerivedDirectImageCompIso Λ m k)
    (moduleUnboundedDerivedDirectImageCompIso_assoc Λ n m k)
    _ _ _ _ rfl rfl rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
