/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquareComposite

/-! # The original unbounded inverse-image square in compositor form -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The localized original square is exactly the original structural composite. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_eq_comp :
    moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h =
      (moduleUnboundedDerivedInverseImageCompIso Λ g f').symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => moduleUnboundedDerivedInverseImage Λ k) h) ≪≫
        moduleUnboundedDerivedInverseImageCompIso Λ f g' := by
  exact Functor.mapDerivedCategorySquareIso_compositors
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (moduleInverseImage (f' ≫ g) Λ) (moduleInverseImage (g' ≫ f) Λ)
    (moduleInverseImageCompIso Λ g f') (moduleInverseImageCompIso Λ f g')
    (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
