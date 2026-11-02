/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAdjunctionComposition
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # The original exact lower-shriek compositor retains its actual adjunction mate -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wT

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Exact localization preserves the original conjugacy, with three independent models. -/
theorem conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    conjugateEquiv ((moduleUnboundedDerivedLowerShriekAdjunction g Λ).comp
        (moduleUnboundedDerivedLowerShriekAdjunction f Λ))
      (moduleUnboundedDerivedLowerShriekAdjunction (g ≫ f) Λ)
      (moduleUnboundedDerivedLowerShriekCompIso Λ f g).hom =
      (moduleUnboundedDerivedInverseImageCompIso Λ f g).inv :=
  Adjunction.mapDerivedCategory_conjugate_comp
    (moduleLowerShriekAdjunction g Λ) (moduleLowerShriekAdjunction f Λ)
    (moduleLowerShriekAdjunction (g ≫ f) Λ)
    (moduleLowerShriekCompIso Λ f g) (moduleInverseImageCompIso Λ f g).symm
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      (moduleLowerShriekAdjunction (g ≫ f) Λ)
      ((moduleLowerShriekAdjunction g Λ).comp (moduleLowerShriekAdjunction f Λ))
      (moduleInverseImageCompIso Λ f g))

end AlgebraicGeometry.Scheme.EtaleCohomology
