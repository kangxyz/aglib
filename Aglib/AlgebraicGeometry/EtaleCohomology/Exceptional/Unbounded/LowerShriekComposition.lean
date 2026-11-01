/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleComposition

/-! # Exact deriving of the original lower-shriek structural comparisons -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wT

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original identity comparison localized on all complexes. -/
def moduleUnboundedDerivedLowerShriekIdIso (X : Scheme.{u})
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    moduleUnboundedDerivedLowerShriek (𝟙 X) Λ ≅ 𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  Functor.mapDerivedCategoryOriginalIso (moduleLowerShriek (𝟙 X) Λ) (𝟭 _)
    (moduleLowerShriekIdIso Λ X) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The original exact compositor with independent source, middle and target models. -/
def moduleUnboundedDerivedLowerShriekCompIso {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) [Etale f] [Etale g]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    moduleUnboundedDerivedLowerShriek (g ≫ f) Λ ≅
      moduleUnboundedDerivedLowerShriek g Λ ⋙ moduleUnboundedDerivedLowerShriek f Λ :=
  Functor.mapDerivedCategoryCompositeIso (moduleLowerShriek g Λ)
    (moduleLowerShriek f Λ) (moduleLowerShriek (g ≫ f) Λ)
    (moduleLowerShriekCompIso Λ f g)

end AlgebraicGeometry.Scheme.EtaleCohomology
