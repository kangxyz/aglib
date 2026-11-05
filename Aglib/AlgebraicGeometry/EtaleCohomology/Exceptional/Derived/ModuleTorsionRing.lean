/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange

/-! # The original bounded-below torsion range over a torsion ring -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- A positive annihilator of the ring unit places every original bounded-below
module complex in the original torsion-cohomology range. -/
theorem moduleTorsionCohomologyPlus_of_nsmul_one_eq_zero
    (n : ℕ) (hn : 0 < n) (hΛ : n • (1 : Λ) = 0)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    moduleTorsionCohomologyPlus X Λ K :=
  moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ n hn hΛ K.obj

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
