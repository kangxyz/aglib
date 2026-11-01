/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-!
# Original bounded-below open extension preserves the torsion range

The native homology comparison of the exact original lower-shriek functor
identifies each derived homology object with the lower shriek of the original
homology object. Preservation of internal torsion therefore holds without a
common annihilator. The source and target derived universes are independent.
This is a range theorem, not a proper-base-change or refinement-isomorphism theorem.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wX

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The actual derived open extension preserves internal torsion in every homology degree. -/
theorem moduleDerivedLowerShriek_preservesTorsionCohomology
    {K : DerivedCategory.Plus (ModuleSheaf U Λ)}
    (hK : moduleTorsionCohomologyPlus U Λ K) :
    moduleTorsionCohomologyPlus X Λ ((moduleDerivedLowerShriek j Λ).obj K) := by
  intro n
  exact moduleIsTorsion_of_iso X Λ
    (((moduleLowerShriek j Λ).rightDerivedFunctorPlusHomologyIso n).app K)
    (moduleIsTorsion_moduleLowerShriek j Λ (hK n))

end AlgebraicGeometry.Scheme.EtaleCohomology
