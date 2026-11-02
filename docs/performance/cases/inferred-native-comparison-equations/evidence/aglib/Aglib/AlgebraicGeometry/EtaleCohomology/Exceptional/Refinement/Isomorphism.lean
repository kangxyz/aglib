/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperIsomorphism
public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare

/-! # The original dense refinement as a common-open specialization

The actual dense refinement supplies its proper map and Cartesian common-open
square to the single general original-unit proof.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u w w₁ w₂

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf D.Xbar Λ)]

/-- The original comparison is invertible using an actual target closed complement. -/
theorem moduleDerivedRefinementComparison_isIso_of_closedComplement
    {Z : Scheme.{u}} (i : Z ⟶ D.Xbar) [IsClosedImmersion i]
    (hcomp : Set.range D.j = (Set.range i)ᶜ)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedRefinementComparison a Λ).app K) :=
  moduleDerivedProperRefinementComparison_isIso_of_closedComplement C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ i hcomp K hK

/-- Proper dense refinement preserves the same original unit comparison on torsion input. -/
theorem moduleDerivedRefinementComparison_isIso
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleTorsionCohomologyPlus X Λ K) :
    IsIso ((moduleDerivedRefinementComparison a Λ).app K) :=
  moduleDerivedProperRefinementComparison_isIso C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ K hK

end AlgebraicGeometry.Scheme.EtaleCohomology
