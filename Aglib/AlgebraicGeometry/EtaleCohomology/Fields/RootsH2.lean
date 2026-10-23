/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GmH2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CohomologyConsequences
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.LocalRing

/-! # Original degree-two root cohomology over algebraic function fields

The original Kummer long exact sequence combines local Picard triviality with
the proved original multiplicative degree-two vanishing. The invertibility
condition is retained literally on the spectrum's global sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

variable (K E : Type u) [Field K] [IsAlgClosed K] [Field E]
  [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

include K

/-- Original degree-two cohomology of every positive invertible root sheaf
vanishes over an algebraic function field in one variable. -/
theorem rootsH2_subsingleton_of_algebraic_ratFunc
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of E), ⊤))) :
    Subsingleton (Sheaf.H.{w} (mu (Spec (.of E)) n) 2) := by
  apply Kummer.roots_subsingleton_of_power_surjective_injective
    (Spec (.of E)) n hn hinv 1
  · intro a
    exact ⟨a, (Picard.gmH1_subsingleton_of_isLocalRing (CommRingCat.of E)).elim _ _⟩
  · intro a b _
    exact (gmH2_eq_zero_of_algebraic_ratFunc K E a).trans
      (gmH2_eq_zero_of_algebraic_ratFunc K E b).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
