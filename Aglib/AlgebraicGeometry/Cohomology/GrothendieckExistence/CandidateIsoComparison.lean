/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # The whole original target-and-stage comparison type -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- An isomorphism preserving the actual target and every original completion unit. -/
def CandidateIsoComparison {X : Scheme.{u}} [IsLocallyNoetherian X]
    {K : X.IdealSheafData} {F : AdicSystem X K} {H G₁ G₂ : X.CoherentSheaf}
    (a₁ : G₁ ⟶ H) (β₁ : (completionFunctor X K).obj G₁ ≅ F)
    (a₂ : G₂ ⟶ H) (β₂ : (completionFunctor X K).obj G₂ ≅ F) :=
  {e : G₁ ≅ G₂ // e.hom ≫ a₂ = a₁ ∧ ∀ n : ℕ,
    e.hom.hom ≫ (idealSheafQuotientUnit X (K ^ n)).app G₂.obj ≫
      β₂.hom.hom.app (op n) =
    (idealSheafQuotientUnit X (K ^ n)).app G₁.obj ≫ β₁.hom.hom.app (op n)}

end AlgebraicGeometry.Scheme.Modules.Coherent
