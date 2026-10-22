/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # Whole original comparisons in two formal coordinate systems -/

@[expose] public noncomputable section
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

/-- Preserve the specified target comparison and every original stage comparison. -/
def CandidateIsoTransportComparison
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I J : X.IdealSheafData}
    {F₁ : AdicSystem X I} {F₂ : AdicSystem X J}
    {H₁ H₂ G₁ G₂ : X.CoherentSheaf}
    (eF : F₁.obj ≅ F₂.obj) (eH : H₁ ≅ H₂)
    (a₁ : G₁ ⟶ H₁) (β₁ : (completionFunctor X I).obj G₁ ≅ F₁)
    (a₂ : G₂ ⟶ H₂) (β₂ : (completionFunctor X J).obj G₂ ≅ F₂) :=
    {e : G₁ ≅ G₂ // e.hom ≫ a₂ = a₁ ≫ eH.hom ∧ ∀ n : ℕ,
      e.hom.hom ≫ (idealSheafQuotientUnit X (J ^ n)).app G₂.obj ≫
        β₂.hom.hom.app (op n) =
      (idealSheafQuotientUnit X (I ^ n)).app G₁.obj ≫ β₁.hom.hom.app (op n) ≫
        eF.hom.app (op n)}

end AlgebraicGeometry.Scheme.Modules.Coherent
