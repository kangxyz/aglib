/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoMapPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoExchange

/-! # Original source-only pasting on native full-unbounded raw models -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX₁ wT wD wX₂
variable {X S X₁ T X₂ : Scheme.{u}} {f : X ⟶ S} {f₁ : X₁ ⟶ T}
  (C : Hom.Compactification f) (D : Hom.Compactification f₁)
  (a : X₁ ⟶ X) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (e : X₂ ≅ X₁) (f₂ : X₂ ⟶ T) (hf₂ : e.hom ≫ f₁ = f₂)
  (hj : IsPullback a D.j C.j q) (hp : IsPullback q D.p C.p b)
  (hj' : IsPullback (e.hom ≫ a) (e.hom ≫ D.j) C.j q)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

local instance unboundedRawPastingTransportModel :
    HasDerivedCategory.{wD} (ModuleSheaf (D.ofSourceIso f₂ e hf₂).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))

/-- The native inverse-image compositor identifies the original exchange to the
source-transported raw model with the original raw source-isomorphism comparison. -/
theorem moduleUnboundedRawSquareMap_sourceIso_pasting :
    CompactifiedSourceIsoPastingEquation
      (moduleUnboundedRawSquareMap C D a q b hj hp Λ)
      (moduleUnboundedRawSquareMap C (D.ofSourceIso f₂ e hf₂) (e.hom ≫ a) q b hj' hp Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ a e.hom)
      (moduleUnboundedRawCompactificationSourceIso e Λ f₂ hf₂ D) :=
  moduleUnboundedCompactifiedBaseChangeMap_sourceIso_pasting C.j C.p D.j D.p a q b e hj hp hj' Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
