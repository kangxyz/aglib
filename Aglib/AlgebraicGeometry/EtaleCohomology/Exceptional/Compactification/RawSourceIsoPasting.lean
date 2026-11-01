/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoMapPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionForgetCoherence

/-! # Original source-only pasting on native torsion-source raw models -/

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

local instance rawPastingTransportModel :
    HasDerivedCategory.{wD} (ModuleSheaf (D.ofSourceIso f₂ e hf₂).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))

/-- The native torsion compositor identifies the original exchange to the
source-transported raw model with the original raw source-isomorphism comparison. -/
theorem moduleRawSquareMap_sourceIso_pasting :
    CompactifiedSourceIsoPastingEquation
      (moduleRawSquareMap C D a q b hj hp Λ)
      (moduleRawSquareMap C (D.ofSourceIso f₂ e hf₂) (e.hom ≫ a) q b hj' hp Λ)
      (moduleDerivedInverseImageTorsionCompIso Λ a e.hom)
      (moduleRawCompactificationSourceIso e Λ f₂ hf₂ D) :=
  sourceIsoPasting_restrict
    (moduleCompactifiedBaseChangeMap C.j C.p D.j D.p a q b hj hp Λ)
    (moduleCompactifiedBaseChangeMap C.j C.p (e.hom ≫ D.j) D.p (e.hom ≫ a) q b hj' hp Λ)
    (moduleCompactifiedSourceIso e D.j D.p Λ) (moduleDerivedInverseImageCompIso Λ a e.hom)
    (moduleDerivedInverseImageTorsionForgetIso a Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso (e.hom ≫ a) Λ).symm
    (moduleDerivedInverseImageTorsionCompIso Λ a e.hom)
    (moduleRawCompactificationSourceIso e Λ f₂ hf₂ D)
    (moduleRawCompactificationSourceIso_restriction e f₂ hf₂ D Λ)
    (moduleCompactifiedBaseChangeMap_sourceIso_pasting C.j C.p D.j D.p a q b e hj hp hj' Λ)
    (moduleDerivedInverseImageTorsionForgetIso_pasting Λ a e.hom)

end AlgebraicGeometry.Scheme.EtaleCohomology
