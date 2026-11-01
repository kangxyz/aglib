/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoBeforeExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoPasting

/-! # Native source transport before an arbitrary original raw exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX₀ wX₁ wX₂ wS wT wM wN
variable {X₀ X₁ X₂ S T : Scheme.{u}} {f₀ : X₀ ⟶ S} {f₂ : X₂ ⟶ T}
  (C : Hom.Compactification f₀) (e : X₁ ≅ X₀) (f₁ : X₁ ⟶ S)
  (hf₁ : e.hom ≫ f₀ = f₁) (D : Hom.Compactification f₂)
  (a : X₂ ⟶ X₁) (q : D.Xbar ⟶ C.Xbar) (b : T ⟶ S)
  (hj : IsPullback a D.j (e.hom ≫ C.j) q)
  (ht : IsPullback (a ≫ e.hom) D.j C.j q) (hp : IsPullback q D.p C.p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

/-- Derived-category instance on module sheaves over `(C.ofSourceIso f₁ e hf₁).Xbar`, using the
instance on `C.Xbar`.
-/
local instance rawSourceBeforeTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf (C.ofSourceIso f₁ e hf₁).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original raw source transport followed by an original raw exchange is the
original composite-source raw exchange, on the unchanged native torsion input. -/
theorem moduleRawSquareMap_sourceIso_before :
    SourceIsoBeforeExchangeEquation (moduleRawCompactificationSourceIso e Λ f₁ hf₁ C)
      (moduleRawSquareMap (C.ofSourceIso f₁ e hf₁) D a q b hj hp Λ)
      (moduleRawSquareMap C D (a ≫ e.hom) q b ht hp Λ)
      (moduleDerivedInverseImageTorsionCompIso Λ e.hom a) :=
  sourceIsoBefore_restrict (moduleCompactifiedSourceIso e C.j C.p Λ)
    (moduleCompactifiedBaseChangeMap (e.hom ≫ C.j) C.p D.j D.p a q b hj hp Λ)
    (moduleCompactifiedBaseChangeMap C.j C.p D.j D.p (a ≫ e.hom) q b ht hp Λ)
    (moduleDerivedInverseImageCompIso Λ e.hom a)
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso a Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso (a ≫ e.hom) Λ).symm
    (moduleDerivedInverseImageTorsionCompIso Λ e.hom a)
    (moduleRawCompactificationSourceIso e Λ f₁ hf₁ C)
    (moduleRawCompactificationSourceIso_restriction e f₁ hf₁ C Λ)
    (moduleCompactifiedBaseChangeMap_sourceIso_before C.j C.p e D.j D.p a q b hj ht hp Λ)
    (moduleDerivedInverseImageTorsionForgetIso_pasting Λ e.hom a)

end AlgebraicGeometry.Scheme.EtaleCohomology
