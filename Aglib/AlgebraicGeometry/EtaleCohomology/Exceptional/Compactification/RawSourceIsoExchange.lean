/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoExchange

/-! # Original source-isomorphism exchange on native torsion inputs -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients


universe u wX wX' wM wS
variable {X X' S : Scheme.{u}} {f : X ⟶ S}
  (e : X' ≅ X) (f' : X' ⟶ S) (h : e.hom ≫ f = f') (C : Hom.Compactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Derived-category instance on module sheaves over `(C.ofSourceIso f' e h).Xbar`, using the
instance on `C.Xbar`.
-/
local instance rawSourceTransportModel :
    HasDerivedCategory.{wM} (ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The actual source-transport isomorphism retains the whole original restriction formula. -/
theorem moduleRawCompactificationSourceIso_restriction :
    SourceIsoRestrictionEquation
      (moduleRawCompactificationSourceIso e Λ f' h C)
      (moduleCompactifiedSourceIso e C.j C.p Λ)
      (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm :=
  sourceIsoRestrictionEquation_factors (moduleDerivedLowerShriekSourceIso e C.j Λ)
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm

/-- The actual compactified source-only square, restricted to the native torsion source. -/
def moduleRawSourceIsoBaseChangeMap :
    moduleRawCompactificationFunctor C Λ ⋙ moduleDerivedInverseImage Λ (𝟙 S) ⟶
      moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleRawCompactificationFunctor (C.ofSourceIso f' e h) Λ :=
  compositeExchange
    (moduleCompactifiedBaseChangeMap C.j C.p (e.hom ≫ C.j) C.p e.hom
      (𝟙 C.Xbar) (𝟙 S) (isPullback_sourceIsoOpen e C.j)
      (isPullback_sourceIsoProperIdentity C.p) Λ)
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm

/-- Source-only raw exchange is exactly the original raw source transport,
normalized by the original base identity comparison. -/
theorem moduleRawSourceIsoBaseChangeMap_identity :
    SourceIsoExchangeEquation (moduleRawSourceIsoBaseChangeMap e f' h C Λ)
      (moduleDerivedInverseImageIdIso Λ S) (moduleRawCompactificationSourceIso e Λ f' h C) :=
  sourceIsoExchange_restrict
    (moduleCompactifiedBaseChangeMap C.j C.p (e.hom ≫ C.j) C.p e.hom
      (𝟙 C.Xbar) (𝟙 S) (isPullback_sourceIsoOpen e C.j)
      (isPullback_sourceIsoProperIdentity C.p) Λ)
    (moduleDerivedInverseImageIdIso Λ S) (moduleCompactifiedSourceIso e C.j C.p Λ)
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm
    (moduleRawCompactificationSourceIso e Λ f' h C)
    (moduleRawCompactificationSourceIso_restriction e f' h C Λ)
    (moduleCompactifiedBaseChangeMap_sourceIso_identity e C.j C.p Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
