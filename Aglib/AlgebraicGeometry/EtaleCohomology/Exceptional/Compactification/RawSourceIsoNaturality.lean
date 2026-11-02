/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence

/-! # Native raw source transport commutes with the original refinement transition -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wC wD wS
variable {X X' S : Scheme.{u}} {f : X ⟶ S}
  (e : X' ≅ X) (f' : X' ⟶ S) (hf' : e.hom ≫ f = f')
  (C D : Hom.Compactification f) (h : C.Xbar ⟶ D.Xbar)
  (sq : IsPullback C.j (𝟙 X) h D.j)
  (sq' : IsPullback (e.hom ≫ C.j) (𝟙 X') h (e.hom ≫ D.j))
  (hp : h ≫ D.p = C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Derived-category instance on module sheaves over `(C.ofSourceIso f' e hf').Xbar`, using the
instance on `C.Xbar`.
-/
local instance rawNaturalityTransportCModel :
    HasDerivedCategory.{wC} (ModuleSheaf (C.ofSourceIso f' e hf').Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
/-- Derived-category instance on module sheaves over `(D.ofSourceIso f' e hf').Xbar`, using the
instance on `D.Xbar`.
-/
local instance rawNaturalityTransportDModel :
    HasDerivedCategory.{wD} (ModuleSheaf (D.ofSourceIso f' e hf').Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))

/-- In particular this applies to the original densification transition; both
source transports are the unchanged raw source-isomorphism comparisons. -/
theorem moduleRawCompactificationSourceIso_refinement_naturality :
    SourceIsoNaturalityEquation
      (moduleRawCompactificationTransition C D h sq hp Λ)
      (moduleRawCompactificationTransition (C.ofSourceIso f' e hf')
        (D.ofSourceIso f' e hf') h sq' hp Λ)
      (moduleRawCompactificationSourceIso e Λ f' hf' C)
      (moduleRawCompactificationSourceIso e Λ f' hf' D) :=
  sourceIsoNaturality_restrict
    (imageComparison (moduleDerivedProperRefinementComparison C.j D.j h sq Λ)
      (moduleDerivedDirectImageOverIso Λ C.p D.p h hp))
    (imageComparison
      (moduleDerivedProperRefinementComparison (e.hom ≫ C.j) (e.hom ≫ D.j) h sq' Λ)
      (moduleDerivedDirectImageOverIso Λ C.p D.p h hp))
    (moduleCompactifiedSourceIso e C.j C.p Λ) (moduleCompactifiedSourceIso e D.j D.p Λ)
    (moduleDerivedInverseImageTorsionForgetIso e.hom Λ).symm
    (moduleRawCompactificationSourceIso e Λ f' hf' C)
    (moduleRawCompactificationSourceIso e Λ f' hf' D)
    (moduleRawCompactificationSourceIso_restriction e f' hf' C Λ)
    (moduleRawCompactificationSourceIso_restriction e f' hf' D Λ)
    (moduleCompactifiedSourceIso_refinement_naturality e C.j D.j h sq sq' C.p D.p hp Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
