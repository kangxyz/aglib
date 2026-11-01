/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoExchange
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality

/-! # The actual source-isomorphism comparison respects original refinements -/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wU' wC wD wS

variable {U U' C D S : Scheme.{u}}
  (e : U' ≅ U) (jC : U ⟶ C) (jD : U ⟶ D) (h : C ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD]
  (sq : IsPullback jC (𝟙 U) h jD)
  (sq' : IsPullback (e.hom ≫ jC) (𝟙 U') h (e.hom ≫ jD))
  (pC : C ⟶ S) (pD : D ⟶ S) (hp : h ≫ pD = pC)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original source transport intertwines the original proper-refinement
unit comparisons and the original over-base direct-image compositors. -/
theorem moduleCompactifiedSourceIso_refinement_naturality :
    SourceIsoNaturalityEquation
      (imageComparison (moduleDerivedProperRefinementComparison jC jD h sq Λ)
        (moduleDerivedDirectImageOverIso Λ pC pD h hp))
      (imageComparison
        (moduleDerivedProperRefinementComparison (e.hom ≫ jC) (e.hom ≫ jD) h sq' Λ)
        (moduleDerivedDirectImageOverIso Λ pC pD h hp))
      (moduleCompactifiedSourceIso e jC pC Λ) (moduleCompactifiedSourceIso e jD pD Λ) :=
  sourceIsoNaturality_of_exchange _ _
    (moduleCompactifiedBaseChangeMap jC pC (e.hom ≫ jC) pC e.hom (𝟙 C) (𝟙 S)
      (isPullback_sourceIsoOpen e jC) (isPullback_sourceIsoProperIdentity pC) Λ)
    (moduleCompactifiedBaseChangeMap jD pD (e.hom ≫ jD) pD e.hom (𝟙 D) (𝟙 S)
      (isPullback_sourceIsoOpen e jD) (isPullback_sourceIsoProperIdentity pD) Λ)
    (moduleDerivedInverseImageIdIso Λ S)
    (moduleCompactifiedSourceIso e jC pC Λ) (moduleCompactifiedSourceIso e jD pD Λ)
    (moduleCompactifiedBaseChangeMap_sourceIso_identity e jC pC Λ)
    (moduleCompactifiedBaseChangeMap_sourceIso_identity e jD pD Λ)
    (moduleCompactifiedBaseChangeMap_refinement_naturality
      jC jD h sq (e.hom ≫ jC) (e.hom ≫ jD) h sq'
      e.hom (𝟙 C) (𝟙 D)
      (isPullback_sourceIsoOpen e jC) (isPullback_sourceIsoOpen e jD)
      (isPullback_sourceIsoProperIdentity h) Λ pC pD hp pC pD hp (𝟙 S)
      (isPullback_sourceIsoProperIdentity pC) (isPullback_sourceIsoProperIdentity pD))

end AlgebraicGeometry.Scheme.EtaleCohomology
