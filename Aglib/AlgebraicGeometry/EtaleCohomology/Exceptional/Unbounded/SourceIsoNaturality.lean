/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoExchange
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

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
theorem moduleUnboundedCompactifiedSourceIso_refinement_naturality :
    SourceIsoNaturalityEquation
      (imageComparison (moduleUnboundedDerivedProperRefinementComparison jC jD h sq Λ)
        (moduleUnboundedDerivedDirectImageOverIso Λ pC pD h hp))
      (imageComparison
        (moduleUnboundedDerivedProperRefinementComparison (e.hom ≫ jC) (e.hom ≫ jD) h sq' Λ)
        (moduleUnboundedDerivedDirectImageOverIso Λ pC pD h hp))
      (moduleUnboundedCompactifiedSourceIso e jC pC Λ)
    (moduleUnboundedCompactifiedSourceIso e jD pD Λ) :=
  sourceIsoNaturality_of_exchange _ _
    (moduleUnboundedCompactifiedBaseChangeMap jC pC (e.hom ≫ jC) pC e.hom (𝟙 C) (𝟙 S)
      (isPullback_sourceIsoOpen e jC) (isPullback_sourceIsoProperIdentity pC) Λ)
    (moduleUnboundedCompactifiedBaseChangeMap jD pD (e.hom ≫ jD) pD e.hom (𝟙 D) (𝟙 S)
      (isPullback_sourceIsoOpen e jD) (isPullback_sourceIsoProperIdentity pD) Λ)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedCompactifiedSourceIso e jC pC Λ)
    (moduleUnboundedCompactifiedSourceIso e jD pD Λ)
    (moduleUnboundedCompactifiedBaseChangeMap_sourceIso_identity e jC pC Λ)
    (moduleUnboundedCompactifiedBaseChangeMap_sourceIso_identity e jD pD Λ)
    (moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
      jC jD h sq (e.hom ≫ jC) (e.hom ≫ jD) h sq'
      e.hom (𝟙 C) (𝟙 D)
      (isPullback_sourceIsoOpen e jC) (isPullback_sourceIsoOpen e jD)
      (isPullback_sourceIsoProperIdentity h) Λ pC pD hp pC pD hp (𝟙 S)
      (isPullback_sourceIsoProperIdentity pC) (isPullback_sourceIsoProperIdentity pD))

end AlgebraicGeometry.Scheme.EtaleCohomology
