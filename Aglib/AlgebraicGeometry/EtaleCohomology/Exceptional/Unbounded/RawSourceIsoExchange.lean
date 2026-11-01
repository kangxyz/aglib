/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoExchange

/-! # Original source-isomorphism exchange on all unbounded inputs -/

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

/-- The derived-category instance in universe `wM` for `Λ`-module sheaves on `(C.ofSourceIso f' e
    h).Xbar`.
-/
local instance unboundedRawSourceTransportModel :
    HasDerivedCategory.{wM} (ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The actual compactified source-only square on the full unbounded category. -/
def moduleUnboundedRawSourceIsoBaseChangeMap :
    moduleUnboundedRawCompactificationFunctor C Λ ⋙ moduleUnboundedDerivedInverseImage Λ (𝟙 S) ⟶
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        moduleUnboundedRawCompactificationFunctor (C.ofSourceIso f' e h) Λ :=
  moduleUnboundedCompactifiedBaseChangeMap C.j C.p (e.hom ≫ C.j) C.p e.hom
    (𝟙 C.Xbar) (𝟙 S) (isPullback_sourceIsoOpen e C.j)
    (isPullback_sourceIsoProperIdentity C.p) Λ

/-- Source-only raw exchange is exactly the original raw source transport,
normalized by the original base identity comparison. -/
theorem moduleUnboundedRawSourceIsoBaseChangeMap_identity :
    SourceIsoExchangeEquation (moduleUnboundedRawSourceIsoBaseChangeMap e f' h C Λ)
      (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedRawCompactificationSourceIso e Λ f' h C) :=
  moduleUnboundedCompactifiedBaseChangeMap_sourceIso_identity e C.j C.p Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
