/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

/-! # Original raw source transport is natural in arbitrary common-open refinements -/

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

/-- The derived-category instance in universe `wC` for `Λ`-module sheaves on `(C.ofSourceIso f' e
    hf').Xbar`.
-/
local instance unboundedRawNaturalityTransportCModel :
    HasDerivedCategory.{wC} (ModuleSheaf (C.ofSourceIso f' e hf').Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
/-- The derived-category instance in universe `wD` for `Λ`-module sheaves on `(D.ofSourceIso f' e
    hf').Xbar`.
-/
local instance unboundedRawNaturalityTransportDModel :
    HasDerivedCategory.{wD} (ModuleSheaf (D.ofSourceIso f' e hf').Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))

/-- In particular this applies to the original densification transition; both
source transports are the unchanged raw source-isomorphism comparisons. -/
theorem moduleUnboundedRawCompactificationSourceIso_refinement_naturality :
    SourceIsoNaturalityEquation
      (moduleUnboundedRawCompactificationTransition C D h sq hp Λ)
      (moduleUnboundedRawCompactificationTransition (C.ofSourceIso f' e hf')
        (D.ofSourceIso f' e hf') h sq' hp Λ)
      (moduleUnboundedRawCompactificationSourceIso e Λ f' hf' C)
      (moduleUnboundedRawCompactificationSourceIso e Λ f' hf' D) :=
  moduleUnboundedCompactifiedSourceIso_refinement_naturality e C.j D.j h sq sq' C.p D.p hp Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
