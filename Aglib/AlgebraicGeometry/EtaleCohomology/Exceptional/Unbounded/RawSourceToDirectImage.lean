/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageSourceTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactifiedToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawToDirectImage

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

/-- The local derived-category model on `ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ`. -/
local instance unboundedRawSourceComparisonModel :
    HasDerivedCategory.{wM} (ModuleSheaf (C.ofSourceIso f' e h).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The actual raw source isomorphism preserves the same canonical comparison. -/
theorem moduleUnboundedRawCompactificationSourceIso_toDirectImage :
    TargetComparisonEquation (moduleUnboundedRawCompactificationSourceIso e Λ f' h C).hom
      (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
        (moduleUnboundedRawCompactificationToDirectImage (C.ofSourceIso f' e h) Λ))
      (moduleUnboundedRawCompactificationToDirectImage C Λ ≫
        moduleUnboundedDirectImageSourceTransport f f' e h Λ) := by
  apply sourceIso_toTarget
    (moduleUnboundedRawCompactificationToDirectImage C Λ)
    (moduleUnboundedRawCompactificationToDirectImage (C.ofSourceIso f' e h) Λ)
    (moduleUnboundedRawSourceIsoBaseChangeMap e f' h C Λ)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' (𝟙 S) e.hom
      ((Category.comp_id f').trans h.symm))
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedRawCompactificationSourceIso e Λ f' h C)
    (moduleUnboundedRawSourceIsoBaseChangeMap_identity e f' h C Λ)
  exact moduleUnboundedCompactifiedBaseChangeMap_toDirectImage
    C.j C.p (e.hom ≫ C.j) C.p f f' C.fac (C.ofSourceIso f' e h).fac
    e.hom (𝟙 C.Xbar) (𝟙 S) (isPullback_sourceIsoOpen e C.j)
    (isPullback_sourceIsoProperIdentity C.p) ((Category.comp_id f').trans h.symm) Λ
end AlgebraicGeometry.Scheme.EtaleCohomology
