/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeIdentityTransition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeNaturality

/-! # Original raw identity exchange compared with actual source transport -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wR
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

local instance rawIdentityModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
local instance rawIdentityTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original raw transition along the actual identity-pullback projection. -/
def moduleIdentityRawProjectionTransition :=
  moduleRawCompactificationTransition
    (C.toCompactification.baseChange (𝟙 S))
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
    (pullback.snd (𝟙 S) C.p)
    (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (Hom.DenseCompactification.identityRawProjection_p C) Λ

/-- The original refinement/base-change square compares the raw identity
pullback with the source-transported original model. -/
theorem moduleRawIdentityBaseChange_naturality :
    Functor.whiskerRight
      (moduleRawCompactificationTransition C.toCompactification C.toCompactification
        (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
        (Category.id_comp C.p) Λ)
      (moduleDerivedInverseImage Λ (𝟙 S)) ≫
      (moduleRawCompactificationBaseChangeIso C.toCompactification (𝟙 S) Λ).hom =
    moduleRawSourceIsoBaseChangeMap (Hom.DenseCompactification.identitySourceIso f)
        (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
        C.toCompactification Λ ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ)
        (moduleIdentityRawProjectionTransition C Λ) := by
  have hc := moduleCompactifiedBaseChangeMap_refinement_naturality
    C.j C.j (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
    (C.toCompactification.baseChange (𝟙 S)).j
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).j
    (pullback.snd (𝟙 S) C.p)
    (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (pullback.snd (𝟙 S) f) (pullback.snd (𝟙 S) C.p) (𝟙 C.Xbar)
    (isPullback_rawCompactificationOpen C.toCompactification (𝟙 S))
    (isPullback_sourceIsoOpen (Hom.DenseCompactification.identitySourceIso f) C.j)
    (Hom.DenseCompactification.isPullback_identityRawProjection C) Λ
    C.p C.p (Category.id_comp C.p)
    (pullback.fst (𝟙 S) C.p) C.p
    (Hom.DenseCompactification.identityRawProjection_p C) (𝟙 S)
    (IsPullback.of_hasPullback (𝟙 S) C.p).flip
    (isPullback_sourceIsoProperIdentity C.p)
  exact compositeExchange_restriction_naturality _ _
    (moduleDerivedInverseImageTorsionForgetIso (pullback.snd (𝟙 S) f) Λ).symm _ _ hc

end AlgebraicGeometry.Scheme.EtaleCohomology
