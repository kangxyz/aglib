/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceBCNormalization
public import Aglib.CategoryTheory.NatTrans.SourceBeforeNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoNaturality

/-! # Normalized source-isomorphism/base-change interchange through the original maps -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wX' wL wL' wS wT wM wR wN wN'
variable {X X' S T : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (b : T ⟶ S) (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wL'} (ModuleSheaf (pullback b f') Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wN'} (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ)]

local instance unboundedNormalizedSourceBCSourceModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((sourceIso f' e he).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance unboundedNormalizedSourceBCRawSourceModel : HasDerivedCategory.{wM}
    (ModuleSheaf (C.toCompactification.ofSourceIso f' e he).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance unboundedNormalizedSourceBCRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance unboundedNormalizedSourceBCRawActualModel : HasDerivedCategory.{wR}
    (ModuleSheaf (((sourceIso f' e he).obj C).toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance unboundedNormalizedSourceBCNativeActualModel : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback b ((sourceIso f' e he).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance unboundedNormalizedSourceBCRawTransportModel : HasDerivedCategory.{wR}
    (ModuleSheaf (sourceBaseChangeTransportModel f f' e he b C.toCompactification).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance unboundedNormalizedSourceBCDensificationModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance unboundedNormalizedSourceBCTransportModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance unboundedNormalizedSourceBCActualDensificationModel : HasDerivedCategory.{wN'}
    (ModuleSheaf (Hom.Compactification.densify
      (((sourceIso f' e he).obj C).toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ))

local instance unboundedNormalizedSourceBCOriginalBaseChangeObj : HasDerivedCategory.{wN}
    (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance unboundedNormalizedSourceBCActualBaseChangeObj : HasDerivedCategory.{wN'}
    (ModuleSheaf (baseChangeObj b ((sourceIso f' e he).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ))

/-- The original composite raw exchange followed by its actual final normalization. -/
def moduleUnboundedNormalizedSourceBCCompositeMap :=
  moduleUnboundedRawSourceBaseChangeCompositeMap f f' e he b C.toCompactification Λ ≫
    Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f' ≫ e.hom))
      (moduleUnboundedCompactificationDensificationMap
        (((sourceIso f' e he).obj C).toCompactification.baseChange b) Λ)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- Source first, then normalized base change, is the original normalized composite map. -/
theorem moduleUnboundedNormalizedSourceBC_before :
    SourceIsoBeforeExchangeEquation
      (moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification)
      (moduleUnboundedNormalizedCompactificationBaseChangeIso ((sourceIso f' e he).obj C) b Λ N hN
        hΛ).hom
      (moduleUnboundedNormalizedSourceBCCompositeMap f' e he b C Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ e.hom (pullback.snd b f')) :=
  sourceIsoBeforeExchange_normalize _ _ _ _ _ _ _
    (moduleUnboundedRawSourceBaseChange_before f f' e he b C.toCompactification Λ N hN hΛ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom ((sourceIso f' e he).obj C) b Λ N
      hN hΛ) rfl

omit [QuasiCompact f']
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ)] in
/-- Source transport is natural for the original normalization map, including the
unchanged source-transported native middle model. -/
theorem moduleUnboundedNormalizedSourceBC_source_naturality :
    SourceIsoNaturalityEquation
      (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
      (moduleUnboundedSourceBCTransportNormalizationMap f' e he b C Λ)
      (moduleUnboundedRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        ((baseChange b).obj C).toCompactification)
      (moduleUnboundedRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        (C.toCompactification.baseChange b)) :=
  moduleUnboundedRawCompactificationSourceIso_refinement_naturality
    (pullbackSourceIso f' e he b) (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
    ((baseChange b).obj C).toCompactification (C.toCompactification.baseChange b)
    (baseChangeNormalization b C) (Hom.Compactification.isPullback_densify _)
    (sourceBCTransportNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b C) Λ

omit [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)] in
/-- Base change first, then the actual normalized source comparison and refinement,
also gives the same original normalized composite map. -/
theorem moduleUnboundedNormalizedSourceBC_after :
    RefinedSourceIsoPastingEquation (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ
      N hN hΛ).hom
      (moduleUnboundedNormalizedSourceBCCompositeMap f' e he b C Λ)
      (moduleUnboundedRawSourceBaseChangeSourceIso f f' e he b Λ)
      (moduleUnboundedRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        ((baseChange b).obj C).toCompactification)
      (moduleUnboundedSourceBCNormalizedTransition f' e he b C Λ) :=
  refinedSourceIsoPastingEquation_normalize _ _ _ _ _ _ _ _ _ _ _ _
    (moduleUnboundedRawSourceBaseChange_after f f' e he b C.toCompactification Λ N hN hΛ)
    (moduleUnboundedNormalizedSourceBC_source_naturality f' e he b C Λ)
    ((moduleUnboundedSourceBCNormalization_raw_triangle f' e he b C Λ).trans
      (moduleUnboundedSourceBCNormalization_dense_triangle f' e he b C Λ).symm)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom C b Λ N hN hΛ) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
