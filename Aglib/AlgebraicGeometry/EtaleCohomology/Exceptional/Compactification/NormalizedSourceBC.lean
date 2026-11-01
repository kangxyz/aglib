/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceBCNormalization
public import Aglib.CategoryTheory.NatTrans.SourceBeforeNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoNaturality

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

local instance normalizedSourceBCSourceModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((sourceIso f' e he).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance normalizedSourceBCRawSourceModel : HasDerivedCategory.{wM}
    (ModuleSheaf (C.toCompactification.ofSourceIso f' e he).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance normalizedSourceBCRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance normalizedSourceBCRawActualModel : HasDerivedCategory.{wR}
    (ModuleSheaf (((sourceIso f' e he).obj C).toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance normalizedSourceBCNativeActualModel : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback b ((sourceIso f' e he).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance normalizedSourceBCRawTransportModel : HasDerivedCategory.{wR}
    (ModuleSheaf (sourceBaseChangeTransportModel f f' e he b C.toCompactification).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
local instance normalizedSourceBCDensificationModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance normalizedSourceBCTransportModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange b ⋙ pullbackSourceTransport f' e he b).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance normalizedSourceBCActualDensificationModel : HasDerivedCategory.{wN'}
    (ModuleSheaf (Hom.Compactification.densify
      (((sourceIso f' e he).obj C).toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ))

local instance normalizedSourceBCOriginalBaseChangeObj : HasDerivedCategory.{wN}
    (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance normalizedSourceBCActualBaseChangeObj : HasDerivedCategory.{wN'}
    (ModuleSheaf (baseChangeObj b ((sourceIso f' e he).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ))

/-- The original composite raw exchange followed by its actual final normalization. -/
def moduleNormalizedSourceBCCompositeMap :=
  moduleRawSourceBaseChangeCompositeMap f f' e he b C.toCompactification Λ ≫
    Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f' ≫ e.hom) Λ)
      (moduleCompactificationDensificationMap
        (((sourceIso f' e he).obj C).toCompactification.baseChange b) Λ)

omit [QuasiCompact f]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- Source first, then normalized base change, is the original normalized composite map. -/
theorem moduleNormalizedSourceBC_before :
    SourceIsoBeforeExchangeEquation
      (moduleRawCompactificationSourceIso e Λ f' he C.toCompactification)
      (moduleNormalizedCompactificationBaseChangeIso ((sourceIso f' e he).obj C) b Λ).hom
      (moduleNormalizedSourceBCCompositeMap f' e he b C Λ)
      (moduleDerivedInverseImageTorsionCompIso Λ e.hom (pullback.snd b f')) :=
  sourceIsoBeforeExchange_normalize _ _ _ _ _ _ _
    (moduleRawSourceBaseChange_before f f' e he b C.toCompactification Λ)
    (moduleNormalizedCompactificationBaseChangeIso_hom ((sourceIso f' e he).obj C) b Λ) rfl

omit [QuasiCompact f']
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ)] in
/-- Source transport is natural for the original normalization map, including the
unchanged source-transported native middle model. -/
theorem moduleNormalizedSourceBC_source_naturality :
    SourceIsoNaturalityEquation
      (moduleCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
      (moduleSourceBCTransportNormalizationMap f' e he b C Λ)
      (moduleRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        ((baseChange b).obj C).toCompactification)
      (moduleRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        (C.toCompactification.baseChange b)) :=
  moduleRawCompactificationSourceIso_refinement_naturality
    (pullbackSourceIso f' e he b) (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
    ((baseChange b).obj C).toCompactification (C.toCompactification.baseChange b)
    (baseChangeNormalization b C) (Hom.Compactification.isPullback_densify _)
    (sourceBCTransportNormalization_isPullback f' e he b C)
    (baseChangeNormalization_fst b C) Λ

omit [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)] in
/-- Base change first, then the actual normalized source comparison and refinement,
also gives the same original normalized composite map. -/
theorem moduleNormalizedSourceBC_after :
    RefinedSourceIsoPastingEquation (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (moduleNormalizedSourceBCCompositeMap f' e he b C Λ)
      (moduleRawSourceBaseChangeSourceIso f f' e he b Λ)
      (moduleRawCompactificationSourceIso (pullbackSourceIso f' e he b) Λ
        (pullback.fst b f') (pullbackSourceIso_hom_fst f' e he b)
        ((baseChange b).obj C).toCompactification)
      (moduleSourceBCNormalizedTransition f' e he b C Λ) :=
  refinedSourceIsoPastingEquation_normalize _ _ _ _ _ _ _ _ _ _ _ _
    (moduleRawSourceBaseChange_after f f' e he b C.toCompactification Λ)
    (moduleNormalizedSourceBC_source_naturality f' e he b C Λ)
    ((moduleSourceBCNormalization_raw_triangle f' e he b C Λ).trans
      (moduleSourceBCNormalization_dense_triangle f' e he b C Λ).symm)
    (moduleNormalizedCompactificationBaseChangeIso_hom C b Λ) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
