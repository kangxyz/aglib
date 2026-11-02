/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedSourceBC
public import Aglib.CategoryTheory.NatTrans.SourceBeforeModels
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoRefinement

/-! # Source/base-change interchange with independent native compactification models -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wX' wL wL' wS wT wM wM' wR wR' wN wN'
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (b : T ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hL : HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [hL' : HasDerivedCategory.{wL'} (ModuleSheaf (pullback b f') Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [changedModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wM'} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [changedTargetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f'),
    HasDerivedCategory.{wN'} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  [changedRawModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wR'} (ModuleSheaf (pullback b C.p) Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
variable (C : Hom.DenseCompactification f)

/-- The derived-category instance in universe `wM` for `Λ`-module sheaves on `C.Xbar`.
-/
local instance unboundedSourceBCModelOriginal : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) :=
  models C
/-- The derived-category instance in universe `wR` for `Λ`-module sheaves on `(pullback b C.p)`.
-/
local instance unboundedSourceBCModelOriginalRaw : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback b C.p) Λ) := rawModels C
/-- The derived-category instance in universe `wN` for `Λ`-module sheaves on `((baseChange b).obj
    C).Xbar`.
-/
local instance unboundedSourceBCModelOriginalTarget : HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange b).obj C).Xbar Λ) := targetModels ((baseChange b).obj C)
/-- The derived-category instance in universe `wN'` for `Λ`-module sheaves on `((sourceIso f' e he ⋙
    baseChange b).obj C).Xbar`.
-/
local instance unboundedSourceBCModelNewTarget : HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ) :=
  changedTargetModels ((sourceIso f' e he ⋙ baseChange b).obj C)
/-- The derived-category instance in universe `wN` for `Λ`-module sheaves on `(baseChangeObj b
    C).Xbar`.
-/
local instance unboundedSourceBCModelOriginalBaseChangeObj : HasDerivedCategory.{wN}
    (ModuleSheaf (baseChangeObj b C).Xbar Λ) := targetModels ((baseChange b).obj C)

/-- Both original normalized exchanges commute with the canonical source-model
comparisons; the source, transported source, and two target families stay independent. -/
theorem moduleUnboundedCompactificationSourceBaseChange_model :
    SourceIsoBaseChangeEquation
      (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
        (sourceModel := models C)
        (targetModel := changedModels ((sourceIso f' e he).obj C)))
      (@moduleUnboundedNormalizedCompactificationBaseChangeIso X' S T f' _
        ((sourceIso f' e he).obj C) b Λ _ hX' hS
        (changedModels ((sourceIso f' e he).obj C)) hL' hT
        (changedRawModels ((sourceIso f' e he).obj C))
        (changedTargetModels ((sourceIso f' e he ⋙ baseChange b).obj C)) N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedCompactificationSourceIsoTo (pullback.fst b f) (pullback.fst b f')
        (pullbackSourceIso f' e he b) (pullbackSourceIso_hom_fst f' e he b) Λ N hN hΛ
        ((baseChange b).obj C) ((sourceIso f' e he ⋙ baseChange b).obj C))
      (moduleUnboundedSourceBaseChangeSquareIso f f' e he b Λ) := by
  let C₁ := (sourceIso f' e he).obj C
  let N₀ := (baseChange b).obj C
  let N₁ := (baseChange b).obj C₁
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C₁.Xbar Λ) := models C
  let hOldRaw : HasDerivedCategory.{wR} (ModuleSheaf (pullback b C₁.p) Λ) := rawModels C
  let m := @moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS
    C₁ C₁ (𝟙 C₁) (changedModels C₁) hOld
  have hn := @moduleUnboundedNormalizedCompactificationBaseChangeIso_naturality X' S T f' _
    C₁ C₁ (𝟙 C₁) b Λ _ hX' hS (changedModels C₁) hOld hL' hT
    (changedRawModels C₁) hOldRaw (changedTargetModels N₁) (changedTargetModels N₁) N hN hΛ
  have ht : moduleUnboundedRawCompactificationTransition N₁.toCompactification N₁.toCompactification
      ((baseChange b).map (𝟙 C₁)).hom
      (isPullback_open ((baseChange b).map (𝟙 C₁)))
      ((baseChange b).map (𝟙 C₁)).base_fac Λ = 𝟙 _ := by
    change moduleUnboundedCompactificationTransition Λ ((baseChange b).map (𝟙 C₁)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    exact moduleUnboundedCompactificationTransition_id Λ N₁
  have hb := sourceIsoBeforeExchange_changeModel _
    (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
      (sourceModel := models C) (targetModel := changedModels C₁)) m _ _ _ _ _
    (moduleUnboundedNormalizedSourceBC_before f' e he b C Λ N hN hΛ) rfl hn ht
  have hs := congrArg Iso.hom (moduleUnboundedCompactificationSourceIsoTo_refinement
    (pullback.fst b f) (pullback.fst b f') (pullbackSourceIso f' e he b)
    (pullbackSourceIso_hom_fst f' e he b) Λ N hN hΛ N₀
    (baseChangeSourceIsoComponent f' e he b C).hom)
  exact sourceIsoBaseChange_of_before_after _ _ _ _ _ _ _ _ _ hb
    (moduleUnboundedNormalizedSourceBC_after f' e he b C Λ N hN hΛ) hs

end AlgebraicGeometry.Scheme.EtaleCohomology
