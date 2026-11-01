/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedSourceBC
public import Aglib.CategoryTheory.NatTrans.SourceBeforeModels
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoRefinement

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

/-- The actual torsion inverse-image square, using original compositors and the
original pullback source-isomorphism projection equality. -/
def moduleSourceBaseChangeSquareIso :
    moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleDerivedInverseImageTorsion (pullback.snd b f') Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleDerivedInverseImageTorsion (pullbackSourceIso f' e he b).hom Λ :=
  (moduleDerivedInverseImageTorsionCompIso Λ e.hom (pullback.snd b f')).symm ≪≫
    moduleRawSourceBaseChangeSourceIso f f' e he b Λ

variable (C : Hom.DenseCompactification f)

local instance sourceBCModelOriginal : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := models C
local instance sourceBCModelOriginalRaw : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback b C.p) Λ) := rawModels C
local instance sourceBCModelOriginalTarget : HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange b).obj C).Xbar Λ) := targetModels ((baseChange b).obj C)
local instance sourceBCModelNewTarget : HasDerivedCategory.{wN'}
    (ModuleSheaf ((sourceIso f' e he ⋙ baseChange b).obj C).Xbar Λ) :=
  changedTargetModels ((sourceIso f' e he ⋙ baseChange b).obj C)
local instance sourceBCModelOriginalBaseChangeObj : HasDerivedCategory.{wN}
    (ModuleSheaf (baseChangeObj b C).Xbar Λ) := targetModels ((baseChange b).obj C)

/-- Both original normalized exchanges commute with the canonical source-model
comparisons; the source, transported source, and two target families stay independent. -/
theorem moduleCompactificationSourceBaseChange_model :
    SourceIsoBaseChangeEquation (moduleCompactificationSourceIsoModel f f' e he Λ C)
      (@moduleNormalizedCompactificationBaseChangeIso X' S T f' _
        ((sourceIso f' e he).obj C) b Λ _ hX' hS
        (changedModels ((sourceIso f' e he).obj C)) hL' hT
        (changedRawModels ((sourceIso f' e he).obj C))
        (changedTargetModels ((sourceIso f' e he ⋙ baseChange b).obj C))).hom
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (moduleCompactificationSourceIsoTo (pullback.fst b f) (pullback.fst b f')
        (pullbackSourceIso f' e he b) (pullbackSourceIso_hom_fst f' e he b) Λ
        ((baseChange b).obj C) ((sourceIso f' e he ⋙ baseChange b).obj C))
      (moduleSourceBaseChangeSquareIso f f' e he b Λ) := by
  let C₁ := (sourceIso f' e he).obj C
  let N₀ := (baseChange b).obj C
  let N₁ := (baseChange b).obj C₁
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C₁.Xbar Λ) := models C
  let hOldRaw : HasDerivedCategory.{wR} (ModuleSheaf (pullback b C₁.p) Λ) := rawModels C
  let m := @moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS
    C₁ C₁ (𝟙 C₁) (changedModels C₁) hOld
  have hn := @moduleNormalizedCompactificationBaseChangeIso_naturality X' S T f' _
    C₁ C₁ (𝟙 C₁) b Λ _ hX' hS (changedModels C₁) hOld hL' hT
    (changedRawModels C₁) hOldRaw (changedTargetModels N₁) (changedTargetModels N₁)
  have ht : moduleRawCompactificationTransition N₁.toCompactification N₁.toCompactification
      ((baseChange b).map (𝟙 C₁)).hom
      (isPullback_open ((baseChange b).map (𝟙 C₁)))
      ((baseChange b).map (𝟙 C₁)).base_fac Λ = 𝟙 _ := by
    change moduleCompactificationTransition Λ ((baseChange b).map (𝟙 C₁)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    exact moduleCompactificationTransition_id Λ N₁
  have hb := sourceIsoBeforeExchange_changeModel _
    (moduleCompactificationSourceIsoModel f f' e he Λ C) m _ _ _ _ _
    (moduleNormalizedSourceBC_before f' e he b C Λ) rfl hn ht
  have hs := congrArg Iso.hom (moduleCompactificationSourceIsoTo_refinement
    (pullback.fst b f) (pullback.fst b f') (pullbackSourceIso f' e he b)
    (pullbackSourceIso_hom_fst f' e he b) Λ N₀
    (baseChangeSourceIsoComponent f' e he b C).hom)
  exact sourceIsoBaseChange_of_before_after _ _ _ _ _ _ _ _ _ hb
    (moduleNormalizedSourceBC_after f' e he b C Λ) hs

end AlgebraicGeometry.Scheme.EtaleCohomology
