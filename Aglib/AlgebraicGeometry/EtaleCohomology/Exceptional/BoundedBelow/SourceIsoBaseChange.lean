/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceBCModel
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChangeTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeModelEquation

/-! # Canonical source-isomorphism/base-change coherence for exceptional direct image -/

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


variable [Nonempty (Hom.DenseCompactification f)] [Nonempty (Hom.DenseCompactification f')]

local instance sourceBCChosenLeftNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance sourceBCChosenRightNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f')) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f')⟩

omit hL hL' hT targetModels changedTargetModels rawModels changedRawModels in
private theorem sourceBC_chosen_source_model (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫
        moduleCompactificationSourceIsoModel f f' e he Λ C =
      moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f' e he Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso f' Λ ((sourceIso f' e he).obj C)) := by
  have hs : moduleCompactificationSourceIsoTo f f' e he Λ C ((sourceIso f' e he).obj C) =
      moduleCompactificationSourceIsoModel f f' e he Λ C := by
    simp only [moduleCompactificationSourceIsoTo, moduleCompactificationComparison_self,
      Functor.isoWhiskerLeft_refl, Iso.trans_refl]
  exact (congrArg (fun z => moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫ z)
    hs.symm).trans (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model
      f f' e he Λ C ((sourceIso f' e he).obj C))

/-- Actual chosen source transport commutes with the original chosen exceptional base change.
The square retains all four independent native source models and independent middle families. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_baseChange :
    SourceIsoBaseChangeEquation
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f' e he Λ)
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f' b Λ).hom
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst b f) (pullback.fst b f')
        (pullbackSourceIso f' e he b) (pullbackSourceIso_hom_fst f' e he b) Λ)
      (moduleSourceBaseChangeSquareIso f f' e he b Λ) := by
  let C := moduleExceptionalSuppliedCompactification f
  let C₁ := (sourceIso f' e he).obj C
  let N₀ := (baseChange b).obj C
  let N₁ := (baseChange b).obj C₁
  exact sourceIsoBaseChange_modelTransport _ _ _ _ _ _ _ _ _
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f' Λ C₁)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ N₀)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f') Λ N₁)
    (sourceBC_chosen_source_model f f' e he Λ C)
    (Iso.ext (moduleExceptionalBaseChange_normalized_model f' b Λ C₁))
    (Iso.ext (moduleExceptionalBaseChange_normalized_model f b Λ C))
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model
      (pullback.fst b f) (pullback.fst b f') (pullbackSourceIso f' e he b)
      (pullbackSourceIso_hom_fst f' e he b) Λ N₀ N₁)
    (moduleCompactificationSourceBaseChange_model f f' e he b Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
