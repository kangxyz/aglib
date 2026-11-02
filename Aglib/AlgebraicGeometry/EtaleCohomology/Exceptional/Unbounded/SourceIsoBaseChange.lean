/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceBCModel
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChangeTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeModelEquation

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

local instance unboundedSourceBCChosenLeftNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance unboundedSourceBCChosenRightNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f')) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f')⟩

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit hL hL' hT targetModels changedTargetModels rawModels changedRawModels in
private theorem sourceBC_chosen_source_model (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C ≪≫
        moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C =
      moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f' e he Λ N hN hΛ ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
          (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ ((sourceIso f' e
            he).obj C)) := by
  have hs : moduleUnboundedCompactificationSourceIsoTo f f' e he Λ N hN hΛ C ((sourceIso f' e
    he).obj C) =
      moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C := by
    simp only [moduleUnboundedCompactificationSourceIsoTo,
      moduleUnboundedCompactificationComparison_self,
      Functor.isoWhiskerLeft_refl, Iso.trans_refl]
  exact (congrArg (fun z => moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C ≪≫ z)
    hs.symm).trans (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model
      f f' e he Λ N hN hΛ C ((sourceIso f' e he).obj C))

/-- Actual chosen source transport commutes with the original chosen exceptional base change.
The square retains all four independent native source models and independent middle families. -/
theorem moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_baseChange :
    SourceIsoBaseChangeEquation
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f' e he Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f' b Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty (pullback.fst b f) (pullback.fst b
        f')
        (pullbackSourceIso f' e he b) (pullbackSourceIso_hom_fst f' e he b) Λ N hN hΛ)
      (moduleUnboundedSourceBaseChangeSquareIso f f' e he b Λ) := by
  let C := moduleExceptionalSuppliedCompactification f
  let C₁ := (sourceIso f' e he).obj C
  let N₀ := (baseChange b).obj C
  let N₁ := (baseChange b).obj C₁
  exact sourceIsoBaseChange_modelTransport _ _ _ _ _ _ _ _ _
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ C₁)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f) Λ N hN hΛ N₀)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f') Λ N hN hΛ N₁)
    (sourceBC_chosen_source_model f f' e he Λ N hN hΛ C)
    (Iso.ext (moduleExceptionalUnboundedBaseChange_normalized_model f' b Λ N hN hΛ C₁))
    (Iso.ext (moduleExceptionalUnboundedBaseChange_normalized_model f b Λ N hN hΛ C))
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model
      (pullback.fst b f) (pullback.fst b f') (pullbackSourceIso f' e he b)
      (pullbackSourceIso_hom_fst f' e he b) Λ N hN hΛ N₀ N₁)
    (moduleUnboundedCompactificationSourceBaseChange_model f f' e he b Λ N hN hΛ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
