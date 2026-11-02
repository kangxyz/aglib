/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIso

/-! # Canonical source transport computed through an actual mixed-model refinement -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wS wM wN
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual source transport followed directly by the specified original mixed refinement. -/
def moduleUnboundedCompactificationSourceIsoRefinement (C : Hom.DenseCompactification f)
    {D : Hom.DenseCompactification f'}
    (r : D ⟶ (Hom.DenseCompactification.sourceIso f' e he).obj C) :
    moduleUnboundedCompactificationFunctor f Λ C ≅
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        moduleUnboundedCompactificationFunctor f' Λ D := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let m := @asIso _ _ _ _
    (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS
      D C' r (targetModels D) hOld)
    (@moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
      D C' r (targetModels D) hOld N hN hΛ)
  letI : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  exact moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom) m

omit [QuasiCompact f] in
/-- The canonical any-model comparison is the original transition for every actual refinement. -/
theorem moduleUnboundedCompactificationSourceIsoTo_refinement (C : Hom.DenseCompactification f)
    {D : Hom.DenseCompactification f'}
    (r : D ⟶ (Hom.DenseCompactification.sourceIso f' e he).obj C) :
    moduleUnboundedCompactificationSourceIsoTo f f' e he Λ N hN hΛ C D =
      moduleUnboundedCompactificationSourceIsoRefinement f f' e he Λ N hN hΛ C r := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let t := @moduleUnboundedCompactificationTransition X' S f' _ Λ _ hX' hS targetModels D C' r
  let : IsIso t := @moduleUnboundedCompactificationTransition_isIso X' S f' _ Λ _ hX' hS
    targetModels N hN hΛ D C' r
  have hcIso : moduleUnboundedCompactificationComparison f' Λ N hN hΛ C' D =
      asIso t := by
    calc
      _ = (moduleUnboundedCompactificationComparison f' Λ N hN hΛ D C').symm :=
        (moduleUnboundedCompactificationComparison_symm f' Λ N hN hΛ D C').symm
      _ = _ := congrArg Iso.symm
        (moduleUnboundedCompactificationComparison_refinement f' Λ N hN hΛ r)
  have hm := @moduleUnboundedCompactificationMixedTransition_comp X' S f' _ Λ _ hX' hS
    D C' r (targetModels D) (targetModels C') C' (𝟙 C') hOld
  have hn :
      @moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
          (targetModels C') hOld ≫ t =
        @moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS D C' r
          (targetModels D) hOld := by
    exact hm.symm.trans (congrArg
      (fun z => @moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        D C' z (targetModels D) hOld) (Category.comp_id r))
  exact sourceIso_refinement_factor (moduleUnboundedDerivedInverseImage Λ e.hom)
    (moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification)
    (@asIso _ _ _ _
      (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        C' C' (𝟙 C') (targetModels C') hOld)
      (@moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
        C' C' (𝟙 C') (targetModels C') hOld N hN hΛ))
    (moduleUnboundedCompactificationComparison f' Λ N hN hΛ C' D)
    (@asIso _ _ _ _
      (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        D C' r (targetModels D) hOld)
      (@moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
        D C' r (targetModels D) hOld N hN hΛ))
    t (congrArg Iso.hom hcIso) hn

end AlgebraicGeometry.Scheme.EtaleCohomology
