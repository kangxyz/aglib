/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIso

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

/-- The actual source transport followed directly by the specified original mixed refinement. -/
def moduleCompactificationSourceIsoRefinement (C : Hom.DenseCompactification f)
    {D : Hom.DenseCompactification f'}
    (r : D ⟶ (Hom.DenseCompactification.sourceIso f' e he).obj C) :
    moduleCompactificationFunctor f Λ C ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙ moduleCompactificationFunctor f' Λ D := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let m := @asIso _ _ _ _
    (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS
      D C' r (targetModels D) hOld)
    (@moduleCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
      D C' r (targetModels D) hOld)
  letI : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  exact moduleRawCompactificationSourceIso e Λ f' he C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ) m

omit [QuasiCompact f] in
/-- The canonical any-model comparison is the original transition for every actual refinement. -/
theorem moduleCompactificationSourceIsoTo_refinement (C : Hom.DenseCompactification f)
    {D : Hom.DenseCompactification f'}
    (r : D ⟶ (Hom.DenseCompactification.sourceIso f' e he).obj C) :
    moduleCompactificationSourceIsoTo f f' e he Λ C D =
      moduleCompactificationSourceIsoRefinement f f' e he Λ C r := by
  let C' := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf C'.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let t := @moduleCompactificationTransition X' S f' _ Λ _ hX' hS targetModels D C' r
  let : IsIso t := @moduleCompactificationTransition_isIso X' S f' _ Λ _ hX' hS
    targetModels D C' r
  have hcIso : moduleCompactificationComparison f' Λ C' D =
      asIso t := by
    calc
      _ = (moduleCompactificationComparison f' Λ D C').symm :=
        (moduleCompactificationComparison_symm f' Λ D C').symm
      _ = _ := congrArg Iso.symm (moduleCompactificationComparison_refinement f' Λ r)
  have hm := @moduleCompactificationMixedTransition_comp X' S f' _ Λ _ hX' hS
    D C' r (targetModels D) (targetModels C') C' (𝟙 C') hOld
  have hn :
      @moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS C' C' (𝟙 C')
          (targetModels C') hOld ≫ t =
        @moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS D C' r
          (targetModels D) hOld := by
    exact hm.symm.trans (congrArg
      (fun z => @moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        D C' z (targetModels D) hOld) (Category.comp_id r))
  exact sourceIso_refinement_factor (moduleDerivedInverseImageTorsion e.hom Λ)
    (moduleRawCompactificationSourceIso e Λ f' he C.toCompactification)
    (@asIso _ _ _ _
      (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        C' C' (𝟙 C') (targetModels C') hOld)
      (@moduleCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
        C' C' (𝟙 C') (targetModels C') hOld))
    (moduleCompactificationComparison f' Λ C' D)
    (@asIso _ _ _ _
      (@moduleCompactificationMixedTransition X' S f' _ Λ _ hX' hS
        D C' r (targetModels D) hOld)
      (@moduleCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS
        D C' r (targetModels D) hOld))
    t (congrArg Iso.hom hcIso) hn

end AlgebraicGeometry.Scheme.EtaleCohomology
