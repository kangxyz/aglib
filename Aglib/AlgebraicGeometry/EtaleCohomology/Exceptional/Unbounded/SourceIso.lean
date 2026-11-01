/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedDirectImage

/-! # Canonical exceptional source-isomorphism comparison with independent model families -/

@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wS wM wN
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]


variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ in
/-- The target diagram retains the original invertible refinement maps. -/
theorem moduleUnboundedCompactificationSourceIsoTargetDiagram_map_isIso
    {C D : (Hom.DenseCompactification f')ᵒᵖ} (a : C ⟶ D) :
    IsIso ((moduleUnboundedCompactificationSourceIsoTargetDiagram f' e Λ).map a) := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f') Λ N hN hΛ
  change IsIso (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
    ((moduleUnboundedCompactificationDiagram (f := f') Λ).map a))
  infer_instance

/-- Original source transport, then canonical comparison to any specified target model. -/
def moduleUnboundedCompactificationSourceIsoTo
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification f')
    [sourceModel : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)] :
    moduleUnboundedCompactificationFunctor f Λ C ≅
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙ moduleUnboundedCompactificationFunctor f' Λ D :=
  moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
      (sourceModel := sourceModel)
      (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj C)) ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
      (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
        ((Hom.DenseCompactification.sourceIso f' e he).obj C) D)

variable [Nonempty (Hom.DenseCompactification f)]

include f e he in
omit [QuasiCompact f] [QuasiCompact f'] in
/-- Actual source transport supplies compactifiability of the new source. -/
theorem moduleUnboundedSourceIsoTargetNonempty : Nonempty (Hom.DenseCompactification f') :=
  ⟨(Hom.DenseCompactification.sourceIso f' e he).obj
    (moduleExceptionalSuppliedCompactification f)⟩

section Chosen
variable [chosenSourceModel : HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalSuppliedCompactification f).Xbar Λ)]

include f f' e he in
/-- Canonical source-isomorphism comparison on full unbounded derived categories.
Only supplied compactifiability is used, not qcqs of the common base. -/
def moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty :
    (letI : Nonempty (Hom.DenseCompactification f') :=
       moduleUnboundedSourceIsoTargetNonempty f f' e he
     moduleExceptionalDirectImageUnboundedOfNonempty f Λ
         (chosenMiddleModel := chosenSourceModel) ≅
       moduleUnboundedDerivedInverseImage Λ e.hom ⋙
         moduleExceptionalDirectImageUnboundedOfNonempty f' Λ
           (chosenMiddleModel := targetModels (moduleExceptionalSuppliedCompactification f'))) := by
  letI : Nonempty (Hom.DenseCompactification f') :=
    moduleUnboundedSourceIsoTargetNonempty f f' e he
  exact moduleUnboundedCompactificationSourceIsoTo f f' e he Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f) (moduleExceptionalSuppliedCompactification f')
    (sourceModel := chosenSourceModel)

end Chosen

variable
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

omit [Nonempty (Hom.DenseCompactification f)] in
/-- Actual source transport intertwines canonical comparisons of every pair of models. -/
theorem moduleUnboundedCompactificationSourceIsoComparison (C D : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
        (sourceModel := sourceModels C)
        (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj C)) ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
          (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
            ((Hom.DenseCompactification.sourceIso f' e he).obj C)
            ((Hom.DenseCompactification.sourceIso f' e he).obj D)) =
      moduleUnboundedCompactificationComparison f Λ N hN hΛ C D ≪≫
        moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ D
        (sourceModel := sourceModels D)
        (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj D)) := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f') Λ N hN hΛ
  let : ∀ (C D : (Hom.DenseCompactification f')ᵒᵖ) (r : C ⟶ D),
      IsIso ((moduleUnboundedCompactificationSourceIsoTargetDiagram f' e Λ).map r) :=
    fun _ _ r => moduleUnboundedCompactificationSourceIsoTargetDiagram_map_isIso f' e Λ N hN hΛ r
  have hn := Functor.cofilteredComparison_natIso
    (Hom.DenseCompactification.sourceIso f' e he)
    (moduleUnboundedCompactificationSourceIsoDiagram f f' e he Λ N hN hΛ) C D
  dsimp only [moduleUnboundedCompactificationSourceIsoTargetDiagram] at hn
  rw [← Functor.cofilteredComparison_postcomp] at hn
  exact hn

include f f' e he in
/-- Every specified source and target compactification computes this same canonical map. -/
theorem moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification f') :
    (letI : Nonempty (Hom.DenseCompactification f') :=
       moduleUnboundedSourceIsoTargetNonempty f f' e he
     moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C ≪≫
         moduleUnboundedCompactificationSourceIsoTo f f' e he Λ N hN hΛ C D =
       moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f' e he Λ N hN hΛ ≪≫
         Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
           (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ D)) := by
  let : Nonempty (Hom.DenseCompactification f') :=
    moduleUnboundedSourceIsoTargetNonempty f f' e he
  exact isoComparison_model_transport
    ((Functor.whiskeringLeft _ _ _).obj (moduleUnboundedDerivedInverseImage Λ e.hom))
    (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification f)
      (sourceModel := sourceModels (moduleExceptionalSuppliedCompactification f))
      (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))))
    (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C
        (sourceModel := sourceModels C)
        (targetModel := targetModels ((Hom.DenseCompactification.sourceIso f' e he).obj C)))
    (moduleUnboundedCompactificationComparison f Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification f) C)
    (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      ((Hom.DenseCompactification.sourceIso f' e he).obj C))
    (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
      ((Hom.DenseCompactification.sourceIso f' e he).obj C) D)
    (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      (moduleExceptionalSuppliedCompactification f'))
    (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification f') D)
    (moduleUnboundedCompactificationSourceIsoComparison f f' e he Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification f) C)
    ((moduleUnboundedCompactificationComparison_trans f' Λ N hN hΛ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      ((Hom.DenseCompactification.sourceIso f' e he).obj C) D).trans
      (moduleUnboundedCompactificationComparison_trans f' Λ N hN hΛ
        ((Hom.DenseCompactification.sourceIso f' e he).obj
          (moduleExceptionalSuppliedCompactification f))
        (moduleExceptionalSuppliedCompactification f') D).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
