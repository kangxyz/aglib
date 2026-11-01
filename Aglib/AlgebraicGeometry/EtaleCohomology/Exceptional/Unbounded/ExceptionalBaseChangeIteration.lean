/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.CategoryTheory.NatTrans.NormalizedIterationTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeModelEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawDenseTransition

/-!
# Consecutive base change for the original chosen exceptional functor

The original normalized-model equation is transported through the original
canonical model squares. The actual source pullback associator, its native
inverse-image compositor, and the original mixed refinement remain explicit.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wS wM wX₁ wT wM₁ wXi wU wMi wXs wMs wR₁ wR₂ wRs wRi
variable {X S T U : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S) (c : U ⟶ T)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [hXi : HasDerivedCategory.{wXi} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [hU : HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wXs} (ModuleSheaf (pullback (c ≫ b) f) Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ)]
  [iteratedModels : ∀ C : Hom.DenseCompactification (pullback.fst c (pullback.fst b f)),
    HasDerivedCategory.{wMi} (ModuleSheaf C.Xbar Λ)]
  [singleModels : ∀ C : Hom.DenseCompactification (pullback.fst (c ≫ b) f),
    HasDerivedCategory.{wMs} (ModuleSheaf C.Xbar Λ)]

local instance unboundedChosenIterationFirstNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance unboundedChosenIterationIteratedNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst c (pullback.fst b f))) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification (pullback.fst b f))⟩
local instance unboundedChosenIterationSingleNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (c ≫ b) f)) :=
  ⟨baseChangeObj (c ≫ b) (moduleExceptionalSuppliedCompactification f)⟩

variable [rawFirstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ)]
  [rawSecondModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wR₂} (ModuleSheaf (pullback c C.p) Λ)]
  [rawSingleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wRs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The independently defined canonical source-associator comparison. -/
def moduleExceptionalUnboundedIterationSourceIso :=
  moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty
    (pullback.fst (c ≫ b) f) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso b c) (iteratedSourceIso_hom_fst b c) Λ N hN hΛ

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]

local instance unboundedChosenIterationFirstRawModel : HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) := rawFirstModels C
local instance unboundedChosenIterationSecondRawModel : HasDerivedCategory.{wR₂}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ) :=
  rawSecondModels ((baseChange b).obj C)
local instance unboundedChosenIterationSingleRawModel : HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ) := rawSingleModels C
local instance unboundedChosenIterationTransportedSingleModel : HasDerivedCategory.{wMs}
    (ModuleSheaf ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).Xbar Λ) :=
  singleModels ((baseChange (c ≫ b)).obj C)

omit [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  models firstModels rawFirstModels rawSecondModels rawSingleModels
  [HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)] in
/-- The source/refinement square is the canonical source comparison's actual
model law, computed by the original transition of the geometric iteration isomorphism. -/
theorem moduleExceptionalUnboundedIterationSourceIso_model :
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (c ≫ b) f) Λ N hN hΛ
      ((baseChange (c ≫ b)).obj C)).hom ≫
        (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
          (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
          ((baseChange (c ≫ b)).obj C).toCompactification).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (iteratedSourceIso b c).hom)
          (moduleUnboundedNormalizedIterationTransition b c C Λ) =
      (moduleExceptionalUnboundedIterationSourceIso f b c Λ N hN hΛ).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (iteratedSourceIso b c).hom)
          (moduleExceptionalDirectImageUnboundedOfNonemptyIso
            (pullback.fst c (pullback.fst b f)) Λ N hN hΛ
            ((baseChange b ⋙ baseChange c).obj C)).hom := by
  have h := moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model
    (pullback.fst (c ≫ b) f) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso b c) (iteratedSourceIso_hom_fst b c) Λ N hN hΛ
    ((baseChange (c ≫ b)).obj C) ((baseChange b ⋙ baseChange c).obj C)
  rw [moduleUnboundedCompactificationSourceIsoTo_refinement _ _ _ _ _ N hN hΛ _
    (baseChangeIterationIso b c C).hom] at h
  let D := (baseChange b ⋙ baseChange c).obj C
  let E := (baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C
  let hOld : HasDerivedCategory.{wMs} (ModuleSheaf E.Xbar Λ) :=
    singleModels ((baseChange (c ≫ b)).obj C)
  let m := @moduleUnboundedCompactificationMixedTransition _ U _ _ Λ _ hXi hU
    D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld
  have hm : IsIso m := @moduleUnboundedCompactificationMixedTransition_isIso _ U _ _ Λ _ hXi hU
    D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld N hN hΛ
  have ht : moduleUnboundedNormalizedIterationTransition b c C Λ = m :=
    @moduleUnboundedRawDenseTransition_eq_mixed _ U _ _ Λ _ hXi hU
      D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld
  exact sourceRefinement_model_equation
    (moduleUnboundedDerivedInverseImage Λ (iteratedSourceIso b c).hom)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (c ≫ b) f) Λ N hN hΛ
      ((baseChange (c ≫ b)).obj C))
    (moduleExceptionalUnboundedIterationSourceIso f b c Λ N hN hΛ)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso
        (pullback.fst c (pullback.fst b f)) Λ N hN hΛ
      ((baseChange b ⋙ baseChange c).obj C))
    (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleUnboundedCompactificationSourceIsoRefinement (pullback.fst (c ≫ b) f)
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso b c)
      (iteratedSourceIso_hom_fst b c) Λ N hN hΛ ((baseChange (c ≫ b)).obj C)
      (baseChangeIterationIso b c C).hom)
    (moduleUnboundedNormalizedIterationTransition b c C Λ)
    m hm rfl ht h

include C in
/-- The chosen two-step exchange equals the chosen one-step exchange followed
by the independently defined actual source-associator comparison. The supplied
model families are independent; no qcqs condition is imposed on either new base. -/
theorem moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_iteration :
    OriginalNormalizedIterationEquation
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty
          (pullback.fst b f) c Λ N hN hΛ).hom
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f (c ≫ b) Λ N hN hΛ).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ b c)
      (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f)))
      (moduleUnboundedRawIterationSourceIso b c Λ)
      (moduleExceptionalUnboundedIterationSourceIso f b c Λ N hN hΛ)
      (𝟙 (moduleExceptionalDirectImageUnboundedOfNonempty (pullback.fst c (pullback.fst b f)) Λ)) :=
  originalNormalizedIterationEquation_transport
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f) Λ N hN hΛ
      ((baseChange b).obj C))
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso
        (pullback.fst c (pullback.fst b f)) Λ N hN hΛ
      ((baseChange b ⋙ baseChange c).obj C))
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (c ≫ b) f) Λ N hN hΛ
      ((baseChange (c ≫ b)).obj C))
    _ _ _ _ _ _ _ _ _ _ _ _
    (moduleExceptionalUnboundedBaseChange_normalized_model f b Λ N hN hΛ C)
    (moduleExceptionalUnboundedBaseChange_normalized_model (pullback.fst b f) c Λ N hN hΛ
      ((baseChange b).obj C))
    (moduleExceptionalUnboundedBaseChange_normalized_model f (c ≫ b) Λ N hN hΛ C)
    (moduleExceptionalUnboundedIterationSourceIso_model f b c Λ N hN hΛ C)
    (moduleUnboundedNormalizedBaseChangeIteration_equation b c C Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
