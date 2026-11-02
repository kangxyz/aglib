/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.CategoryTheory.NatTrans.NormalizedIterationTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeModelEquation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawDenseTransition

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

local instance firstNonempty : Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance iteratedNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst c (pullback.fst b f))) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification (pullback.fst b f))⟩
local instance singleNonempty : Nonempty (Hom.DenseCompactification (pullback.fst (c ≫ b) f)) :=
  ⟨baseChangeObj (c ≫ b) (moduleExceptionalSuppliedCompactification f)⟩

variable [rawFirstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ)]
  [rawSecondModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wR₂} (ModuleSheaf (pullback c C.p) Λ)]
  [rawSingleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wRs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ)]

/-- The independently defined canonical source-associator comparison. -/
def moduleExceptionalIterationSourceIso :=
  moduleExceptionalDirectImagePlusSourceIsoOfNonempty
    (pullback.fst (c ≫ b) f) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso b c) (iteratedSourceIso_hom_fst b c) Λ

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]

/-- Derived-category instance on module sheaves over `(C.toCompactification.baseChange b).Xbar`,
supplied by `rawFirstModels C`.
-/
local instance firstRawModel : HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) := rawFirstModels C
/-- Derived-category instance on module sheaves over `(((baseChange b).obj
C).toCompactification.baseChange c).Xbar`, supplied by `rawSecondModels ((baseChange b).obj C)`.
-/
local instance secondRawModel : HasDerivedCategory.{wR₂}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ) :=
  rawSecondModels ((baseChange b).obj C)
/-- Derived-category instance on module sheaves over `(C.toCompactification.baseChange (c ≫
b)).Xbar`, supplied by `rawSingleModels C`.
-/
local instance singleRawModel : HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ) := rawSingleModels C
/-- Derived-category instance on module sheaves over `((baseChange (c ≫ b) ⋙ iteratedSourceTransport
b c).obj C).Xbar`, supplied by `singleModels ((baseChange (c ≫ b)).obj C)`.
-/
local instance transportedSingleModel : HasDerivedCategory.{wMs}
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
theorem moduleExceptionalIterationSourceIso_model :
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (c ≫ b) f) Λ
      ((baseChange (c ≫ b)).obj C)).hom ≫
        (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
          (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
          ((baseChange (c ≫ b)).obj C).toCompactification).hom ≫
        Functor.whiskerLeft (moduleDerivedInverseImageTorsion (iteratedSourceIso b c).hom Λ)
          (moduleNormalizedIterationTransition b c C Λ) =
      (moduleExceptionalIterationSourceIso f b c Λ).hom ≫
        Functor.whiskerLeft (moduleDerivedInverseImageTorsion (iteratedSourceIso b c).hom Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso
            (pullback.fst c (pullback.fst b f)) Λ ((baseChange b ⋙ baseChange c).obj C)).hom := by
  have h := moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model
    (pullback.fst (c ≫ b) f) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso b c) (iteratedSourceIso_hom_fst b c) Λ
    ((baseChange (c ≫ b)).obj C) ((baseChange b ⋙ baseChange c).obj C)
  rw [moduleCompactificationSourceIsoTo_refinement _ _ _ _ _ _
    (baseChangeIterationIso b c C).hom] at h
  let D := (baseChange b ⋙ baseChange c).obj C
  let E := (baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C
  let hOld : HasDerivedCategory.{wMs} (ModuleSheaf E.Xbar Λ) :=
    singleModels ((baseChange (c ≫ b)).obj C)
  let m := @moduleCompactificationMixedTransition _ U _ _ Λ _ hXi hU
    D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld
  have hm : IsIso m := @moduleCompactificationMixedTransition_isIso _ U _ _ Λ _ hXi hU
    D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld
  have ht : moduleNormalizedIterationTransition b c C Λ = m :=
    @moduleRawDenseTransition_eq_mixed _ U _ _ Λ _ hXi hU
      D E (baseChangeIterationIso b c C).hom (iteratedModels D) hOld
  exact sourceRefinement_model_equation
    (moduleDerivedInverseImageTorsion (iteratedSourceIso b c).hom Λ)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (c ≫ b) f) Λ
      ((baseChange (c ≫ b)).obj C))
    (moduleExceptionalIterationSourceIso f b c Λ)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst c (pullback.fst b f)) Λ
      ((baseChange b ⋙ baseChange c).obj C))
    (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleCompactificationSourceIsoRefinement (pullback.fst (c ≫ b) f)
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso b c)
      (iteratedSourceIso_hom_fst b c) Λ ((baseChange (c ≫ b)).obj C)
      (baseChangeIterationIso b c C).hom)
    (moduleNormalizedIterationTransition b c C Λ)
    m hm rfl ht h

include C in
/-- The chosen two-step exchange equals the chosen one-step exchange followed
by the independently defined actual source-associator comparison. The supplied
model families are independent; no qcqs condition is imposed on either new base. -/
theorem moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_iteration :
    OriginalNormalizedIterationEquation
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty (pullback.fst b f) c Λ).hom
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f (c ≫ b) Λ).hom
      (moduleDerivedInverseImageCompIso Λ b c)
      (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f)))
      (moduleRawIterationSourceIso b c Λ)
      (moduleExceptionalIterationSourceIso f b c Λ)
      (𝟙 (moduleExceptionalDirectImagePlusOfNonempty (pullback.fst c (pullback.fst b f)) Λ)) :=
  originalNormalizedIterationEquation_transport
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ
      ((baseChange b).obj C))
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst c (pullback.fst b f)) Λ
      ((baseChange b ⋙ baseChange c).obj C))
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (c ≫ b) f) Λ
      ((baseChange (c ≫ b)).obj C))
    _ _ _ _ _ _ _ _ _ _ _ _
    (moduleExceptionalBaseChange_normalized_model f b Λ C)
    (moduleExceptionalBaseChange_normalized_model (pullback.fst b f) c Λ
      ((baseChange b).obj C))
    (moduleExceptionalBaseChange_normalized_model f (c ≫ b) Λ C)
    (moduleExceptionalIterationSourceIso_model f b c Λ C)
    (moduleNormalizedBaseChangeIteration_equation b c C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
