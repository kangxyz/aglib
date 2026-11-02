/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Native module-sheaf evaluation

The original variable-ring evaluation functor is additive. Its transparent
additiveEvaluation view forgets only the section-ring module structure.
Both use the same native evaluator and preserve independent ring, module,
site and morphism universes, without another section carrier or functor record.
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

universe r m c h

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})

/-- Evaluation of actual module sheaves is additive, with the original component maps. -/
instance evaluation_additive (U : Cᵒᵖ) : (evaluation.{m} R U).Additive := by
  unfold evaluation
  infer_instance

/-- The underlying additive-group view of native module-sheaf evaluation. -/
abbrev additiveEvaluation (U : Cᵒᵖ) : SheafOfModules.{m} R ⥤ AddCommGrpCat.{m} :=
  evaluation.{m} R U ⋙
    forget₂ (ModuleCat.{m} (R.obj.obj U)) AddCommGrpCat.{m}

/-- The native additive evaluation view preserves any valid zero-morphism structures. -/
instance additiveEvaluation_preservesZeroMorphisms (U : Cᵒᵖ)
    [sourceZero : Limits.HasZeroMorphisms (SheafOfModules.{m} R)]
    [targetZero : Limits.HasZeroMorphisms AddCommGrpCat.{m}] :
    (additiveEvaluation R U :
      SheafOfModules.{m} R ⥤ AddCommGrpCat.{m}).PreservesZeroMorphisms := by
  let nativeSourceZero : Limits.HasZeroMorphisms (SheafOfModules.{m} R) :=
    @Preadditive.preadditiveHasZeroMorphisms (SheafOfModules.{m} R) inferInstance
      (SheafOfModules.instPreadditive R)
  let nativeTargetZero : Limits.HasZeroMorphisms AddCommGrpCat.{m} :=
    @Preadditive.preadditiveHasZeroMorphisms AddCommGrpCat.{m} inferInstance
      AddCommGrpCat.instPreadditive
  let preserves (s : Limits.HasZeroMorphisms (SheafOfModules.{m} R))
      (t : Limits.HasZeroMorphisms AddCommGrpCat.{m}) : Prop :=
    @Functor.PreservesZeroMorphisms (SheafOfModules.{m} R) inferInstance
      AddCommGrpCat.{m} inferInstance s t (additiveEvaluation R U)
  have native : preserves nativeSourceZero nativeTargetZero := ⟨fun _ _ => rfl⟩
  exact Eq.mp (congrArg₂ preserves (Subsingleton.elim nativeSourceZero sourceZero)
    (Subsingleton.elim nativeTargetZero targetZero)) native

end SheafOfModules
