/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedStalk
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The original surjective unit and its finite cokernel stalks

Surjectivity makes the actual inverse-image adjunction unit monic. For a finite
map, a singleton actual geometric fibre makes that same unit invertible at
the original geometric stalk, so its literal cokernel has zero stalk there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open CoefficientStalkBaseChange

attribute [local instance] hasSheafifyLarge

/-- The original unit is monic for every surjective scheme morphism and every
abelian coefficient in the standard value universe. -/
theorem inverseImageAdjunction_unit_mono_of_surjective
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Surjective f]
    (F : AbelianSheaf.{u, u + 1} X) :
    Mono ((inverseImageAdjunction f).unit.app F) := by
  let := Proper.Reduction.inverseImage_faithful_of_surjective f
  exact Adjunction.unit_mono_of_L_faithful (inverseImageAdjunction f) F

namespace Finite

/-- A unique actual geometric lift makes the displayed finite direct-image
evaluation coordinate invertible. -/
theorem directImageEvaluation_isIso_of_unique
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [Unique {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}]
    (G : AbelianSheaf.{u, u + 1} Y) :
    IsIso (pointedDirectImageEvaluation f
      (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}).val s
      (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}).property G) := by
  let e : directImageEvaluationTupleTarget f s G ≅
      coefficientFiber (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}).val G :=
    (AddEquiv.piUnique (fun y : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s} =>
      coefficientFiber y.val G)).toAddCommGrpIso
  have h : pointedDirectImageEvaluation f
      (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}).val s
      (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}).property G =
      directImageEvaluationTuple f s G ≫ e.hom := by
    ext a
    rfl
  rw [h]
  let := finiteDirectImageEvaluationTuple_isIso f s G
  infer_instance

/-- The original finite unit is invertible at a point with one actual geometric lift. -/
theorem unit_stalk_isIso_of_unique
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [Unique {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction f).unit.app F)) := by
  let y := (default : {y : Spec (.of Ω) ⟶ Y // y ≫ f = s})
  let := directImageEvaluation_isIso_of_unique f s ((inverseImage f).obj F)
  let := pointedStalkUnit_isIso f y.val s y.property F
  have h : IsIso ((pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction f).unit.app F) ≫
      pointedDirectImageEvaluation f y.val s y.property ((inverseImage f).obj F)) := by
    rw [closedDirectImage_unit_stalk_evaluation]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

/-- The literal cokernel of the original finite unit has zero geometric stalk
where the actual geometric fibre is a singleton. -/
theorem unit_cokernel_stalk_isZero_of_unique
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [Unique {y : Spec (.of Ω) ⟶ Y // y ≫ f = s}]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsZero (coefficientFiber s (cokernel ((inverseImageAdjunction f).unit.app F))) := by
  let := unit_stalk_isIso_of_unique f s F
  exact (isZero_cokernel_of_epi
    ((pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction f).unit.app F))).of_iso
      (PreservesCokernel.iso (pointSmallEtale s).sheafFiber
        ((inverseImageAdjunction f).unit.app F))

end Finite

end AlgebraicGeometry.Scheme.EtaleCohomology
