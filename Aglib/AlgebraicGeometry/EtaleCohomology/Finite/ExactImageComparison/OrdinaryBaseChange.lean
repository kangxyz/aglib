/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Canonical finite ordinary base change on arbitrary bases -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  [IsFinite f] (h : IsPullback g' f' f g)

/-- The original finite ordinary exchange is invertible on every original
geometric stalk, by its literal unit/counit coordinate formula. -/
theorem finiteBaseChange_stalk_isIso
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s' : Spec (.of Ω) ⟶ S')
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((pointSmallEtale s').sheafFiber.map
      ((baseChangeMap f f' g g' h.w.symm).app F)) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let s := s' ≫ g
  let e := cartesianPointOverEquiv g' f' f g h s'
  let a := finiteDirectImageEvaluationIso f s F
  let b := finiteDirectImageEvaluationIso f' s' ((inverseImage g').obj F)
  let k (x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = s'}) :
      coefficientFiber (e x).val F ≅ coefficientFiber x.val ((inverseImage g').obj F) := by
    let := pointedStalkUnit_isIso g' x.val (e x).val rfl F
    exact asIso (pointedStalkUnit g' x.val F (e x).val rfl)
  let v := pointedStalkUnit g s' ((directImage f).obj F) s rfl
  let := pointedStalkUnit_isIso g s' s rfl ((directImage f).obj F)
  let β := (pointSmallEtale s').sheafFiber.map
    ((baseChangeMap f f' g g' h.w.symm).app F)
  have ht : IsIso (v ≫ β) := by
    apply isIso_of_tuple_coordinates a b e k (v ≫ β)
    intro z x
    change pointedDirectImageEvaluation f' x.val s' x.property
        ((inverseImage g').obj F) ((v ≫ β) z) =
      pointedStalkUnit g' x.val F (e x).val rfl
        (pointedDirectImageEvaluation f (e x).val s (e x).property F z)
    exact ConcreteCategory.congr_hom
      (pointedDirectImageEvaluation_baseChange f f' g g' h.w.symm
        (e x).val s x.val s' (e x).property rfl x.property rfl F) z
  exact (isIso_comp_left_iff v β).mp ht

/-- Finite base change for arbitrary abelian coefficients and arbitrary base
schemes, for the original canonical ordinary mate. -/
theorem finiteBaseChange_app_isIso (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((baseChangeMap f f' g g' h.w.symm).app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 S')
  intro Ω _ _ s' _
  exact finiteBaseChange_stalk_isIso f f' g g' h s' F

/-- The entire original ordinary exchange natural transformation is invertible. -/
theorem finiteBaseChange_isIso : IsIso (baseChangeMap f f' g g' h.w.symm) := by
  have (F : AbelianSheaf.{u, u + 1} X) :
      IsIso ((baseChangeMap f f' g g' h.w.symm).app F) :=
    finiteBaseChange_app_isIso f f' g g' h F
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
