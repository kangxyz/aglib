/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedPointLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationIso

/-!
# Original closed direct-image stalks

The existing finite direct-image evaluation tuple has an empty or singleton
index for a closed immersion. These specializations preserve its original
pointed evaluation and the inverse-image adjunction unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open CoefficientStalkBaseChange

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The original closed direct-image stalk vanishes when its geometric point has no lift. -/
theorem isZero_closedDirectImage_stalk_of_no_lift (η : Spec (.of Ω) ⟶ X)
    (hη : ∀ ζ : Spec (.of Ω) ⟶ Z, ζ ≫ i ≠ η) (F : AbelianSheaf.{u, u + 1} Z) :
    IsZero (coefficientFiber η ((directImage i).obj F)) := by
  let : IsEmpty {ζ : Spec (.of Ω) ⟶ Z // ζ ≫ i = η} :=
    ⟨fun ζ => hη ζ.val ζ.property⟩
  have h : IsZero (directImageEvaluationTupleTarget i η F) := by
    unfold directImageEvaluationTupleTarget
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact h.of_iso (Finite.finiteDirectImageEvaluationIso i η F)

/-- The singleton coordinate of the original finite tuple is invertible for a closed immersion. -/
theorem closedDirectImageEvaluation_isIso (ζ : Spec (.of Ω) ⟶ Z)
    (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ i = η) (F : AbelianSheaf.{u, u + 1} Z) :
    IsIso (pointedDirectImageEvaluation i ζ η hζ F) := by
  let : Unique {x : Spec (.of Ω) ⟶ Z // x ≫ i = η} :=
    ⟨⟨⟨ζ, hζ⟩⟩, fun _ => Subsingleton.elim _ _⟩
  let e : directImageEvaluationTupleTarget i η F ≅ coefficientFiber ζ F :=
    (AddEquiv.piUnique (fun x : {x : Spec (.of Ω) ⟶ Z // x ≫ i = η} =>
      coefficientFiber x.val F)).toAddCommGrpIso
  have h : pointedDirectImageEvaluation i ζ η hζ F =
      directImageEvaluationTuple i η F ≫ e.hom := by
    ext a
    rfl
  rw [h]
  let := Finite.finiteDirectImageEvaluationTuple_isIso i η F
  infer_instance

omit [IsClosedImmersion i] in
/-- Closed-unit stalk evaluation equals the original pointed inverse-image stalk unit. -/
@[reassoc]
theorem closedDirectImage_unit_stalk_evaluation (ζ : Spec (.of Ω) ⟶ Z)
    (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ i = η) (F : AbelianSheaf.{u, u + 1} X) :
    (pointSmallEtale η).sheafFiber.map ((inverseImageAdjunction i).unit.app F) ≫
        pointedDirectImageEvaluation i ζ η hζ ((inverseImage i).obj F) =
      pointedStalkUnit i ζ F η hζ := by
  unfold pointedDirectImageEvaluation
  have hn := pointedStalkUnit_naturality i ζ η hζ
    ((inverseImageAdjunction i).unit.app F)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, (inverseImageAdjunction i).left_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- On the closed part, the original inverse-image/direct-image unit is invertible on stalks. -/
theorem closedDirectImage_unit_stalk_isIso (ζ : Spec (.of Ω) ⟶ Z)
    (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ i = η) (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((pointSmallEtale η).sheafFiber.map ((inverseImageAdjunction i).unit.app F)) := by
  let := closedDirectImageEvaluation_isIso i ζ η hζ ((inverseImage i).obj F)
  let := pointedStalkUnit_isIso i ζ η hζ F
  have h : IsIso ((pointSmallEtale η).sheafFiber.map ((inverseImageAdjunction i).unit.app F) ≫
      pointedDirectImageEvaluation i ζ η hζ ((inverseImage i).obj F)) := by
    rw [closedDirectImage_unit_stalk_evaluation]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
