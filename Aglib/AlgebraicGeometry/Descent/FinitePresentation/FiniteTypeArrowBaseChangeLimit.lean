/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeArrowLimit
public import Aglib.CategoryTheory.Over.PullbackMapSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual base changes along the original simultaneous target stages

The same directed arrow index and original targetStage rings define the
coefficient-base system. Pulling back its actual Over limit constructs the
total-space limit, retaining both original projections. No cohomology,
vanishing or target-refinement statement is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange

universe u
open Algebra.FiniteTypeArrowLimit

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- Use the same opposite-category Hom carrier as the original stage diagram. -/
local instance : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every finite-generated stage retains its original coefficient map. -/
def baseStructure : targetSpecDiagram α ⟶
    (Functor.const (Index A B)ᵒᵖ).obj (Spec (.of R)) where
  app s := Spec.algebraMap R (targetStage α s.unop)
  naturality s t g := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1

/-- The native spectrum diagram regarded over the original coefficient base. -/
def baseDiagram : (Index A B)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  Over.lift (targetSpecDiagram α) (baseStructure α)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original limiting spectrum map respects every stage's coefficient map. -/
theorem baseStructure_fac (s : (Index A B)ᵒᵖ) :
    (targetSpecCone α).π.app s ≫ (baseStructure α).app s = Spec.algebraMap R B := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The limiting cone in the native over category. -/
def baseCone : Cone (baseDiagram α) :=
  Over.liftCone (targetSpecDiagram α) (baseStructure α) (targetSpecCone α)
    (Spec.algebraMap R B) (baseStructure_fac α)

/-- The original spectrum cone remains limiting over the coefficient spectrum. -/
def baseConeIsLimit : IsLimit (baseCone α) :=
  Over.isLimitLiftCone (targetSpecDiagram α) (baseStructure α) (targetSpecCone α)
    (Spec.algebraMap R B) (baseStructure_fac α) (targetSpecConeIsLimit α)

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The original finite-generated base changes, viewed as schemes. -/
def schemeDiagram : (Index A B)ᵒᵖ ⥤ Scheme.{u} :=
  baseDiagram α ⋙ Over.pullback p ⋙ Over.forget X

/-- The cone of actual base changes. Its point is `pullback (Spec.algebraMap R B) p`. -/
def schemeCone : Cone (schemeDiagram α p) :=
  (Over.pullback p ⋙ Over.forget X).mapCone (baseCone α)

/-- The actual base-change cone is a limit. -/
def schemeConeIsLimit : IsLimit (schemeCone α p) :=
  isLimitOfPreserves (Over.pullback p ⋙ Over.forget X) (baseConeIsLimit α)

/-- The original total cone leg is Cartesian over the original coefficient leg. -/
theorem coefficientProjection_isPullback (s : (Index A B)ᵒᵖ) :
    IsPullback (pullback.fst (Spec.algebraMap R B) p)
      ((schemeCone α p).π.app s) ((targetSpecCone α).π.app s)
      (pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p) :=
  Over.pullback_map_isPullback p ((baseCone α).π.app s)

instance stage_isAffine [IsAffine X] (s : (Index A B)ᵒᵖ) :
    IsAffine ((schemeDiagram α p).obj s) := by
  change IsAffine (pullback (Spec.algebraMap R (targetStage α s.unop)) p)
  infer_instance

instance coefficientProjection_smooth [Smooth p] (s : (Index A B)ᵒᵖ) :
    Smooth (pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p) :=
  inferInstance

instance transition_isAffineHom {s t : (Index A B)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((schemeDiagram α p).map g) := by
  apply MorphismProperty.overPullbackMap (P := @IsAffineHom) p ((baseDiagram α).map g)
  change IsAffineHom (Spec.map _)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance stage_compact [QuasiCompact p] (s : (Index A B)ᵒᵖ) :
    CompactSpace ((schemeDiagram α p).obj s) := by
  change CompactSpace (pullback (Spec.algebraMap R (targetStage α s.unop)) p : Scheme)
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p)

set_option backward.isDefEq.respectTransparency.types false in
instance stage_quasiSeparated [QuasiSeparated p] (s : (Index A B)ᵒᵖ) :
    QuasiSeparatedSpace ((schemeDiagram α p).obj s) := by
  change QuasiSeparatedSpace (pullback (Spec.algebraMap R (targetStage α s.unop)) p : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p)

/-- The canonical projection from the standard-order base change to a
finite-generated coefficient stage. -/
def projection (s : (Index A B)ᵒᵖ) :
    pullback p (Spec.algebraMap R B) ⟶ (schemeDiagram α p).obj s :=
  (pullbackSymmetry p (Spec.algebraMap R B)).hom ≫ (schemeCone α p).π.app s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem projection_snd (s : (Index A B)ᵒᵖ) :
    projection α p s ≫
      pullback.snd (Spec.algebraMap R (targetStage α s.unop)) p =
        pullback.fst p (Spec.algebraMap R B) := by
  have h : (schemeCone α p).π.app s ≫
      pullback.snd (Spec.algebraMap R (targetStage α s.unop)) p =
        pullback.snd (Spec.algebraMap R B) p :=
    Over.w ((Over.pullback p).map ((baseCone α).π.app s))
  rw [projection, Category.assoc, h]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem projection_fst (s : (Index A B)ᵒᵖ) :
    projection α p s ≫
      pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p =
        pullback.snd p (Spec.algebraMap R B) ≫
          Spec.map (CommRingCat.ofHom (targetStage α s.unop).val.toRingHom) := by
  have h : (schemeCone α p).π.app s ≫
      pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p =
        pullback.fst (Spec.algebraMap R B) p ≫
          Spec.map (CommRingCat.ofHom (targetStage α s.unop).val.toRingHom) :=
    pullback.lift_fst _ _ _
  rw [projection, Category.assoc, h]
  simp

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
