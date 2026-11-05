/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeArrowBaseChangeLimit

/-! # Original source families for simultaneous arrow base changes

The source-stage base changes and family arrows are obtained by applying the
same native Over pullback functor to the actual original algebra arrows.
Their Cartesian coefficient squares and commuting cone squares retain all
original maps. No additional limit or finite presentation model is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
universe u
open Algebra.FiniteTypeArrowLimit

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- The quiver of the original opposite stage category. -/
local instance familyIndexQuiver : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver

/-- Original source stage over the same base. -/
def sourceStageBase (s : (Index A B)ᵒᵖ) : Over (Spec (.of R)) :=
  Over.mk (Spec.algebraMap R (sourceStage α s.unop))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original arrow as a morphism over its scalar base. -/
def originalBaseArrow : (baseCone α).pt ⟶ Over.mk (Spec.algebraMap R A) :=
  Over.homMk (Spec.map (CommRingCat.ofHom α.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact α.commutes r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual restriction of the original arrow at the same finite-type stage. -/
def stageBaseArrow (s : (Index A B)ᵒᵖ) : (baseDiagram α).obj s ⟶ sourceStageBase α s :=
  Over.homMk ((specDiagramMap α).app s) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (stageMap α s.unop).commutes r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original source inclusion leg over the scalar base. -/
def sourceBaseLeg (s : (Index A B)ᵒᵖ) : Over.mk (Spec.algebraMap R A) ⟶ sourceStageBase α s :=
  Over.homMk ((sourceSpecCone α).π.app s) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1)

/-- The actual coefficient arrows commute before base change. -/
theorem baseArrow_cone (s : (Index A B)ᵒᵖ) :
    originalBaseArrow α ≫ sourceBaseLeg α s =
      (baseCone α).π.app s ≫ stageBaseArrow α s := by
  apply Over.OverMorphism.ext
  exact (specDiagramMap_cone α s).symm

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The actual source-stage family target. -/
abbrev sourceStageFamily (s : (Index A B)ᵒᵖ) : Scheme.{u} :=
  ((Over.pullback p).obj (sourceStageBase α s)).left

/-- Original family map obtained by the native base-change functor. -/
def familyArrow : (schemeCone α p).pt ⟶ pullback (Spec.algebraMap R A) p :=
  ((Over.pullback p).map (originalBaseArrow α)).left

/-- Stage family map obtained by the same native base-change functor. -/
def stageFamilyArrow (s : (Index A B)ᵒᵖ) :
    (schemeDiagram α p).obj s ⟶ sourceStageFamily α p s :=
  ((Over.pullback p).map (stageBaseArrow α s)).left

/-- The original target-to-stage map used to retain geometric points. -/
def sourceFamilyLeg (s : (Index A B)ᵒᵖ) :
    pullback (Spec.algebraMap R A) p ⟶ sourceStageFamily α p s :=
  ((Over.pullback p).map (sourceBaseLeg α s)).left

/-- The coefficient square of each original stage family is Cartesian. -/
theorem stageFamily_isPullback (s : (Index A B)ᵒᵖ) :
    IsPullback (stageFamilyArrow α p s)
      (pullback.fst (Spec.algebraMap R (targetStage α s.unop)) p)
      (pullback.fst (Spec.algebraMap R (sourceStage α s.unop)) p)
      ((specDiagramMap α).app s) :=
  (Over.pullback_map_isPullback p (stageBaseArrow α s)).flip

/-- The limiting family has the same original Cartesian coefficient square. -/
theorem family_isPullback :
    IsPullback (familyArrow α p) (pullback.fst (Spec.algebraMap R B) p)
      (pullback.fst (Spec.algebraMap R A) p)
      (Spec.map (CommRingCat.ofHom α.toRingHom)) :=
  (Over.pullback_map_isPullback p (originalBaseArrow α)).flip

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original family and stage family commute with the original cone leg. -/
theorem familyArrow_cone (s : (Index A B)ᵒᵖ) :
    familyArrow α p ≫ sourceFamilyLeg α p s =
      (schemeCone α p).π.app s ≫ stageFamilyArrow α p s := by
  have h := congrArg (fun k => ((Over.pullback p).map k).left) (baseArrow_cone α s)
  simp only [Functor.map_comp, Over.comp_left] at h
  change familyArrow α p ≫ sourceFamilyLeg α p s =
    ((Over.pullback p).map ((baseCone α).π.app s)).left ≫ stageFamilyArrow α p s
  exact h

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
