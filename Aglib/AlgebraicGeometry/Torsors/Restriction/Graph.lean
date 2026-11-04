/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Torsors.Restriction

/-! The original graph and action of a cover in the relative slice. -/

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Torsors.Restriction

open Relative

universe u

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {Y E : Over S}

/-- The graph of the original cover map into the pullback of its source. -/
def relativeCoverLift (f : Y ⟶ E) :
    canonicalRelativeSpace E f ⟶ (Over.pullback E.hom).obj Y :=
  Over.homMk (pullback.lift (𝟙 Y.left) f.left (by simp))
    (by simp)

/-- The diagonal point of the base change of the original target to itself. -/
def relativeTargetDiagonal (E : Over S) :
    Over.mk (𝟙 E.left) ⟶ (Over.pullback E.hom).obj E :=
  Over.homMk (pullback.lift (𝟙 E.left) (𝟙 E.left) rfl) (by simp)

/-- The original graph lies over the diagonal section on every test scheme. -/
theorem relativeCoverLift_over (f : Y ⟶ E) {U : Over E.left}
    (v : U ⟶ canonicalRelativeSpace E f) :
    v ≫ relativeCoverLift f ≫ (Over.pullback E.hom).map f =
      (Over.homMk U.hom (by simp) : U ⟶ Over.mk (𝟙 E.left)) ≫ relativeTargetDiagonal E := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, relativeCoverLift,
      relativeTargetDiagonal, Over.homMk_left, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
    exact Over.w v
  · simp only [Over.comp_left, Over.pullback_map_left, relativeCoverLift,
      relativeTargetDiagonal, Over.homMk_left, Category.assoc, pullback.lift_snd]
    exact Over.w v

variable {K G H : Grp (Over S)} {q : G ⟶ H}

private theorem relativeCoverLift_global {U : Over H.X.left}
    (v : U ⟶ canonicalRelativeSpace H.X q.hom.hom) :
    globalCoefficient H.X G (v ≫ relativeCoverLift q.hom.hom) =
      (Over.map H.X.hom).map v ≫ (canonicalTotalIso H.X q.hom.hom).hom := by
  apply Over.OverMorphism.ext
  simp only [globalCoefficient_left, Over.comp_left, relativeCoverLift,
    Over.homMk_left, Category.assoc, pullback.lift_fst, Over.map_map_left]
  rfl

private theorem globalCoefficient_map {U : Over H.X.left}
    (i : K ⟶ G) (a : U ⟶ (pullbackGroup H.X K).X) :
    globalCoefficient H.X G (a ≫ (Over.pullback H.X.hom).map i.hom.hom) =
      globalCoefficient H.X K a ≫ i.hom.hom := by
  apply Over.OverMorphism.ext
  simp only [globalCoefficient_left, Over.comp_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]

/-- The original graph carries the restricted action to the original kernel translation. -/
theorem relativeCoverLift_act (m : KernelMarking K G H q) {U : Over H.X.left}
    (a : U ⟶ (pullbackGroup H.X K).X)
    (v : U ⟶ canonicalRelativeSpace H.X q.hom.hom) :
    let : GrpObj ((Over.pullback H.X.hom).obj G.X) := (pullbackGroup H.X G).grp
    (relativeTorsorRestrictionOfMap H.X K q.hom.hom m.toTorsorAction).act a v ≫
        relativeCoverLift q.hom.hom =
      (a ≫ (Over.pullback H.X.hom).map m.inclusion.hom.hom) *
        (v ≫ relativeCoverLift q.hom.hom) := by
  dsimp only
  let : GrpObj ((Over.pullback H.X.hom).obj G.X) := (pullbackGroup H.X G).grp
  apply (pullbackHomMulEquiv H.X G U).symm.injective
  rw [map_mul]
  change globalCoefficient H.X G
    ((relativeTorsorRestrictionOfMap H.X K q.hom.hom m.toTorsorAction).act a v ≫
      relativeCoverLift q.hom.hom) =
    globalCoefficient H.X G (a ≫ (Over.pullback H.X.hom).map m.inclusion.hom.hom) *
      globalCoefficient H.X G (v ≫ relativeCoverLift q.hom.hom)
  rw [relativeCoverLift_global, relativeCoverLift_global, globalCoefficient_map]
  apply Over.OverMorphism.ext
  change ((relativeTorsorRestrictionOfMap H.X K q.hom.hom m.toTorsorAction).act a v).left ≫
      𝟙 G.X.left =
    (m.toTorsorAction.act (globalCoefficient H.X K a)
      ((Over.map H.X.hom).map v ≫ (canonicalTotalIso H.X q.hom.hom).hom)).left
  have h := relativeTorsorRestrictionOfMap_point H.X K q.hom.hom m.toTorsorAction a v
  let w : U.left ⟶ G.X.left :=
    ((relativeTorsorRestrictionOfMap H.X K q.hom.hom m.toTorsorAction).act a v).left
  exact (Category.comp_id w).trans h

end AlgebraicGeometry.Scheme.Torsors.Restriction
