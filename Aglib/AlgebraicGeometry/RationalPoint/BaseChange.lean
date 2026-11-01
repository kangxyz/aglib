/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual rational sections under cartesian base change

The actual lifted section and its cartesian square are shared by rational-point
boundary geometry and divisor-class transport. No smoothness, genus, properness
or algebraic closure is needed for these constructions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RationalPoint

variable {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}

/-- Compatible rational sections of a cartesian structure square themselves
form a cartesian square. -/
theorem isPullback_section (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback b s.structureMap r.structureMap q)
    (h : s.sectionMap ≫ b = q ≫ r.sectionMap) :
    IsPullback q s.sectionMap r.sectionMap b := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := s.structureMap) (h₂₂ := r.structureMap)
    (v₁₃ := q) _ h H.flip
  simpa only [s.section_comp, r.section_comp] using (IsPullback.of_id_fst (f := q))

/-- The actual rational section of the literal base change, with no independent
choice of a target point. -/
def baseChange (r : RationalPoint k X) (q : Spec (.of K) ⟶ Spec (.of k)) :
    RationalPoint K (pullback r.structureMap q) where
  structureMap := pullback.snd r.structureMap q
  sectionMap := pullback.lift (q ≫ r.sectionMap) (𝟙 _)
    (by rw [Category.assoc, r.section_comp, Category.comp_id, Category.id_comp])
  section_comp := pullback.lift_snd _ _ _

/-- The lifted section retains the original first-projection equation. -/
@[reassoc (attr := simp)]
theorem baseChange_sectionMap_fst (r : RationalPoint k X)
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    (r.baseChange q).sectionMap ≫ pullback.fst r.structureMap q = q ≫ r.sectionMap :=
  pullback.lift_fst _ _ _

/-- The actual lifted section is the cartesian pullback of the original section. -/
theorem baseChange_isPullback (r : RationalPoint k X)
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    IsPullback q (r.baseChange q).sectionMap r.sectionMap (pullback.fst r.structureMap q) :=
  isPullback_section r (r.baseChange q) q (pullback.fst r.structureMap q)
    (IsPullback.of_hasPullback _ _) (baseChange_sectionMap_fst r q)

end AlgebraicGeometry.Scheme.RationalPoint
