/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base-first pullback arrows

The actual pullback arrow of a morphism in an over category is constructed
with the base-first pullback convention. Projection equations, comparison
with `Over.pullback`, and its cartesian square are supplied once here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Pull back an over-category arrow, using the base-first convention. -/
def baseChangeOverHom {S T : Scheme.{u}} (b : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) : pullback b A.hom ⟶ pullback b B.hom :=
  pullback.lift (pullback.fst b A.hom) (pullback.snd b A.hom ≫ a.left) (by
    rw [Category.assoc, a.w]
    exact pullback.condition)

@[reassoc (attr := simp)]
lemma baseChangeOverHom_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) :
    baseChangeOverHom b a ≫ pullback.fst b B.hom = pullback.fst b A.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeOverHom_snd {S T : Scheme.{u}} (b : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) :
    baseChangeOverHom b a ≫ pullback.snd b B.hom = pullback.snd b A.hom ≫ a.left :=
  pullback.lift_snd _ _ _

/-- Explicit orientation comparison with the native over-category functor. -/
lemma baseChangeOverHom_eq_overPullback {S T : Scheme.{u}} (b : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) :
    baseChangeOverHom b a = (pullbackSymmetry b A.hom).hom ≫
      ((Over.pullback b).map a).left ≫ (pullbackSymmetry B.hom b).hom := by
  apply pullback.hom_ext <;> simp [baseChangeOverHom, Over.pullback_map_left]

/-- The base-first pulled arrow is cartesian over its original arrow. -/
lemma isPullback_baseChangeOverHom {S T : Scheme.{u}} (b : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) :
    IsPullback (baseChangeOverHom b a) (pullback.snd b A.hom)
      (pullback.snd b B.hom) a.left := by
  apply IsPullback.of_right (h₁₂ := pullback.fst b B.hom)
    (h₂₂ := B.hom) (v₁₃ := b) _ (baseChangeOverHom_snd b a)
    (IsPullback.of_hasPullback b B.hom)
  simpa only [baseChangeOverHom_fst, Over.w] using
    (IsPullback.of_hasPullback b A.hom)

end AlgebraicGeometry.Scheme
