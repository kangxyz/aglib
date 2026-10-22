/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Generic lifts through integral morphisms from a normal scheme

For an actual map from a normal integral scheme, any lift of its original
generic point through an integral morphism extends uniquely over the whole
scheme. The construction uses the relative normalization of the original
generic inclusion to lift into the literal pullback. No assumption on the integral target's
reducedness, irreducibility, dimension or finiteness is imposed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [hX : IsIntegral X] (hN : NormalStalks X)
  {P Y : Scheme.{u}} (f : X ⟶ P) (q : Y ⟶ P) [IsIntegralHom q]
  (g : Spec X.functionField ⟶ Y)
  (hg : g ≫ q = X.fromSpecStalk (genericPoint X) ≫ f)

/-- Extend the supplied generic lift through the actual integral morphism.
The normal scheme is recovered from the normalization of its own generic inclusion. -/
def integralGenericLift : X ⟶ Y := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
  let j := X.fromSpecStalk (genericPoint X)
  exact inv j.fromNormalization ≫
    j.normalizationDesc (pullback.lift g j hg) (pullback.snd q f) (by simp) ≫
      pullback.fst q f

/-- The extension has the original structural map over the original target. -/
@[reassoc (attr := simp)]
theorem integralGenericLift_over : integralGenericLift X hN f q g hg ≫ q = f := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
  simp only [integralGenericLift, Category.assoc, pullback.condition]
  rw [← Category.assoc _ _ f, Hom.normalizationDesc_comp]
  simp

/-- Restriction along the literal generic inclusion is the originally supplied lift. -/
@[reassoc (attr := simp)]
theorem integralGenericLift_generic :
    X.fromSpecStalk (genericPoint X) ≫ integralGenericLift X hN f q g hg = g := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
  let j := X.fromSpecStalk (genericPoint X)
  have hj : j ≫ inv j.fromNormalization = j.toNormalization := by
    calc
      _ = (j.toNormalization ≫ j.fromNormalization) ≫ inv j.fromNormalization :=
        congrArg (fun k => k ≫ inv j.fromNormalization)
          j.toNormalization_fromNormalization.symm
      _ = _ := by simp
  change j ≫ (inv j.fromNormalization ≫
    j.normalizationDesc (pullback.lift g j hg) (pullback.snd q f) (by simp) ≫
      pullback.fst q f) = g
  rw [← Category.assoc, hj]
  simp only [Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]

include hX hN hg in
/-- A generic lift through an integral morphism has exactly one extension from
the original normal integral scheme, retaining both original triangles. -/
theorem existsUnique_integralGenericLift :
    ∃! l : X ⟶ Y, l ≫ q = f ∧ X.fromSpecStalk (genericPoint X) ≫ l = g := by
  refine ⟨integralGenericLift X hN f q g hg,
    ⟨integralGenericLift_over X hN f q g hg, integralGenericLift_generic X hN f q g hg⟩,
    ?_⟩
  intro l hl
  exact ext_of_isDominant_of_isSeparated q
    (hl.1.trans (integralGenericLift_over X hN f q g hg).symm)
    (X.fromSpecStalk (genericPoint X))
    (hl.2.trans (integralGenericLift_generic X hN f q g hg).symm)

end AlgebraicGeometry.Scheme
