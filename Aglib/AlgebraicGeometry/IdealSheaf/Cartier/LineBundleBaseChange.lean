/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic

/-! Pullback of the actual positive Cartier line-bundle class. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Invertibility of the original ideal comparison gives the positive
line-bundle class comparison on the same Cartier divisors. -/
theorem pullbackClass_positiveCartier_of_isIso {D X D' X' : Scheme.{u}}
    (i : D ⟶ X) (j : D' ⟶ X') (a : D' ⟶ D) (b : X' ⟶ X)
    (w : a ≫ i = j ≫ b) (hi : IsEffectiveCartier i) (hj : IsEffectiveCartier j)
    (he : IsIso (idealPullbackMap i j b a w)) :
    pullbackClass b (classOf X (dualLineBundle X hi.idealLineBundle)) =
      classOf X' (dualLineBundle X' hj.idealLineBundle) := by
  have h : pullbackClass b (classOf X hi.idealLineBundle) = classOf X' hj.idealLineBundle := by
    rw [pullbackClass_classOf]
    let e := @asIso _ _ _ _ (idealPullbackMap i j b a w) he
    exact Quotient.sound ⟨e⟩
  rw [classOf_dual, classOf_dual, pullbackClass_neg, h]

/-- The positive class of the original Cartier divisor commutes with
flat base change through the actual Cartesian square. -/
theorem pullbackClass_positiveCartier_of_isPullback_of_flat {D X D' X' : Scheme.{u}}
    (i : D ⟶ X) (j : D' ⟶ X') (a : D' ⟶ D) (b : X' ⟶ X)
    (H : IsPullback a j i b) [Flat b] (hi : IsEffectiveCartier i) (hj : IsEffectiveCartier j) :
    pullbackClass b (classOf X (dualLineBundle X hi.idealLineBundle)) =
      classOf X' (dualLineBundle X' hj.idealLineBundle) := by
  let : IsClosedImmersion i := hi.isClosedImmersion
  have he := idealPullbackMap_isIso_of_flat i b j a H.w H
  exact pullbackClass_positiveCartier_of_isIso i j a b H.w hi hj he

end AlgebraicGeometry.Scheme.Hom
