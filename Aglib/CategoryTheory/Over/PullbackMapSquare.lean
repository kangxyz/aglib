/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The original coefficient square of an Over pullback map

The existing Over pullback map, not a new chosen comparison, is Cartesian
with the original first projections. The proof cancels the actual bottom
pullback square from the actual outer pullback square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over
universe u v

/-- Original Over base-change arrows form actual Cartesian coefficient squares. -/
theorem pullback_map_isPullback
    {C : Type u} [Category.{v} C] [HasPullbacks C] {S X : C}
    (p : X ⟶ S) {A B : Over S} (f : A ⟶ B) :
    IsPullback (Limits.pullback.fst A.hom p) ((Over.pullback p).map f).left
      f.left (Limits.pullback.fst B.hom p) := by
  have hfst : ((Over.pullback p).map f).left ≫ Limits.pullback.fst B.hom p =
      Limits.pullback.fst A.hom p ≫ f.left := by
    change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
    exact Limits.pullback.lift_fst _ _ _
  have hsnd : ((Over.pullback p).map f).left ≫ Limits.pullback.snd B.hom p =
      Limits.pullback.snd A.hom p := by
    change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
    exact Limits.pullback.lift_snd _ _ _
  have hout : IsPullback (Limits.pullback.fst A.hom p)
      (((Over.pullback p).map f).left ≫ Limits.pullback.snd B.hom p)
      (f.left ≫ B.hom) p := by
    rw [hsnd, Over.w]
    exact IsPullback.of_hasPullback A.hom p
  exact hout.of_bot hfst.symm (IsPullback.of_hasPullback B.hom p)

end CategoryTheory.Over
