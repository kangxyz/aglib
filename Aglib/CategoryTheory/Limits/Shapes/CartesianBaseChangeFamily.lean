/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The same Cartesian family after Cartesian base change

Two actual Cartesian squares determine the family map on the literal
coefficient pullback. Both the new family square and the original-target
square are proved Cartesian, with the original projections retained.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.IsPullback

universe v u

variable {C : Type u} [Category.{v} C]
    {Y X S B E D : C} {a : Y ⟶ X} {b : Y ⟶ B} {p : X ⟶ S} {β : B ⟶ S}
    (H : IsPullback a b p β)
    {δ : D ⟶ E} {i : D ⟶ B} {e : E ⟶ S} (K : IsPullback δ i e β)
    [HasPullback i b] [HasPullback p e]

/-- The actual base-changed family map, on the original coefficient pullback. -/
def baseChangeFamilyMap : pullback i b ⟶ pullback p e :=
  pullback.lift (pullback.snd i b ≫ a) (pullback.fst i b ≫ δ) (by
    calc
      (pullback.snd i b ≫ a) ≫ p = pullback.snd i b ≫ b ≫ β := by
        rw [Category.assoc, H.w]
      _ = pullback.fst i b ≫ i ≫ β := by rw [pullback.condition_assoc]
      _ = (pullback.fst i b ≫ δ) ≫ e := by rw [Category.assoc, K.w])

@[reassoc (attr := simp)]
theorem baseChangeFamilyMap_fst :
    H.baseChangeFamilyMap K ≫ pullback.fst p e = pullback.snd i b ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeFamilyMap_snd :
    H.baseChangeFamilyMap K ≫ pullback.snd p e = pullback.fst i b ≫ δ :=
  pullback.lift_snd _ _ _

/-- The base-changed family is Cartesian over the same new base. -/
theorem baseChangeFamilyMap_isPullback :
    IsPullback (H.baseChangeFamilyMap K) (pullback.fst i b) (pullback.snd p e) δ := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p e) (h₂₂ := e)
    _ (H.baseChangeFamilyMap_snd K) (IsPullback.of_hasPullback p e)
  rw [H.baseChangeFamilyMap_fst K, K.w]
  exact (IsPullback.of_hasPullback i b).flip.paste_horiz H

/-- The original-target square is Cartesian as well; this is the square
needed to return a target refinement of the changed family. -/
theorem baseChangeFamilyMap_target_isPullback :
    IsPullback (H.baseChangeFamilyMap K) (pullback.snd i b) (pullback.fst p e) a := by
  apply IsPullback.of_bot (v₂₁ := b) (v₂₂ := p)
    _ (H.baseChangeFamilyMap_fst K) H
  have h := (H.baseChangeFamilyMap_isPullback K).paste_vert K
  rw [show pullback.fst i b ≫ i = pullback.snd i b ≫ b from pullback.condition,
    show pullback.snd p e ≫ e = pullback.fst p e ≫ p from pullback.condition.symm] at h
  exact h

end CategoryTheory.IsPullback
