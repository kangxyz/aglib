/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! Original test points under the original family base-change comparison. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

/-- The original pair of test points is transported by the original
family comparison to the adjoint source point and the same parameter
point over the original base. -/
theorem lift_left_comp_familyBaseChangeIso
    {S S' : Scheme.{u}} (b : S' ⟶ S) (A : Over S) {U T : Over S'}
    (x : U ⟶ (Over.pullback b).obj A) (t : U ⟶ T) :
    (lift x t).left ≫ (familyBaseChangeIso A.hom b T).hom =
      (lift (((Over.mapPullbackAdj b).homEquiv U A).symm x) ((Over.map b).map t)).left := by
  let d := ((Over.mapPullbackAdj b).homEquiv U A).symm x
  let s := (Over.map b).map t
  have hd : d.left = x.left ≫ pullback.fst A.hom b := rfl
  have hs : s.left = t.left := rfl
  let e := (familyBaseChangeIso A.hom b T).hom
  let v := (lift x t).left
  let w := (lift d s).left
  have hv₁ : v ≫ pullback.fst (pullback.snd A.hom b) T.hom = x.left := by
    simpa only [v, Over.comp_left, Over.fst_left, Over.pullback_obj_hom, Over.pullback_obj_left]
      using congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x t)
  have hv₂ : v ≫ pullback.snd (pullback.snd A.hom b) T.hom = t.left := by
    simpa only [v, Over.comp_left, Over.snd_left, Over.pullback_obj_hom]
      using congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x t)
  have hw₁ : w ≫ pullback.fst A.hom (T.hom ≫ b) = d.left := by
    simpa only [w, Over.comp_left, Over.fst_left, Over.map_obj_hom]
      using congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst d s)
  have hw₂ : w ≫ pullback.snd A.hom (T.hom ≫ b) = s.left := by
    simpa only [w, Over.comp_left, Over.snd_left, Over.map_obj_hom, Over.map_obj_left]
      using congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd d s)
  apply pullback.hom_ext
  · change (v ≫ e) ≫ pullback.fst A.hom (T.hom ≫ b) =
      w ≫ pullback.fst A.hom (T.hom ≫ b)
    calc
      _ = v ≫ (e ≫ pullback.fst A.hom (T.hom ≫ b)) := Category.assoc _ _ _
      _ = v ≫ pullback.fst (pullback.snd A.hom b) T.hom ≫ pullback.fst A.hom b :=
        congrArg (fun a => v ≫ a) (familyBaseChangeIso_hom_fst A.hom b T)
      _ = x.left ≫ pullback.fst A.hom b := by rw [← Category.assoc, hv₁]
      _ = d.left := hd.symm
      _ = _ := hw₁.symm
  · change (v ≫ e) ≫ pullback.snd A.hom (T.hom ≫ b) =
      w ≫ pullback.snd A.hom (T.hom ≫ b)
    calc
      _ = v ≫ (e ≫ pullback.snd A.hom (T.hom ≫ b)) := Category.assoc _ _ _
      _ = v ≫ pullback.snd (pullback.snd A.hom b) T.hom :=
        congrArg (fun a => v ≫ a) (familyBaseChangeIso_hom_snd A.hom b T)
      _ = t.left := hv₂
      _ = s.left := hs.symm
      _ = _ := hw₂.symm

end AlgebraicGeometry.Scheme.RelativePicard
