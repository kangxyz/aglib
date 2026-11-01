/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Transport

/-! # Actual action and difference morphisms construct the existing torsor action

Four equations on the original finite products imply the action and unique
transport laws on every generalized point. The resulting object is the
existing TorsorAction, and its action morphism is the supplied original map.
Represented sheaf actions and full-faithful descent derive these finite
equations from their actual suppliers before invoking this constructor.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.TorsorAction

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A : Grp C} {Y : C}

/-- Evaluate the actual action morphism on the actual product of the two points. -/
def actOfMap (m : A.X ⊗ Y ⟶ Y) {T : C} (a : T ⟶ A.X) (x : T ⟶ Y) : T ⟶ Y :=
  lift a x ≫ m

theorem actOfMap_naturality (m : A.X ⊗ Y ⟶ Y) {T U : C} (f : T ⟶ U)
    (a : U ⟶ A.X) (x : U ⟶ Y) :
    f ≫ actOfMap m a x = actOfMap m (f ≫ a) (f ≫ x) := by
  simp only [actOfMap, ← comp_lift, Category.assoc]

/-- Evaluate the actual positive difference morphism on a pair of existing points. -/
def differenceOfMap (d : Y ⊗ Y ⟶ A.X) {T : C} (x y : T ⟶ Y) : T ⟶ A.X :=
  lift x y ≫ d

theorem differenceOfMap_naturality (d : Y ⊗ Y ⟶ A.X) {T U : C} (f : T ⟶ U)
    (x y : U ⟶ Y) :
    f ≫ differenceOfMap d x y = differenceOfMap d (f ≫ x) (f ≫ y) := by
  simp only [differenceOfMap, ← comp_lift, Category.assoc]

variable (m : A.X ⊗ Y ⟶ Y) (d : Y ⊗ Y ⟶ A.X)
  (hOne : actOfMap m 1 (𝟙 Y) = 𝟙 Y)
  (hMul : actOfMap m
    ((fst (A.X ⊗ A.X) Y ≫ fst A.X A.X) *
      (fst (A.X ⊗ A.X) Y ≫ snd A.X A.X)) (snd (A.X ⊗ A.X) Y) =
    actOfMap m (fst (A.X ⊗ A.X) Y ≫ fst A.X A.X)
      (actOfMap m (fst (A.X ⊗ A.X) Y ≫ snd A.X A.X) (snd (A.X ⊗ A.X) Y)))
  (hDifference : actOfMap m (differenceOfMap d (fst Y Y) (snd Y Y)) (fst Y Y) = snd Y Y)
  (hRecover : differenceOfMap d (snd A.X Y)
    (actOfMap m (fst A.X Y) (snd A.X Y)) = fst A.X Y)

include hOne in
/-- One actual finite-product unit equation implies the law on every point. -/
theorem actOfMap_one {T : C} (x : T ⟶ Y) : actOfMap m 1 x = x := by
  have h := congrArg (fun k => x ≫ k) hOne
  simpa only [actOfMap_naturality, MonObj.comp_one, Category.comp_id] using h

include hMul in
/-- One actual finite-product associativity equation implies the law on every point. -/
theorem actOfMap_mul {T : C} (a b : T ⟶ A.X) (x : T ⟶ Y) :
    actOfMap m (a * b) x = actOfMap m a (actOfMap m b x) := by
  have h := congrArg (fun k => lift (lift a b) x ≫ k) hMul
  rw [actOfMap_naturality, actOfMap_naturality, actOfMap_naturality, MonObj.comp_mul] at h
  simpa only [lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc] using h

include hDifference in
/-- The same positive difference acts correctly on all pairs of existing points. -/
theorem actOfMap_difference {T : C} (x y : T ⟶ Y) :
    actOfMap m (differenceOfMap d x y) x = y := by
  have h := congrArg (fun k => lift x y ≫ k) hDifference
  rw [actOfMap_naturality, differenceOfMap_naturality] at h
  simpa only [lift_fst, lift_snd] using h

include hRecover in
/-- The actual difference recovers every translating coefficient on every point. -/
theorem differenceOfMap_act {T : C} (a : T ⟶ A.X) (x : T ⟶ Y) :
    differenceOfMap d x (actOfMap m a x) = a := by
  have h := congrArg (fun k => lift a x ≫ k) hRecover
  rw [differenceOfMap_naturality, actOfMap_naturality] at h
  simpa only [lift_fst, lift_snd] using h

/-- The complete original action, with its unique transporter derived from the actual maps. -/
def ofCartesianMaps : TorsorAction A (toUnit Y) where
  act := actOfMap m
  naturality := actOfMap_naturality m
  one_act := actOfMap_one m hOne
  mul_act := actOfMap_mul m hMul
  over _ _ := toUnit_unique _ _
  transport x y _ := ⟨differenceOfMap d x y, actOfMap_difference m d hDifference x y,
    fun a ha => by
      rw [← ha]
      exact (differenceOfMap_act m d hRecover a x).symm⟩

/-- The constructed action keeps precisely the supplied original action morphism. -/
theorem ofCartesianMaps_actionMap :
    (ofCartesianMaps m d hOne hMul hDifference hRecover).actionMap = m := by
  change lift (fst A.X Y) (snd A.X Y) ≫ m = m
  rw [lift_fst_snd, Category.id_comp]

/-- The chosen positive transport is identified with the original difference by uniqueness. -/
theorem ofCartesianMaps_positiveTransport {T : C} (x y : T ⟶ Y) :
    (ofCartesianMaps m d hOne hMul hDifference hRecover).positiveTransport x y =
      differenceOfMap d x y :=
  (ofCartesianMaps m d hOne hMul hDifference hRecover).positiveTransport_eq x y _
    (actOfMap_difference m d hDifference x y)

end CategoryTheory.TorsorAction
