/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Transport

/-! # The original categorical point torsor in additive coefficient coordinates

The carrier is the same set of generalized points. A genuine group marking
expresses its existing action additively; the original unique transporter proves
UniqueTransport. Its difference is identified with the same positive categorical
transporter. No topology, finiteness, geometric points or nonemptiness is used.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.TorsorAction

universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A : Grp C} {Y : C} (τ : TorsorAction A (toUnit Y)) (T : C)
  {M : Type w} [AddCommGroup M] (mark : (T ⟶ A.X) ≃* Multiplicative M)

/-- The same actual point action written through its supplied coefficient marking. -/
@[instance_reducible] def pointTranslation : AddAction M (T ⟶ Y) where
  vadd a t := τ.act (mark.symm (Multiplicative.ofAdd a)) t
  zero_vadd t := by
    change τ.act (mark.symm 1) t = t
    rw [map_one, τ.one_act]
  add_vadd a b t := by
    change τ.act (mark.symm (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) t =
      τ.act (mark.symm (Multiplicative.ofAdd a))
        (τ.act (mark.symm (Multiplicative.ofAdd b)) t)
    rw [map_mul, τ.mul_act]

/-- Unique transport on the original points, with no global nonempty instance. -/
theorem pointTranslation_unique :
    letI := pointTranslation τ T mark
    AddAction.TorsorAugmentation.UniqueTransport M (T ⟶ Y) := by
  let := pointTranslation τ T mark
  intro x y
  obtain ⟨a, ha, hu⟩ := τ.transport x y (toUnit_unique _ _)
  refine ⟨(mark a).toAdd, ?_, ?_⟩
  · change τ.act (mark.symm (mark a)) x = y
    rw [mark.symm_apply_apply]
    exact ha
  · intro b hb
    change τ.act (mark.symm (Multiplicative.ofAdd b)) x = y at hb
    have hm := congrArg mark (hu _ hb)
    rw [mark.apply_symm_apply] at hm
    exact congrArg Multiplicative.toAdd hm

/-- The additive difference is exactly the original positive categorical transport value. -/
theorem pointTranslation_difference (s t : T ⟶ Y) :
    letI := pointTranslation τ T mark
    AddAction.TorsorAugmentation.difference (pointTranslation_unique τ T mark) t s =
      (mark (τ.positiveTransport s t)).toAdd := by
  let := pointTranslation τ T mark
  apply AddAction.TorsorAugmentation.difference_eq
  change τ.act (mark.symm (mark (τ.positiveTransport s t))) s = t
  rw [mark.symm_apply_apply]
  exact τ.act_positiveTransport s t

end CategoryTheory.TorsorAction
