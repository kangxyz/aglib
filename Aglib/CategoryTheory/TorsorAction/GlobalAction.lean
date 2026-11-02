/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-! # Original global translations of a cartesian torsor action

Actual terminal sections act by automorphisms of the unchanged torsor object.
The inverse is translation by the inverse section, and the multiplication
orientation is the native automorphism-group orientation. The construction
uses only the original action laws and retains the original structural map.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.TorsorAction

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {H : Grp C} {Y B : C} {p : Y ⟶ B} (τ : TorsorAction H p)

/-- The original endomorphism obtained by acting with a terminal section. -/
def globalTranslation (a : 𝟙_ C ⟶ H.X) : Y ⟶ Y :=
  τ.act (toUnit Y ≫ a) (𝟙 Y)

/-- Translation acts on every original generalized point by the given action. -/
theorem comp_globalTranslation {T : C} (x : T ⟶ Y) (a : 𝟙_ C ⟶ H.X) :
    x ≫ τ.globalTranslation a = τ.act (toUnit T ≫ a) x := by
  dsimp only [globalTranslation]
  rw [τ.naturality]
  simp only [comp_toUnit_assoc, Category.comp_id]

@[simp]
theorem globalTranslation_one : τ.globalTranslation 1 = 𝟙 Y := by
  simp only [globalTranslation, MonObj.comp_one, τ.one_act]

/-- Categorical composition reverses the order of the two left translations. -/
theorem globalTranslation_comp (a b : 𝟙_ C ⟶ H.X) :
    τ.globalTranslation a ≫ τ.globalTranslation b = τ.globalTranslation (b * a) := by
  rw [τ.comp_globalTranslation]
  dsimp only [globalTranslation]
  rw [← τ.mul_act, ← MonObj.comp_mul]

/-- Every original global translation preserves the original torsor map. -/
@[reassoc (attr := simp)]
theorem globalTranslation_over (a : 𝟙_ C ⟶ H.X) :
    τ.globalTranslation a ≫ p = p := by
  exact (τ.over _ (𝟙 Y)).trans (Category.id_comp p)

/-- The actual translation automorphism, with inverse from the inverse section. -/
def globalTranslationIso (a : 𝟙_ C ⟶ H.X) : Aut Y where
  hom := τ.globalTranslation a
  inv := τ.globalTranslation a⁻¹
  hom_inv_id := by rw [τ.globalTranslation_comp, inv_mul_cancel, τ.globalTranslation_one]
  inv_hom_id := by rw [τ.globalTranslation_comp, mul_inv_cancel, τ.globalTranslation_one]

/-- The native automorphism group receives the original global-section group
with its actual multiplication orientation. -/
def globalAction : (𝟙_ C ⟶ H.X) →* Aut Y where
  toFun := τ.globalTranslationIso
  map_one' := by
    apply Aut.ext
    exact τ.globalTranslation_one
  map_mul' a b := by
    apply Aut.ext
    exact (τ.globalTranslation_comp b a).symm

/-- The global action's original pointwise formula. -/
theorem globalAction_apply {T : C} (x : T ⟶ Y) (a : 𝟙_ C ⟶ H.X) :
    x ≫ (τ.globalAction a).hom = τ.act (toUnit T ≫ a) x :=
  τ.comp_globalTranslation x a


/-- If original terminal coefficient sections evaluate bijectively on a test
object, the original torsor translations have a regular orbit at every point
with that test object. The bijection is derived from genuine unique transport. -/
theorem globalAction_orbit_bijective (τ : TorsorAction H (toUnit Y))
    {T : C} (x : T ⟶ Y)
    (h : Function.Bijective (fun a : 𝟙_ C ⟶ H.X => toUnit T ≫ a)) :
    Function.Bijective (fun a => x ≫ (τ.globalAction a).hom) := by
  constructor
  · intro a b hab
    apply h.injective
    apply (τ.fiberEquiv x).injective
    apply Subtype.ext
    change τ.act (toUnit T ≫ a) x = τ.act (toUnit T ≫ b) x
    simpa only [τ.globalAction_apply] using hab
  · intro y
    obtain ⟨b, hb, _⟩ := τ.transport x y (by simp only [comp_toUnit])
    obtain ⟨a, ha⟩ := h.surjective b
    refine ⟨a, ?_⟩
    exact (τ.globalAction_apply x a).trans
      ((congrArg (fun b => τ.act b x) ha).trans hb)

end CategoryTheory.TorsorAction
