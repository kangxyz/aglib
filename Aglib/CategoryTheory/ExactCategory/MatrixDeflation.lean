/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
/-!
# Admissible epimorphisms with an extra matrix entry

In a Quillen exact category, adding an arbitrary summand to the source of an
admissible epimorphism again gives an admissible epimorphism. The argument uses
only the base-change and composition axioms.
-/
@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The identity in the first coordinate and an arbitrary map in the second
coordinate form a pullback square. -/
lemma isPullback_biprod_map_right {A B T : C} (p : B ⟶ T) :
    IsPullback (biprod.snd : A ⊞ B ⟶ B) (biprod.map (𝟙 A) p)
      p (biprod.snd : A ⊞ T ⟶ T) := by
  apply IsPullback.mk' (by simp)
  · intro W φ ψ h₁ h₂
    apply biprod.hom_ext
    · simpa using congrArg (fun k => k ≫ biprod.fst) h₂
    · exact h₁
  · intro W a b h
    refine ⟨biprod.lift (b ≫ biprod.fst) a, by simp, ?_⟩
    apply biprod.hom_ext
    · simp
    · simpa using h

open ZeroObject in
/-- The split epimorphism `[f, 1]` is a base change of the map `A ⟶ 0`.
The universal lift sends `(a,b)` to `(a,b-af)`. -/
lemma isPullback_biprod_desc_id {A T : C} (f : A ⟶ T) :
    IsPullback (biprod.fst : A ⊞ T ⟶ A) (biprod.desc f (𝟙 T))
      (0 : A ⟶ 0) (0 : T ⟶ 0) := by
  apply IsPullback.mk' (by simp)
  · intro W φ ψ h₁ h₂
    apply biprod.hom_ext _ _ h₁
    simp only [biprod.desc_eq, Category.comp_id, Preadditive.comp_add,
      ← Category.assoc, h₁] at h₂
    exact add_left_cancel h₂
  · intro W a b h
    refine ⟨biprod.lift a (b - a ≫ f), by simp, ?_⟩
    simp [sub_eq_add_neg, add_left_comm]

/-- Adding an arbitrary component to an admissible epimorphism preserves
admissibility. -/
lemma deflation_biprod_desc (E : CategoryTheory.ExactCategory.ExactStructure C) {A B T : C}
    (f : A ⟶ T) (p : B ⟶ T) (hp : E.deflation p) :
    E.deflation (biprod.desc f p) := by
  have hmap : E.deflation (biprod.map (𝟙 A) p) :=
    E.deflation.of_isPullback (isPullback_biprod_map_right p) hp
  have hdesc : E.deflation (biprod.desc f (𝟙 T)) :=
    E.deflation.of_isPullback (isPullback_biprod_desc_id f) (E.deflation_zero A)
  have hcomp := E.deflation_comp _ _ hmap hdesc
  convert hcomp using 1
  ext <;> simp

end CategoryTheory.ExactCategory.ExactStructure
