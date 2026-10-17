/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Chosen pullbacks of a ring map in `CommRingCatᵒᵖ`

For `f : A ⟶ B` in `CommRingCat`, the pushout `B ⊗_A B = pushout₂ f` gives a chosen pullback of
`f.op` with itself in `CommRingCatᵒᵖ` (`CommRingCat.opChosenPullback f`). The threefold pullback
is the pushout `pushout₃ f` of the two copies of `B ⊗_A B` over the middle copy of `B`
(`opChosenPullback₃`). All projections are `op` of named ring maps (`pushoutInl`, `pushoutInr`,
`pushout₃Inl`, `pushout₃Inr`, `pushout₃Outer`, `pushout₃ι₁`, `pushout₃ι₂`, `pushout₃ι₃`), so that
`Spec` maps them to `Spec.map` of these ring maps, to which Aglib's
`Scheme.Modules.tildePullbackIso` applies; `Spec` maps the two chosen pullbacks to pullbacks of
schemes by Mathlib's `isPullback_SpecMap_of_isPushout`.

The pushout objects and maps are definitions, not abbreviations of Mathlib's `pushout`: every
later occurrence then carries the same `HasPushout` instance term, which keeps kernel checks
syntactic.

These are the chosen pullbacks for Mathlib's `Pseudofunctor.DescentData'` on `CommRingCatᵒᵖ`,
which reduce descent data along `f.op` to data over `B ⊗_A B` and `pushout₃ f`
(`Pseudofunctor.DescentData'.descentDataEquivalence`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace CommRingCat

variable {A B : CommRingCat.{u}} (f : A ⟶ B)

/-- The ring `B ⊗_A B`, Mathlib's `pushout f f`. -/
def pushout₂ : CommRingCat.{u} := pushout f f

/-- The first inclusion `B ⟶ B ⊗_A B`. -/
def pushoutInl : B ⟶ pushout₂ f := pushout.inl f f

/-- The second inclusion `B ⟶ B ⊗_A B`. -/
def pushoutInr : B ⟶ pushout₂ f := pushout.inr f f

lemma pushout₂_condition : f ≫ pushoutInl f = f ≫ pushoutInr f := pushout.condition

lemma isPushout₂ : IsPushout f f (pushoutInl f) (pushoutInr f) := IsPushout.of_hasPushout f f

/-- The ring of the threefold pullback: the pushout of the two copies of `B ⊗_A B` over the middle
copy of `B`. -/
def pushout₃ : CommRingCat.{u} := pushout (pushoutInr f) (pushoutInl f)

/-- The inclusion `B ⊗_A B ⟶ pushout₃ f` of the factors `1, 2`. -/
def pushout₃Inl : pushout₂ f ⟶ pushout₃ f := pushout.inl (pushoutInr f) (pushoutInl f)

/-- The inclusion `B ⊗_A B ⟶ pushout₃ f` of the factors `2, 3`. -/
def pushout₃Inr : pushout₂ f ⟶ pushout₃ f := pushout.inr (pushoutInr f) (pushoutInl f)

lemma isPushout₃ : IsPushout (pushoutInr f) (pushoutInl f) (pushout₃Inl f) (pushout₃Inr f) :=
  IsPushout.of_hasPushout _ _

/-- The two inclusions of `B ⊗_A B` into `pushout₃ f` agree on the middle factor. -/
lemma pushout₃_condition : pushoutInl f ≫ pushout₃Inr f = pushoutInr f ≫ pushout₃Inl f :=
  (isPushout₃ f).w.symm

/-- The first factor `B ⟶ pushout₃ f`. -/
def pushout₃ι₁ : B ⟶ pushout₃ f := pushoutInl f ≫ pushout₃Inl f

/-- The second factor `B ⟶ pushout₃ f`. -/
def pushout₃ι₂ : B ⟶ pushout₃ f := pushoutInr f ≫ pushout₃Inl f

/-- The third factor `B ⟶ pushout₃ f`. -/
def pushout₃ι₃ : B ⟶ pushout₃ f := pushoutInr f ≫ pushout₃Inr f

lemma pushoutInl_pushout₃Inl : pushoutInl f ≫ pushout₃Inl f = pushout₃ι₁ f := rfl

lemma pushoutInr_pushout₃Inl : pushoutInr f ≫ pushout₃Inl f = pushout₃ι₂ f := rfl

lemma pushoutInl_pushout₃Inr : pushoutInl f ≫ pushout₃Inr f = pushout₃ι₂ f :=
  pushout₃_condition f

lemma pushoutInr_pushout₃Inr : pushoutInr f ≫ pushout₃Inr f = pushout₃ι₃ f := rfl

/-- The inclusion `B ⊗_A B ⟶ pushout₃ f` of the factors `1, 3`. -/
def pushout₃Outer : pushout₂ f ⟶ pushout₃ f :=
  (isPushout₂ f).desc (pushout₃ι₁ f) (pushout₃ι₃ f) (by
    simp only [pushout₃ι₁, pushout₃ι₃, ← Category.assoc, pushout₂_condition]
    rw [Category.assoc, pushoutInr_pushout₃Inl, ← pushoutInl_pushout₃Inr, ← Category.assoc,
      pushout₂_condition, Category.assoc])

lemma pushoutInl_pushout₃Outer : pushoutInl f ≫ pushout₃Outer f = pushout₃ι₁ f :=
  (isPushout₂ f).inl_desc _ _ _

lemma pushoutInr_pushout₃Outer : pushoutInr f ≫ pushout₃Outer f = pushout₃ι₃ f :=
  (isPushout₂ f).inr_desc _ _ _

/-- The chosen pullback of `f.op` with itself in `CommRingCatᵒᵖ`: `op (B ⊗_A B)`. -/
abbrev opChosenPullback : ChosenPullback f.op f.op where
  pullback := op (pushout₂ f)
  p₁ := (pushoutInl f).op
  p₂ := (pushoutInr f).op
  condition := by rw [← op_comp, ← op_comp, pushout₂_condition]
  isLimit := (isPushout₂ f).op.flip.isLimit
  p := (f ≫ pushoutInl f).op
  hp₁ := by rw [← op_comp]

/-- The chosen threefold pullback of `f.op` in `CommRingCatᵒᵖ`: `op (pushout₃ f)`. -/
abbrev opChosenPullback₃ :
    ChosenPullback₃ (opChosenPullback f) (opChosenPullback f) (opChosenPullback f) where
  chosenPullback :=
    { pullback := op (pushout₃ f)
      p₁ := (pushout₃Inl f).op
      p₂ := (pushout₃Inr f).op
      condition := by
        change (pushout₃Inl f).op ≫ (pushoutInr f).op = (pushout₃Inr f).op ≫ (pushoutInl f).op
        rw [← op_comp, ← op_comp, pushout₃_condition]
      isLimit := (isPushout₃ f).op.flip.isLimit
      p := (pushout₃ι₂ f).op
      hp₁ := by
        change (pushout₃Inl f).op ≫ (pushoutInr f).op = (pushout₃ι₂ f).op
        rw [← op_comp, pushoutInr_pushout₃Inl] }
  p₁ := (pushout₃ι₁ f).op
  p₃ := (pushout₃ι₃ f).op
  l :=
    { f := (pushout₃Outer f).op
      f_p₁ := by
        change (pushout₃Outer f).op ≫ (pushoutInl f).op = (pushout₃ι₁ f).op
        rw [← op_comp, pushoutInl_pushout₃Outer]
      f_p₂ := by
        change (pushout₃Outer f).op ≫ (pushoutInr f).op = (pushout₃ι₃ f).op
        rw [← op_comp, pushoutInr_pushout₃Outer]
      f_p := by
        change (pushout₃Outer f).op ≫ (f ≫ pushoutInl f).op =
          (pushout₃Inl f).op ≫ (f ≫ pushoutInl f).op
        rw [← op_comp, ← op_comp, Category.assoc, Category.assoc, pushoutInl_pushout₃Outer,
          pushoutInl_pushout₃Inl] }
  hp₁ := by
    change (pushout₃Inl f).op ≫ (pushoutInl f).op = (pushout₃ι₁ f).op
    rw [← op_comp, pushoutInl_pushout₃Inl]
  hp₃ := by
    change (pushout₃Inr f).op ≫ (pushoutInr f).op = (pushout₃ι₃ f).op
    rw [← op_comp, pushoutInr_pushout₃Inr]

end CommRingCat
