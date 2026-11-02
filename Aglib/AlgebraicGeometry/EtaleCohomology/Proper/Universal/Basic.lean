/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.Property
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.HigherReduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.GeometryCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DerivedBaseChange
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Universal bounded exchange through the original maps

The initial predicate tests the original higher exchange on every coefficient
of its original source killed by the specified integer. Its native universal
closure also tests every coefficient on every pulled-back source. The latter
distinction is necessary for arbitrary base-change stability.

These predicates use the native standard derived models. The statement for
independently supplied models, the projective-line input and general proper
base change are separate obligations. No coefficient marking or invertibility
of its order is part of these predicates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Original all-degree exchange on coefficients of the original source,
using the native standard derived models. -/
def boundedBaseChange (n : ℕ) : MorphismProperty Scheme.{u} := fun {X S} f =>
  ∀ {X' S' : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g), boundedExchange n f f' g g' h.w.symm

private theorem boundedExchange_comp (n : ℕ) {Y X S Y' X' S' : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
    (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
    (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))
    (hf : boundedExchange n f f' g g' h₁)
    (hk : boundedExchange n k k' g' g'' h₂) :
    boundedExchange n (k ≫ f) (k' ≫ f') g g'' h := by
  intro F hF q
  exact Reduction.higherBaseChangeMap_comp_on_killedCoefficients
    f k f' k' g g' g'' h₁ h₂ h n hf hk F hF q

private theorem boundedExchange_descent (n : ℕ) {Y X S Y' X' S' : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y) [Surjective k]
    (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
    (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))
    (hk : boundedExchange n k k' g' g'' h₂)
    (hcomp : boundedExchange n (k ≫ f) (k' ≫ f') g g'' h) :
    boundedExchange n f f' g g' h₁ := by
  intro F hF q
  exact Reduction.higherBaseChangeMap_descent_on_killedCoefficients
    f k f' k' g g' g'' h₁ h₂ h n hk hcomp F hF q

/-- Every base change satisfies the original-source coefficient test.
Thus the coefficient quantifier ranges over every pulled-back source. -/
def universallyBoundedBaseChange (n : ℕ) : MorphismProperty Scheme.{u} :=
  (boundedBaseChange n).universally

/-- Actual finite geometry supplies the original all-coefficient test. -/
theorem boundedBaseChange_of_finite (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [IsFinite f] : boundedBaseChange n f := by
  intro X' S' f' g g' h F _ q
  have := Finite.finiteHigherBaseChange_isIso f f' g g' h q
  infer_instance

/-- The original-source test is stable under composition by the actual
all-coefficient higher-exchange composition theorem. -/
theorem boundedBaseChange_comp (n : ℕ) {Y X S : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X)
    (hf : boundedBaseChange n f) (hk : boundedBaseChange n k) :
    boundedBaseChange n (k ≫ f) := by
  intro Y' S' m g g'' h
  let a : Y' ⟶ pullback f g :=
    pullback.lift (g'' ≫ k) m (by simpa only [Category.assoc] using h.w)
  have ha : a ≫ pullback.fst f g = g'' ≫ k := pullback.lift_fst _ _ _
  have hb : a ≫ pullback.snd f g = m := pullback.lift_snd _ _ _
  clear_value a
  subst m
  have hOuter : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have hInner : IsPullback a g'' (pullback.fst f g) k :=
    h.flip.of_right ha hOuter.flip
  exact boundedExchange_comp n f k (pullback.snd f g) a g (pullback.fst f g) g''
    hOuter.w.symm hInner.w h.w.symm
    (hf (pullback.snd f g) g (pullback.fst f g) hOuter)
    (hk a (pullback.fst f g) g'' hInner.flip)

instance boundedBaseChange_isStableUnderComposition (n : ℕ) :
    (boundedBaseChange n).IsStableUnderComposition where
  comp_mem k f hk hf := boundedBaseChange_comp n f k hf hk

/-- The original-source test descends along any actual surjection, from
the tests for that surjection and its composite. -/
theorem boundedBaseChange_of_surjective (n : ℕ) {Y X S : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X) [Surjective k]
    (hk : boundedBaseChange n k) (hcomp : boundedBaseChange n (k ≫ f)) :
    boundedBaseChange n f := by
  intro X' S' f' g g' h
  let a := pullback.snd k g'
  let b := pullback.fst k g'
  have hInner : IsPullback b a k g' := IsPullback.of_hasPullback k g'
  have hTotal := hInner.paste_vert h
  exact boundedExchange_descent n f k f' a g g' b h.w.symm hInner.w.symm hTotal.w.symm
    (hk a g' b hInner) (hcomp (a ≫ f') g b hTotal)

instance universallyBoundedBaseChange_isStableUnderBaseChange (n : ℕ) :
    (universallyBoundedBaseChange n).IsStableUnderBaseChange := by
  unfold universallyBoundedBaseChange
  infer_instance

instance universallyBoundedBaseChange_isStableUnderComposition (n : ℕ) :
    (universallyBoundedBaseChange n).IsStableUnderComposition := by
  unfold universallyBoundedBaseChange
  infer_instance

/-- Actual finite maps satisfy the universal test on every pulled-back source. -/
theorem universallyBoundedBaseChange_of_finite (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [IsFinite f] : universallyBoundedBaseChange n f := by
  intro X' S' g' g f' h
  have : IsFinite f' := MorphismProperty.of_isPullback h.flip (inferInstance : IsFinite f)
  exact @boundedBaseChange_of_finite.{u} n X' S' f' inferInstance

/-- Universal original exchange descends along an actual surjection. Each
test uses all coefficients on the actual pulled-back source. -/
theorem universallyBoundedBaseChange_of_surjective (n : ℕ) {Y X S : Scheme.{u}}
    (f : X ⟶ S) (k : Y ⟶ X) [Surjective k]
    (hk : universallyBoundedBaseChange n k)
    (hcomp : universallyBoundedBaseChange n (k ≫ f)) :
    universallyBoundedBaseChange n f := by
  intro X' S' g' g f' h
  let a := pullback.snd k g'
  let b := pullback.fst k g'
  have hInner : IsPullback b a k g' := IsPullback.of_hasPullback k g'
  have : Surjective a := MorphismProperty.of_isPullback hInner (inferInstance : Surjective k)
  exact @boundedBaseChange_of_surjective.{u} n (pullback k g') X' S' f' a inferInstance
    (hk b g' a hInner.flip)
    (hcomp b g (a ≫ f') (hInner.paste_vert h.flip).flip)

/-- The constructed universal exchange property reduces every proper morphism
over an arbitrary spectrum to the universal projective-line input. -/
theorem universallyBoundedBaseChange_proper_affine_of_projectiveLine
    (n : ℕ) (R : Type u) [CommRing R]
    (hline : universallyBoundedBaseChange n (ProjectiveLine.structureMap R))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    universallyBoundedBaseChange n f := by
  apply Reduction.proper_affine_mem_of_projectiveLine (universallyBoundedBaseChange n)
    (fun k hk => by
      have := hk
      exact universallyBoundedBaseChange_of_finite n k)
    (fun k p _ _ hp hpbc hcomp => by
      have := hp
      exact universallyBoundedBaseChange_of_surjective n k p hpbc hcomp)
    R hline f

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
