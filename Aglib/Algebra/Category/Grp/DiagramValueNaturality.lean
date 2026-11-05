/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.Category

/-! # Whole diagram naturality on specified surjective values

This construction retains the supplied functors and component transformations.
Its value types need no algebraic structure and may lie in an independent
universe. In particular, it never reconstructs Shrink or its group instances.
-/

@[expose] public section

namespace CategoryTheory

universe r e uI vI uC vC

variable {I : Type uI} [Category.{vI} I]
  {C : Type uC} [Category.{vC} C]

/-- The given component maps are natural if their square holds on specified
surjective original values, with the actual source and target map-value laws. -/
def additiveDiagramNatTransOfSurjectiveValues
    (F : C ⥤ I ⥤ AddCommGrpCat.{r}) (H : C ⥤ I ⥤ AddCommGrpCat.{r})
    (A : C → I → Type e)
    (p : ∀ c i, A c i → (F.obj c).obj i)
    (hp : ∀ c i, Function.Surjective (p c i))
    (a : ∀ {c d : C}, (c ⟶ d) → ∀ i, A c i → A d i)
    (b : ∀ {c d : C}, (c ⟶ d) → ∀ i, (H.obj c).obj i → (H.obj d).obj i)
    (ha : ∀ {c d : C} (g : c ⟶ d) i (x : A c i),
      (F.map g).app i (p c i x) = p d i (a g i x))
    (hb : ∀ {c d : C} (g : c ⟶ d) i (y : (H.obj c).obj i),
      (H.map g).app i y = b g i y)
    (k : ∀ c, F.obj c ⟶ H.obj c)
    (hk : ∀ {c d : C} (g : c ⟶ d) i (x : A c i),
      (k d).app i (p d i (a g i x)) = b g i ((k c).app i (p c i x))) :
    F ⟶ H where
  app := k
  naturality c d g := by
    ext i y
    obtain ⟨x, rfl⟩ := hp c i y
    exact (congrArg ((k d).app i) (ha g i x)).trans
      ((hk g i x).trans (hb g i ((k c).app i (p c i x))).symm)

universe e'

/-- Assemble two actual comparison maps and their complete coefficient square
from their separate original-value laws, before specializing either comparison. -/
def additiveDiagramNatTransOfTwoComparisons
    (F H : C ⥤ I ⥤ AddCommGrpCat.{r}) (M : C → I ⥤ AddCommGrpCat.{r})
    (A : C → I → Type e) (B : C → I → Type e')
    (p : ∀ c i, A c i → (F.obj c).obj i)
    (q : ∀ c i, B c i → (M c).obj i)
    (hp : ∀ c i, Function.Surjective (p c i))
    (a : ∀ {c d : C}, (c ⟶ d) → ∀ i, A c i → A d i)
    (b : ∀ {c d : C}, (c ⟶ d) → ∀ i, (H.obj c).obj i → (H.obj d).obj i)
    (d : ∀ {c d : C}, (c ⟶ d) → ∀ i, B c i → B d i)
    (ha : ∀ {c d : C} (g : c ⟶ d) i (x : A c i),
      (F.map g).app i (p c i x) = p d i (a g i x))
    (hb : ∀ {c d : C} (g : c ⟶ d) i (y : (H.obj c).obj i),
      (H.map g).app i y = b g i y)
    (α : ∀ c, F.obj c ⟶ M c) (β : ∀ c, M c ⟶ H.obj c)
    (E : ∀ c i, A c i → B c i)
    (R : ∀ c i, B c i → (H.obj c).obj i)
    (hα : ∀ c i (x : A c i), (α c).app i (p c i x) = q c i (E c i x))
    (hβ : ∀ c i (x : B c i), (β c).app i (q c i x) = R c i x)
    (hE : ∀ {c c' : C} (g : c ⟶ c') i (x : A c i),
      E c' i (a g i x) = d g i (E c i x))
    (hR : ∀ {c c' : C} (g : c ⟶ c') i (x : B c i),
      R c' i (d g i x) = b g i (R c i x)) : F ⟶ H := by
  have hcomp (c : C) (i : I) (x : A c i) :
      ((α c ≫ β c).app i) (p c i x) = R c i (E c i x) :=
    (congrArg ((β c).app i) (hα c i x)).trans (hβ c i (E c i x))
  exact additiveDiagramNatTransOfSurjectiveValues F H A p hp a b ha hb
    (fun c => α c ≫ β c) (by
      intro c c' g i x
      exact (hcomp c' i (a g i x)).trans
        ((congrArg (R c' i) (hE g i x)).trans
          ((hR g i (E c i x)).trans (congrArg (b g i) (hcomp c i x).symm))))

end CategoryTheory
