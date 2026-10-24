/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Functorial injective embeddings for the unbounded injective step

The objects and maps below are the original functorial monomorphism
factorization applied to the arrows to zero. No additive structure on the
resulting functor is asserted.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits MorphismProperty
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The functor assigning to an object its unique arrow to zero. -/
def injectiveStepZeroArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : X ⟶ 0)
  map f := Arrow.homMk f (𝟙 _) (by simp)
  map_id X := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- Functorial injective objects from the native monomorphism factorization. -/
def injectiveStepObjects : C ⥤ C :=
  injectiveStepZeroArrow C ⋙
    (functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp).Z

/-- The original first factor, retained as a natural transformation. -/
def injectiveStepObjectsι : 𝟭 C ⟶ injectiveStepObjects C where
  app X := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i
  naturality {X Y} f := by
    exact (functorialFactorizationData (monomorphisms C)
      (monomorphisms C).rlp).i.naturality ((injectiveStepZeroArrow C).map f)

instance injectiveStepObjects_injective (X : C) :
    Injective ((injectiveStepObjects C).obj X) :=
  inferInstanceAs (Injective (monoMapFactorizationDataRlp (0 : X ⟶ 0)).Z)

instance injectiveStepObjectsι_mono (X : C) :
    Mono ((injectiveStepObjectsι C).app X) :=
  inferInstanceAs (Mono (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i)

@[reassoc (attr := simp)]
lemma injectiveStepObjectsι_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (injectiveStepObjectsι C).app Y =
      (injectiveStepObjectsι C).app X ≫ (injectiveStepObjects C).map f :=
  (injectiveStepObjectsι C).naturality f

end CategoryTheory.IsGrothendieckAbelian
