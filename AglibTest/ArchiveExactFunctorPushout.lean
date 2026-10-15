/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.FunctorPushout

/-! # The public exact-functor pushout interface on its original admissible square -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
universe u v u' v'

namespace AglibTest.ArchiveExactFunctorPushout
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- The native method preserves the original square from its original inflation hypothesis. -/
theorem original_mapped_square {A B T P : C} {i : A ⟶ B} {f : A ⟶ T}
    {g : B ⟶ P} {j : T ⟶ P} (hi : EC.inflation i) (h : IsPushout i f g j) :
    IsPushout (F.toFunctor.map i) (F.toFunctor.map f)
      (F.toFunctor.map g) (F.toFunctor.map j) :=
  F.map_isPushout hi h

end AglibTest.ArchiveExactFunctorPushout
