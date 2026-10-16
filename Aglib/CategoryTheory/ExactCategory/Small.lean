/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor

/-!
# Bundled small exact categories

The objects are additive categories small in one fixed universe, equipped with
selected exact structures. Their morphisms are the existing exact functors.
This bundle is distinct from transport through a chosen small-model equivalence.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory

/-- A small additive category equipped with a selected exact structure. -/
structure SmallExactCategory : Type (u + 1) where
  /-- The type of objects of the bundled category, small in the selected universe. -/
  Obj : Type u
  [category : Category.{u} Obj]
  [preadditive : Preadditive Obj]
  [finiteBiproducts : HasFiniteBiproducts Obj]
  /-- The selected exact structure on the bundled additive category. -/
  exactStructure : ExactStructure Obj

attribute [instance] SmallExactCategory.category SmallExactCategory.preadditive
  SmallExactCategory.finiteBiproducts

namespace ExactFunctor

/-- The proof data of exactness do not alter equality of exact functors. -/
@[ext]
theorem ext_toFunctor {C D : Type u} [Category.{u} C] [Category.{u} D]
    [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
    {E : ExactStructure C} {E' : ExactStructure D} {F G : ExactFunctor E E'}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

end ExactFunctor

namespace SmallExactCategory

/-- Bundle an existing small category with its selected exact structure. -/
def ofExactStructure {C : Type u} [Category.{u} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) : SmallExactCategory.{u} where
  Obj := C
  exactStructure := E

instance instCategory : Category.{u} SmallExactCategory.{u} where
  Hom C D := ExactFunctor C.exactStructure D.exactStructure
  id C := CategoryTheory.ExactCategory.ExactFunctor.id C.exactStructure
  comp F G := F.comp G
  id_comp := by intros; apply CategoryTheory.ExactCategory.ExactFunctor.ext_toFunctor; rfl
  comp_id := by intros; apply CategoryTheory.ExactCategory.ExactFunctor.ext_toFunctor; rfl
  assoc := by intros; apply CategoryTheory.ExactCategory.ExactFunctor.ext_toFunctor; rfl

end SmallExactCategory
end CategoryTheory.ExactCategory
