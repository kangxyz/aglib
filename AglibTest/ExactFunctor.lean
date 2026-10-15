/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.ExactCategory.Abelian

/-! Canonical exact-category interfaces through precise foundation imports. Exactness
uses the specified exact structures, and the actual additive functor's map. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]

example (E : CategoryTheory.ExactCategory.ExactStructure C) :
    (CategoryTheory.ExactCategory.ExactFunctor.id E).toFunctor = 𝟭 C := rfl

example {E : CategoryTheory.ExactCategory.ExactStructure C} {E' : CategoryTheory.ExactCategory.ExactStructure D}
    (F : CategoryTheory.ExactCategory.ExactFunctor E E') {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E'.deflation (F.toFunctor.map p) :=
  F.map_deflation p hp

example (E : CategoryTheory.ExactCategory.ExactStructure C) (S : ShortComplex C) (hS : E.conflation S) :
    E.conflation (S.map (CategoryTheory.ExactCategory.ExactFunctor.id E).toFunctor) :=
  (CategoryTheory.ExactCategory.ExactFunctor.id E).map_conflation S hS

attribute [local instance] Abelian.hasFiniteBiproducts

example {B : Type u} [Category.{v} B] [Abelian B] :
    (CategoryTheory.ExactCategory.abelianExactStructure B).conflation = ShortComplex.ShortExact := rfl
