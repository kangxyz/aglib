/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Additivity at the native sheaf-section functor head

The native section functor is a flip-object of the sheaf inclusion. Register
its actual pointwise addition law directly, without rebuilding an evaluation
composite or searching for preservation of products.
-/

@[expose] public section

namespace CategoryTheory

universe u v w vA

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{vA} A] [Preadditive A]

/-- Evaluation of actual sheaf morphisms preserves their native addition. -/
instance sheafSections_additive (U : Cᵒᵖ) : ((sheafSections J A).obj U).Additive where
  map_add {_P _Q} {f g} := Sheaf.Hom.add_app f g U

end CategoryTheory
