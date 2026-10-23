/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The original opposite augmented object

The native extra-degeneracy API is simplicial. The opposite of the actual
augmented cosimplicial object supplies its exact input without changing
the original component maps. No additive-category premise occurs here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace AlgebraicTopology.Amitsur

universe v u

variable {C : Type u} [Category.{v} C]

/-- The opposite of the original augmented cosimplicial object. -/
def opAugmented (X : CosimplicialObject.Augmented C) : SimplicialObject.Augmented Cᵒᵖ where
  left := X.right.op
  right := op X.left
  hom := NatTrans.op X.hom

@[simp]
theorem opAugmented_δ (X : CosimplicialObject.Augmented C) (n : ℕ) (i : Fin (n + 2)) :
    (opAugmented X).left.δ i = (X.right.δ i).op := rfl

@[simp]
theorem opAugmented_σ (X : CosimplicialObject.Augmented C) (n : ℕ) (i : Fin (n + 1)) :
    (opAugmented X).left.σ i = (X.right.σ i).op := rfl

@[simp]
theorem opAugmented_hom_app (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (opAugmented X).hom.app (op ⦋n⦌) = (X.hom.app ⦋n⦌).op := rfl

end AlgebraicTopology.Amitsur
