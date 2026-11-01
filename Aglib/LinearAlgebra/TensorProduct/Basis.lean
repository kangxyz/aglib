/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Original basis coordinates under scalar tensor maps

The base-changed original basis identifies the actual tensor map with the
original coefficient algebra map on every coordinate. Neither a finite index
nor a free-module replacement or flatness hypothesis is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module.Basis

variable {A S T M ι : Type*} [CommRing A] [CommRing S] [CommRing T]
  [Algebra A S] [Algebra A T] [AddCommGroup M] [Module A M]

/-- Base-changed basis coordinates preserve the actual scalar tensor map. -/
theorem baseChange_repr_tensorMap (b : Basis ι A M) (f : S →ₐ[A] T)
    (z : S ⊗[A] M) (i : ι) :
    (b.baseChange T).repr (TensorProduct.map f.toLinearMap LinearMap.id z) i =
      f ((b.baseChange S).repr z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul s m => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Module.Basis
