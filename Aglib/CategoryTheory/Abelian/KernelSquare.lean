/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Interchanging the two ordinary kernels of a commutative square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
  (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ g)

/-- Interchange ordinary kernels of the two directions in a commuting square.
The comparison preserves the original composite inclusions into the corner. -/
def kernelSquareIso :
    kernel (kernel.map f g a b w) ≅ kernel (kernel.map a b f g w.symm) where
  hom := kernel.lift _
    (kernel.lift a (kernel.ι (kernel.map f g a b w) ≫ kernel.ι f) (by
      calc
        _ = kernel.ι (kernel.map f g a b w) ≫
            kernel.map f g a b w ≫ kernel.ι g := by simp
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp])) (by
      apply (cancel_mono (kernel.ι b)).mp
      simp)
  inv := kernel.lift _
    (kernel.lift f (kernel.ι (kernel.map a b f g w.symm) ≫ kernel.ι a) (by
      calc
        _ = kernel.ι (kernel.map a b f g w.symm) ≫
            kernel.map a b f g w.symm ≫ kernel.ι b := by simp
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp])) (by
      apply (cancel_mono (kernel.ι g)).mp
      simp)
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (kernel.map f g a b w))).mp
    apply (cancel_mono (kernel.ι f)).mp
    simp
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (kernel.map a b f g w.symm))).mp
    apply (cancel_mono (kernel.ι a)).mp
    simp

@[reassoc (attr := simp)]
theorem kernelSquareIso_hom_ι_ι :
    (kernelSquareIso f g a b w).hom ≫
        kernel.ι (kernel.map a b f g w.symm) ≫ kernel.ι a =
      kernel.ι (kernel.map f g a b w) ≫ kernel.ι f := by
  simp [kernelSquareIso]

end CategoryTheory.Abelian
