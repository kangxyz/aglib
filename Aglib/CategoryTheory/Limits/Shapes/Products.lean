/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Zero morphisms into preserved products -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits

/-- Vanishing of all mapped components detects a zero map into a preserved product. -/
lemma map_pi_lift_comp_eq_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) {J : Type*} {Y : J → C}
    [HasProduct Y] [PreservesLimit (Discrete.functor Y) F]
    {T : C} {A : D} (i : A ⟶ F.obj T) (f : ∀ j, T ⟶ Y j)
    (hf : ∀ j, i ≫ F.map (f j) = 0) :
    i ≫ F.map (Pi.lift f) = 0 := by
  apply (isLimitOfPreserves F (productIsProduct Y)).hom_ext
  intro j
  change (i ≫ F.map (Pi.lift f)) ≫ F.map (Pi.π Y j.as) =
    0 ≫ F.map (Pi.π Y j.as)
  simp only [Category.assoc, ← F.map_comp, Pi.lift_comp_π, hf, zero_comp]

end CategoryTheory.Limits
