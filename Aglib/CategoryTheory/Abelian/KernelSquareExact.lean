/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.KernelSquare
public import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Surjectivity on the second pair of kernels of a commutative square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
  (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ g)

/-- A commutative square whose top map and relation-kernel map are onto
also maps the kernels in the other direction onto one another. This is the
right-exact portion of the ordinary kernel diagram chase. -/
theorem epi_kernel_map_of_epi_of_epi_kernel_map [Epi f]
    [Epi (kernel.map f g a b w)] : Epi (kernel.map a b f g w.symm) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T₁, π₁, _, x, hx⟩ :=
    surjective_up_to_refinements_of_epi f (z ≫ kernel.ι b)
  have hxg : (x ≫ a) ≫ g = 0 := by
    rw [Category.assoc, ← w, ← Category.assoc, ← hx]
    simp
  let k := kernel.lift g (x ≫ a) hxg
  obtain ⟨T₂, π₂, _, y, hy⟩ :=
    surjective_up_to_refinements_of_epi (kernel.map f g a b w) k
  have hya : y ≫ kernel.ι f ≫ a = π₂ ≫ x ≫ a := by
    simpa only [Category.assoc, kernel.lift_ι, k] using
      congrArg (fun h => h ≫ kernel.ι g) hy.symm
  let x' := π₂ ≫ x - y ≫ kernel.ι f
  have hxa : x' ≫ a = 0 := by
    dsimp only [x']
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hya, sub_self]
  refine ⟨T₂, π₂ ≫ π₁, inferInstance, kernel.lift a x' hxa, ?_⟩
  apply (cancel_mono (kernel.ι b)).mp
  simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  dsimp only [x']
  simp only [Preadditive.sub_comp, Category.assoc, kernel.condition, comp_zero, sub_zero]
  simpa only [Category.assoc] using congrArg (fun h => π₂ ≫ h) hx

end CategoryTheory.Abelian
