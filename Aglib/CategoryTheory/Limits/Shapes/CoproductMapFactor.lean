/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The original coproduct map of a family of commuting triangles

The native coproduct map retains the supplied structural maps componentwise.
The proof takes place in the original category, independently of any extra
structure or implementation carried by the objects in native applications.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe u v w

/-- A componentwise commuting family gives the exact structural equation for
the original coproduct map and the original two coproduct descents. -/
theorem Sigma.map_desc_of_component_eq
    {C : Type u} [Category.{v} C] {ι : Type w}
    {X Y : ι → C} [HasCoproduct X] [HasCoproduct Y] {S T : C}
    (κ : ∀ i, X i ⟶ Y i) (a : ∀ i, X i ⟶ S) (b : ∀ i, Y i ⟶ T)
    (r : S ⟶ T) (h : ∀ i, κ i ≫ b i = a i ≫ r) :
    Sigma.map κ ≫ Sigma.desc b = Sigma.desc a ≫ r := by
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  exact h i

end CategoryTheory.Limits
