/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite coproducts in preadditive categories

In a preadditive category the projections `Sigma.π f j` and the inclusions `Sigma.ι f j` of a
finite coproduct sum to the identity (`Sigma.sum_π_ι`), so every morphism into a finite
coproduct is the sum of its components (`exists_eq_sum_sigma_ι`). An additive functor vanishes
on the point of a finite bilimit bicone when it vanishes on every summand
(`isZero_obj_of_isBilimit`).
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]

/-- The projections and inclusions of a finite coproduct sum to the identity. -/
theorem Sigma.sum_π_ι {J : Type*} [Fintype J] [DecidableEq J] (f : J → C) [HasCoproduct f] :
    ∑ j, Sigma.π f j ≫ Sigma.ι f j = 𝟙 (∐ f) := by
  apply Sigma.hom_ext
  intro k
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Sigma.ι_π_of_ne_assoc f (Ne.symm hj), zero_comp]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- A morphism into a finite coproduct is the sum of its components. -/
theorem exists_eq_sum_sigma_ι {J : Type*} [Fintype J] {f : J → C} [HasCoproduct f] {W : C}
    (a : W ⟶ ∐ f) : ∃ c : ∀ j, W ⟶ f j, a = ∑ j, c j ≫ Sigma.ι f j := by
  classical
  refine ⟨fun j => a ≫ Sigma.π f j, ?_⟩
  conv_lhs => rw [← Category.comp_id a, ← Sigma.sum_π_ι f, Preadditive.comp_sum]
  simp only [Category.assoc]

/-- An additive functor vanishes on the point of a finite bilimit bicone when it vanishes on
every summand. -/
theorem isZero_obj_of_isBilimit {D : Type*} [Category D] [Preadditive D] (H : C ⥤ D)
    [H.Additive] {J : Type*} [Finite J] {f : J → C} {b : Bicone f} (hb : b.IsBilimit)
    (h : ∀ j, IsZero (H.obj (f j))) : IsZero (H.obj b.pt) := by
  let := Fintype.ofFinite J
  rw [IsZero.iff_id_eq_zero, ← H.map_id, ← IsBilimit.total hb, H.map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [H.map_comp, (h j).eq_of_tgt (H.map (b.π j)) 0, zero_comp]

end CategoryTheory.Limits
