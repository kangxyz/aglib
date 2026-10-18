/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# A left adjoint on morphisms into an object where the unit is invertible

For an adjunction `adj : F ⊣ G` and an object `N'` at which the unit `N' ⟶ G (F N')` is an
isomorphism, `F` is bijective on morphisms `N ⟶ N'` for every `N`
(`Adjunction.bijective_map_of_isIso_unit_app`): through the hom-equivalence, `F.map φ`
corresponds to `φ ≫ adj.unit.app N'`. This is the pointwise form of the full faithfulness of a
left adjoint whose unit is an isomorphism (Mathlib's `Adjunction.fullyFaithfulLOfIsIsoUnit`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {G : D ⥤ C} (adj : F ⊣ G)

/-- If the unit of `adj : F ⊣ G` at `N'` is an isomorphism, `F` is bijective on morphisms
into `N'`. -/
theorem bijective_map_of_isIso_unit_app (N N' : C) [IsIso (adj.unit.app N')] :
    Function.Bijective (fun φ : N ⟶ N' ↦ F.map φ) := by
  have e : (fun φ : N ⟶ N' ↦ F.map φ) =
      (adj.homEquiv N (F.obj N')).symm ∘ (fun φ ↦ φ ≫ adj.unit.app N') := by
    funext φ
    apply (adj.homEquiv _ _).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality φ).symm
  rw [e]
  exact (Equiv.bijective _).comp ⟨fun φ ψ h ↦ (cancel_mono _).1 h, fun ψ ↦
    ⟨ψ ≫ inv (adj.unit.app N'), by simp⟩⟩

end CategoryTheory.Adjunction
