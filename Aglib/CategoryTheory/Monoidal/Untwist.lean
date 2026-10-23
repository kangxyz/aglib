/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Untwisting by an invertible pairing

In a braided monoidal category, an isomorphism `P : L ⊗ L' ≅ 𝟙_ C` untwists every object:
`untwistIso P I : (L ⊗ I) ⊗ L' ≅ I` moves `L'` next to `L` by the associators and the braiding of
`I` and `L'`, contracts `L ⊗ L'` through `P` and removes the unit. For a morphism `j : I ⟶ 𝟙_ C`,
the untwisting followed by `j` is `(L ◁ j) ≫ ρ_L` tensored with `L'`, followed by `P`
(`untwistIso_hom_comp`): untwisting commutes with the inclusion of a twisted ideal. The proof uses
the naturality of the associators, unitors and braiding, `(β_ 𝟙_ L').hom = λ ≫ ρ⁻¹`
(`braiding_rightUnitor`) and the `monoidal` coherence tactic. The untwisting is natural in `I`
(`untwistIso_hom_naturality`), and at `I = 𝟙_ C`, after `(ρ_ L).inv ▷ L'`, it is the pairing
(`rightUnitor_inv_whiskerRight_untwistIso_hom`).

This is the identification `I_Z(r) ⊗ 𝒪(-r) ≅ I_Z` with `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`, under which the image
of `I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` is the ideal `I_Z`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

namespace MonoidalCategory

/-- **Untwisting by an invertible pairing** `P : L ⊗ L' ≅ 𝟙_ C`: the isomorphism
`(L ⊗ I) ⊗ L' ≅ L ⊗ (I ⊗ L') ≅ L ⊗ (L' ⊗ I) ≅ (L ⊗ L') ⊗ I ≅ 𝟙_ C ⊗ I ≅ I`. -/
def untwistIso {L L' : C} (P : L ⊗ L' ≅ 𝟙_ C) (I : C) : (L ⊗ I) ⊗ L' ≅ I :=
  α_ L I L' ≪≫ whiskerLeftIso L (β_ I L') ≪≫ (α_ L L' I).symm ≪≫ whiskerRightIso P I ≪≫ λ_ I

/-- **Untwisting commutes with a map to the unit**: for `j : I ⟶ 𝟙_ C`, the untwisting followed by
`j` is `(L ◁ j) ≫ ρ_L` tensored with `L'`, followed by the pairing `P`. -/
theorem untwistIso_hom_comp {L L' I : C} (P : L ⊗ L' ≅ 𝟙_ C) (j : I ⟶ 𝟙_ C) :
    (untwistIso P I).hom ≫ j = ((L ◁ j ≫ (ρ_ L).hom) ▷ L') ≫ P.hom := by
  have hβ : (β_ (𝟙_ C) L').hom = (λ_ L').hom ≫ (ρ_ L').inv := by
    rw [← braiding_rightUnitor, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [untwistIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [← leftUnitor_naturality j, ← whisker_exchange_assoc,
    ← associator_inv_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    ← braiding_naturality_left, whiskerLeft_comp_assoc, ← associator_naturality_middle_assoc,
    comp_whiskerRight, Category.assoc]
  congr 1
  rw [unitors_equal, rightUnitor_naturality, hβ]
  monoidal

/-- **The untwisting is natural**: for `f : I ⟶ I'`, `(L ◁ f) ▷ L'` followed by the untwisting of
`I'` is the untwisting of `I` followed by `f`. -/
theorem untwistIso_hom_naturality {L L' I I' : C} (P : L ⊗ L' ≅ 𝟙_ C) (f : I ⟶ I') :
    ((L ◁ f) ▷ L') ≫ (untwistIso P I').hom = (untwistIso P I).hom ≫ f := by
  simp only [untwistIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_left, whiskerLeft_comp_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]

/-- The untwisting of the unit, after `(ρ_ L).inv ▷ L'`, is the pairing. -/
@[reassoc]
theorem rightUnitor_inv_whiskerRight_untwistIso_hom {L L' : C} (P : L ⊗ L' ≅ 𝟙_ C) :
    ((ρ_ L).inv ▷ L') ≫ (untwistIso P (𝟙_ C)).hom = P.hom := by
  have h := untwistIso_hom_comp P (𝟙 (𝟙_ C))
  rw [Category.comp_id, whiskerLeft_id, Category.id_comp] at h
  rw [h, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

end MonoidalCategory

end CategoryTheory
