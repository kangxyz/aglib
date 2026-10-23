/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Untwist
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Vanishing through an invertible pairing

Let `C` be a braided monoidal category and `P : L ⊗ L' ≅ 𝟙_ C` an invertible pairing. The
naturality of the untwisting `untwistIso P` is in `CategoryTheory/Monoidal/Untwist`.

* `eq_zero_of_whiskerRight_eq_zero` (`C` preadditive, tensor additive): tensoring on the right
  with `L'` detects zero morphisms, since `(X ⊗ L') ⊗ L ≅ X` naturally.
* `comp_rightUnitor_inv_whiskerLeft_eq_zero`: for `j : X ⟶ L` and `t : 𝟙_ C ⟶ Q`, if the
  untwisted map `(j ▷ L') ≫ P ≫ t` vanishes, then so does `j ≫ (ρ_ L).inv ≫ (L ◁ t)`.

This is the step "the cokernel of `h` is `F(r)`, twisting by `−r`" of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, read backwards: if the twist by `−r` of
a map to `𝒪(r)` lands in the ideal of `Z`, the map vanishes on `𝒪_Z(r)`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits MonoidalCategory BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

namespace MonoidalCategory

variable [Preadditive C] [MonoidalPreadditive C]

/-- **Tensoring with an invertible object detects zero morphisms**: for `P : L ⊗ L' ≅ 𝟙_ C`, if
`f ▷ L' = 0` then `f = 0`, since `(X ⊗ L') ⊗ L ≅ X ⊗ (L' ⊗ L) ≅ X` naturally in `X`. -/
theorem eq_zero_of_whiskerRight_eq_zero {L L' X Y : C} (P : L ⊗ L' ≅ 𝟙_ C) {f : X ⟶ Y}
    (hf : f ▷ L' = 0) : f = 0 := by
  have h : ((f ▷ L') ▷ L) ≫ (α_ Y L' L).hom ≫ (Y ◁ ((β_ L' L).hom ≫ P.hom)) ≫ (ρ_ Y).hom =
      (α_ X L' L).hom ≫ (X ◁ ((β_ L' L).hom ≫ P.hom)) ≫ (ρ_ X).hom ≫ f := by
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  rw [hf, MonoidalPreadditive.zero_whiskerRight, zero_comp] at h
  have h' : ((α_ X L' L).hom ≫ (X ◁ ((β_ L' L).hom ≫ P.hom)) ≫ (ρ_ X).hom) ≫ f =
      ((α_ X L' L).hom ≫ (X ◁ ((β_ L' L).hom ≫ P.hom)) ≫ (ρ_ X).hom) ≫ 0 := by
    rw [comp_zero, Category.assoc, Category.assoc, ← h]
  exact (cancel_epi _).mp h'

/-- **Vanishing through an invertible pairing**: for `P : L ⊗ L' ≅ 𝟙_ C`, `j : X ⟶ L` and
`t : 𝟙_ C ⟶ Q`, if `(j ▷ L') ≫ P ≫ t = 0`, then `j ≫ (ρ_ L).inv ≫ (L ◁ t) = 0`. -/
theorem comp_rightUnitor_inv_whiskerLeft_eq_zero {L L' X Q : C} (P : L ⊗ L' ≅ 𝟙_ C)
    (j : X ⟶ L) (t : 𝟙_ C ⟶ Q) (h : (j ▷ L') ≫ P.hom ≫ t = 0) :
    j ≫ (ρ_ L).inv ≫ (L ◁ t) = 0 := by
  refine eq_zero_of_whiskerRight_eq_zero P ?_
  rw [← cancel_mono (untwistIso P Q).hom, zero_comp, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc, untwistIso_hom_naturality,
    rightUnitor_inv_whiskerRight_untwistIso_hom_assoc]
  exact h

end MonoidalCategory

end CategoryTheory
