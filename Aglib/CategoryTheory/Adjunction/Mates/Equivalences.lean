/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Original mates across equivalences

The inverse mate of an invertible square is invertible when its relevant
unit and counit are invertible. Iterating the native mate correspondence then
shows that a commuting square with equivalences on its other two sides has
invertible original mate. No replacement exchange transformation is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory.Functor

namespace CategoryTheory

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The original inverse mate preserves invertibility when its unit and counit do. -/
theorem mateEquiv_symm_isIso_of_unit_counit
    [IsIso adj₁.unit] [IsIso adj₂.counit]
    (β : TwoSquare R₁ H G R₂) [IsIso β.natTrans] :
    IsIso (((mateEquiv adj₁ adj₂).symm β).natTrans) := by
  change IsIso ((G ⋙ L₂).leftUnitor.inv ≫
    whiskerRight adj₁.unit (G ⋙ L₂) ≫
    ((L₁ ⋙ R₁).associator G L₂).inv ≫
    whiskerRight (L₁.associator R₁ G).hom L₂ ≫
    whiskerRight (whiskerLeft L₁ β.natTrans) L₂ ≫
    whiskerRight (L₁.associator H R₂).inv L₂ ≫
    ((L₁ ⋙ H).associator R₂ L₂).hom ≫
    whiskerLeft (L₁ ⋙ H) adj₂.counit ≫ (L₁ ⋙ H).rightUnitor.hom)
  infer_instance

/-- A square with equivalences on the two untransposed sides has invertible
original mate whenever its original square transformation is invertible. -/
theorem mateEquiv_isIso_of_equivalences
    [G.IsEquivalence] [H.IsEquivalence]
    (α : TwoSquare G L₁ L₂ H) [IsIso α.natTrans] :
    IsIso ((mateEquiv adj₁ adj₂ α).natTrans) := by
  let adj₃ : G ⊣ G.inv := G.adjunction
  let adj₄ : H ⊣ H.inv := H.adjunction
  let β := mateEquiv adj₁ adj₂ α
  change IsIso β.natTrans
  let γ := mateEquiv adj₄ adj₃ β
  have : IsIso γ.natTrans := by
    dsimp only [γ, β]
    rw [iterated_mateEquiv_conjugateEquiv]
    exact conjugateEquiv_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α.natTrans
  have hi := mateEquiv_symm_isIso_of_unit_counit adj₄ adj₃ γ
  change IsIso (((mateEquiv adj₄ adj₃).symm ((mateEquiv adj₄ adj₃) β)).natTrans) at hi
  simpa only [Equiv.symm_apply_apply] using hi

end CategoryTheory
