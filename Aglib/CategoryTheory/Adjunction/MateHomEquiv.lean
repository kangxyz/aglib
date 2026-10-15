/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Transposing original adjunction mates

The hom-set equivalences retain the original conjugate natural transformation.
-/


/-!
Source: `Quillen/CategoryTheory/Adjunction/MateHomEquiv.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 37]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
/-- Adjunction transposition retains the original mate on morphisms. -/
theorem homEquiv_conjugate (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    a₂.homEquiv X Y (α.app X ≫ f) =
      a₁.homEquiv X Y f ≫ (conjugateEquiv a₁ a₂ α).app Y := by
  apply (a₂.homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit, ← Category.assoc, α.naturality]
  rw [Category.assoc, ← Adjunction.homEquiv_symm_apply, Equiv.symm_apply_apply]
/-- The identity-adjunction specialization of the original mate formula. -/
theorem homEquiv_to_identity {L R : C ⥤ C} (a : L ⊣ R) (α : L ⟶ 𝟭 C) (X : C) :
    a.homEquiv X X (α.app X) = (conjugateEquiv Adjunction.id a α).app X := by
  simp [Adjunction.homEquiv_apply]
end CategoryTheory
