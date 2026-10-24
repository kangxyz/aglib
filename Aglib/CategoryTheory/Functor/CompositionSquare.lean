/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Source squares from coherent composition comparisons

Two original composition comparisons and a compatible middle comparison determine
the source square. Whole natural-isomorphism equalities identify the specified square
before its components are evaluated, keeping concrete functor constructions out of
the categorical cancellation argument.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₀ L₁ L₂ L₃ : A ⥤ C} {R₀ R₁ R₂ R₃ : B ⥤ D}

/-- Coherent composition comparisons and a compatible middle isomorphism give
the component square for the specified original natural isomorphisms. -/
theorem comparisonSquare_app_of_composition
    (G : A ⥤ B) (U : C ⥤ D)
    (m₀ : L₀ ≅ L₁) (m₁ : L₂ ≅ L₃) (m : L₀ ≅ L₂)
    (a₀ : R₀ ≅ R₁) (a₁ : R₂ ≅ R₃) (a : R₀ ≅ R₂)
    (sm : L₁ ≅ L₃) (sa : R₁ ≅ R₃)
    (hsm : sm = m₀.symm ≪≫ m ≪≫ m₁) (hsa : sa = a₀.symm ≪≫ a ≪≫ a₁)
    (M : A) {P Q : D}
    (x₀ : R₁.obj (G.obj M) ⟶ P) (y₀ : P ⟶ U.obj (L₁.obj M))
    (x₁ : R₃.obj (G.obj M) ⟶ Q) (y₁ : Q ⟶ U.obj (L₃.obj M))
    (u₀ : R₀.obj (G.obj M) ⟶ U.obj (L₀.obj M))
    (u₁ : R₂.obj (G.obj M) ⟶ U.obj (L₂.obj M))
    (h₀ : a₀.hom.app (G.obj M) ≫ x₀ ≫ y₀ = u₀ ≫ U.map (m₀.hom.app M))
    (h₁ : a₁.hom.app (G.obj M) ≫ x₁ ≫ y₁ = u₁ ≫ U.map (m₁.hom.app M))
    (h : a.hom.app (G.obj M) ≫ u₁ = u₀ ≫ U.map (m.hom.app M)) :
    sa.hom.app (G.obj M) ≫ x₁ ≫ y₁ = x₀ ≫ y₀ ≫ U.map (sm.hom.app M) := by
  subst sm
  subst sa
  apply (cancel_epi (a₀.hom.app (G.obj M))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, U.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [h₁, reassoc_of% h₀]
  rw [← U.map_comp_assoc, Iso.hom_inv_id_app, U.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ U.map (m₁.hom.app M)) h

end CategoryTheory.Functor
