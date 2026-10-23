/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Localized adjunction comparisons retain the actual conjugate maps -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction
open CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- The original unit equation uniquely characterizes a conjugate natural transformation. -/
theorem conjugateEquiv_eq_of_unit
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (a : L₂ ⟶ L₁) (b : R₁ ⟶ R₂)
    (h : adj₁.unit ≫ whiskerLeft L₁ b = adj₂.unit ≫ whiskerRight a R₂) :
    conjugateEquiv adj₁ adj₂ a = b := by
  apply (conjugateEquiv adj₁ adj₂).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext X
  apply (adj₂.homEquiv X (L₁.obj X)).injective
  rw [homEquiv_unit, homEquiv_unit, ← unit_conjugateEquiv_symm]
  exact (congr_app h X).symm

/-- Localization preserves the actual mate when both unit-factorization squares and
both comparison squares commute. Only the exact left comparison is cancelled. -/
theorem conjugateEquiv_eq_of_localization
    (Q : C ⥤ C') (T : D ⥤ D') (W : MorphismProperty C) [Q.IsLocalization W]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (c₁ : Q ⋙ L₁' ≅ L₁ ⋙ T) (c₂ : Q ⋙ L₂' ≅ L₂ ⋙ T)
    (ρ₁ : R₁ ⋙ Q ⟶ T ⋙ R₁') (ρ₂ : R₂ ⋙ Q ⟶ T ⋙ R₂')
    (a : L₂ ⟶ L₁) (b : R₁ ⟶ R₂) (a' : L₂' ⟶ L₁') (b' : R₁' ⟶ R₂')
    (hconj : conjugateEquiv adj₁ adj₂ a = b)
    (hunit₁ : ∀ X, adj₁'.unit.app (Q.obj X) ≫ R₁'.map (c₁.hom.app X) =
      Q.map (adj₁.unit.app X) ≫ ρ₁.app (L₁.obj X))
    (hunit₂ : ∀ X, adj₂'.unit.app (Q.obj X) ≫ R₂'.map (c₂.hom.app X) =
      Q.map (adj₂.unit.app X) ≫ ρ₂.app (L₂.obj X))
    (ha : ∀ X, a'.app (Q.obj X) ≫ c₁.hom.app X = c₂.hom.app X ≫ T.map (a.app X))
    (hb : ∀ Y, ρ₁.app Y ≫ b'.app (T.obj Y) = Q.map (b.app Y) ≫ ρ₂.app Y) :
    conjugateEquiv adj₁' adj₂' a' = b' := by
  apply conjugateEquiv_eq_of_unit
  apply Localization.natTrans_ext Q W
  intro X
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  apply (cancel_mono (R₂'.map (c₁.hom.app X))).mp
  have hn := b'.naturality (c₁.hom.app X)
  have hr := ρ₂.naturality (a.app X)
  have hu := unit_conjugateEquiv adj₁ adj₂ a X
  rw [hconj] at hu
  simp only [Functor.comp_map, Functor.comp_obj] at hn hr
  calc
    _ = (adj₁'.unit.app (Q.obj X) ≫ R₁'.map (c₁.hom.app X)) ≫
        b'.app (T.obj (L₁.obj X)) := by rw [Category.assoc, ← hn, ← Category.assoc]
    _ = Q.map (adj₁.unit.app X) ≫ (ρ₁.app (L₁.obj X) ≫
        b'.app (T.obj (L₁.obj X))) := by rw [hunit₁, Category.assoc]
    _ = Q.map (adj₁.unit.app X ≫ b.app (L₁.obj X)) ≫ ρ₂.app (L₁.obj X) := by
      rw [hb, Q.map_comp, Category.assoc]
    _ = Q.map (adj₂.unit.app X ≫ R₂.map (a.app X)) ≫ ρ₂.app (L₁.obj X) := by rw [hu]
    _ = (Q.map (adj₂.unit.app X) ≫ ρ₂.app (L₂.obj X)) ≫
        R₂'.map (T.map (a.app X)) := by rw [Q.map_comp, Category.assoc, hr, ← Category.assoc]
    _ = adj₂'.unit.app (Q.obj X) ≫ R₂'.map (c₂.hom.app X ≫ T.map (a.app X)) := by
      rw [← hunit₂, R₂'.map_comp, Category.assoc]
    _ = _ := by rw [← ha, R₂'.map_comp, Category.assoc]

end CategoryTheory.Adjunction
