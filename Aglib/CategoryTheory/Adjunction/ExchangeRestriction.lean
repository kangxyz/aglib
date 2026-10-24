/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Exchange transported from alternative left adjoints

An exchange for alternative left adjoints determines an exchange for the original
adjunctions whenever the comparison isomorphisms preserve their actual units.
The horizontal-unit equation and its uniqueness use no coefficient hypotheses.
The current consumer is module-valued étale base change.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (G : A ⥤ B) (H : D ⥤ C) {L₀ M₀ : A ⥤ D} {N : D ⥤ A}
  {L₁ M₁ : B ⥤ C} {R : C ⥤ B}
  (a₀ : L₀ ⊣ N) (a₁ : L₁ ⊣ R) (m₀ : M₀ ⊣ N) (m₁ : M₁ ⊣ R)
  (e₀ : L₀ ≅ M₀) (e₁ : L₁ ≅ M₁) (E : G ⋙ M₁ ≅ M₀ ⋙ H)
  (ρ : N ⋙ G ⟶ H ⋙ R)
  (h₀ : ∀ F, a₀.unit.app F ≫ N.map (e₀.hom.app F) = m₀.unit.app F)
  (h₁ : ∀ F, a₁.unit.app F ≫ R.map (e₁.hom.app F) = m₁.unit.app F)
  (hE : ∀ F, m₁.unit.app (G.obj F) ≫ R.map (E.hom.app F) =
    G.map (m₀.unit.app F) ≫ ρ.app (M₀.obj F))

include m₀ m₁ h₀ h₁ hE

/-- Transporting an exchange along unit-preserving comparison isomorphisms preserves
its horizontal-unit equation for the original adjunctions. -/
theorem exchangeRestriction_unit (F : A) :
    G.map (a₀.unit.app F) ≫ ρ.app (L₀.obj F) =
      a₁.unit.app (G.obj F) ≫ R.map
        ((Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫
          Functor.isoWhiskerRight e₀.symm H).hom.app F) := by
  have hg := hE F
  rw [← h₁, ← h₀] at hg
  simp only [Category.assoc, Functor.map_comp] at hg
  have hn : G.map (N.map (e₀.hom.app F)) ≫ ρ.app (M₀.obj F) =
      ρ.app (L₀.obj F) ≫ R.map (H.map (e₀.hom.app F)) :=
    ρ.naturality (e₀.hom.app F)
  rw [hn] at hg
  have hc := congrArg (fun k => k ≫ R.map (H.map (e₀.inv.app F))) hg
  simp only [Category.assoc] at hc
  rw [← R.map_comp (H.map (e₀.hom.app F)) (H.map (e₀.inv.app F)),
    ← H.map_comp (e₀.hom.app F) (e₀.inv.app F),
    e₀.hom_inv_id_app, H.map_id, R.map_id] at hc
  have hi : ρ.app (L₀.obj F) ≫ 𝟙 (R.obj (H.obj (L₀.obj F))) =
      ρ.app (L₀.obj F) := Category.comp_id _
  rw [hi] at hc
  change G.map (a₀.unit.app F) ≫ ρ.app (L₀.obj F) =
    a₁.unit.app (G.obj F) ≫ R.map
      (e₁.hom.app (G.obj F) ≫ E.hom.app F ≫ H.map (e₀.inv.app F))
  simpa only [Functor.map_comp, Category.assoc, Category.comp_id] using hc.symm

/-- The transported exchange agrees with any exchange satisfying the same original
horizontal-unit equation, by the actual adjunction hom-equivalence. -/
theorem exchangeRestriction_hom_eq (β : G ⋙ L₁ ⟶ L₀ ⋙ H)
    (hβ : ∀ F, G.map (a₀.unit.app F) ≫ ρ.app (L₀.obj F) =
      a₁.unit.app (G.obj F) ≫ R.map (β.app F)) :
    (Functor.isoWhiskerLeft G e₁ ≪≫ E ≪≫
      Functor.isoWhiskerRight e₀.symm H).hom = β := by
  apply NatTrans.ext
  funext F
  apply (a₁.homEquiv (G.obj F) (H.obj (L₀.obj F))).injective
  exact (exchangeRestriction_unit G H a₀ a₁ m₀ m₁ e₀ e₁ E ρ h₀ h₁ hE F).symm.trans
    (hβ F)

end CategoryTheory.Adjunction
