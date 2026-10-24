/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Transport of original exchange-unit equations through faithful coefficient functors -/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

open CategoryTheory

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {G : A ⥤ B} {H : D ⥤ C} {L₀ : A ⥤ D} {R₀ : D ⥤ A}
  {L₁ : B ⥤ C} {R₁ : C ⥤ B}
  {G' : A' ⥤ B'} {H' : D' ⥤ C'} {L₀' : A' ⥤ D'} {R₀' : D' ⥤ A'}
  {L₁' : B' ⥤ C'} {R₁' : C' ⥤ B'}
  (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₀' : L₀' ⊣ R₀') (a₁' : L₁' ⊣ R₁')
  (Qₐ : A ⥤ A') (Qᵦ : B ⥤ B') (Q𝒸 : C ⥤ C') (Q𝒹 : D ⥤ D')
  [Qᵦ.Faithful]
  (eG : G ⋙ Qᵦ ≅ Qₐ ⋙ G') (eH : H ⋙ Q𝒸 ≅ Q𝒹 ⋙ H')
  (eR₀ : R₀ ⋙ Qₐ ≅ Q𝒹 ⋙ R₀') (eR₁ : R₁ ⋙ Qᵦ ≅ Q𝒸 ⋙ R₁')
  (eL₀ : L₀ ⋙ Q𝒹 ≅ Qₐ ⋙ L₀') (eL₁ : L₁ ⋙ Q𝒸 ≅ Qᵦ ⋙ L₁')
  (ρ : R₀ ⋙ G ⟶ H ⋙ R₁) (ρ' : R₀' ⋙ G' ⟶ H' ⋙ R₁')
  (β : G ⋙ L₁ ⟶ L₀ ⋙ H) (β' : G' ⋙ L₁' ⟶ L₀' ⋙ H')

/-- Faithful transport preserves the original horizontal-unit equation, provided both
adjunction units and both square comparisons retain their specified transport equations. -/
theorem exchangeTransport_unit
    (h₀ : ∀ M, Qₐ.map (a₀.unit.app M) ≫ eR₀.hom.app (L₀.obj M) ≫
      R₀'.map (eL₀.hom.app M) = a₀'.unit.app (Qₐ.obj M))
    (h₁ : ∀ N, Qᵦ.map (a₁.unit.app N) ≫ eR₁.hom.app (L₁.obj N) ≫
      R₁'.map (eL₁.hom.app N) = a₁'.unit.app (Qᵦ.obj N))
    (hρ : ∀ N, Qᵦ.map (ρ.app N) ≫ eR₁.hom.app (H.obj N) ≫
      R₁'.map (eH.hom.app N) = eG.hom.app (R₀.obj N) ≫
        G'.map (eR₀.hom.app N) ≫ ρ'.app (Q𝒹.obj N))
    (hβ : ∀ M, Q𝒸.map (β.app M) ≫ eH.hom.app (L₀.obj M) ≫
      H'.map (eL₀.hom.app M) = eL₁.hom.app (G.obj M) ≫
        L₁'.map (eG.hom.app M) ≫ β'.app (Qₐ.obj M))
    (hv : ∀ M, G'.map (a₀'.unit.app M) ≫ ρ'.app (L₀'.obj M) =
      a₁'.unit.app (G'.obj M) ≫ R₁'.map (β'.app M)) (M : A) :
    G.map (a₀.unit.app M) ≫ ρ.app (L₀.obj M) =
      a₁.unit.app (G.obj M) ≫ R₁.map (β.app M) := by
  apply Qᵦ.map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (eR₁.hom.app (H.obj (L₀.obj M)) ≫
    R₁'.map (eH.hom.app (L₀.obj M)) ≫
      R₁'.map (H'.map (eL₀.hom.app M)))).1
  have ng := eG.hom.naturality (a₀.unit.app M)
  have nr := eR₁.hom.naturality (β.app M)
  have np := ρ'.naturality (eL₀.hom.app M)
  have nu := a₁'.unit.naturality (eG.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at ng nr np nu
  have hb := congrArg R₁'.map (hβ M)
  have hu := congrArg G'.map (h₀ M)
  simp only [Functor.map_comp] at hb hu
  calc
    _ = eG.hom.app M ≫ G'.map (Qₐ.map (a₀.unit.app M)) ≫
        G'.map (eR₀.hom.app (L₀.obj M)) ≫ ρ'.app (Q𝒹.obj (L₀.obj M)) ≫
          R₁'.map (H'.map (eL₀.hom.app M)) := by
      simp only [Category.assoc]
      rw [reassoc_of% (hρ (L₀.obj M)), reassoc_of% ng]
    _ = eG.hom.app M ≫ G'.map (a₀'.unit.app (Qₐ.obj M)) ≫
        ρ'.app (L₀'.obj (Qₐ.obj M)) := by
      rw [← np]
      rw [reassoc_of% hu]
    _ = a₁'.unit.app (Qᵦ.obj (G.obj M)) ≫
        R₁'.map (L₁'.map (eG.hom.app M)) ≫ R₁'.map (β'.app (Qₐ.obj M)) := by
      rw [hv]
      rw [reassoc_of% nu]
    _ = _ := by
      simp only [Category.assoc]
      rw [reassoc_of% nr, hb, reassoc_of% (h₁ (G.obj M))]

end CategoryTheory.Adjunction
