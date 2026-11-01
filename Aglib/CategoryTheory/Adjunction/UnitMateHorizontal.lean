/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Horizontal composition after original identity-source normalization -/

@[expose] public section

namespace CategoryTheory

variable {A B B' C C' : Type*}
  [Category* A] [Category* B] [Category* B'] [Category* C] [Category* C']
  {I : A ⥤ A} {J : A ⥤ B} {J' : A ⥤ B'}
  {L : B ⥤ C} {L' : B' ⥤ C'} {T : A ⥤ C} {T' : A ⥤ C'}
  {R : B' ⥤ B} {S : C' ⥤ C}

/-- Normalized original unit maps satisfy the horizontal comparison equation. -/
def UnitMateHorizontalEquation (δJ : J ⟶ J' ⋙ R) (δT : T ⟶ T' ⋙ S)
    (σ : R ⋙ L ⟶ L' ⋙ S) (c : T ≅ J ⋙ L) (c' : T' ≅ J' ⋙ L') : Prop :=
  ∀ K, c.hom.app K ≫ L.map (δJ.app K) ≫ σ.app (J'.obj K) =
    δT.app K ≫ S.map (c'.hom.app K)

/-- Remove the actual source identity from a horizontal mixed-mate law.
Only naturality of the specified compositor and the specified normalizations
are used; all original comparison maps are retained. -/
theorem unitMateHorizontalEquation (d : I ≅ 𝟭 A)
    (δJ : J ⟶ J' ⋙ R) (δT : T ⟶ T' ⋙ S)
    (σJ : I ⋙ J ⟶ J' ⋙ R) (σT : I ⋙ T ⟶ T' ⋙ S)
    (σ : R ⋙ L ⟶ L' ⋙ S) (c : T ≅ J ⋙ L) (c' : T' ≅ J' ⋙ L')
    (hJ : ∀ K, δJ.app K = J.map (d.inv.app K) ≫ σJ.app K)
    (hT : ∀ K, δT.app K = T.map (d.inv.app K) ≫ σT.app K)
    (hσ : ∀ K, c.hom.app (I.obj K) ≫ L.map (σJ.app K) ≫ σ.app (J'.obj K) =
      σT.app K ≫ S.map (c'.hom.app K)) :
    UnitMateHorizontalEquation δJ δT σ c c' := by
  intro K
  rw [hJ, hT, L.map_comp]
  have hn := c.hom.naturality (d.inv.app K)
  change T.map (d.inv.app K) ≫ c.hom.app (I.obj K) =
    c.hom.app K ≫ L.map (J.map (d.inv.app K)) at hn
  calc
    _ = (c.hom.app K ≫ L.map (J.map (d.inv.app K))) ≫
        L.map (σJ.app K) ≫ σ.app (J'.obj K) := by simp only [Category.assoc]
    _ = T.map (d.inv.app K) ≫
        (c.hom.app (I.obj K) ≫ L.map (σJ.app K) ≫ σ.app (J'.obj K)) := by
      rw [← hn]
      simp only [Category.assoc]
    _ = _ := by rw [hσ]; simp only [Category.assoc]

end CategoryTheory
