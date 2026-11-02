/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Identity-source mates and the original unit transpose

Removing a specified identity adjunction from an original square gives exactly
its original unit transpose. The identity comparisons must be actual conjugates.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {I R : A ⥤ A} {P : B ⥤ C} {Q : C ⥤ B} {G : A ⥤ B} {H : A ⥤ C}

/-- The original identity-source mixed mate, normalized by its actual right
identity comparison, is the specified original unit comparison. -/
def IdentitySourceMateEquation (aI : I ⊣ R) (aP : P ⊣ Q)
    (β : TwoSquare G I P H) (d : R ≅ 𝟭 A) (δ : G ⟶ H ⋙ Q) : Prop :=
  ∀ K, G.map (d.inv.app K) ≫ (mateEquiv aI aP β).app K = δ.app K

/-- Actual conjugacy and actual left-square normalization identify the original
unit map with the normalized mixed mate, without replacing either map. -/
theorem identitySourceMateEquation
    (aI : I ⊣ R) (aP : P ⊣ Q) (c : I ≅ 𝟭 A) (d : R ≅ 𝟭 A)
    (hc : conjugateEquiv Adjunction.id aI c.hom = d.inv)
    (β : TwoSquare G I P H) (p : G ⋙ P ⟶ H) (δ : G ⟶ H ⋙ Q)
    (hp : ∀ K, p.app K = β.app K ≫ H.map (c.hom.app K))
    (hδ : ∀ K, δ.app K = aP.unit.app (G.obj K) ≫ Q.map (p.app K)) :
    IdentitySourceMateEquation aI aP β d δ := by
  let α : TwoSquare G (𝟭 A) P H := TwoSquare.mk _ _ _ _ p
  have hs : α.whiskerRight (Iso.refl P).hom = β.whiskerLeft c.hom := by
    ext K
    change (𝟙 _) ≫ p.app K = β.app K ≫ H.map (c.hom.app K)
    exact (Category.id_comp _).trans (hp K)
  intro K
  have hm := mateEquiv_conjugate_comparisons Adjunction.id aI aP aP
    c (Iso.refl P) d (Iso.refl Q) hc (by simp) α β hs K
  have hu : (mateEquiv Adjunction.id aP α).app K = δ.app K := by
    rw [hδ]
    simp [mateEquiv, α]
  have he : G.map (d.hom.app K) ≫ δ.app K = (mateEquiv aI aP β).app K := by
    change G.map (d.hom.app K) ≫ (mateEquiv Adjunction.id aP α).app K =
      (mateEquiv aI aP β).app K ≫ 𝟙 _ at hm
    rw [hu, Category.comp_id] at hm
    exact hm
  rw [← he, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id_app, G.map_id,
    Category.id_comp]

end CategoryTheory
