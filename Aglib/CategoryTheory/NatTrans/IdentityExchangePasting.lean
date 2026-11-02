/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Contraction of an identity-last exchange pasting

The last square is normalized to its original transition, using the actual
identity comparisons. All component algebra occurs in abstract categories.
-/

@[expose] public section
namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {R₀ : A ⥤ B} {R₁ R₂ : C ⥤ D} {G G₁ : B ⥤ D} {H H₁ : A ⥤ C}
  {I : D ⥤ D} {F : C ⥤ C}

/-- Actual consecutive exchange and the actual identity-last contraction
identify the total with the first exchange followed by the original transition. -/
theorem identityExchangePasting
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ I ⟶ F ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂) (γ : G ≅ G₁ ⋙ I) (δ : H ≅ H₁ ⋙ F)
    (i : I ≅ 𝟭 D) (s : F ≅ 𝟭 C) (t : R₁ ⟶ R₂)
    (u : G ≅ G₁) (v : H ≅ H₁)
    (hγ : γ ≪≫ Functor.isoWhiskerLeft G₁ i ≪≫ Functor.rightUnitor G₁ = u)
    (hδ : δ ≪≫ Functor.isoWhiskerLeft H₁ s ≪≫ Functor.rightUnitor H₁ = v)
    (hp : ∀ K, ActualHorizontalMateEquation β₁ β₂ β γ.hom δ.hom K)
    (hi : ∀ N, β₂.app N ≫ R₂.map (s.hom.app N) =
      i.hom.app (R₁.obj N) ≫ t.app N) :
    β ≫ Functor.whiskerRight v.hom R₂ =
      Functor.whiskerLeft R₀ u.hom ≫ β₁ ≫ Functor.whiskerLeft H₁ t := by
  have hu (N : B) : γ.hom.app N ≫ i.hom.app (G₁.obj N) = u.hom.app N := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
      Functor.id_obj, Category.comp_id] using
      congrArg (fun e => e.hom.app N) hγ
  have hv (K : A) : δ.hom.app K ≫ s.hom.app (H₁.obj K) = v.hom.app K := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
      Functor.id_obj, Category.comp_id] using
      congrArg (fun e => e.hom.app K) hδ
  apply NatTrans.ext
  funext K
  have h := congrArg (fun z => z ≫ R₂.map (s.hom.app (H₁.obj K))) (hp K)
  change (γ.hom.app (R₀.obj K) ≫ I.map (β₁.app K) ≫ β₂.app (H₁.obj K)) ≫
      R₂.map (s.hom.app (H₁.obj K)) =
    (β.app K ≫ R₂.map (δ.hom.app K)) ≫ R₂.map (s.hom.app (H₁.obj K)) at h
  simp only [Category.assoc] at h
  rw [hi, ← R₂.map_comp, hv] at h
  have hn := i.hom.naturality (β₁.app K)
  change I.map (β₁.app K) ≫ i.hom.app (R₁.obj (H₁.obj K)) =
    i.hom.app (G₁.obj (R₀.obj K)) ≫ β₁.app K at hn
  rw [reassoc_of% hn, ← Category.assoc (γ.hom.app (R₀.obj K)), hu] at h
  exact h.symm

end CategoryTheory
