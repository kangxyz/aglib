/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.Whole
/-! # Original inverse-mate naturality

A face law on right-adjoint squares yields the corresponding face law on the
original left-adjoint squares. No invertibility of the mates is assumed.
-/
@[expose] public section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G G' : C ⥤ E} {H H' : D ⥤ F}

@[reassoc]
theorem mateEquiv_symm_app_eq (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (ρ : TwoSquare R₁ H G R₂) (X : C) :
    ((mateEquiv a₁ a₂).symm ρ).app X =
      L₂.map (G.map (a₁.unit.app X)) ≫ L₂.map (ρ.natTrans.app (L₁.obj X)) ≫
        a₂.counit.app (H.obj (L₁.obj X)) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app,
    leftUnitor_inv_app, whiskerRight_app, associator_inv_app,
    associator_hom_app, whiskerLeft_app, rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_id,
    Category.id_comp]
  change L₂.map (G.map (a₁.unit.app X)) ≫
    L₂.map (ρ.natTrans.app (L₁.obj X)) ≫
      (a₂.counit.app (H.obj (L₁.obj X)) ≫ 𝟙 _) = _
  rw [Category.comp_id]

theorem mateEquiv_symm_top_bottom_naturality
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (ρ : TwoSquare R₁ H G R₂) (ρ' : TwoSquare R₁ H' G' R₂)
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ K, γ.app (R₁.obj K) ≫ ρ'.natTrans.app K = ρ.natTrans.app K ≫ R₂.map (δ.app K))
    (X : C) :
    L₂.map (γ.app X) ≫ ((mateEquiv a₁ a₂).symm ρ').app X =
      ((mateEquiv a₁ a₂).symm ρ).app X ≫ δ.app (L₁.obj X) := by
  rw [mateEquiv_symm_app_eq, mateEquiv_symm_app_eq]
  rw [← L₂.map_comp_assoc, ← γ.naturality, L₂.map_comp]
  simp only [Functor.comp_obj, Category.assoc]
  rw [← L₂.map_comp_assoc (γ.app (R₁.obj (L₁.obj X))) (ρ'.natTrans.app (L₁.obj X)), h]
  simp only [L₂.map_comp, Category.assoc]
  have hn := a₂.counit.naturality (δ.app (L₁.obj X))
  change L₂.map (R₂.map (δ.app (L₁.obj X))) ≫ a₂.counit.app (H'.obj (L₁.obj X)) =
    a₂.counit.app (H.obj (L₁.obj X)) ≫ δ.app (L₁.obj X) at hn
  rw [hn]

/-- Changing only the boundary functors transports the original mate by the
same actual boundary isomorphisms. -/
theorem mateEquiv_boundary_iso_app (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (s : G' ≅ G) (t : H ≅ H') (K : D) :
    (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight s.hom L₂ ≫ α.natTrans ≫ Functor.whiskerLeft L₁ t.hom))).app K =
      s.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₂ α).app K ≫ R₂.map (t.hom.app K) := by
  let β : TwoSquare G' L₁ L₂ H' := TwoSquare.mk _ _ _ _
    (Functor.whiskerRight s.hom L₂ ≫ α.natTrans ≫ Functor.whiskerLeft L₁ t.hom)
  have h : ∀ X, L₂.map (s.hom.app X) ≫ α.natTrans.app X = β.app X ≫ t.inv.app (L₁.obj X) := by
    intro X
    simp only [β, TwoSquare.mk, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app]
    change _ = L₂.map (s.hom.app X) ≫ (α.natTrans.app X ≫ 𝟙 _)
    rw [Category.comp_id]
  have hm := mateEquiv_top_bottom_naturality a₁ a₂ β α s.hom t.inv h K
  have he := congrArg (fun z => z ≫ R₂.map (t.hom.app K)) hm
  simp only [Category.assoc, ← R₂.map_comp, Iso.inv_hom_id_app,
    R₂.map_id] at he
  change _ = (mateEquiv a₁ a₂ β).natTrans.app K ≫ 𝟙 _ at he
  rw [Category.comp_id] at he
  exact he.symm

end CategoryTheory
