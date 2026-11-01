/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightUnit
public import Aglib.CategoryTheory.Adjunction.UnitMateHorizontal

/-! # Contracting the two same-model identities in a source-open face -/

@[expose] public section
namespace CategoryTheory
variable {U A B : Type*} [Category* U] [Category* A] [Category* B]
  {J : U ⥤ A} {L : U ⥤ B} {M N : A ⥤ B} {I H : A ⥤ A}

/-- Normalizing only the first-model identities gives the original open face.
No models on the final ambient or the identity target are identified. -/
theorem rightUnitOpenEquation_of_horizontal
    (δJ : J ⟶ J ⋙ I) (δ : L ⟶ J ⋙ N)
    (σ : I ⋙ M ⟶ H ⋙ N) (c : L ≅ J ⋙ M) (c' : J ≅ J ⋙ H)
    (d : I ≅ 𝟭 A) (l : H ≅ 𝟭 A) (δM : M ⟶ H ⋙ N)
    (h : UnitMateHorizontalEquation δJ δ σ c c')
    (hJ : ∀ K, δJ.app K = d.inv.app (J.obj K))
    (hM : ∀ K, δM.app K = M.map (d.inv.app K) ≫ σ.app K)
    (hc : ∀ K, c'.hom.app K = l.inv.app (J.obj K)) :
    RightUnitOpenEquation c.symm δ
      (δM ≫ Functor.whiskerRight l.hom N ≫ (Functor.leftUnitor N).hom) := by
  intro K
  have hh := h K
  rw [hJ, ← hM, hc] at hh
  change c.inv.app K ≫ δ.app K =
    δM.app (J.obj K) ≫ N.map (l.hom.app (J.obj K)) ≫ 𝟙 _
  rw [Category.comp_id]
  apply (cancel_epi (c.hom.app K)).mp
  rw [Iso.hom_inv_id_app_assoc, ← Category.assoc, hh]
  rw [Category.assoc, ← N.map_comp, Iso.inv_hom_id_app]
  change δ.app K = δ.app K ≫ N.map (𝟙 (J.obj K))
  rw [N.map_id]
  exact (Category.comp_id (δ.app K)).symm

end CategoryTheory
