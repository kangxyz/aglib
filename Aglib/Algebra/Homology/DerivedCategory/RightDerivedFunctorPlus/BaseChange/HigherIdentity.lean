/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontal

/-! # Native homology and single comparisons give the actual higher identity edges -/

@[expose] public section
namespace CategoryTheory

/-- The actual homology identity comparison gives the normalized source edge. -/
theorem mapped_identity_source_edge
    {A D : Type*} [Category* A] [Category* D]
    (H : D ⥤ A) (G : A ⥤ A) (GD : D ⥤ D)
    (γ : GD ⋙ H ≅ H ⋙ G) (d : G ≅ 𝟭 A) (dD : GD ≅ 𝟭 D)
    (K : D) (h : H.map (dD.hom.app K) = γ.hom.app K ≫ d.hom.app (H.obj K))
    {Z : A} (e : Z ≅ H.obj K) (s : G.obj Z ≅ H.obj (GD.obj K))
    (hs : s.hom = G.map e.hom ≫ γ.inv.app K) :
    d.hom.app Z ≫ e.hom = s.hom ≫ H.map (dD.hom.app K) := by
  rw [hs, h, Category.assoc, Iso.inv_hom_id_app_assoc]
  simpa only [Functor.id_map] using (d.hom.naturality e.hom).symm

/-- The actual exact-single identity comparison gives the normalized target edge. -/
theorem mapped_identity_target_edge
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    (J : A ⥤ D) (R : D ⥤ E) (H : E ⥤ B) (V : A ⥤ B)
    (e : V ≅ J ⋙ R ⋙ H) (G : A ⥤ A) (GD : D ⥤ D)
    (σ : J ⋙ GD ≅ G ⋙ J) (d : G ≅ 𝟭 A) (dD : GD ≅ 𝟭 D)
    (F : A) (h : dD.hom.app (J.obj F) = σ.hom.app F ≫ J.map (d.hom.app F))
    (t : H.obj (R.obj (GD.obj (J.obj F))) ≅ V.obj (G.obj F))
    (ht : t.hom = H.map (R.map (σ.hom.app F)) ≫ e.inv.app (G.obj F)) :
    V.map (d.hom.app F) ≫ e.hom.app F =
      t.inv ≫ H.map (R.map (dD.hom.app (J.obj F))) := by
  apply (cancel_epi t.hom).mp
  rw [Iso.hom_inv_id_assoc, ht]
  simp only [Category.assoc]
  have hn := e.hom.naturality (d.hom.app F)
  simp only [Functor.id_obj, Functor.comp_map] at hn
  rw [hn, Iso.inv_hom_id_app_assoc]
  change H.map (R.map (σ.hom.app F)) ≫ H.map (R.map (J.map (d.hom.app F))) = _
  rw [← H.map_comp, ← R.map_comp, ← h]

end CategoryTheory
