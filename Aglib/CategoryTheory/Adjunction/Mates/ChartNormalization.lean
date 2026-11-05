/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.Chart

/-! # Whole component normalization at the original chart boundaries -/
@[expose] public section
open CategoryTheory
namespace CategoryTheory.SourceChartMates
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]

/-- Cancel the two original boundary isomorphisms using only the naturality
of the original middle comparison. -/
theorem normalize_component (F : C ⥤ E) (G : D ⥤ V) (R : D ⥤ C) (S : V ⥤ E)
    (δ : R ⋙ F ⟶ G ⋙ S) {A A' : C} {B B' : D} {X : E} {Y : V}
    (i : A ≅ A') (j : B ≅ B') (s : X ⟶ F.obj A')
    (r : A' ⟶ R.obj B') (t : G.obj B' ⟶ Y) :
    𝟙 X ≫ s ≫ F.map i.inv ≫ F.map i.hom ≫ F.map r ≫
        F.map (R.map j.inv) ≫ δ.app B ≫ S.map (G.map j.hom ≫ t) =
      s ≫ F.map r ≫ δ.app B' ≫ S.map t := by
  rw [Category.id_comp, ← F.map_comp_assoc i.inv i.hom, Iso.inv_hom_id,
    F.map_id, Category.id_comp]
  have hn := δ.naturality j.inv
  change F.map (R.map j.inv) ≫ δ.app B = δ.app B' ≫ S.map (G.map j.inv) at hn
  rw [reassoc_of% hn]
  simp only [← S.map_comp, ← G.map_comp_assoc, Iso.inv_hom_id,
    G.map_id, Category.id_comp]

end CategoryTheory.SourceChartMates
