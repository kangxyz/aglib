/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Adjunction.Triple
/-! # Original-unit normalization of the canonical outer-adjoint map -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {J S : C ⥤ D} {U : D ⥤ C} {J' S' : C' ⥤ D'} {U' : D' ⥤ C'}
  (t : Triple J U S) (t' : Triple J' U' S') [J'.Full] [J'.Faithful]
  (Q : C ⥤ C') (T : D ⥤ D')
  (aJ : J ⋙ T ⟶ Q ⋙ J') (aU : U ⋙ Q ⟶ T ⋙ U') (aS : S ⋙ T ⟶ Q ⋙ S')
  (hJ : ∀ X, t'.adj₁.unit.app (Q.obj X) =
    Q.map (t.adj₁.unit.app X) ≫ aU.app (J.obj X) ≫ U'.map (aJ.app X))
  (hU : ∀ Y, t'.adj₂.unit.app (T.obj Y) =
    T.map (t.adj₂.unit.app Y) ≫ aS.app (U.obj Y) ≫ S'.map (aU.app Y))
  (b : J ⟶ S)
  (hb : ∀ X, b.app X ≫ S.map (t.adj₁.unit.app X) = t.adj₂.unit.app (J.obj X))

include hJ hU hb in
/-- Two original adjunction-unit squares determine the canonical outer-adjoint map. -/
theorem Triple.leftToRight_normalized (X : C) :
    aJ.app X ≫ t'.leftToRight.app (Q.obj X) = T.map (b.app X) ≫ aS.app X := by
  apply (cancel_mono (S'.map (t'.adj₁.unit.app (Q.obj X)))).1
  rw [Category.assoc, Triple.leftToRight_app, ← S'.map_inv]
  simp only [Category.assoc, ← S'.map_comp, IsIso.inv_hom_id, S'.map_id]
  have hi := Category.comp_id (t'.adj₂.unit.app (J'.obj (Q.obj X)))
  dsimp only [Functor.comp_obj] at hi
  rw [hi]
  have hn := t'.adj₂.unit.naturality (aJ.app X)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, hU, hJ]
  have ha := aS.naturality (t.adj₁.unit.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ha
  simp only [S'.map_comp, Category.assoc]
  rw [← reassoc_of% ha, ← T.map_comp_assoc, hb]

end CategoryTheory.Adjunction
