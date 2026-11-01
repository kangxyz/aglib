/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitMateHorizontal
public import Aglib.CategoryTheory.Functor.ImageComparison

/-! # Image-level contraction of the original horizontal unit face

The supplied original composition map is identified by its actual formula;
the conclusion is the original image comparison, not a newly chosen map.
-/

@[expose] public section
namespace CategoryTheory
variable {A B B' C C' Z : Type*}
  [Category* A] [Category* B] [Category* B'] [Category* C] [Category* C'] [Category* Z]
  {J : A ⥤ B} {J' : A ⥤ B'} {L : B ⥤ C} {L' : B' ⥤ C'}
  {T : A ⥤ C} {T' : A ⥤ C'} {R : B' ⥤ B} {S : C' ⥤ C}
  {P : C ⥤ Z} {P' : C' ⥤ Z}
  (δJ : J ⟶ J' ⋙ R) (δT : T ⟶ T' ⋙ S)
  (σ : R ⋙ L ⟶ L' ⋙ S) (c : T ≅ J ⋙ L) (c' : T' ≅ J' ⋙ L')
  (e : S ⋙ P ≅ P') (α : J' ⋙ R ⋙ L ⋙ P ⟶ T' ⋙ P')

/-- The supplied original composition map retains its interchange and compositor formula. -/
def ImageUnitHorizontalFormula : Prop :=
  ∀ K, α.app K = P.map (σ.app (J'.obj K)) ≫
    P.map (S.map (c'.inv.app K)) ≫ e.hom.app (T'.obj K)

/-- The original unit face contracts to the actual original image comparison. -/
def ImageUnitHorizontalEquation : Prop :=
  Functor.whiskerRight c.hom P ≫
      Functor.whiskerRight (Functor.whiskerRight δJ L) P ≫ α = imageComparison δT e

/-- Proved horizontal original-unit pasting gives the actual image-level unit triangle. -/
theorem imageUnitHorizontalEquation
    (h : UnitMateHorizontalEquation δJ δT σ c c')
    (hα : ImageUnitHorizontalFormula σ c' e α) :
    ImageUnitHorizontalEquation δJ δT c e α := by
  apply NatTrans.ext
  funext K
  change P.map (c.hom.app K) ≫ P.map (L.map (δJ.app K)) ≫ α.app K = _
  rw [hα, imageComparison_app]
  have hk := h K
  have he := congrArg (fun t => P.map t) hk
  simp only [Functor.map_comp] at he
  calc
    _ = (P.map (c.hom.app K) ≫ P.map (L.map (δJ.app K)) ≫
        P.map (σ.app (J'.obj K))) ≫
        P.map (S.map (c'.inv.app K)) ≫ e.hom.app (T'.obj K) := by
      simp only [Category.assoc]
    _ = (P.map (δT.app K) ≫ P.map (S.map (c'.hom.app K))) ≫
        P.map (S.map (c'.inv.app K)) ≫ e.hom.app (T'.obj K) := by rw [he]
    _ = _ := by
      have hc : P.map (S.map (c'.hom.app K)) ≫ P.map (S.map (c'.inv.app K)) =
          𝟙 (P.obj (S.obj (T'.obj K))) := by
        rw [← P.map_comp, ← S.map_comp, Iso.hom_inv_id_app, S.map_id, P.map_id]
      have ht := congrArg (fun t => P.map (δT.app K) ≫ t ≫ e.hom.app (T'.obj K)) hc
      have hi : 𝟙 (P.obj (S.obj (T'.obj K))) ≫ e.hom.app (T'.obj K) =
          e.hom.app (T'.obj K) := Category.id_comp _
      have ht' : (P.map (δT.app K) ≫ P.map (S.map (c'.hom.app K))) ≫
          P.map (S.map (c'.inv.app K)) ≫ e.hom.app (T'.obj K) =
          P.map (δT.app K) ≫ (𝟙 (P.obj (S.obj (T'.obj K))) ≫ e.hom.app (T'.obj K)) := by
        simpa only [Category.assoc] using ht
      exact ht'.trans (congrArg (fun t => P.map (δT.app K) ≫ t) hi)

end CategoryTheory
