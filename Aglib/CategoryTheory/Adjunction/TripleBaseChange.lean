/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleLocalization
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Original left and right mates preserve the canonical outer-adjoint comparison -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {J S : A ⥤ B} {Q : B ⥤ A} {J' S' : C ⥤ D} {Q' : D ⥤ C}
  (t : Triple J Q S) (t' : Triple J' Q' S')
  [J.Full] [J.Faithful] [J'.Full] [J'.Faithful]
  (P : B ⥤ D) (P' : A ⥤ C)

/-- The whole square retains both actual base-change maps and both canonical comparisons. -/
def TripleBaseChangeEquation (α : J ⋙ P ≅ P' ⋙ J') (β : S ⋙ P ⟶ P' ⋙ S') : Prop :=
  α.hom ≫ whiskerLeft P' t'.leftToRight = whiskerRight t.leftToRight P ≫ β

/-- The two original mate identities suffice; no invertibility of the right mate is assumed. -/
theorem Triple.leftToRight_baseChange (e : Q ⋙ P' ≅ P ⋙ Q')
    (α : J ⋙ P ≅ P' ⋙ J') (β : S ⋙ P ⟶ P' ⋙ S')
    (hα : mateEquiv t.adj₁ t'.adj₁ (TwoSquare.mk _ _ _ _ α.inv) =
      TwoSquare.mk _ _ _ _ e.hom)
    (hβ : (mateEquiv t.adj₂ t'.adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans = β) :
    TripleBaseChangeEquation t t' P P' α β := by
  have hJ (X : A) : t'.adj₁.unit.app (P'.obj X) =
      P'.map (t.adj₁.unit.app X) ≫ e.hom.app (J.obj X) ≫ Q'.map (α.hom.app X) := by
    have h := unit_mateEquiv t.adj₁ t'.adj₁ (TwoSquare.mk _ _ _ _ α.inv) X
    rw [hα] at h
    have h' := congrArg (fun z => z ≫ Q'.map (α.hom.app X)) h
    simpa only [TwoSquare.mk, Functor.id_obj, Functor.comp_obj, Category.assoc, ← Q'.map_comp,
      Iso.inv_hom_id_app, Q'.map_id, Category.comp_id] using h'.symm
  have hQ (Y : B) : t'.adj₂.unit.app (P.obj Y) =
      P.map (t.adj₂.unit.app Y) ≫ β.app (Q.obj Y) ≫ S'.map (e.hom.app Y) := by
    have h := unit_mateEquiv t.adj₂ t'.adj₂ (TwoSquare.mk _ _ _ _ e.inv) Y
    have h' := congrArg (fun z => z ≫ S'.map (e.hom.app Y)) h
    change _ = _ at h'
    rw [show (mateEquiv t.adj₂ t'.adj₂ (TwoSquare.mk _ _ _ _ e.inv)).app (Q.obj Y) =
      β.app (Q.obj Y) from congrArg (fun z => z.app (Q.obj Y)) hβ] at h'
    simpa only [TwoSquare.mk, Functor.id_obj, Functor.comp_obj, Category.assoc, ← S'.map_comp,
      Iso.inv_hom_id_app, S'.map_id, Category.comp_id] using h'.symm
  apply NatTrans.ext
  funext X
  exact Triple.leftToRight_normalized t t' P' P α.hom e.hom β hJ hQ
    t.leftToRight t.leftToRight_app_map_adj₁_unit_app X
end CategoryTheory.Adjunction
