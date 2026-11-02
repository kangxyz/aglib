/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightUnitMiddle
public import Aglib.CategoryTheory.Functor.ImageStructuralRectangle

/-! # Contracting the last same-endpoint identity in a structural image rectangle -/

@[expose] public section
namespace CategoryTheory
variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  {N : A ⥤ B} {Q : A ⥤ E} {P : B ⥤ D} {P₀ : B ⥤ E}
  {S : E ⥤ D} {R : D ⥤ E} {I : E ⥤ E}

/-- An original structural rectangle and the original final identity comparison give the
whole right-unit structural triangle, without evaluating concrete native derived maps. -/
theorem rightUnitStructuralEquation_of_rectangle
    (c : N ⋙ P ≅ Q ⋙ S) (d : P ⋙ R ≅ P₀) (e : N ⋙ P₀ ≅ Q)
    (s : S ⋙ R ≅ I) (u : I ≅ 𝟭 E) (t : Q ⋙ I ≅ Q)
    (h : ImageCompositionStructuralEquation d c s e t)
    (ht : t = Functor.isoWhiskerLeft Q u ≪≫ Functor.rightUnitor Q) :
    RightUnitStructuralEquation c d e (s ≪≫ u) := by
  subst t
  apply Iso.ext
  ext K
  have hh := h K
  change d.hom.app (N.obj K) ≫ e.hom.app K =
    R.map (c.hom.app K) ≫ s.hom.app (Q.obj K) ≫
      u.hom.app (Q.obj K) ≫ 𝟙 _ at hh
  rw [Category.comp_id] at hh
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  change d.hom.app (N.obj K) ≫ e.hom.app K =
    R.map (c.hom.app K) ≫ (s.hom.app (Q.obj K) ≫
      u.hom.app (Q.obj K)) ≫ 𝟙 _
  rw [Category.comp_id]
  exact hh


end CategoryTheory
