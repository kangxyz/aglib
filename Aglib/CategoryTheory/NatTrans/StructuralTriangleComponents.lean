/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Whiskering

/-! # Whole original structural triangles retain their component equation -/
@[expose] public section
namespace CategoryTheory
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {S : A ⥤ B} {R : B ⥤ C} {T : B ⥤ D} {P : C ⥤ D} {V : A ⥤ C} {H : A ⥤ D}

/-- A whole triangle gives the exact original component contraction, without concrete expansion. -/
theorem structuralTriangle_components (e : R ⋙ P ≅ T) (a : S ⋙ T ≅ H)
    (c : S ⋙ R ≅ V) (b : V ⋙ P ≅ H)
    (h : Functor.isoWhiskerLeft S e ≪≫ a =
      (Functor.associator S R P).symm ≪≫ Functor.isoWhiskerRight c P ≪≫ b) :
    ∀ K, e.hom.app (S.obj K) ≫ a.hom.app K = P.map (c.hom.app K) ≫ b.hom.app K := by
  intro K
  have hK := congrArg (fun z => z.hom.app K) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] using hK
end CategoryTheory
