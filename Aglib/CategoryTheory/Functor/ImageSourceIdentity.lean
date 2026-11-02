/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageComparison

/-! # Original image comparison with an identity target factor -/

@[expose] public section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {J : A ⥤ B} {K : A ⥤ C} {Q : C ⥤ B} {I : B ⥤ B}

/-- The original comparison contracts by the original identity normalization and naturality. -/
theorem imageComparison_identityTarget
    (δ : J ⟶ K ⋙ Q) (d : I ≅ 𝟭 B) (e : Q ⋙ I ≅ Q)
    (he : e = Functor.isoWhiskerLeft Q d ≪≫ Functor.rightUnitor Q) :
    imageComparison δ e = Functor.whiskerLeft J d.hom ≫
      (Functor.rightUnitor J).hom ≫ δ := by
  subst e
  apply NatTrans.ext
  funext X
  have h := d.hom.naturality (δ.app X)
  change I.map (δ.app X) ≫ d.hom.app (Q.obj (K.obj X)) =
    d.hom.app (J.obj X) ≫ δ.app X at h
  simp only [imageComparison_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  have hQ : d.hom.app (Q.obj (K.obj X)) ≫ 𝟙 (Q.obj (K.obj X)) =
      d.hom.app (Q.obj (K.obj X)) := Category.comp_id _
  have hJ : 𝟙 (J.obj X) ≫ δ.app X = δ.app X := Category.id_comp _
  rw [hQ, hJ]
  exact h

end CategoryTheory
