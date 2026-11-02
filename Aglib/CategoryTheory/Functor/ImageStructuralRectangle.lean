/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionRefinement
public import Mathlib.CategoryTheory.Whiskering

/-! # Original structural rectangles from whole composition triangles

Only abstract functors are expanded when passing from the two whole original
triangle equations to the structural face. Concrete consumers retain the same
regular output predicate and the same specified comparison maps.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* Z]
  {T : A ⥤ C} {U : C ⥤ D} {V : A ⥤ B} {W : B ⥤ D} {P : D ⥤ Z}
  {P' : C ⥤ Z} {S : B ⥤ Z} {S' : A ⥤ Z} {N M : A ⥤ D}

/-- Two original whole composition triangles and their original equality
transport give the structural face with the specified original rectangle iso. -/
theorem imageCompositionStructuralEquation_of_triangles
    (p : U ⋙ P ≅ P') (r : T ⋙ U ≅ V ⋙ W)
    (s : W ⋙ P ≅ S) (s' : T ⋙ P' ≅ S') (t : V ⋙ S ≅ S')
    (s₀ : W ⋙ P ≅ S) (s₁ : T ⋙ P' ≅ S') (hs₀ : s₀ = s) (hs₁ : s₁ = s')
    (c : N ≅ T ⋙ U) (d : M ≅ V ⋙ W) (e : N ≅ M)
    (eC : N ⋙ P ≅ S') (eD : M ⋙ P ≅ S')
    (hc : Functor.isoWhiskerLeft T p ≪≫ s₁ =
      (Functor.associator T U P).symm ≪≫ Functor.isoWhiskerRight c.symm P ≪≫ eC)
    (hd : Functor.isoWhiskerLeft V s₀ ≪≫ t =
      (Functor.associator V W P).symm ≪≫ Functor.isoWhiskerRight d.symm P ≪≫ eD)
    (he : Functor.isoWhiskerRight e P ≪≫ eD = eC)
    (hr : r = c.symm ≪≫ e ≪≫ d) :
    ImageCompositionStructuralEquation p r s s' t := by
  subst s₀
  subst s₁
  subst r
  intro K
  have hC := congrArg (fun z => z.hom.app K) hc
  have hD := congrArg (fun z => z.hom.app K) hd
  have hE := congrArg (fun z => z.hom.app K) he
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hC hD hE
  change p.hom.app (T.obj K) ≫ s'.hom.app K =
    P.map ((c.symm ≪≫ e ≪≫ d).hom.app K) ≫ s.hom.app (V.obj K) ≫ t.hom.app K
  rw [hC, ← hE, hD]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, P.map_comp, Category.assoc]
  simp only [← P.map_comp_assoc, Iso.hom_inv_id_app, Category.comp_id]

end CategoryTheory
