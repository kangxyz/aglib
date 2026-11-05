/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Sheafification comparison is natural in the whole coefficient functor

This includes transformations such as noncentral left multiplication on a
forgetful coefficient functor. No fullness or linear coefficient category is
required, and the original comparison and unit maps are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoryTheory
universe u v a b c d
variable {C : Type u} [Category.{v} C] {A : Type a} [Category.{b} A]
  {B : Type c} [Category.{d} B] (J : GrothendieckTopology C)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  (F G : A ⥤ B) [J.PreservesSheafification F] [J.HasSheafCompose F]
  [J.PreservesSheafification G] [J.HasSheafCompose G]

/-- The specified comparison commutes with every coefficient transformation. -/
theorem sheafComposeNatIso_coefficient_naturality (α : F ⟶ G) (P : Cᵒᵖ ⥤ A) :
    (sheafComposeNatIso J F (sheafificationAdjunction J A)
        (sheafificationAdjunction J B)).hom.app P ≫
      (sheafCompose_map J α).app ((presheafToSheaf J A).obj P) =
    (presheafToSheaf J B).map (Functor.whiskerLeft P α) ≫
      (sheafComposeNatIso J G (sheafificationAdjunction J A)
        (sheafificationAdjunction J B)).hom.app P := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((sheafCompose J G).obj ((presheafToSheaf J A).obj P)).property
  ext U
  have hF := NatTrans.congr_app (sheafComposeIso_hom_fac J F P) U
  have hG := NatTrans.congr_app (sheafComposeIso_hom_fac J G P) U
  have hn := NatTrans.congr_app
    (toSheafify_naturality J (Functor.whiskerLeft P α)) U
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hF hG hn
  change (toSheafify J (P ⋙ F)).app U ≫
      (sheafifyComposeIso J F P).hom.app U ≫
        α.app ((sheafify J P).obj U) =
    (toSheafify J (P ⋙ F)).app U ≫
      ((presheafToSheaf J B).map (Functor.whiskerLeft P α)).hom.app U ≫
        (sheafifyComposeIso J G P).hom.app U
  rw [← Category.assoc, hF, ← Category.assoc, ← hn, Category.assoc, hG]
  exact α.naturality ((toSheafify J P).app U)

end CategoryTheory
