/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.ConstantSheaf.Unit

/-! # Coefficient naturality of the original constant-sheaf comparison

The constant-composition comparison is natural in transformations of the
coefficient functor, not only morphisms of coefficient objects. In particular,
it retains noncentral scalar actions on a forgetful coefficient functor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
namespace CategoryTheory

universe u v a b c d
variable {C : Type u} [Category.{v} C] {A : Type a} [Category.{b} A]
  {B : Type c} [Category.{d} B] (J : GrothendieckTopology C)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  (F G : A ⥤ B) [J.PreservesSheafification F] [J.HasSheafCompose F]
  [J.PreservesSheafification G] [J.HasSheafCompose G]

/-- The original constant comparison commutes with any transformation of
coefficient functors, without fullness or constant-object faithfulness. -/
theorem constantCommuteCompose_coefficient_naturality (α : F ⟶ G) (X : A) :
    (sheafCompose_map J α).app ((constantSheaf J A).obj X) ≫
        (constantCommuteCompose J G).hom.app X =
      (constantCommuteCompose J F).hom.app X ≫
        (constantSheaf J B).map (α.app X) := by
  let e := (constantCommuteCompose J F).app X
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj X)
  have hF (U : Cᵒᵖ) : F.map (η.app U) ≫ e.hom.hom.app U =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X))).app U := by
    simpa only [e, η, Iso.app_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.constComp_hom_app, Category.id_comp] using
      NatTrans.congr_app (constantCommuteCompose_toSheafify J F X) U
  have hG (U : Cᵒᵖ) : G.map (η.app U) ≫
      ((constantCommuteCompose J G).hom.app X).hom.app U =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (G.obj X))).app U := by
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.constComp_hom_app, Category.id_comp] using
      NatTrans.congr_app (constantCommuteCompose_toSheafify J G X) U
  have hFinv (U : Cᵒᵖ) :
      (toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X))).app U ≫ e.inv.hom.app U =
        F.map (η.app U) := by
    rw [← hF U, Category.assoc]
    have hi := congrArg (fun f => f.hom.app U) e.hom_inv_id
    change e.hom.hom.app U ≫ e.inv.hom.app U = 𝟙 _ at hi
    rw [hi]
    exact Category.comp_id (F.map (η.app U))
  apply (cancel_epi e.inv).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((constantSheaf J B).obj (G.obj X)).property
  ext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ← Category.assoc]
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X))).app U ≫
      e.inv.hom.app U) ≫ α.app ((sheafify J ((Functor.const Cᵒᵖ).obj X)).obj U)) ≫
      ((constantCommuteCompose J G).hom.app X).hom.app U =
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X))).app U ≫
      e.inv.hom.app U) ≫ e.hom.hom.app U) ≫
      ((constantSheaf J B).map (α.app X)).hom.app U
  rw [hFinv U, hF U, α.naturality (η.app U), Category.assoc, hG U]
  exact NatTrans.congr_app
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (α.app X))) U

end CategoryTheory
