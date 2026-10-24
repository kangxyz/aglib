/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageComposition

/-! # Original direct-image squares and scalar forgetting

The native precomposition square retains both original composition isomorphisms
and the equality transport between the original site maps. Its scalar comparison
is proved before either geometric site functors or inverse images are introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r

variable {C D D' E : Type u}
  [Category.{v} C] [Category.{v} D] [Category.{v} D'] [Category.{v} E]
  (R : Type r) [Ring R] (G : C ⥤ D) (H : D ⥤ E) (G' : C ⥤ D') (H' : D' ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (K' : GrothendieckTopology D') (L : GrothendieckTopology E)
  [G.IsContinuous J K] [H.IsContinuous K L]
  [G'.IsContinuous J K'] [H'.IsContinuous K' L]

/-- The original native direct-image square has its original underlying abelian square. -/
theorem pushforwardUnderlyingIso_square
    {I : Sort*} (F : I → C ⥤ E) [∀ i, (F i).IsContinuous J L]
    {i j : I} (h : i = j) (a : G ⋙ H ≅ F i) (b : G' ⋙ H' ≅ F j)
    (p : H.sheafPushforwardContinuous (ModuleCat.{max u v} R) K L ⋙
        G.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K ≅
      H'.sheafPushforwardContinuous (ModuleCat.{max u v} R) K' L ⋙
        G'.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K')
    (p' : H.sheafPushforwardContinuous AddCommGrpCat.{max u v} K L ⋙
        G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K ≅
      H'.sheafPushforwardContinuous AddCommGrpCat.{max u v} K' L ⋙
        G'.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K')
    (hp : p = Functor.sheafPushforwardContinuousComp' a (ModuleCat.{max u v} R) J K L ≪≫
      eqToIso (congrArg (fun k => (F k).sheafPushforwardContinuous
        (ModuleCat.{max u v} R) J L) h) ≪≫
      (Functor.sheafPushforwardContinuousComp' b (ModuleCat.{max u v} R) J K' L).symm)
    (hp' : p' = Functor.sheafPushforwardContinuousComp' a AddCommGrpCat.{max u v} J K L ≪≫
      eqToIso (congrArg (fun k => (F k).sheafPushforwardContinuous
        AddCommGrpCat.{max u v} J L) h) ≪≫
      (Functor.sheafPushforwardContinuousComp' b AddCommGrpCat.{max u v} J K' L).symm)
    (M : Sheaf L (ModuleCat.{max u v} R)) :
    (underlying R J).map (p.hom.app M) ≫
        (pushforwardUnderlyingIso R G' J K').hom.app
          ((H'.sheafPushforwardContinuous (ModuleCat.{max u v} R) K' L).obj M) ≫
        (G'.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K').map
          ((pushforwardUnderlyingIso R H' K' L).hom.app M) =
      ((pushforwardUnderlyingIso R G J K).hom.app
          ((H.sheafPushforwardContinuous (ModuleCat.{max u v} R) K L).obj M) ≫
        (G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).map
          ((pushforwardUnderlyingIso R H K L).hom.app M)) ≫
        p'.hom.app ((underlying R L).obj M) := by
  subst p
  subst p'
  subst j
  simp only [pushforwardUnderlyingIso, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

end ModuleCat.Sheaf
