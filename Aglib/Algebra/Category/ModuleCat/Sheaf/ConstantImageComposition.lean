/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImages

/-! # Scalar forgetting and original direct-image composition

This is the coefficient/site-level precomposition identity for the actual
native direct-image composition. No inverse-image construction or geometric
site comparison is unfolded in its consumers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (R : Type r) [Ring R] (G : C ⥤ D) (H : D ⥤ E) (I : C ⥤ E)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E)
  [G.IsContinuous J K] [H.IsContinuous K L] [I.IsContinuous J L]

/-- The original direct-image composition commutes with actual scalar forgetting. -/
theorem pushforwardUnderlyingIso_comp (e : G ⋙ H ≅ I)
    (M : Sheaf L (ModuleCat.{max u v} R)) :
    (underlying R J).map
        ((Functor.sheafPushforwardContinuousComp' e (ModuleCat.{max u v} R) J K L).inv.app M) ≫
        (pushforwardUnderlyingIso R G J K).hom.app
          ((H.sheafPushforwardContinuous (ModuleCat.{max u v} R) K L).obj M) ≫
        (G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).map
          ((pushforwardUnderlyingIso R H K L).hom.app M) =
      (pushforwardUnderlyingIso R I J L).hom.app M ≫
        (Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{max u v} J K L).inv.app
          ((underlying R L).obj M) := by
  simp only [pushforwardUnderlyingIso, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rfl

end ModuleCat.Sheaf
