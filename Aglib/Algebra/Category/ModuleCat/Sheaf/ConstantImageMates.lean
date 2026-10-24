/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImages

/-! # Scalar forgetting and the native image adjunction

The original Lan/sheafification comparison respects the actual adjunction unit.
The coefficient ring retains its own universe, and scalar forgetting is never
assumed full.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r w

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (R : Type r) [Ring R] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

attribute [local instance] hasSheafify forget_preservesSheafification

local instance constantImageMates_preservesColimits : PreservesColimitsOfSize.{w, w}
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} R

/-- The original scalar-forgetting pullback comparison preserves the native unit. -/
@[reassoc]
theorem pullbackUnderlyingIso_unit (L : Sheaf J (ModuleCat.{max u v} R)) :
    (underlying R J).map
        ((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app L) ≫
      (G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).map
        ((pullbackUnderlyingIso R G J K).hom.app L) =
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app
      ((underlying R J).obj L) := by
  let eA := Functor.sheafPullbackConstruction.sheafPullbackIso G
    (ModuleCat.{max u v} R) J K
  let eT := Functor.sheafPullbackConstruction.sheafPullbackIso G
    AddCommGrpCat.{max u v} J K
  let c := sheafComposeNatIso K (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    (sheafificationAdjunction _ (ModuleCat.{max u v} R))
    (sheafificationAdjunction _ AddCommGrpCat.{max u v})
  let k := (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).lanCompIsoOfPreserves G.op
  have hA := Adjunction.unit_leftAdjointUniq_hom_app
    (G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
      (ModuleCat.{max u v} R) J K) L
  have hT := Adjunction.unit_leftAdjointUniq_hom_app
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
      AddCommGrpCat.{max u v} J K)
        ((underlying R J).obj L)
  apply (cancel_mono ((G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).map
    (eT.hom.app ((underlying R J).obj L)))).mp
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hAU := congrArg
    (fun a => (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map (a.hom.app U)) hA
  have hTU := congrArg (fun a => a.hom.app U) hT
  let F := G.op
  let A := F.lan.obj L.obj
  let V := F.obj U
  change (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map
      (((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app L).hom.app U) ≫
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map ((eA.hom.app L).hom.app V) =
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map
      ((F.leftKanExtensionUnit L.obj).app U ≫ (toSheafify K A).app V) at hAU
  change ((G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app
      ((underlying R J).obj L)).hom.app U ≫
      (eT.hom.app ((underlying R J).obj L)).hom.app V =
    (F.leftKanExtensionUnit
      (L.obj ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}))).app U ≫
      (toSheafify K
        (F.lan.obj
          (L.obj ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})))).app V at hTU
  have hcancel : (eT.inv.app ((underlying R J).obj L)).hom.app V ≫
      (eT.hom.app ((underlying R J).obj L)).hom.app V = 𝟙 _ :=
    congrArg (fun a => a.hom.app V) (eT.inv_hom_id_app ((underlying R J).obj L))
  change (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map
      (((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app L).hom.app U) ≫
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map ((eA.hom.app L).hom.app V) ≫
      (c.inv.app A).hom.app V ≫
      ((presheafToSheaf K AddCommGrpCat.{max u v}).map
        (k.hom.app L.obj)).hom.app V ≫
      (eT.inv.app ((underlying R J).obj L)).hom.app V ≫
      (eT.hom.app ((underlying R J).obj L)).hom.app V = _
  erw [hcancel, Category.comp_id]
  change ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map
      (((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app L).hom.app U) ≫
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map ((eA.hom.app L).hom.app V)) ≫
      (c.inv.app A).hom.app V ≫
      ((presheafToSheaf K AddCommGrpCat.{max u v}).map
        (k.hom.app L.obj)).hom.app V =
    ((G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app
      ((underlying R J).obj L)).hom.app U ≫
      (eT.hom.app ((underlying R J).obj L)).hom.app V
  erw [hAU, hTU, Functor.map_comp]
  have hc : (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map ((toSheafify
    K A).app V) ≫
      (c.inv.app A).hom.app V =
    (toSheafify K (A ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}))).app V :=
    congr_app (sheafComposeIso_inv_fac K (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      A) V
  have hn := (congr_app (toSheafify_naturality K (k.hom.app L.obj))
    V).symm
  have hk := Functor.leftKanExtensionCompIsoOfPreserves_hom_fac_app
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) L.obj F U
  change (toSheafify K (A ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}))).app V ≫
      ((presheafToSheaf K AddCommGrpCat.{max u v}).map
        (k.hom.app L.obj)).hom.app V =
    (k.hom.app L.obj).app V ≫
      (toSheafify K
        (F.lan.obj
          (L.obj ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})))).app V at hn
  change (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map
      ((F.leftKanExtensionUnit L.obj).app U) ≫
      (k.hom.app L.obj).app V =
    (F.leftKanExtensionUnit
      (L.obj ⋙ (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}))).app U at hk
  simp only [Category.assoc] at ⊢
  erw [← Category.assoc ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map ((toSheafify
    K A).app V)),
    hc, hn, ← Category.assoc, hk]

end ModuleCat.Sheaf
