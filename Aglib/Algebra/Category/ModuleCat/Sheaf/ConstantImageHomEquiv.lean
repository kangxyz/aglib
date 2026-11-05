/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageMates

/-! # Native image-adjunction transposition after forgetting scalars

The original unit comparison determines the complete Hom-equivalence equation.
No fullness or alternative left-adjoint realization is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (R : Type r) [Ring R] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

attribute [local instance] hasSheafify

/-- Transposition under the original native image adjunction commutes with
scalar forgetting through the original inverse-image comparison. -/
theorem pullbackUnderlyingIso_homEquiv
    (M : Sheaf J (ModuleCat.{max u v} R)) (N : Sheaf K (ModuleCat.{max u v} R))
    (f : (G.sheafPullback (ModuleCat.{max u v} R) J K).obj M ⟶ N) :
    (underlying R J).map
        ((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).homEquiv M N f) =
      (G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).homEquiv
        ((underlying R J).obj M) ((underlying R K).obj N)
        ((pullbackUnderlyingIso R G J K).inv.app M ≫ (underlying R K).map f) := by
  let P := G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K
  let e := pullbackUnderlyingIso R G J K
  have hunit : (underlying R J).map
      ((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app M) =
      (G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app
        ((underlying R J).obj M) ≫ P.map (e.inv.app M) := by
    apply (cancel_mono (P.map (e.hom.app M))).mp
    rw [Category.assoc, ← P.map_comp, e.inv_hom_id_app]
    erw [P.map_id, Category.comp_id]
    exact pullbackUnderlyingIso_unit R G J K M
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  change (underlying R J).map
      ((G.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K).unit.app M) ≫
      P.map ((underlying R K).map f) =
    (G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app
      ((underlying R J).obj M) ≫ P.map (e.inv.app M ≫ (underlying R K).map f)
  rw [hunit, P.map_comp, Category.assoc]

end ModuleCat.Sheaf
