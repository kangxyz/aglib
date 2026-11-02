/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionValues

/-! # Canonical projection evaluation of the original restriction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w₁ w₂

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)
  [hU : HasExt.{w₁} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hV : HasExt.{w₂} (AbelianSheaf.{u, u + 1} (pullback V.hom f))]

local instance : HasExt.{w₁}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hU
local instance : HasExt.{w₂}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj V).left) := hV

local instance : HasExt.{w₁}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hU
local instance : HasExt.{w₂}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj V).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hV

/-- The native restriction evaluates by its original cohomology pullback and
original inverse-image triangle, before any affine-test specialization. -/
theorem fibreProductCohomologyRestriction_apply_canonical
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.H.{w₁} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyRestriction f g F q x =
      Sheaf.H.map ((pullbackTriangleIso
        (X := X) (Y := pullback V.hom f) (Z := pullback U.hom f)
        (pullback.snd V.hom f)
        (pullback.snd U.hom f) ((siteBaseChange f).map g).left
        (siteBaseChange_map_snd f g)).inv.app F) q
        (cohomologyPullback (X := pullback U.hom f) (S := pullback V.hom f)
          ((siteBaseChange f).map g).left
          ((inverseImage (pullback.snd U.hom f)).obj F) q x) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
