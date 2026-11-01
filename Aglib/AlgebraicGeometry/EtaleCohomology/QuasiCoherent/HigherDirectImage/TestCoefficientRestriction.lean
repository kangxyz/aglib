/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModulePullbackCompositionCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionCanonical

/-! # Original coefficient restriction on native étale tests

The complete inverse-coefficient square is assembled before an affine ring,
a module higher image or its section comparison is instantiated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [hU : HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]
  [hV : HasExt.{e'} (AbelianSheaf.{u, u + 1} (Limits.pullback V.hom f))]

local instance : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hU
local instance : HasExt.{e'}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj V).left) := hV

local instance : Etale U.hom := U.prop
local instance : Etale V.hom := V.prop

/-- The original inverse coefficient comparison intertwines native module
chart transition and the unchanged fibre-product cohomology restriction. -/
theorem additiveCoefficientCohomologyPullback_test_restriction
    (z : Sheaf.H.{e} (additiveCoefficient (Limits.pullback U.hom f)
      ((Scheme.Modules.pullback (Limits.pullback.snd U.hom f)).obj M)) q) :
    let a := Limits.pullback.snd U.hom f
    let a' := Limits.pullback.snd V.hom f
    let c : Limits.pullback V.hom f ⟶ Limits.pullback U.hom f :=
      ((siteBaseChange f).map g).left
    let ha : c ≫ a = a' := siteBaseChange_map_snd f g
    let : ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback c).obj M).IsQuasicoherent :=
      inferInstanceAs (((Scheme.Modules.pullback c).obj
        ((Scheme.Modules.pullback a).obj M)).IsQuasicoherent)
    Sheaf.H.map (inv (additiveCoefficientPullback a' M)) q
      (Sheaf.H.map (additiveCoefficientMap (Limits.pullback V.hom f)
        ((Scheme.Modules.pullbackComp c a).hom.app M ≫
          (Scheme.Modules.pullbackCongr ha).hom.app M)) q
        (additiveCoefficientCohomologyPullback.{u, e, e'} c
          ((Scheme.Modules.pullback a).obj M) q z)) =
    fibreProductCohomologyRestriction f g (additiveCoefficient X M) q
      (Sheaf.H.map (inv (additiveCoefficientPullback a M)) q z) := by
  dsimp only
  have hb := additiveCoefficientCohomologyPullback_triangle_inv.{u, e, e'}
    (S := Limits.pullback U.hom f) (T := Limits.pullback V.hom f)
    (Limits.pullback.snd U.hom f) ((siteBaseChange f).map g).left
    (Limits.pullback.snd V.hom f) (siteBaseChange_map_snd f g) M q z
  rw [fibreProductCohomologyRestriction_apply_canonical]
  simp only [Scheme.Modules.pullbackTriangleIso_hom_app] at hb
  convert hb using 1

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
