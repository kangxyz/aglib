/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartRestrictionNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology

/-! # Actual restriction between the fibre-product cohomology groups -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w s₁ s₂ w₁ w₂

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

/-- Restriction uses the actual fibre-product morphism, original cohomology pullback,
and original inverse-image triangle transport. -/
def fibreProductCohomologyRestriction (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{w₁} ((inverseImage (pullback.snd U.hom f)).obj F) q →+
      Sheaf.H.{w₂} ((inverseImage (pullback.snd V.hom f)).obj F) q :=
  (Sheaf.H.map ((pullbackTriangleIso ((siteBaseChange f).obj V).hom
    ((siteBaseChange f).obj U).hom ((siteBaseChange f).map g).left
    (MorphismProperty.Over.w ((siteBaseChange f).map g))).inv.app F) q).comp
    (cohomologyPullback ((siteBaseChange f).map g).left
      ((inverseImage (pullback.snd U.hom f)).obj F) q)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s₁} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [HasExt.{s₂} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj V)) AddCommGrpCat.{u + 1})]

/-- The original represented restrictions agree with actual scheme cohomology restriction. -/
theorem fibreProductCohomologyEquiv_restriction
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    fibreProductCohomologyEquiv f V F q
      ((originalCohomologyPresheaf f F q).map g.op x) =
    fibreProductCohomologyRestriction f g F q
      (fibreProductCohomologyEquiv f U F q x) :=
  originalCohomologyChartEquiv_restriction ((siteBaseChange f).map g) F q x

end AlgebraicGeometry.Scheme.EtaleCohomology
