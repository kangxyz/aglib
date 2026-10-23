/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalGerms

/-! # The actual fibre-product schemes in higher-image cohomology -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₂} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hPullbackExt : HasExt.{w₃} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance : HasExt.{w₃}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) :=
  hPullbackExt

/-- The chart comparison on the genuine scheme fibre product and its original
projection inverse image. No cohomology on a replacement site appears in the target. -/
def fibreProductCohomologyEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.LargeCohomology.H.{w₁, u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U) ≃+
      Sheaf.H.{w₃} ((inverseImage (pullback.snd U.hom f)).obj F) q :=
  originalCohomologyChartEquiv ((siteBaseChange f).obj U) F q

/-- Original cohomology on the fibre-product scheme maps to the native higher-image
stalk through the proved original class comparison. -/
def fibreProductCohomologyGerm (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U) :
    Sheaf.H.{w₃} ((inverseImage (pullback.snd U.hom f)).obj F) q →+
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) :=
  (originalCohomologyGerm f F q η U p).comp
    (fibreProductCohomologyEquiv f U F q).symm.toAddMonoidHom

end AlgebraicGeometry.Scheme.EtaleCohomology
