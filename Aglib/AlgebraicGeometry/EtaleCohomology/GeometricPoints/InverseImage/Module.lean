/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Point
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients

/-! # Native module stalk pullback with an independently sized coefficient ring

The actual geometric-point comap comparison and native sheaf-fibre comparison
construct this isomorphism. Neither exceptional operations nor finiteness is
used. The original module-valued inverse image is retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
  (R : Type r) [Ring R]

attribute [local instance] geometricPointComap_initiallySmall ModuleCat.Sheaf.hasSheafify

local instance geometricModulePointRepresentablyFlat : RepresentablyFlat (siteBaseChange f) :=
  flat_of_preservesFiniteLimits (siteBaseChange f)

local instance geometricModulePointHasLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, r}

/-- Actual geometric stalks commute with native module-valued inverse image,
with no restriction on the independent coefficient-ring universe. -/
def geometricModuleStalkInverseImageIso :
    (pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} R) ≅
      (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} R)
        X.smallEtaleTopology S.smallEtaleTopology ⋙ (pointSmallEtale η).sheafFiber := by
  let e := geometricPointComapIso f η
  let e' : (pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} R) ≅
      ((pointSmallEtale η).comap (siteBaseChange f)
        (siteBaseChange_coverPreserving f)).sheafFiber :=
    { hom := e.inv.sheafFiber
      inv := e.hom.sheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id]
        exact GrothendieckTopology.Point.Hom.sheafFiber_id _
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id]
        exact GrothendieckTopology.Point.Hom.sheafFiber_id _ }
  exact e' ≪≫ (pointSmallEtale η).sheafFiberComapIso (siteBaseChange f)
    (siteBaseChange_coverPreserving f) (ModuleCat.{u + 1} R)

end AlgebraicGeometry.Scheme.EtaleCohomology
