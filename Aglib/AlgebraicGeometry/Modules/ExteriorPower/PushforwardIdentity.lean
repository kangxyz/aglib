/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward

/-!
# Identity of the original exterior coefficient map

The original identity-pushforward inverse induces exactly that same inverse
on exterior powers. The proof uses the original wedge universal property.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Exterior coefficients preserve the original identity-pushforward comparison. -/
theorem exteriorCoefficientMap_id (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    exteriorCoefficientMap (𝟙 X) ((pushforwardId X).inv.app M) n =
      (pushforwardId X).inv.app (moduleExteriorPower X M n) := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X.sheaf M _ n
  intro V v
  change (exteriorCoefficientMap (𝟙 X) ((pushforwardId X).inv.app M) n).val.app V
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app V v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app V v
  exact SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward (𝟙 X)).obj (moduleExteriorPower X M n)) n
    (exteriorCoefficientAlternating (𝟙 X) ((pushforwardId X).inv.app M) n) V v

end AlgebraicGeometry.Scheme.Modules
