/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward


/-!
# Composition of original exterior coefficient arrows

The sole exterior coefficient construction respects composition through
native pushforward composition, and respects an original target map. Both
equalities are proved on original exterior generators with the actual maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (b : Y ⟶ X) (c : Z ⟶ Y)
  (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
  (φ : M ⟶ (pushforward b).obj N) (ψ : N ⟶ (pushforward c).obj P) (n : ℕ)

/-- Original exterior coefficients compose through the original pushforward comparison. -/
theorem exteriorCoefficientMap_comp :
    exteriorCoefficientMap (c ≫ b)
      (φ ≫ (pushforward b).map ψ ≫ (pushforwardComp c b).hom.app P) n =
    exteriorCoefficientMap b φ n ≫ (pushforward b).map (exteriorCoefficientMap c ψ n) ≫
      (pushforwardComp c b).hom.app (moduleExteriorPower Z P n) := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X.sheaf M _ n
  intro V v
  have hleft := SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward (c ≫ b)).obj (moduleExteriorPower Z P n)) n
    (exteriorCoefficientAlternating (c ≫ b)
      (φ ≫ (pushforward b).map ψ ≫ (pushforwardComp c b).hom.app P) n) V v
  have hfirst := SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward b).obj (moduleExteriorPower Y N n)) n
    (exteriorCoefficientAlternating b φ n) V v
  have hsecond := SheafOfModulesOfCommRing.exteriorPowerDesc_mk Y.sheaf N
    ((pushforward c).obj (moduleExteriorPower Z P n)) n
    (exteriorCoefficientAlternating c ψ n) (op (b ⁻¹ᵁ V.unop))
    (fun i => φ.val.app V (v i))
  exact hleft.trans (hsecond.symm.trans
    (congrArg ((exteriorCoefficientMap c ψ n).val.app (op (b ⁻¹ᵁ V.unop))) hfirst).symm)

/-- An original target map commutes with the same exterior coefficient construction. -/
theorem exteriorCoefficientMap_postcomp {Q : Y.Modules} (χ : N ⟶ Q) :
    exteriorCoefficientMap b φ n ≫ (pushforward b).map
      ((moduleExteriorPowerFunctor Y n).map χ) =
    exteriorCoefficientMap b (φ ≫ (pushforward b).map χ) n := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X.sheaf M _ n
  intro V v
  have hfirst := SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward b).obj (moduleExteriorPower Y N n)) n
    (exteriorCoefficientAlternating b φ n) V v
  have hmap := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk Y.sheaf χ n
    (op (b ⁻¹ᵁ V.unop)) (fun i => φ.val.app V (v i))
  have hlast := SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward b).obj (moduleExteriorPower Y Q n)) n
    (exteriorCoefficientAlternating b (φ ≫ (pushforward b).map χ) n) V v
  exact (congrArg (((moduleExteriorPowerFunctor Y n).map χ).val.app
    (op (b ⁻¹ᵁ V.unop))) hfirst).trans (hmap.trans hlast.symm)

end AlgebraicGeometry.Scheme.Modules
