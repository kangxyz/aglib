/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward


/-!
# Original exterior coefficients and open restriction

Taking exterior coefficients of an original restriction adjoint agrees with
the original exterior restriction comparison. The equality is checked on
actual wedges and their original section restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) (N : U.Modules) (ψ : M.restrict j ⟶ N) (n : ℕ)

/-- Exterior descent retains the original restriction adjoint and wedge arrows. -/
theorem exteriorCoefficientMap_restrictAdjoint :
    exteriorCoefficientMap j ((restrictAdjunction j).homEquiv M N ψ) n =
    (restrictAdjunction j).homEquiv _ _
      ((moduleExteriorPowerRestrictionIso j M n).inv ≫
        (moduleExteriorPowerFunctor U n).map ψ) := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X.sheaf M _ n
  intro V v
  let W := V.unop
  let p : j ''ᵁ (j ⁻¹ᵁ W) ⟶ W := homOfLE (j.image_preimage_le W)
  let w : Fin n → (M.restrict j).val.obj (op (j ⁻¹ᵁ W)) :=
    fun i => M.val.map p.op (v i)
  have hr := wedgeAt_naturality X M n p v
  have hi := moduleExteriorPowerRestrictionIso_inv_mk j M n (j ⁻¹ᵁ W) w
  have hm := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk U.sheaf ψ n
    (op (j ⁻¹ᵁ W)) w
  have hd := SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf M
    ((pushforward j).obj (moduleExteriorPower U N n)) n
    (exteriorCoefficientAlternating j ((restrictAdjunction j).homEquiv M N ψ) n) V v
  have hu := congrArg (fun t => t.val.app V
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app V v))
    (Adjunction.homEquiv_unit (restrictAdjunction j) _ _
      ((moduleExteriorPowerRestrictionIso j M n).inv ≫
        (moduleExteriorPowerFunctor U n).map ψ))
  refine hd.trans (Eq.trans ?_ hu.symm)
  change (SheafOfModulesOfCommRing.exteriorPowerMk U.sheaf N n).app (op (j ⁻¹ᵁ W))
      (fun i => ψ.val.app (op (j ⁻¹ᵁ W)) (w i)) =
    ((moduleExteriorPowerFunctor U n).map ψ).val.app (op (j ⁻¹ᵁ W))
      ((moduleExteriorPowerRestrictionIso j M n).inv.val.app (op (j ⁻¹ᵁ W))
        ((moduleExteriorPower X M n).val.map p.op
          ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app V v)))
  exact (hm.symm.trans (congrArg
    (((moduleExteriorPowerFunctor U n).map ψ).val.app (op (j ⁻¹ᵁ W))) hi.symm)).trans
      (congrArg (fun z => ((moduleExteriorPowerFunctor U n).map ψ).val.app
        (op (j ⁻¹ᵁ W)) ((moduleExteriorPowerRestrictionIso j M n).inv.val.app
          (op (j ⁻¹ᵁ W)) z)) hr.symm)

end AlgebraicGeometry.Scheme.Modules
