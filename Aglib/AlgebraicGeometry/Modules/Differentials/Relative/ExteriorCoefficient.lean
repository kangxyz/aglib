/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map


/-!
# Original exterior coefficient maps for integral trace

The raw exterior coefficient sends original differential wedges to original
pulled-back differential wedges. Its bidual coefficient uses the actual
bidual evaluation. Neither a determinant pullback isomorphism nor a
one-pole comparison is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ X) (n : ℕ)

/-- The actual raw-form coefficient map, retaining the original relative differentials. -/
def rawFormsCoefficient :
    moduleExteriorPower X (relativeDifferentialSheaf f) n ⟶
      (pushforward b).obj (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n) :=
  exteriorCoefficientMap b (differentialCoefficient f b) n

/-- The raw-form pullback is the original adjoint of the same exterior coefficient map. -/
def rawFormsPullback :
    (pullback b).obj (moduleExteriorPower X (relativeDifferentialSheaf f) n) ⟶
      moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n :=
  ((pullbackPushforwardAdjunction b).homEquiv _ _).symm (rawFormsCoefficient f b n)

/-- Original raw-form wedges retain their original sectionwise coefficient values. -/
theorem rawFormsCoefficient_wedge (U : X.Opens)
    (v : Fin n → (relativeDifferentialSheaf f).val.obj (op U)) :
    (rawFormsCoefficient f b n).val.app (op U)
      (wedgeAt X (relativeDifferentialSheaf f) n U v) =
        wedgeAt Y (relativeDifferentialSheaf (b ≫ f)) n (b ⁻¹ᵁ U)
          (fun i => (differentialCoefficient f b).val.app (op U) (v i)) :=
  SheafOfModulesOfCommRing.exteriorPowerDesc_mk X.sheaf
    (relativeDifferentialSheaf f) _ n
    (exteriorCoefficientAlternating b (differentialCoefficient f b) n) (op U) v

/-- The exterior coefficient followed by the original bidual evaluation. -/
def bidualFormsCoefficient :
    moduleExteriorPower X (relativeDifferentialSheaf f) n ⟶
      (pushforward b).obj (Invertible.dualSheaf Y (Invertible.dualSheaf Y
        (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n))) :=
  rawFormsCoefficient f b n ≫ (pushforward b).map
    (Invertible.bidualMap Y (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n))

/-- The raw-form adjunction preserves the chosen original coefficient arrow exactly. -/
theorem rawFormsPullback_adjoint :
    (pullbackPushforwardAdjunction b).homEquiv _ _ (rawFormsPullback f b n) =
      rawFormsCoefficient f b n :=
  Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Scheme.Modules.Differentials
