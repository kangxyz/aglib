/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# Original differential values of the bidual coefficient map

The original exterior coefficient followed by actual bidual evaluation sends
a wedge of original differentials to the evaluated wedge of the original
pulled-back differentials. This fixes the raw coefficient normalization
before constructing any canonical transpose or trace.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The exact original raw differential-wedge formula for the bidual coefficient. -/
theorem bidualFormsCoefficient_wedge_d
    {X Y S : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ X) (n : ℕ)
    (U : X.Opens) (a : Fin n → Γ(X, U)) :
    (bidualFormsCoefficient f b n).val.app (op U)
      (wedgeAt X (relativeDifferentialSheaf f) n U
        (fun i => (relativeDifferentialDerivation f).d (a i))) =
      (Invertible.bidualMap Y
        (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n)).val.app
          (op (b ⁻¹ᵁ U))
            (wedgeAt Y (relativeDifferentialSheaf (b ≫ f)) n (b ⁻¹ᵁ U)
              (fun i => (relativeDifferentialDerivation (b ≫ f)).d (b.app U (a i)))) := by
  change (Invertible.bidualMap Y
    (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ f)) n)).val.app
      (op (b ⁻¹ᵁ U)) ((rawFormsCoefficient f b n).val.app (op U) _) = _
  rw [rawFormsCoefficient_wedge]
  congr 2
  funext i
  exact differentialCoefficient_d f b U (a i)

end AlgebraicGeometry.Scheme.Modules.Differentials
