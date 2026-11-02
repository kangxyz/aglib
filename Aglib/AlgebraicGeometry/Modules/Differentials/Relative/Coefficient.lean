/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / Coefficient

Source: `IntegralTrace/DifferentialMaps.lean`.
Incoming SHA256: `fea917fb14f28e58858299fb92d2f21d04ae30b21a496ec4baeb75038f6d55ba`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ X)

/-- The original relative derivation after the original structure-section pullback. -/
def differentialCoefficient :
    relativeDifferentialSheaf f ⟶
      (pushforward b).obj (relativeDifferentialSheaf (b ≫ f)) :=
  relativeDifferentialDesc f _
    (pushforwardRelativeDerivation f b _ (relativeDifferentialDerivation (b ≫ f)))
/-- The exact section formula retains both original differentials. -/
theorem differentialCoefficient_d (U : X.Opens) (a : Γ(X, U)) :
    (differentialCoefficient f b).val.app (op U)
      ((relativeDifferentialDerivation f).d a) =
        (relativeDifferentialDerivation (b ≫ f)).d (b.app U a) :=
  relativeDifferentialDesc_d f _ _ (op U) a
/-- The actual coefficient pullback is the original adjoint, not a selected isomorphism. -/
def differentialPullback :
    (pullback b).obj (relativeDifferentialSheaf f) ⟶
      relativeDifferentialSheaf (b ≫ f) :=
  ((pullbackPushforwardAdjunction b).homEquiv _ _).symm (differentialCoefficient f b)
/-- The original adjunction recovers the same sectionwise coefficient map. -/
theorem differentialPullback_adjoint :
    (pullbackPushforwardAdjunction b).homEquiv _ _ (differentialPullback f b) =
      differentialCoefficient f b :=
  Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Scheme.Modules.Differentials
