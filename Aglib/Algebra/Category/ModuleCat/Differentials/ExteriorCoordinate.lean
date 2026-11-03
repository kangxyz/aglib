/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.TopDegree
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf


/-!
# Algebra / Category / ModuleCat / Differentials / ExteriorCoordinate

Source: `IntegralTrace/ModelCoefficient.lean`.
Incoming SHA256: `c4cd5f6ebd4abe49f67b518559d5fc18671a7aabbc53c77e0c1fdf604a8ca2db`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory

universe u

namespace CommRingCat.KaehlerDifferential

variable {Λ A : CommRingCat.{u}} [IsDomain A] (ρ : Λ ⟶ A) (n : ℕ)
  (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential ρ))

omit [IsDomain A] in
/-- The fixed raw rank-one coordinate is the inverse of the original ordered
basis determinant, not a merely nonzero generic wedge. -/
def baseRawFormCoordinate : A ≃ₗ[A] (⋀[A]^n (CommRingCat.KaehlerDifferential ρ)) :=
  b.exteriorPowerTopEquiv.symm
omit [IsDomain A] in
/-- This same raw coordinate is normalized by the original ordered basis wedge. -/
theorem baseRawFormCoordinate_apply (r : A) :
    baseRawFormCoordinate ρ n b r = r • exteriorPower.ιMulti A n b :=
  b.exteriorPowerTopEquiv_symm_apply r

end CommRingCat.KaehlerDifferential
