/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / BaseForms

Source: `IntegralTrace/ModelCoefficient.lean`.
Incoming SHA256: `c4cd5f6ebd4abe49f67b518559d5fc18671a7aabbc53c77e0c1fdf604a8ca2db`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- Original raw forms over the affine base, before any model or chosen basis. -/
def baseRawFormsIso {Λ A : CommRingCat.{u}} (ρ : Λ ⟶ A) (n : ℕ) :
    moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map ρ)) n ≅
      tilde (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential ρ))) :=
  (moduleExteriorPowerFunctor (Spec A) n).mapIso (relativeDifferentialAffineIso ρ) ≪≫
    exteriorTildeIso (CommRingCat.KaehlerDifferential ρ) n

end AlgebraicGeometry.Scheme.Modules.Differentials
