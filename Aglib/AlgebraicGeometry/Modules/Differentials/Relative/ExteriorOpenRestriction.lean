/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / ExteriorOpenRestriction

Source: `IntegralTrace/RawFormsOpenRestriction.lean`.
Incoming SHA256: `aa7df6ace0004643fe1b5c990839bc85b5932960760afba9ecf88716442284b0`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X U : Scheme.{u}} {Λ : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

/-- The raw comparison uses the original differential and exterior restriction maps. -/
def rawFormsOpenIso :
    (moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j ≅
      moduleExteriorPower U (relativeDifferentialSheaf (j ≫ a)) n :=
  (moduleExteriorPowerRestrictionIso j (relativeDifferentialSheaf a) n).symm ≪≫
    (moduleExteriorPowerFunctor U n).mapIso (relativeDifferentialRestrictIso a j)

end AlgebraicGeometry.Scheme.Modules.Differentials
