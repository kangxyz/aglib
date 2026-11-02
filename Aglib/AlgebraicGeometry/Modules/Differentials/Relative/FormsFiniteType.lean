/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FiniteType
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / FormsFiniteType

Source: `IntegralTrace/DifferentialMaps.lean`.
Incoming SHA256: `fea917fb14f28e58858299fb92d2f21d04ae30b21a496ec4baeb75038f6d55ba`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ X)

/-- Raw relative forms are coherent under the actual finite-type hypothesis. -/
theorem rawForms_affineLocallyFiniteType
    {Λ : CommRingCat.{u}} (a : X ⟶ Spec Λ) [LocallyOfFiniteType a] (n : ℕ) :
    affineLocallyFiniteType X (moduleExteriorPower X (relativeDifferentialSheaf a) n) :=
  moduleExteriorPower_affineLocallyFiniteType _
    (relativeDifferentialSheaf_affineLocallyFiniteType a) n
/-- The actual bidual coefficient is coherent on a locally Noetherian model. -/
theorem bidualForms_affineLocallyFiniteType [IsLocallyNoetherian X]
    {Λ : CommRingCat.{u}} (a : X ⟶ Spec Λ) [LocallyOfFiniteType a] (n : ℕ) :
    affineLocallyFiniteType X
      (Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n))) :=
  affineLocallyFiniteType_bidualSheaf _ (rawForms_affineLocallyFiniteType a n)

end AlgebraicGeometry.Scheme.Modules.Differentials
