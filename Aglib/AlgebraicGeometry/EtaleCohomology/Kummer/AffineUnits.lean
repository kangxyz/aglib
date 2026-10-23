/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GlobalUnits

/-! # Affine global-unit coefficients

Whiskering the native Spec/global-sections natural isomorphism identifies the
original global-unit coefficient functor on affine schemes with actual ring
units, including every algebra map and the original value-universe lift.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group.MultiplicativeGroup

namespace GroupCohomology.Kummer.Coefficients

universe u

/-- Actual ring units with the original small-etale value universe. -/
def ringUnitCoefficients : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  unitsFunctor ⋙ CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The affine comparison is the native Spec/global-sections counit on units. -/
def affineGlobalUnitsIso :
    Scheme.Spec.rightOp ⋙ globalUnitCoefficients ≅ ringUnitCoefficients :=
  Functor.isoWhiskerRight Scheme.SpecΓIdentity ringUnitCoefficients

end GroupCohomology.Kummer.Coefficients
