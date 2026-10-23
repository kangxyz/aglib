/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! # Original multiplicative coefficients and global units

The original small-etale Gm presheaf is the restriction of the native global
units functor, with its canonical additive spelling and value-universe lift.
The comparison preserves literal restrictions, so it can be used with actual
product-nerve and affine Amitsur comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Group.MultiplicativeGroup

namespace GroupCohomology.Kummer.Coefficients

universe u

/-- Native global units with the original small-etale coefficient value universe. -/
def globalUnitCoefficients : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  globalUnitsFunctor ⋙ CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Gm presheaf is the restriction of native global units. -/
def gmGlobalUnitsIso (X : Scheme.{u}) :
    (gm X).obj ≅ (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ globalUnitCoefficients :=
  NatIso.ofComponents
    (fun U => ((unitsSections X U).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro U V f
      ext a
      apply ULift.ext
      exact unitsSections_naturality X f a)

end GroupCohomology.Kummer.Coefficients
