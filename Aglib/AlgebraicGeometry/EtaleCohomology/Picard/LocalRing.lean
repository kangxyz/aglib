/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing

/-!
# Original multiplicative H1 over local rings

The original Picard/cohomology equivalence transfers the native triviality of
line bundles on a local spectrum. In particular this applies to every field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w

/-- Original H1 of the multiplicative sheaf vanishes on every local spectrum. -/
instance gmH1_subsingleton_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))] :
    Subsingleton (Sheaf.H.{w} (gm (Spec R)) 1) :=
  (picardCohomologyEquiv (Spec R)).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
