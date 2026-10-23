/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine

/-!
# Original multiplicative H1 over semilocal rings

The native affine Picard equivalence and semilocal algebraic Picard triviality
imply vanishing of the original multiplicative H1, with an independent Ext universe.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w

/-- Original H1 of the multiplicative sheaf vanishes on a semilocal spectrum. -/
instance gmH1_subsingleton_of_finite_maximalSpectrum (R : CommRingCat.{u})
    [Finite (MaximalSpectrum R)]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))] :
    Subsingleton (Sheaf.H.{w} (gm (Spec R)) 1) := by
  let : Subsingleton (Modules.Invertible.PicardGroup (Spec R)) :=
    (Modules.Invertible.picardGroupEquivCommRingPic R).injective.subsingleton
  exact (picardCohomologyEquiv (Spec R)).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
