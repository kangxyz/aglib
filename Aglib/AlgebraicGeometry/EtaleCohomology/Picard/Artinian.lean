/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.Semilocal
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Original multiplicative H1 of an Artinian scheme

The actual Artinian scheme is affine with semilocal section ring. Native
Picard pullback along its affine isomorphism and the original Picard/H1
comparison give H1 triviality without discarding nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients
open Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe u w

/-- Original multiplicative H1 vanishes on every actual Artinian scheme. -/
instance gmH1_subsingleton_of_isArtinianScheme (X : Scheme.{u}) [IsArtinianScheme X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] :
    Subsingleton (Sheaf.H.{w} (gm X) 1) := by
  let e := X.isoSpec
  let : Subsingleton (PicardGroup (Spec Γ(X, ⊤))) :=
    (picardGroupEquivCommRingPic Γ(X, ⊤)).injective.subsingleton
  have h : Function.LeftInverse (pullbackClass e.hom) (pullbackClass e.inv) := by
    intro a
    rw [← pullbackClass_comp, e.hom_inv_id, pullbackClass_id]
  let : Subsingleton (PicardGroup X) := h.injective.subsingleton
  exact (picardCohomologyEquiv X).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
