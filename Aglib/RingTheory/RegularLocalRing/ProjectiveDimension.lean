/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.RegularSequence
public import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Projective dimension of the residue field of a regular local ring

The regular system of parameters supplies the native regular-sequence
projective-dimension formula. In particular, no finite-resolution or
projective-dimension assumption is imposed on the residue field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory IsLocalRing

namespace IsRegularLocalRing

/-- The projective dimension of the residue field equals the dimension of its regular local ring. -/
theorem projectiveDimension_residueField_eq (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = ringKrullDim R := by
  let d := (maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : ℕ) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  obtain ⟨rs, hlen, hreg, hspan⟩ := exists_regular_sequence_maximalIdeal R d hd
  let e : Shrink.{u} (R ⧸ Ideal.ofList rs) ≃ₗ[R] ResidueField R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hspan)
  calc
    projectiveDimension (ModuleCat.of R (ResidueField R)) =
        projectiveDimension (ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs))) :=
      (ModuleCat.projectiveDimension_eq_of_linearEquiv e).symm
    _ = (rs.length : ℕ) := ModuleCat.projectiveDimension_quotient_eq_length rs hreg
    _ = ringKrullDim R := by rw [hlen, hd]

end IsRegularLocalRing
