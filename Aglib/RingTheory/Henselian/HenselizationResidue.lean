/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationLocalRing

/-!
# The original residue field of the actual henselization

The constructed residue map induces the canonical equivalence of residue
fields. Its inverse is exactly the residue map of the henselization unit,
not an unspecified field isomorphism.
-/

@[expose] public noncomputable section

universe u

namespace Henselization

open IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The canonical residue-field equivalence induced by the original residue
map of the constructed henselization. -/
def residueEquiv : ResidueField (Henselization R) ≃+* ResidueField R :=
  RingEquiv.ofBijective (ResidueField.lift (residue R).toRingHom)
    ⟨RingHom.injective _, fun x => by
      obtain ⟨a, ha⟩ := residue_surjective R x
      exact ⟨IsLocalRing.residue (Henselization R) a, ha⟩⟩

@[simp] theorem residueEquiv_residue (x : Henselization R) :
    residueEquiv R (IsLocalRing.residue (Henselization R) x) = residue R x := rfl

@[simp] theorem residueEquiv_residue_algebraMap (r : R) :
    residueEquiv R (IsLocalRing.residue (Henselization R)
      (algebraMap R (Henselization R) r)) = IsLocalRing.residue R r :=
  RingHom.congr_fun (residue_comp_of R) r

@[simp] theorem residueEquiv_symm_residue (r : R) :
    (residueEquiv R).symm (IsLocalRing.residue R r) =
      IsLocalRing.residue (Henselization R) (algebraMap R (Henselization R) r) := by
  apply (residueEquiv R).injective
  simp

/-- The inverse residue equivalence is the map of residue fields induced
by the actual henselization unit. -/
theorem residueEquiv_symm_toRingHom :
    (residueEquiv R).symm.toRingHom =
      ResidueField.map (algebraMap R (Henselization R)) := by
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
  exact residueEquiv_symm_residue R r

end Henselization
