/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.LocalTarget
public import Aglib.RingTheory.Henselian.HenselizationResidue

/-!
# Residue compatibility for the selected local henselization

The map on residue fields of the selected henselization agrees, through the
canonical henselization residue equivalence, with the original local map
from the prime localization to the target.
-/

@[expose] public noncomputable section

universe u v

namespace Henselization.AtLocalTarget

open IsLocalRing

variable {B : Type u} {R : Type v} [CommRing B] [CommRing R]
  [HenselianLocalRing R] (f : B →+* R)

/-- The two actual maps from the residue field of the selected prime
localization to the target residue field coincide. -/
theorem residueMap_comp_residueEquiv_symm :
    (ResidueField.map (map f)).comp
        (Henselization.residueEquiv (Localization.AtLocalTarget.Ring f)).symm.toRingHom =
      ResidueField.map (Localization.AtLocalTarget.map f) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective
    (R := Localization.AtLocalTarget.Ring f) x
  change ResidueField.map (map f)
      ((Henselization.residueEquiv (Localization.AtLocalTarget.Ring f)).symm
        (IsLocalRing.residue (Localization.AtLocalTarget.Ring f) a)) =
    ResidueField.map (Localization.AtLocalTarget.map f)
      (IsLocalRing.residue (Localization.AtLocalTarget.Ring f) a)
  rw [Henselization.residueEquiv_symm_residue, ResidueField.map_residue,
    ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue R) (RingHom.congr_fun (map_comp_algebraMap f) a)

/-- The actual target residue map factors through the original residue
field of the prime localization via its canonical henselization equivalence. -/
theorem residueMap_eq_comp_residueEquiv :
    ResidueField.map (map f) =
      (ResidueField.map (Localization.AtLocalTarget.map f)).comp
        (Henselization.residueEquiv (Localization.AtLocalTarget.Ring f)).toRingHom := by
  apply RingHom.ext
  intro x
  have h := RingHom.congr_fun (residueMap_comp_residueEquiv_symm f)
    (Henselization.residueEquiv (Localization.AtLocalTarget.Ring f) x)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using h

end Henselization.AtLocalTarget
