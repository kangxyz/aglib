/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.LocalTarget
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Ideal-residue compatibility for an actual local target

The native residue field at the maximal ideal is canonically the quotient
residue field of the local ring. This comparison identifies the residue map
from the selected prime localization with the original ideal-residue map.
-/

@[expose] public noncomputable section

universe u v

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The residue field at the actual maximal ideal agrees with the original
quotient residue field, via the native localization-quotient equivalence. -/
def residueFieldAtMaximalEquiv : (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (maximalIdeal R)
    (Localization.AtPrime (maximalIdeal R))).symm

@[simp] theorem residueFieldAtMaximalEquiv_algebraMap (r : R) :
    residueFieldAtMaximalEquiv R
      (algebraMap R (maximalIdeal R).ResidueField r) = residue R r := by
  apply (IsLocalization.AtPrime.equivQuotMaximalIdeal (maximalIdeal R)
    (Localization.AtPrime (maximalIdeal R))).symm_apply_eq.mpr
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk (maximalIdeal R)
    (Localization.AtPrime (maximalIdeal R)) r).symm

end IsLocalRing

namespace Localization.AtLocalTarget

open IsLocalRing

variable {B : Type u} {R : Type v} [CommRing B] [CommRing R] [IsLocalRing R]
  (f : B →+* R)

/-- The residue map of the actual local lift agrees with the original
ideal-residue map followed by the canonical target residue equivalence. -/
theorem residueMap_eq_idealResidueMap :
    ResidueField.map (map f) =
      (residueFieldAtMaximalEquiv R).toRingHom.comp
        (Ideal.ResidueField.map (prime f) (maximalIdeal R) f rfl) := by
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro b
  change ResidueField.map (map f) (algebraMap B (prime f).ResidueField b) =
    residueFieldAtMaximalEquiv R
      (Ideal.ResidueField.map (prime f) (maximalIdeal R) f rfl
        (algebraMap B (prime f).ResidueField b))
  rw [Ideal.ResidueField.map_algebraMap, residueFieldAtMaximalEquiv_algebraMap]
  change residue R (map f (algebraMap B (Ring f) b)) = residue R (f b)
  rw [map_algebraMap]

end Localization.AtLocalTarget
