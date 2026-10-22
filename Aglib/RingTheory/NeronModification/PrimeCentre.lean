/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.LocalizedCentre
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # The actual centre in the native localized target

The target is literally `Localization.AtPrime I`, and the point is the native
localization of the original global map. Its actual residue kernel equals the
extension of the global centre. No separately supplied residue comparison or
kernel equality is required.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

variable {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
variable (S : Submonoid B) [Algebra B D] [IsLocalization S D]
variable (I : Ideal C) [I.IsPrime] (f : B →+* C)
variable (hS : S ≤ I.primeCompl.comap f)

/-- The actual point on the source localization with values in the native target localization. -/
def localizedPointAtPrime : D →+* Localization.AtPrime I :=
  IsLocalization.map (Localization.AtPrime I) f hS

@[simp] theorem localizedPointAtPrime_algebraMap (b : B) :
    localizedPointAtPrime (D := D) S I f hS (algebraMap B D b) =
      algebraMap C (Localization.AtPrime I) (f b) :=
  by simp only [localizedPointAtPrime, IsLocalization.map_eq]

include hS in
/-- The source denominators have nonzero actual target residues. -/
theorem localizedPointAtPrime_residue_units (s : S) :
    IsUnit (algebraMap C I.ResidueField (f s)) := by
  apply IsUnit.mk0
  intro hs
  exact hS s.property (Ideal.algebraMap_residueField_eq_zero.mp hs)

/-- The residue of the actual localized point is the localized original residue point. -/
theorem residue_comp_localizedPointAtPrime :
    (IsLocalRing.residue (Localization.AtPrime I)).comp
      (localizedPointAtPrime (D := D) S I f hS) =
    localizedResiduePoint S ((algebraMap C I.ResidueField).comp f)
      (RingHom.id I.ResidueField) (localizedPointAtPrime_residue_units S I f hS) := by
  apply IsLocalization.ringHom_ext S
  ext b
  change IsLocalRing.residue (Localization.AtPrime I)
    (localizedPointAtPrime S I f hS (algebraMap B D b)) = _
  rw [RingHom.comp_apply, localizedPointAtPrime_algebraMap,
    localizedResiduePoint_algebraMap]
  rfl

/-- The actual local residue kernel is exactly the extension of the actual global centre. -/
theorem ker_residue_localizedPointAtPrime :
    RingHom.ker ((IsLocalRing.residue (Localization.AtPrime I)).comp
      (localizedPointAtPrime (D := D) S I f hS)) =
      (I.comap f).map (algebraMap B D) := by
  rw [residue_comp_localizedPointAtPrime,
    ker_localizedResiduePoint S _ (RingHom.id I.ResidueField) _ Function.injective_id]
  rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]

/-- The same identity expressed using the literal global quotient-kernel centre. -/
theorem ker_residue_localizedPointAtPrime_eq_map_quotient_kernel :
    RingHom.ker ((IsLocalRing.residue (Localization.AtPrime I)).comp
      (localizedPointAtPrime (D := D) S I f hS)) =
      (RingHom.ker ((Ideal.Quotient.mk I).comp f)).map (algebraMap B D) := by
  rw [ker_residue_localizedPointAtPrime, ← RingHom.comap_ker, Ideal.mk_ker]

end Algebra.NeronModification
