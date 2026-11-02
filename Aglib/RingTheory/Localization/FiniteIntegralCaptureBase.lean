/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.FiniteIntegralCaptureAway
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The actual finite surjective coefficient base change

Localizing an actual finite base subalgebra at the same original denominator
gives the original finite map from the localized base. Its injection follows
from the given base-to-field injection. Integral lying over then gives a
surjective map on prime spectra; no extra flatness or rank premise is needed.
-/

@[expose] public noncomputable section

namespace IsFractionRing

universe u v

variable {R : Type u} [CommRing R] {L : Type v} [Field L] [Algebra R L]

/-- The original map between the two principal localizations. -/
def finiteSubalgebraAwayBaseMap (B : Subalgebra R L) (r : R) :
    Localization.Away r →ₐ[R] Localization.Away (algebraMap R B r) := by
  letI : IsLocalization.Away ((Algebra.ofId R B) r)
      (Localization.Away (algebraMap R B r)) := by
    rw [Algebra.ofId_apply]
    infer_instance
  exact IsLocalization.Away.mapₐ _ _ (Algebra.ofId R B) r

/-- Module finiteness survives the original principal localization. -/
theorem finiteSubalgebraAwayBaseMap_finite (B : Subalgebra R L) [Module.Finite R B]
    (r : R) : (finiteSubalgebraAwayBaseMap B r).toRingHom.Finite := by
  let : Algebra (Localization.Away r) (Localization.Away (algebraMap R B r)) :=
    (finiteSubalgebraAwayBaseMap B r).toRingHom.toAlgebra
  have : IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap R B r)) :=
    IsScalarTower.of_algebraMap_eq fun x => (finiteSubalgebraAwayBaseMap B r).commutes x |>.symm
  change Module.Finite (Localization.Away r) (Localization.Away (algebraMap R B r))
  exact Module.Finite.of_isLocalization R B (Submonoid.powers r)

/-- The localized base map is injective when the original base embeds in the
ambient field. This concerns the original base map, not arbitrary tensors. -/
theorem finiteSubalgebraAwayBaseMap_injective (B : Subalgebra R L) (r : R)
    (hR : Function.Injective (algebraMap R L)) :
    Function.Injective (finiteSubalgebraAwayBaseMap B r) := by
  have : IsLocalization.Away ((Algebra.ofId R B) r)
      (Localization.Away (algebraMap R B r)) := by
    rw [Algebra.ofId_apply]
    infer_instance
  exact IsLocalization.Away.mapₐ_injective_of_injective (f := Algebra.ofId R B) r
    (fun x y h => hR (congrArg B.val h))

/-- Integral lying over supplies the actual surjective map on spectra. -/
theorem finiteSubalgebraAwayBaseMap_comap_surjective (B : Subalgebra R L)
    [Module.Finite R B] (r : R) (hR : Function.Injective (algebraMap R L)) :
    Function.Surjective (PrimeSpectrum.comap (finiteSubalgebraAwayBaseMap B r).toRingHom) := by
  let : Algebra (Localization.Away r) (Localization.Away (algebraMap R B r)) :=
    (finiteSubalgebraAwayBaseMap B r).toRingHom.toAlgebra
  have : Module.Finite (Localization.Away r) (Localization.Away (algebraMap R B r)) :=
    finiteSubalgebraAwayBaseMap_finite B r
  have : FaithfulSMul (Localization.Away r) (Localization.Away (algebraMap R B r)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (finiteSubalgebraAwayBaseMap_injective B r hR)
  exact Algebra.IsIntegral.comap_surjective _ _

end IsFractionRing
