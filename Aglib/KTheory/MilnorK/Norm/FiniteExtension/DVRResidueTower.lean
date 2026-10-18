/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower
public import Aglib.KTheory.MilnorK.Residue.DVR
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Composition of actual DVR norm-residue squares

This induction step retains both lower and upper square hypotheses explicitly.
The fraction-field and residue-field towers use their literal algebra maps.
No completeness, unramifiedness, or implicit residue compatibility is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

universe u v

/-- Two proved local norm-residue squares compose by the actual field and
residue-field norm towers, with no restriction on ramification. -/
theorem residue_finiteExtensionNorm_of_tower
    (R S T : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [IsLocalHom (algebraMap R T)]
    [CharZero (ResidueField R)] [CharZero (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField S) (ResidueField T)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    (F E L : Type u) [Field F] [CharZero F] [Field E] [CharZero E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    [Algebra T L] [IsFractionRing T L]
    (n : ℕ)
    (lower : ∀ y : K E (n + 1),
      DVR.residue R F n (finiteExtensionNorm F E (n + 1) y) =
        finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n y))
    (upper : ∀ z : K L (n + 1),
      DVR.residue S E n (finiteExtensionNorm E L (n + 1) z) =
        finiteExtensionNorm (ResidueField S) (ResidueField T) n (DVR.residue T L n z))
    (x : K L (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F L (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField T) n (DVR.residue T L n x) := by
  rw [finiteExtensionNorm_tower E L (n + 1), lower, upper,
    ← finiteExtensionNorm_tower (ResidueField S) (ResidueField T) n]

end MilnorK
