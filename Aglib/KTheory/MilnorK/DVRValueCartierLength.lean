/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DVR.Basic
public import Aglib.RingTheory.DVRCartierLength

/-! # Milnor integer order equals actual Cartier multiplicity -/

@[expose] public noncomputable section
namespace MilnorK.K2.DVR

variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra R E] [IsFractionRing R E]

/-- The integer valuation used by Milnor residues is the actual nonnegative
DVR order of every nonzero ring element, without a chosen-order hypothesis. -/
theorem value_ringElement_eq_addVal (t : R) (ht : t ≠ 0) :
    value R E (Additive.ofMul
      (Units.mk0 (algebraMap R E t)
        ((map_ne_zero_iff (algebraMap R E) (IsFractionRing.injective R E)).mpr ht))) =
        ((IsDiscreteValuationRing.addVal R t).toNat : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hπ
  have he : Units.mk0 (algebraMap R E t)
      ((map_ne_zero_iff (algebraMap R E) (IsFractionRing.injective R E)).mpr ht) =
      fieldUnits R E u * uniformizer (K := E) hπ ^ n := by
    apply Units.ext
    change algebraMap R E t = algebraMap R E (u : R) * (algebraMap R E π) ^ n
    rw [hu, map_mul, map_pow]
  rw [he, ofMul_mul, map_add, ofMul_pow, map_nsmul,
    value_fieldUnits, value_uniformizer, zero_add, nsmul_eq_mul, mul_one,
    hu, IsDiscreteValuationRing.addVal_def' u hπ]
  simp

/-- Actual Cartier quotient length, including multiplicity, is exactly the
integer coefficient occurring in the tame residue of a last parameter. -/
theorem value_ringElement_eq_cartierLength (t : R) (ht : t ≠ 0) :
    value R E (Additive.ofMul
      (Units.mk0 (algebraMap R E t)
        ((map_ne_zero_iff (algebraMap R E) (IsFractionRing.injective R E)).mpr ht))) =
        ((Module.length R (R ⧸ Ideal.ofList [t])).toNat : ℤ) := by
  rw [IsDiscreteValuationRing.length_quotient_ofList_eq_addVal t ht]
  exact value_ringElement_eq_addVal R E t ht

end MilnorK.K2.DVR
