/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.HenselianUniformizerNormalization
public import Aglib.RingTheory.DVRRamificationDegree
public import Aglib.RingTheory.DVRUniformizerBinomial
public import Aglib.RingTheory.DVRNormResidueUnit

/-!
# Exact normalized uniformizer norms in residue degree one

Hensel lifting adjusts the extension uniformizer by a residue-one unit. The
adjusted uniformizer satisfies an Eisenstein binomial of the actual field
degree. Its determinant norm gives the exact sign. Returning to the original
uniformizer uses the actual unit-norm reduction formula, not cancellation of
powers in a residue field.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsDiscreteValuationRing

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]

include F E

/-- In actual residue degree one, the normalized integral norm of the original
uniformizer has the exact residue sign and inverse ramification-unit norm.
Invertibility of the exponent in the henselian extension ring is explicit. -/
theorem exists_uniformizer_norm_coefficient_of_residue_finrank_one
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S))
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have hdegree : Module.finrank F E = e := by
    simpa only [hf, mul_one] using
      finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u e he
  have hepos : 0 < e := hdegree ▸ Module.finrank_pos (R := F) (M := E)
  obtain ⟨a, v, hv, _, hθeq⟩ :=
    HenselianLocalRing.exists_principal_adjusted_uniformizer_of_residue_finrank_one
      R S hf hϖ u e hepos heunit he
  have hθ : ((v : S) * ϖ) ^ e = algebraMap R S (π * ((a⁻¹ : Rˣ) : R)) := by
    rw [map_mul, hθeq, mul_right_comm, ← map_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, map_one, one_mul]
  have hc : Irreducible (π * ((a⁻¹ : Rˣ) : R)) :=
    (irreducible_mul_units a⁻¹).mpr hπ
  have hroot : (algebraMap S E ((v : S) * ϖ)) ^ e =
      algebraMap F E (algebraMap R F (π * ((a⁻¹ : Rˣ) : R))) := by
    rw [← map_pow, hθ, ← IsScalarTower.algebraMap_apply R S E,
      ← IsScalarTower.algebraMap_apply R F E]
  have hnorm := norm_uniformizer_binomial_root F hc e hepos hdegree
    (algebraMap S E ((v : S) * ϖ)) hroot
  have hnormR : Algebra.intNorm R S ((v : S) * ϖ) =
      (-1 : R) ^ (e - 1) * (π * ((a⁻¹ : Rˣ) : R)) := by
    apply IsFractionRing.injective R F
    rw [Algebra.algebraMap_intNorm (K := F) (L := E), hnorm]
    simp only [map_mul, map_pow, map_neg, map_one]
  let t : Rˣ := Units.map (Algebra.intNorm R S) v
  have hnormR' : (t : R) * Algebra.intNorm R S ϖ =
      (-1 : R) ^ (e - 1) * (π * ((a⁻¹ : Rˣ) : R)) := by
    simpa only [map_mul, Units.coe_map, t] using hnormR
  let b : Rˣ := (-1) ^ (e - 1) * a⁻¹ * t⁻¹
  refine ⟨b, ?_, ?_⟩
  · calc
      Algebra.intNorm R S ϖ = ((t⁻¹ : Rˣ) : R) *
          ((t : R) * Algebra.intNorm R S ϖ) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = π * (b : R) := by
        rw [hnormR']
        dsimp only [b]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        ring
  · have hvunit : Units.map (residue S).toMonoidHom v = 1 := Units.ext hv
    have htres : Units.map (residue R).toMonoidHom t = 1 := by
      dsimp only [t]
      rw [Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he v,
        hvunit, map_one, one_pow]
    have hua : residue S (u : S) = residue S (algebraMap R S (a : R)) := by
      have hu : Units.map (algebraMap R S).toMonoidHom a * v ^ e = u := by
        apply Units.ext
        apply (mul_right_cancel₀ (pow_ne_zero e hϖ.ne_zero))
        change algebraMap R S (a : R) * (v : S) ^ e * ϖ ^ e = (u : S) * ϖ ^ e
        rw [← he, hθeq, mul_pow, mul_assoc]
      have huval := congrArg Units.val hu
      change algebraMap R S (a : R) * (v : S) ^ e = (u : S) at huval
      rw [← huval, map_mul, map_pow, hv, one_pow, mul_one]
    have hnorma : Algebra.norm (ResidueField R) (residue S (u : S)) =
        residue R (a : R) := by
      rw [hua]
      change Algebra.norm (ResidueField R)
        (algebraMap (ResidueField R) (ResidueField S) (residue R (a : R))) = _
      rw [Algebra.norm_algebraMap, hf, pow_one]
    rw [hnorma]
    change ((Units.map (residue R).toMonoidHom b : (ResidueField R)ˣ) : ResidueField R) = _
    simp only [b, map_mul, map_pow, map_inv, htres, inv_one, mul_one,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map]
    simp

end IsDiscreteValuationRing
