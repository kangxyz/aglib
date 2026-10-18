/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Basic
public import Aglib.RingTheory.DVRRamificationDegree

/-!
# Degree annihilation from ramified residue restriction

The actual finite DVR degree formula and proved norm projection convert a
ramification-weighted restriction kernel into a fraction-field degree
annihilator. The finite integral-closure hypotheses remain explicit.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

/-- A ramification-weighted residue restriction is detected up to the actual
fraction-field extension degree, not merely the residue degree. -/
theorem degree_smul_eq_zero_of_ramified_residue_restrict
    (R S F E : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
    [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E] [FiniteDimensional F E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (n : ℕ) (z : K (ResidueField R) n)
    (hz : e • map n (algebraMap (ResidueField R) (ResidueField S)) z = 0) :
    Module.finrank F E • z = 0 := by
  have h := congrArg (finiteExtensionNorm (ResidueField R) (ResidueField S) n) hz
  rw [map_nsmul, finiteExtensionNorm_map_constants, map_zero, natCast_zsmul,
    smul_smul] at h
  rw [IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he]
  exact h

end MilnorK
