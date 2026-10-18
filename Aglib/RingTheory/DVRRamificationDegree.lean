/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRNormValuation

/-!
# Degree from an actual DVR uniformizer equation

The ordinary norm-order theorem, evaluated on the image of a base
uniformizer, identifies the product of the literal ramification exponent and
residue degree with the actual finite field degree. In prime degree this
forces ramification exponent one or residue degree one.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing.NormValuation

namespace IsDiscreteValuationRing

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]

/-- The degree formula uses the actual exponent in the supplied uniformizer
equation, rather than an independent or assumed ramification index. -/
theorem finrank_eq_ramification_mul_residue_finrank
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.finrank F E = e * Module.finrank (ResidueField R) (ResidueField S) := by
  let a := uniformizerUnit R F hπ
  have ha : Units.map (algebraMap F E).toMonoidHom a =
      Units.map (algebraMap S E).toMonoidHom u * uniformizerUnit S E hϖ ^ e := by
    apply Units.ext
    change algebraMap F E (algebraMap R F π) =
      algebraMap S E (u : S) * algebraMap S E ϖ ^ e
    rw [← IsScalarTower.algebraMap_apply R F E,
      IsScalarTower.algebraMap_apply R S E, he, map_mul, map_pow]
  have hn : Units.map (Algebra.norm F) (Units.map (algebraMap F E).toMonoidHom a) =
      a ^ Module.finrank F E := by
    apply Units.ext
    exact Algebra.norm_algebraMap (R := F) (S := E) (a : F)
  have hv := order_norm R S F E (Units.map (algebraMap F E).toMonoidHom a)
  rw [hn, ha] at hv
  have hpowR := order_zpow R F a (Module.finrank F E : ℤ)
  have hpowS := order_zpow S E (uniformizerUnit S E hϖ) (e : ℤ)
  have haorder : order R F a = 1 := order_uniformizer R F hπ
  simp only [zpow_natCast, haorder, mul_one] at hpowR
  simp only [zpow_natCast, order_uniformizer, mul_one] at hpowS
  rw [hpowR, order_mul, order_ringUnit, hpowS, zero_add, mul_comm] at hv
  exact_mod_cast hv

/-- In actual prime field degree, either the literal ramification exponent or
the actual residue-field degree is one. -/
theorem ramification_eq_one_or_residue_finrank_eq_one
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (hp : Nat.Prime (Module.finrank F E)) :
    e = 1 ∨ Module.finrank (ResidueField R) (ResidueField S) = 1 := by
  have hd := finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u e he
  rw [hd] at hp
  exact (Nat.prime_mul_iff.mp hp).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

end IsDiscreteValuationRing
