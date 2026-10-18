/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRCharpolyResidue
public import Mathlib.Algebra.CharZero.Infinite
public import Lean.Util.CollectAxioms

/-! Actual integral and field multiplication characteristic-polynomial reduction. -/

@[expose] public noncomputable section

open IsLocalRing

namespace AglibTest.DVRCharpolyResidue

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
  [CharZero (ResidueField R)]

/-- The exponent includes the actual residual relative degree, not a supplied weight. -/
theorem actualMinimalPolynomialPower
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^
        (e * Module.finrank
          (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) :=
  Algebra.residue_charpoly_lmul_eq_minpoly_pow R S hπ hϖ u e he b

/-- A literal primitive residue generator removes only the relative-degree factor. -/
theorem actualPrimitiveResiduePower
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^ e :=
  Algebra.residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis R S hπ hϖ u e he b B hB

/-- The same integral polynomial gives both the original fraction-field
characteristic polynomial and its residue reduction. There is no field-to-residue map. -/
theorem originalFieldAndResidue
    (F E : Type*) [Field F] [Field E] [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [Algebra R E] [Algebra S E]
    [IsScalarTower R F E] [IsScalarTower R S E] [IsIntegralClosure S R E]
    [FiniteDimensional F E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (algebraMap R F) =
        (Algebra.lmul F E (algebraMap S E b)).charpoly ∧
      (Algebra.lmul R S b).charpoly.map (residue R) =
        (minpoly (ResidueField R) (residue S b)) ^
          (e * Module.finrank
            (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) :=
  ⟨Algebra.map_charpoly_lmul_integralClosure R F S E b,
    Algebra.residue_charpoly_lmul_eq_minpoly_pow R S hπ hϖ u e he b⟩

open Lean in
run_cmd do
  for name in #[``Algebra.eval_charpoly_lmul_eq_norm,
      ``Algebra.map_charpoly_lmul_integralClosure,
      ``Algebra.residue_charpoly_lmul_eq_pow,
      ``Algebra.residue_charpoly_lmul_eq_minpoly_pow,
      ``Algebra.residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis,
      ``actualMinimalPolynomialPower, ``actualPrimitiveResiduePower,
      ``originalFieldAndResidue] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual DVR characteristic-polynomial reduction uses only standard foundations."

end AglibTest.DVRCharpolyResidue
