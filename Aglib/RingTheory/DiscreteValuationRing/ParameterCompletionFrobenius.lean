/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionValuation
public import Aglib.RingTheory.AdicCompletion.ValuativeCompleteness
public import Aglib.RingTheory.Valuation.ParameterMonomials
public import Aglib.RingTheory.MvPolynomial.RationalFrobenius

/-!
# Frobenius independence in the actual parameter completion
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped WithZero

namespace Valuation

/-- In positive prime characteristic, literal valuation-ring residues retain
that characteristic. This is not true for exponential characteristic one. -/
theorem expChar_residueField_of_prime
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (p : ℕ) (hp : p.Prime) [ExpChar K p] :
    ExpChar (ResidueField v.valuationSubring) p := by
  let A := v.valuationSubring
  let : CharP K p := (expChar_prime_iff K hp).mp inferInstance
  let : CharP A p := A.subtype.charP Subtype.val_injective p
  let : CharP (ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (residue A), CharP.cast_eq_zero A p, map_zero])
  exact ExpChar.prime hp

end Valuation

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (π : R) [Fact (Irreducible π)]

attribute [local instance] isDiscreteValuationRing algebraMap_isLocalHom
  completionAlgebra completionAlgebra_isLocalHom

local notation "T" => Ring R ι π
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T
local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "Q" => MvPolynomial ι K
local notation "vA" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal A)
local notation "vB" =>
  IsDedekindDomain.HeightOneSpectrum.valuation L (IsDiscreteValuationRing.maximalIdeal B)

/-- Restrict the actual completed rational map to its polynomial ring. -/
abbrev completedFractionPolynomialAlgebra : Algebra Q L :=
  ((completedRationalMap R ι π).comp (algebraMap Q (FractionRing Q))).toAlgebra

attribute [local instance] completedFractionPolynomialAlgebra completedRationalAlgebra

/-- The polynomial action is literally the restriction of the actual rational action. -/
theorem completedFractionPolynomialAlgebra_tower : IsScalarTower Q (FractionRing Q) L := by
  apply IsScalarTower.of_algebraMap_eq
  intro q
  rfl

/-- The chosen polynomial action evaluates the supplied coefficient field map
and the original variables. No abstract field equivalence changes this action. -/
theorem completedFractionPolynomialAlgebra_eq_eval₂Hom :
    algebraMap Q L = MvPolynomial.eval₂Hom (completionFractionMap R ι π)
      (fun x => (completedIntegerVariable R ι π x : L)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    change completedRationalMap R ι π
      (algebraMap Q (FractionRing Q) (MvPolynomial.C c)) = completionFractionMap R ι π c
    have hh := RingHom.congr_fun (completedRationalMap_coeff R ι π) c
    simpa only [RingHom.comp_apply, IsScalarTower.algebraMap_apply K Q (FractionRing Q),
      MvPolynomial.algebraMap_eq] using hh
  · intro x
    rw [MvPolynomial.eval₂Hom_X']
    change completedRationalMap R ι π
      (algebraMap Q (FractionRing Q) (MvPolynomial.X x)) =
        algebraMap B L (completedVariable R ι π x)
    exact completedRationalMap_X R ι π x

/-- Section 4 for the actual parameter DVR completion: arbitrary finite
Frobenius-independent completed coefficients times bounded monomials remain
independent over the target fraction field's Frobenius range. -/
theorem completionFiniteMonomialFrobeniusIndependent
    (p : ℕ) (hp : p.Prime) [ExpChar K p] [ExpChar L p] :
    MvPolynomial.FiniteMonomialFrobeniusIndependent (k := K) («L» := L) (σ := ι) p := by
  classical
  let : ExpChar (ResidueField (Valuation.valuationSubring vA)) p :=
    Valuation.expChar_residueField_of_prime vA p hp
  let : ExpChar (ResidueField (Valuation.valuationSubring vB)) p :=
    Valuation.expChar_residueField_of_prime vB p hp
  let := valuationResiduePolynomialAlgebra R ι π
  let := valuationResidue_isFractionRing R ι π
  intro b r hb hr
  have H := Valuation.linearIndependent_parameterMonomials vA vB p hp.pos
    (AdicCompletion.fractionRing_isSeqComplete R)
    (completionFractionMap R ι π) (completionFractionMap_valuation R ι π)
    (algebraMap A K (algebraMap R A π)) (completionFractionMap_uniformizer_value R π)
    (completedIntegerVariable R ι π) (completedIntegerVariable_value R ι π)
    (residue_completionIntegerMap R ι π) (residue_completedIntegerVariable R ι π)
    hb ((↑) : r → ι →₀ ℕ) (fun e x => hr e e.property x) Subtype.val_injective
  simpa only [completedFractionPolynomialAlgebra_eq_eval₂Hom] using H

end ParameterLocalization
