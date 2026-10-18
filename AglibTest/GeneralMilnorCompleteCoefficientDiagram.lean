/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteCoprimeDescent

/-!
# Actual complete coefficient diagram consumer

Every extension ring below is the literal integral closure. No extension DVR,
locality, finite module, torsion-free module, residue characteristic or Henselian
structure is assumed. The final conclusion supplies the three new positive
uniformizer equations used by coprime descent.
-/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorCompleteCoefficientDiagram

open MilnorK
open Polynomial PolynomialResidue IsLocalRing
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower
open MilnorK.PolynomialNorm
open MilnorK.PolynomialNorm.CompleteCoefficientDiagram

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [Module.Finite F L]

/-- All three new arrows have literal positive uniformizer factorizations. -/
theorem actual_complete_coefficient_diagram
    (p : MonicIrreducible F) (hcop : p.val.natDegree.Coprime (Module.finrank F L))
    {π : R} (hπ : Irreducible π) :
    let E := AdjoinRoot p.val
    let D := AdjoinRoot (coprimeCoefficientPolynomial p hcop).val
    let S := integralClosure R E
    let T := integralClosure R L
    let U := integralClosure R D
    let _ := coefficientAlgebra p hcop
    let _ := closureAlgebra R E D
    let _ := closureAlgebra R L D
    ∃ (ϖ : S) (τ : T) (ρ : U), Irreducible ϖ ∧ Irreducible τ ∧ Irreducible ρ ∧
      (∃ (a : ℕ) (_ : 0 < a) (v : Tˣ), algebraMap R T π = v * τ ^ a) ∧
      (∃ (b : ℕ) (_ : 0 < b) (w : Uˣ), algebraMap S U ϖ = w * ρ ^ b) ∧
      (∃ (c : ℕ) (_ : 0 < c) (z : Uˣ), algebraMap T U τ = z * ρ ^ c) := by
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let E := AdjoinRoot p.val
  let D := AdjoinRoot (coprimeCoefficientPolynomial p hcop).val
  let S := integralClosure R E
  let T := integralClosure R L
  let U := integralClosure R D
  let : Algebra E D := coefficientAlgebra p hcop
  let : Algebra S U := closureAlgebra R E D
  let : Algebra T U := closureAlgebra R L D
  let : FiniteDimensional F E := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
  let : FiniteDimensional L D :=
    (AdjoinRoot.powerBasis (coprimeCoefficientPolynomial p hcop).property.2.ne_zero).finite
  let : FiniteDimensional F D := Module.Finite.trans L D
  let : IsDiscreteValuationRing S := integralClosure_isDiscreteValuationRing R F E
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F L
  let : IsDiscreteValuationRing U := integralClosure_isDiscreteValuationRing R F D
  let : IsFractionRing S E := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : IsFractionRing U D := IsIntegralClosure.isFractionRing_of_finite_extension R F D U
  let : IsIntegralClosure U S D := upper_isIntegralClosure R E D
  let : IsIntegralClosure U T D := upper_isIntegralClosure R L D
  let : Module.Finite R S := IsIntegralClosure.finite R F E S
  let : Module.Finite R T := IsIntegralClosure.finite R F L T
  let : Module.Finite S U := upper_finite R F E D
  let : Module.Finite T U := upper_finite R F L D
  let : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integralClosure_algebraMap_injective R F E)
  let : Module.IsTorsionFree R T :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integralClosure_algebraMap_injective R F L)
  let : Module.IsTorsionFree S U := upper_torsionFree R F E D
  let : Module.IsTorsionFree T U := upper_torsionFree R F L D
  let : IsLocalHom (algebraMap R S) := integralClosure_isLocalHom R F E
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : IsLocalHom (algebraMap R U) := integralClosure_isLocalHom R F D
  let : IsLocalHom (algebraMap S U) := upper_isLocalHom R E D
  let : IsLocalHom (algebraMap T U) := upper_isLocalHom R L D
  let : IsAdicComplete (maximalIdeal S) S := integralClosure_isAdicComplete R F E
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F L
  let : IsAdicComplete (maximalIdeal U) U := integralClosure_isAdicComplete R F D
  let : HenselianLocalRing S := integralClosure_henselianLocalRing R F E
  let : HenselianLocalRing T := integralClosure_henselianLocalRing R F L
  let : HenselianLocalRing U := integralClosure_henselianLocalRing R F D
  let : Module.Finite (ResidueField R) (ResidueField T) :=
    integralClosure_residue_finite R F L
  let : Module.Finite (ResidueField S) (ResidueField U) :=
    IsLocalRing.ResidueField.finite_of_module_finite
  let : Module.Finite (ResidueField T) (ResidueField U) :=
    IsLocalRing.ResidueField.finite_of_module_finite
  let : CharZero (ResidueField S) :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField S)).injective
  let : CharZero (ResidueField T) :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField T)).injective
  let : CharZero (ResidueField U) :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField U)).injective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨τ, hτ⟩ := IsDiscreteValuationRing.exists_irreducible T
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible U
  refine ⟨ϖ, τ, ρ, hϖ, hτ, hρ, ?_, ?_, ?_⟩
  · exact integralClosure_exists_positive_ramification R F L hπ hτ
  · exact exists_positive_ramification (algebraMap S U)
      (FaithfulSMul.algebraMap_injective S U) hϖ hρ
  · exact exists_positive_ramification (algebraMap T U)
      (FaithfulSMul.algebraMap_injective T U) hτ hρ

open Lean in
run_cmd do
  for name in #[``IsDiscreteValuationRing.IntegralClosureTower.upper_isIntegralClosure,
      ``IsDiscreteValuationRing.IntegralClosureTower.upper_finite,
      ``IsDiscreteValuationRing.IntegralClosureTower.upper_torsionFree,
      ``CompleteCoefficientDiagram.coefficient_algebraMap_eq,
      ``residue_polynomialNorm_of_complete_coprime_mixed,
      ``actual_complete_coefficient_diagram] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The literal complete coefficient diagram uses only standard foundations."

end AglibTest.GeneralMilnorCompleteCoefficientDiagram
