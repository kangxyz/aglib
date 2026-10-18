/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteCoefficientDiagram
public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRCoprimeDescent

/-!
# Complete-DVR coprime descent on the literal coefficient diagram

All upper DVR, finite, torsion-free, local, Henselian and residue characteristic
structures are derived from completeness of the base and actual integral
closures. Only classwise mixedness after the specified finite coprime extension
is retained as input. No norm-residue compatibility is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower
open CompleteCoefficientDiagram

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [Module.Finite F L]

/-- Actual finite complete integral closures discharge every diagram hypothesis
of coprime descent; only upper mixedness and the original residue presentation remain. -/
theorem residue_polynomialNorm_of_complete_coprime_mixed
    (p : MonicIrreducible F) [Normal F (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime)
    (hcop : p.val.natDegree.Coprime (Module.finrank F L))
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (hx : map (n + 1) (adjoinRootMap (algebraMap F L) p.val
      (coprimeCoefficientPolynomial p hcop).val dvd_rfl) x ∈
        mixedSpan (algebraMap L (AdjoinRoot (coprimeCoefficientPolynomial p hcop).val)) n)
    (q : MonicIrreducible (ResidueField R)) :
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    ∀ ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField (integralClosure R (AdjoinRoot p.val)),
      DVR.residue R F n (polynomialNorm (n + 1) p x) =
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x)) := by
  let : CharZero R := RingHom.charZero (IsLocalRing.residue R)
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let E := AdjoinRoot p.val
  let D := AdjoinRoot (coprimeCoefficientPolynomial p hcop).val
  let S := integralClosure R E
  let T := integralClosure R L
  let U := integralClosure R D
  let : Algebra E D := coefficientAlgebra p hcop
  let : Algebra S U := closureAlgebra R E D
  let : Algebra T U := closureAlgebra R L D
  let : IsScalarTower R S U := baseTower R E D
  let : IsScalarTower R T U := baseTower R L D
  let : IsScalarTower S U D := topTower R E D
  let : @IsScalarTower T U D _ _
      (AdjoinRoot.instSMulAdjoinRoot (S := T) (coprimeCoefficientPolynomial p hcop).val) := by
    let : Algebra T D := AdjoinRoot.instAlgebra (S := T)
      (coprimeCoefficientPolynomial p hcop).val
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
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
  dsimp only
  intro ε
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨τ, hτ⟩ := IsDiscreteValuationRing.exists_irreducible T
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible U
  obtain ⟨e, _, u, hRS⟩ := integralClosure_exists_positive_ramification R F E hπ hϖ
  obtain ⟨a, _, v, hRT⟩ := integralClosure_exists_positive_ramification R F L hπ hτ
  obtain ⟨b, _, w, hSU⟩ := exists_positive_ramification (algebraMap S U)
    (FaithfulSMul.algebraMap_injective S U) hϖ hρ
  obtain ⟨c, hc, z, hTU⟩ := exists_positive_ramification (algebraMap T U)
    (FaithfulSMul.algebraMap_injective T U) hτ hρ
  have hcunit : IsUnit (c : U) := (residue_ne_zero_iff_isUnit _).mp (by
    rw [map_natCast]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
  exact residue_polynomialNorm_of_coprime_mixed_diagram R p S T
    (coprimeCoefficientPolynomial p hcop) rfl U (coefficient_algebraMap_eq p hcop)
    n x hx hπ hϖ hτ hρ u v w z e a b c hRS hRT hSU hTU hcunit hp hcop q ε

end MilnorK.PolynomialNorm
