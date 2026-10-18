/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRPGroupDescent
public import Aglib.KTheory.MilnorK.Norm.Polynomial.CompleteScalarBranch

/-!
# Actual complete-DVR coefficient descent to p-group branches

All finite integral closures, uniformizer equations, and branch maps are
constructed. The resulting degree annihilator has no valuation diagram,
ramification, residue compatibility, or multiplicity-count premise.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension IsDiscreteValuationRing.IntegralClosureTower

universe u

attribute [local instance] scalarBranchAlgebra closureAlgebra

/-- Actual coefficient extensions whose every branch lies in a p-group ambient
annihilate the complete norm-residue defect by their actual field degree. -/
theorem degree_smul_normResidue_defect_complete_of_pGroup_branches
    (R F L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra R L] [IsScalarTower R F L]
    (p : MonicIrreducible F)
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : IrreducibleBranch (p.val.map (algebraMap F L)), AdjoinRoot r.val.val →ₐ[L] Ω)
    (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    let _ := p.property.1.finite_adjoinRoot
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    let _ := integralClosure_residue_finite R F (AdjoinRoot p.val)
    Module.finrank F L •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        finiteExtensionNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot p.val))) n
          (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x)) = 0 := by
  classical
  dsimp only
  let E := AdjoinRoot p.val
  let S := integralClosure R E
  let T := integralClosure R L
  let I := IrreducibleBranch (p.val.map (algebraMap F L))
  let D := fun r : I => AdjoinRoot r.val.val
  let U := fun r : I => integralClosure R (D r)
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let : FiniteDimensional F E := p.property.1.finite_adjoinRoot
  let : ∀ r : I, FiniteDimensional L (D r) := fun r => r.val.property.1.finite_adjoinRoot
  let : ∀ r : I, FiniteDimensional F (D r) := fun r => Module.Finite.trans L (D r)
  let : IsDiscreteValuationRing S := integralClosure_isDiscreteValuationRing R F E
  let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F L
  let : ∀ r : I, IsDiscreteValuationRing (U r) := fun r =>
    integralClosure_isDiscreteValuationRing R F (D r)
  let : IsLocalHom (algebraMap R S) := integralClosure_isLocalHom R F E
  let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F L
  let : ∀ r : I, IsLocalHom (algebraMap R (U r)) := fun r =>
    integralClosure_isLocalHom R F (D r)
  let : IsFractionRing S E := IsIntegralClosure.isFractionRing_of_finite_extension R F E S
  let : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  let : ∀ r : I, IsFractionRing (U r) (D r) := fun r =>
    IsIntegralClosure.isFractionRing_of_finite_extension R F (D r) (U r)
  let : Module.Finite R S := IsIntegralClosure.finite R F E S
  let : Module.Finite R T := IsIntegralClosure.finite R F L T
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F E)
  let : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure_algebraMap_injective R F L)
  let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F L
  let : CharZero (ResidueField T) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField T)).injective
  let : ∀ r : I, IsScalarTower R E (D r) := fun r => CompleteScalarBranch.baseBranchTower R p r
  let : ∀ r : I, Algebra S (U r) := fun r => closureAlgebra R E (D r)
  let : ∀ r : I, Algebra T (U r) := fun r => closureAlgebra R L (D r)
  let : ∀ r : I, IsScalarTower R S (U r) := fun r => baseTower R E (D r)
  let : ∀ r : I, IsScalarTower R T (U r) := fun r => baseTower R L (D r)
  let : ∀ r : I, IsLocalHom (algebraMap S (U r)) := fun r =>
    CompleteScalarBranch.oldRoot_isLocalHom R p r
  let : ∀ r : I, IsLocalHom (algebraMap T (U r)) := fun r =>
    CompleteScalarBranch.coefficient_isLocalHom R p r
  let : ∀ r : I, Module.Finite T (U r) := fun r =>
    CompleteScalarBranch.coefficient_finite R F L p r
  let : ∀ r : I, Module.IsTorsionFree T (U r) := fun r => upper_torsionFree R F L (D r)
  let : ∀ r : I, @IsScalarTower T (U r) (D r) _ _
      (AdjoinRoot.instSMulAdjoinRoot (S := T) r.val.val) := fun r => by
    let : Algebra T (D r) := AdjoinRoot.instAlgebra (S := T) r.val.val
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : ∀ r : I, Algebra T (D r) := fun r =>
    AdjoinRoot.instAlgebra (S := T) r.val.val
  let : ∀ r : I, IsIntegralClosure (U r) T (D r) := fun r =>
    CompleteScalarBranch.coefficient_isIntegralClosure R p r
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨τ, hτ⟩ := IsDiscreteValuationRing.exists_irreducible T
  choose ρ hρ using fun r : I => IsDiscreteValuationRing.exists_irreducible (U r)
  obtain ⟨e, _, u, he⟩ := integralClosure_exists_positive_ramification R F E hπ hϖ
  obtain ⟨a, _, v, ha⟩ := integralClosure_exists_positive_ramification R F L hπ hτ
  have hs (r : I) : Function.Injective (algebraMap S (U r)) := by
    intro s t h
    apply (IsFractionRing.injective S E)
    apply (algebraMap E (D r)).injective
    simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap (U r) (D r)) h
  have ht (r : I) : Function.Injective (algebraMap T (U r)) := by
    intro s t h
    apply (IsFractionRing.injective T L)
    apply (algebraMap L (D r)).injective
    simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap (U r) (D r)) h
  choose b _ w hb using fun r : I => exists_positive_ramification
    (algebraMap S (U r)) (hs r) hϖ (hρ r)
  choose c _ z hc using fun r : I => exists_positive_ramification
    (algebraMap T (U r)) (ht r) hτ (hρ r)
  exact degree_smul_normResidue_defect_eq_zero_of_pGroup_branches R S T p
    (fun r => ↥(U r)) Ω ℓ hG g
    (fun r s => (CompleteScalarBranch.oldRoot_closureMap_apply R p r s).symm)
    hπ hϖ hτ ρ hρ u e he v a ha w z b c hb hc n x

end MilnorK.PolynomialNorm
