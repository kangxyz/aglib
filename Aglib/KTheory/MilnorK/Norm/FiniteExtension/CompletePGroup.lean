/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompletePrime
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompleteDegreeOne
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVRResidueTower
public import Aglib.RingTheory.IntermediateIntegralClosureTower
public import Aglib.FieldTheory.PGroupNormalSubfieldEmbedding

/-!
# Complete-DVR norm-residue compatibility in a p-group ambient

Actual normal-prime intermediate fields give strict degree descent. All
intermediate integral-closure maps are literal, and the original upper DVR is
retained. No unramifiedness or residue compatibility premise is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing IsDiscreteValuationRing.CompleteExtension

universe u

/-- Complete-DVR compatibility for every extension embedded in a Galois p-group. -/
theorem residue_finiteExtensionNorm_complete_of_pGroup
    (R S F E Ω : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [CharZero F] [Field E] [CharZero E] [Field Ω]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [FiniteDimensional F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[F] Ω)) (g : E →ₐ[F] Ω)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) := by
  induction hd : Module.finrank F E using Nat.strong_induction_on
      generalizing R S F E Ω with
  | h d ih =>
    by_cases hdeg : Module.finrank F E = 1
    · exact residue_finiteExtensionNorm_complete_degree_one R F E S hdeg n x
    have hgt : 1 < Module.finrank F E := by
      have := Module.finrank_pos (R := F) (M := E)
      omega
    obtain ⟨J, hnormal, hdegree, hdrop⟩ :=
      IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hG g hgt
    let : Normal F J := hnormal
    let : CharZero J := charZero_of_injective_algebraMap (algebraMap F J).injective
    let : Algebra E Ω := g.toRingHom.toAlgebra
    let : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    let : FiniteDimensional J E := FiniteDimensional.right F J E
    let : FiniteDimensional J Ω := FiniteDimensional.right F J Ω
    let : IsGalois J Ω := IsGalois.tower_top_of_isGalois F J Ω
    have hJG : IsPGroup ℓ (Ω ≃ₐ[J] Ω) :=
      hG.of_injective (AlgEquiv.restrictScalarsHom F)
        (AlgEquiv.restrictScalarsHom_injective F)
    let : IsScalarTower R J E := IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R F E, IsScalarTower.algebraMap_apply R F J,
        IsScalarTower.algebraMap_apply F J E]
    let T := integralClosure R J
    let : IsDiscreteValuationRing T := integralClosure_isDiscreteValuationRing R F J
    let : IsLocalHom (algebraMap R T) := integralClosure_isLocalHom R F J
    let : Module.Finite R T := IsIntegralClosure.finite R F J T
    let : IsFractionRing T J := IsIntegralClosure.isFractionRing_of_finite_extension R F J T
    let : IsAdicComplete (maximalIdeal T) T := integralClosure_isAdicComplete R F J
    let : Module.Finite (ResidueField R) (ResidueField T) :=
      integralClosure_residue_finite R F J
    let : CharZero (ResidueField T) :=
      charZero_of_injective_algebraMap (algebraMap (ResidueField R) (ResidueField T)).injective
    let : Algebra T S := IsIntegralClosure.IntermediateTower.closureAlgebra R S J E
    let : IsScalarTower R T S := IsIntegralClosure.IntermediateTower.baseTower R S J E
    let : IsScalarTower T S E := IsIntegralClosure.IntermediateTower.topTower R S J E
    let : IsIntegralClosure S T E :=
      IsIntegralClosure.IntermediateTower.upper_isIntegralClosure R S J E
    let : Module.Finite T S := IsIntegralClosure.IntermediateTower.upper_finite R S J E
    let : IsLocalHom (algebraMap T S) :=
      IsIntegralClosure.IntermediateTower.upper_isLocalHom R S J E
    have hprime : (Module.finrank F J).Prime := hdegree ▸ (Fact.out : ℓ.Prime)
    apply residue_finiteExtensionNorm_of_tower R T S F J E n
    · exact residue_finiteExtensionNorm_complete_prime R F J T hprime n
    · intro y
      apply ih (Module.finrank J E) (hd ▸ hdrop) T S J E Ω
      · exact hJG
      · exact IsScalarTower.toAlgHom J E Ω
      · rfl

end MilnorK
