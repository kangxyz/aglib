/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVR
public import Aglib.KTheory.MilnorK.Dedekind.ResidueSupport
public import Aglib.RingTheory.FiniteLocalResidue
public import Aglib.RingTheory.LocalizedDedekindFractions

/-!
# Original-point residue pushforward for a finite Dedekind map

The local comparison uses the actual localized rings and their maps to the
same original fraction field. No residue compatibility premise is introduced.
-/

@[expose] public noncomputable section

namespace MilnorK

open IsLocalRing

/-- Equivalent actual local models compute the same residue norm in the
original base residue field. -/
theorem residueNorm_eq_of_localAlgEquiv
    {R S T E : Type*}
    [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
    [FiniteDimensional (ResidueField R) (ResidueField S)]
    [FiniteDimensional (ResidueField R) (ResidueField T)]
    [Field E] [Algebra S E] [IsFractionRing S E] [Algebra T E] [IsFractionRing T E]
    (j : S ≃ₐ[R] T)
    (hj : ∀ s : S, algebraMap S E s = algebraMap T E (j s))
    (n : ℕ) (x : K E (n + 1)) :
    finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) =
      finiteExtensionNorm (ResidueField R) (ResidueField T) n (DVR.residue T E n x) := by
  have hr := DVR.residue_equiv_apply j.toRingEquiv (RingEquiv.refl E) hj n x
  have hid : (RingEquiv.refl E).toRingHom = RingHom.id E := rfl
  rw [hid, map_id, LinearMap.id_apply] at hr
  rw [← hr]
  exact (finiteExtensionNorm_map_algEquiv (ResidueField.mapAlgEquiv' j) n _).symm

open AdicCompletion IsDedekindDomain
attribute [local instance] Classical.decEq

section Dedekind

universe u
variable (A S F E : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
  (p : HeightOneSpectrum A) [CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

omit F in
/-- The actual norm of the original residue at one original prime above `p`. -/
def originalBranchResidueNorm (n : ℕ) (x : K E (n + 1))
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    K (ResidueField (Localization.AtPrime p.asIdeal)) n := by
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := originalBranchFractionAlgebra S E q
  let := originalBranchIsFractionRing S E q
  exact finiteExtensionNorm (ResidueField (Localization.AtPrime p.asIdeal))
    (ResidueField (Localization.AtPrime q.val)) n
      (DVR.residue (Localization.AtPrime q.val) E n x)

/-- The finite norm-residue square at an original height-one point, summing
all original prime ideals above it. -/
theorem residue_finiteExtensionNorm_atPrime (n : ℕ) (x : K E (n + 1)) :
    DVR.residue (Localization.AtPrime p.asIdeal) F n
      (finiteExtensionNorm F E (n + 1) x) =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        originalBranchResidueNorm A S E p n x q := by
  classical
  let R := Localization.AtPrime p.asIdeal
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A R E := IsScalarTower.to₁₂₄ A R F E
  let := Localization.baseLocalizedFractionAlgebra (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionTower (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionRing (S := S) p.asIdeal E
  let := Localization.baseLocalizedFractionBaseTower (S := S) p.asIdeal E
  let J := (maximalIdeal R).map (algebraMap R B)
  let := fun q : IdealBranch J => originalBranchFractionAlgebra B E q
  let := fun q : IdealBranch J => originalBranchIsFractionRing B E q
  let := fun q : IdealBranch J => originalBranchFractionTower B E q
  rw [residue_finiteExtensionNorm_dvr R B F E]
  let e := Localization.originalIdealBranchEquivLocalizedBranches (S := S) p
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  let Q := e q
  let := originalBranchFractionAlgebra S E q
  let := originalBranchIsFractionRing S E q
  let := originalBranchFractionTower S E q
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocalTower p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let jR := Localization.originalIdealBranchLocalEquiv (S := S) p q
  apply residueNorm_eq_of_localAlgEquiv jR
  intro b
  have ht : IsScalarTower S (Localization.AtPrime Q.val) E :=
    IsScalarTower.to₁₃₄ S B (Localization.AtPrime Q.val) E
  let := ht
  have hh := Localization.atPrime_basePrimeCompl_equiv_comp p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
    (IsScalarTower.toAlgHom S (Localization.AtPrime Q.val) E)
    (IsScalarTower.toAlgHom S (Localization.AtPrime q.val) E)
  exact (AlgHom.congr_fun hh b).symm

end Dedekind

end MilnorK
