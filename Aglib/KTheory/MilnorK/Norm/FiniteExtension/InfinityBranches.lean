/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.InfinityTwist
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.DVR
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Actual infinity branches in a finite rational-function extension

The integral closure of the inverted-parameter DVR in the original field
provides all branches above infinity. Residues are taken in that original
field, not in completions or a constant-field replacement.
-/

@[expose] public noncomputable section
namespace MilnorK

open Polynomial PolynomialResidue Polynomial.LocalResidue IsLocalRing AdicCompletion

universe u
variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Sum over every actual prime of the normalization above the inverted parameter. -/
def infinityBranchResidueSum (n : ℕ) (x : K E (n + 1)) : K k n := by
  classical
  let fin := infinityTwistFinite k E
  letI := infinityTwistAlgebra k E
  letI := fin
  let R := Ring (X : k[X])
  letI : Algebra R E := ((algebraMap (RatFunc k) E).comp (algebraMap R (RatFunc k))).toAlgebra
  letI : IsScalarTower R (RatFunc k) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (RatFunc k) E).injective.comp (IsFractionRing.injective R (RatFunc k)))
  let S : Type u := integralClosure R E
  letI : CommRing S := inferInstance
  letI : IsDedekindDomain S := integralClosure.isDedekindDomain R (RatFunc k) E
  letI : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R E (A := S)
  letI : Module.Finite R S := IsIntegralClosure.finite R (RatFunc k) E S
  letI : IsFractionRing S E :=
    IsIntegralClosure.isFractionRing_of_finite_extension R (RatFunc k) E S
  letI : CharZero (IsLocalRing.ResidueField R) :=
    RingHom.charZero ((InfinityResidue.rootXEquiv k).toRingHom.comp
      (residueEquiv (X : k[X])).toRingHom)
  let J := (maximalIdeal R).map (algebraMap R S)
  letI := fun q : IdealBranch (R := S) J => originalBranchFractionAlgebra S E q
  letI := fun q : IdealBranch (R := S) J => originalBranchIsFractionRing S E q
  refine map n (InfinityResidue.rootXEquiv k).toRingHom
    (map n (residueEquiv (X : k[X])).toRingHom
      (∑ q : IdealBranch (R := S) J, ?_))
  letI := originalBranchResidueFinite R S q
  exact finiteExtensionNorm (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (Localization.AtPrime q.val)) n
    (DVR.residue (Localization.AtPrime q.val) E n x)

/-- The original norm's infinity residue is the sum over all original infinity branches. -/
theorem infinityResidue_finiteExtensionNorm (n : ℕ) (x : K E (n + 1)) :
    InfinityResidue.residue k n (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      infinityBranchResidueSum k E n x := by
  rw [infinityResidue_finiteExtensionNorm_eq_twist]
  classical
  let fin := infinityTwistFinite k E
  let := infinityTwistAlgebra k E
  let := fin
  let R := Ring (X : k[X])
  let : Algebra R E := ((algebraMap (RatFunc k) E).comp (algebraMap R (RatFunc k))).toAlgebra
  let : IsScalarTower R (RatFunc k) E := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (RatFunc k) E).injective.comp (IsFractionRing.injective R (RatFunc k)))
  let S : Type u := integralClosure R E
  let : CommRing S := inferInstance
  let : IsDedekindDomain S := integralClosure.isDedekindDomain R (RatFunc k) E
  let : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R E (A := S)
  let : Module.Finite R S := IsIntegralClosure.finite R (RatFunc k) E S
  let : IsFractionRing S E :=
    IsIntegralClosure.isFractionRing_of_finite_extension R (RatFunc k) E S
  let : CharZero (IsLocalRing.ResidueField R) :=
    RingHom.charZero ((InfinityResidue.rootXEquiv k).toRingHom.comp
      (residueEquiv (X : k[X])).toRingHom)
  let J := (maximalIdeal R).map (algebraMap R S)
  let := fun q : IdealBranch (R := S) J => originalBranchFractionAlgebra S E q
  let := fun q : IdealBranch (R := S) J => originalBranchIsFractionRing S E q
  change map n (InfinityResidue.rootXEquiv k).toRingHom
    (residueAt (X : k[X]) n (finiteExtensionNorm (RatFunc k) E (n + 1) x)) = _
  rw [residueAt_eq_dvr, LinearMap.comp_apply]
  exact congrArg (fun z => map n (InfinityResidue.rootXEquiv k).toRingHom
    (map n (residueEquiv (X : k[X])).toRingHom z))
    (residue_finiteExtensionNorm_dvr R S (RatFunc k) E n x)

end MilnorK
