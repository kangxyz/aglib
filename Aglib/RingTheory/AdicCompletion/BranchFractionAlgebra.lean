/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BranchBaseLocal

/-!
# The actual completed-base fraction field action on each branch fraction field

The field map is the universal fraction-ring lift of the already constructed
injective completed-base map. Its scalar triangle is proved on base elements.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing

universe u

variable (R S : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]

/-- The actual universal fraction-field lift of the completed-base map. -/
@[instance_reducible] def localCompletionFractionAlgebra
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
    Algebra (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
  exact (IsFractionRing.lift (K := FractionRing (AdicCompletion (maximalIdeal R) R))
    (g := (algebraMap (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))).comp
        (algebraMap (AdicCompletion (maximalIdeal R) R)
          (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)))
    ((IsFractionRing.injective
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))).comp
        (localCompletionBase_injective R S hI q))).toAlgebra

/-- The fraction-field action extends the actual completed-base action. -/
theorem localCompletionFractionIsScalarTower
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
    letI := localCompletionFractionAlgebra R S hI q
    IsScalarTower (AdicCompletion (maximalIdeal R) R)
      (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) hI q
  let := localCompletionFractionAlgebra R S hI q
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (IsFractionRing.lift_algebraMap
    (K := FractionRing (AdicCompletion (maximalIdeal R) R))
    (g := (algebraMap (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))).comp
        (algebraMap (AdicCompletion (maximalIdeal R) R)
          (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)))
    ((IsFractionRing.injective
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))).comp
        (localCompletionBase_injective R S hI q)) x).symm

end AdicCompletion
