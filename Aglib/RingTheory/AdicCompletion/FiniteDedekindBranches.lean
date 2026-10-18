/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteAlgebra
public import Aglib.RingTheory.AdicCompletion.DedekindBranches

/-!
# The actual finite Dedekind algebra completion branch product

The scalar tensor product is identified with the completions of all original
localized rings above the extended ideal, using its proved ideal factorization.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [IsNoetherianRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [DecidableEq (Ideal S)]

/-- Full actual completion tensor decomposition; neither a tensor isomorphism
nor an ideal factorization is assumed. -/
def tensorEquivLocalCompletions (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0) :
    AdicCompletion I R ⊗[R] S ≃ₐ[R]
      ∀ q : IdealBranch (I.map (algebraMap R S)),
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) :=
  (tensorEquivExtendedCompletion I).trans
    ((dedekindBranchesAlgEquiv (I.map (algebraMap R S)) hI).restrictScalars R)

/-- The original element enters each actual local completion by its native map. -/
@[simp]
theorem tensorEquivLocalCompletions_one_tmul (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (s : S)
    (q : IdealBranch (I.map (algebraMap R S))) :
    tensorEquivLocalCompletions I hI (1 ⊗ₜ[R] s) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap S (Localization.AtPrime q.val) s) := by
  simp only [tensorEquivLocalCompletions, AlgEquiv.trans_apply,
    tensorEquivExtendedCompletion_one_tmul, AlgEquiv.restrictScalars_apply,
    dedekindBranchesAlgEquiv_algebraMap]

end AdicCompletion
