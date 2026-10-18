/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.SemilocalBranches
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Completed local branches of a nonzero Dedekind ideal

The factors and their positive multiplicities are the actual normalized ideal
factors. No factorization or completion decomposition is an input.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open Function IsLocalRing UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [DecidableEq (Ideal R)]

/-- Actual distinct prime ideal factors of the original ideal. -/
abbrev IdealBranch (I : Ideal R) := ↥(normalizedFactors I).toFinset

instance idealBranchIsMaximal (I : Ideal R) (q : IdealBranch I) : q.val.IsMaximal := by
  have hp := prime_of_normalized_factor q.val (Multiset.mem_toFinset.mp q.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

/-- The displayed positive exponent is the actual ideal-factor multiplicity. -/
theorem idealBranch_count_pos (I : Ideal R) (q : IdealBranch I) :
    0 < (normalizedFactors I).count q.val :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp q.property)

/-- Unique ideal factorization supplies the full product, with no omitted branch. -/
theorem idealBranch_factorization (I : Ideal R) (hI : I ≠ 0) :
    I = ∏ q : IdealBranch I, q.val ^ (normalizedFactors I).count q.val := by
  rw [Finset.prod_coe_sort (normalizedFactors I).toFinset
    (fun J => J ^ (normalizedFactors I).count J)]
  rw [← Finset.prod_multiset_count]
  exact (associated_iff_eq.mp (prod_normalizedFactors hI)).symm

/-- Canonical completion decomposition over all actual prime ideal factors,
using their actual localized rings. -/
def dedekindBranchesAlgEquiv (I : Ideal R) (hI : I ≠ 0) :
    AdicCompletion I R ≃ₐ[R]
      ∀ q : IdealBranch I,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) :=
  semilocalBranchesAlgEquiv (fun q : IdealBranch I => q.val)
    (fun _ _ h => Ideal.isCoprime_of_isMaximal (fun heq => h (Subtype.ext heq)))
    (fun q => (normalizedFactors I).count q.val) (idealBranch_count_pos I)
    (fun q => Localization.AtPrime q.val) I (idealBranch_factorization I hI)

@[simp]
theorem dedekindBranchesAlgEquiv_algebraMap (I : Ideal R) (hI : I ≠ 0)
    (r : R) (q : IdealBranch I) :
    dedekindBranchesAlgEquiv I hI (algebraMap R (AdicCompletion I R) r) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap R (Localization.AtPrime q.val) r) :=
  congrFun ((dedekindBranchesAlgEquiv I hI).commutes r) q

end AdicCompletion
