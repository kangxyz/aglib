/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ChineseRemainder
public import Aglib.RingTheory.AdicCompletion.Localization
public import Mathlib.Algebra.Algebra.Pi

/-!
# Actual local branches of a factored ideal completion

An explicitly factored ideal has completion equal to the product of the
completed original local rings. Positive ramification powers are retained in
the factorization and removed only by the proved cofinal filtration equivalence.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open Function IsLocalRing

variable {R ι : Type*} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) [∀ i, (J i).IsMaximal]
  (hJ : Pairwise (IsCoprime on J)) (e : ι → ℕ) (he : ∀ i, 0 < e i)
  (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  [∀ i, IsLocalization.AtPrime (S i) (J i)] [∀ i, IsLocalRing (S i)]

/-- All actual maximal localizations occur, with their original ring maps.
The only factorization input is the displayed equality of ideals. -/
def semilocalBranchesAlgEquiv (I : Ideal R) (hI : I = ∏ i, J i ^ e i) :
    AdicCompletion I R ≃ₐ[R] ∀ i, AdicCompletion (maximalIdeal (S i)) (S i) := by
  subst I
  exact (prodCompletionAlgEquiv (fun i => J i ^ e i)
    (fun i j hij => (hJ hij).pow)).trans
      (AlgEquiv.piCongrRight fun i =>
        (powAlgEquiv (J i) (e i) (he i)).trans (localizationAlgEquiv (J i) (S i)))

@[simp]
theorem semilocalBranchesAlgEquiv_algebraMap (I : Ideal R)
    (hI : I = ∏ i, J i ^ e i) (r : R) (i : ι) :
    semilocalBranchesAlgEquiv J hJ e he S I hI (algebraMap R (AdicCompletion I R) r) i =
      algebraMap (S i) (AdicCompletion (maximalIdeal (S i)) (S i))
        (algebraMap R (S i) r) :=
  congrFun ((semilocalBranchesAlgEquiv J hJ e he S I hI).commutes r) i

end AdicCompletion
