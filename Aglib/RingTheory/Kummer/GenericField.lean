/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization

/-! # The original root in the original fraction field

For a domain literal root algebra, the image of its root generates its supplied
fraction field over the supplied fraction field of the coefficients. The monic
power basis gives the degree and the original binomial is its minimal polynomial.
No discrete valuation, normality, localness or replacement field is used.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.Kummer

variable (R : Type*) [CommRing R] [IsDomain R] (N : ℕ) (f : R)
  (K F : Type*) [Field K] [Field F]
  [Algebra R K] [IsFractionRing R K]
  [IsDomain (RootAlgebra N f)]
  [Algebra (RootAlgebra N f) F] [IsFractionRing (RootAlgebra N f) F]
  [Algebra R F] [Algebra K F]
  [IsScalarTower R (RootAlgebra N f) F] [IsScalarTower R K F]

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)
local notation "α" => algebraMap T F θ

omit [IsDomain R] [IsFractionRing R K] [IsDomain T] [IsFractionRing T F] in
/-- The image of the original root satisfies the original coefficient equation. -/
theorem genericRoot_pow : α ^ N = algebraMap K F (algebraMap R K f) := by
  rw [← map_pow, root_pow, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

omit [IsDomain R] [IsFractionRing R K] [IsDomain T] in
/-- The original root generates the supplied fraction field; no irreducibility
assumption or chosen field realization is needed. -/
theorem genericRoot_adjoin_eq_top : IntermediateField.adjoin K {α} = ⊤ := by
  let S := IntermediateField.adjoin K ({α} : Set F)
  have hmem (t : T) : algebraMap T F t ∈ S := by
    have hle : Algebra.adjoin R ({θ} : Set T) ≤
        (S.toSubalgebra.restrictScalars R).comap (IsScalarTower.toAlgHom R T F) := by
      apply Algebra.adjoin_le
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.mem_adjoin_simple_self K α
    rw [AdjoinRoot.adjoinRoot_eq_top] at hle
    exact hle (show t ∈ (⊤ : Subalgebra R T) from trivial)
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective T z
  exact S.div_mem (hmem a) (hmem b)

include R f in
omit [IsDomain T] in
/-- The degree of the original fraction-field extension is the root order. -/
theorem genericRoot_finrank (hN : 0 < N) : Module.finrank K F = N := by
  rw [IsFractionRing.finrank_eq R K T F]
  exact (AdjoinRoot.powerBasis' (monic_X_pow_sub_C f (Nat.ne_of_gt hN))).finrank.trans
    natDegree_X_pow_sub_C

omit [IsDomain R] [IsFractionRing R K] [IsDomain T] [IsFractionRing T F] in
/-- The original root is integral over the supplied coefficient fraction field. -/
theorem genericRoot_isIntegral (hN : 0 < N) : IsIntegral K α := by
  refine ⟨rootPolynomial N (algebraMap R K f),
    monic_X_pow_sub_C _ (Nat.ne_of_gt hN), ?_⟩
  simpa only [rootPolynomial, Polynomial.aeval_def, eval₂_sub, eval₂_pow,
      eval₂_X, eval₂_C, sub_eq_zero]
    using genericRoot_pow R N f K F

omit [IsDomain T] in
/-- The original binomial, rather than a chosen defining polynomial, is the
minimal polynomial of the original root in the original fraction field. -/
theorem genericRoot_minpoly (hN : 0 < N) :
    minpoly K α = rootPolynomial N (algebraMap R K f) := by
  have hi := genericRoot_isIntegral R N f K F hN
  have hd : (minpoly K α).natDegree = N := by
    let pb := PowerBasis.ofAdjoinSimpleEqTop hi (genericRoot_adjoin_eq_top R N f K F)
    have h := pb.finrank
    rw [PowerBasis.ofAdjoinSimpleEqTop_dim] at h
    exact h.symm.trans (genericRoot_finrank R N f K F hN)
  apply Eq.symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi)
    (monic_X_pow_sub_C _ (Nat.ne_of_gt hN))
  · apply minpoly.dvd
    simpa only [rootPolynomial, Polynomial.aeval_def, eval₂_sub, eval₂_pow,
      eval₂_X, eval₂_C, sub_eq_zero]
      using genericRoot_pow R N f K F
  · rw [hd, natDegree_X_pow_sub_C]

include F in
omit [IsDomain T] in
/-- Domain of the literal monic root algebra implies irreducibility of its
original binomial over the supplied fraction field. -/
theorem genericRoot_irreducible (hN : 0 < N) :
    Irreducible (rootPolynomial N (algebraMap R K f)) := by
  rw [← genericRoot_minpoly R N f K F hN]
  exact minpoly.irreducible (genericRoot_isIntegral R N f K F hN)

end Algebra.Kummer
