/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.FittingIdeal.Stratification

/-! Focused consumer of the Fitting-ideal local freeness criteria (Picard plan row F12; Stacks
Project, Tags 07ZC and 07ZD) and the fibre-rank stratification consumed by the flattening
stratification (Nitsure, arXiv:math/0504590v1, Theorem 4.3). -/

@[expose] public section

open TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Local criterion for rank `r + 1` (Stacks 07ZD (1) ⇔ (2), local case). -/
example [IsLocalRing R] [Module.Finite R M] {r : ℕ} :
    Module.Free R M ∧ Module.finrank R M = r + 1 ↔
      Module.fittingIdeal R M r = ⊥ ∧ Module.fittingIdeal R M (r + 1) = ⊤ :=
  Module.free_and_finrank_eq_succ_iff_of_isLocalRing

/-- Rank `0` over a local ring: `Fitt_0(M) = R` if and only if `M` is free of rank `0`. -/
example [IsLocalRing R] [Module.Finite R M] :
    Module.fittingIdeal R M 0 = ⊤ ↔ Module.Free R M ∧ Module.finrank R M = 0 := by
  simpa using Module.fittingIdeal_eq_bot_and_eq_top_iff_of_isLocalRing (R := R) (M := M) (r := 0)

/-- Global criterion for rank `r + 1` (Stacks 07ZD (1) ⇔ (2)). -/
example [Module.Finite R M] {r : ℕ} :
    (Module.fittingIdeal R M r = ⊥ ∧ Module.fittingIdeal R M (r + 1) = ⊤) ↔
      ∀ p : PrimeSpectrum R, p ∈ Module.freeLocus R M ∧ Module.rankAtStalk M p = r + 1 :=
  Module.fittingIdeal_eq_bot_and_eq_top_iff_succ

/-- Projective of constant rank, for finitely presented modules. -/
example [Module.FinitePresentation R M] {r : ℕ} :
    ((∀ k < r, Module.fittingIdeal R M k = ⊥) ∧ Module.fittingIdeal R M r = ⊤) ↔
      Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r :=
  Module.fittingIdeal_eq_bot_and_eq_top_iff_projective

/-- Stacks 07ZC (1) ⇔ (2) at a prime. -/
example [Module.Finite R M] (p : Ideal R) [p.IsPrime] (k : ℕ) :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] M) ≤ k ↔
      ¬Module.fittingIdeal R M k ≤ p :=
  Module.finrank_residueField_tensor_le_iff p

/-- The universal property of the rank-`r` stratum. -/
example [Module.Finite R M] (S : Type*) [CommRing S] [Algebra R S] {r : ℕ} :
    ((∀ k < r, (Module.fittingIdeal R M k).map (algebraMap R S) = ⊥) ∧
        (Module.fittingIdeal R M r).map (algebraMap R S) = ⊤) ↔
      ∀ q : PrimeSpectrum S,
        q ∈ Module.freeLocus S (S ⊗[R] M) ∧ Module.rankAtStalk (S ⊗[R] M) q = r :=
  Module.fittingIdeal_map_eq_bot_and_eq_top_iff S

/-- info: 'Module.span_compl_range_eq_top_of_isUnit_det' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.span_compl_range_eq_top_of_isUnit_det

/-- info: 'Module.fittingIdeal_eq_top_iff_exists_finset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_top_iff_exists_finset

/-- info: 'Module.fittingIdeal_eq_bot_and_eq_top_iff_of_isLocalRing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_bot_and_eq_top_iff_of_isLocalRing

/-- info: 'Module.free_and_finrank_eq_succ_iff_of_isLocalRing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.free_and_finrank_eq_succ_iff_of_isLocalRing

/-- info: 'Module.fittingIdeal_eq_bot_and_eq_top_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_bot_and_eq_top_iff

/-- info: 'Module.fittingIdeal_eq_bot_and_eq_top_iff_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_bot_and_eq_top_iff_succ

/-- info: 'Module.fittingIdeal_eq_bot_and_eq_top_iff_projective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_bot_and_eq_top_iff_projective

/-- info: 'Module.fittingIdeal_eq_top_iff_finrank_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_eq_top_iff_finrank_le

/-- info: 'Module.finrank_residueField_tensor_le_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.finrank_residueField_tensor_le_iff

/-- info: 'Module.setOf_finrank_residueField_tensor_eq_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.setOf_finrank_residueField_tensor_eq_succ

/-- info: 'Module.setOf_finrank_residueField_tensor_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.setOf_finrank_residueField_tensor_eq_zero

/-- info: 'Module.fittingIdeal_map_eq_bot_and_eq_top_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.fittingIdeal_map_eq_bot_and_eq_top_iff

/-- info: 'Module.finitePresentation_and_flat_of_forall_free' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.finitePresentation_and_flat_of_forall_free
