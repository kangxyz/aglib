/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Smooth.Reduced
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Reduced local rings with principal maximal ideal

A reduced Noetherian local ring with principal maximal ideal is a domain.
Krull intersection factors each nonzero element as a power of a maximal-ideal
generator times a unit. The cotangent-dimension-at-most-one criterion supplies
the principal maximal ideal in the last theorem.

Reducedness of smooth algebras is imported directly from upstream
`Aglib.RingTheory.Smooth.Reduced`; no duplicate implementation is retained here.
The declarations now use the native `IsLocalRing` namespace.

## Source correspondence

Auxiliary geometry for `K2-018#sec:k2018-splitting`, lines 240–249,
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, and
`K2-018#prop:k2018-arithmetic-characters`, lines 341–445, in
`research/exposes/K2/018/expose.tex` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, source SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
These are reusable algebraic preliminaries, not proofs of those complete claims.

Implementation basis: `6987216b7dfb16036f94cc41b3c33a2da4e5e535`;
Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/LocalRing/PrincipalMaximalIdeal.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`32efff363b10806f7ee5e1dfa06f842b68b55ca4340373cbc4c04e142c290a54`.
-/

@[expose] public section

noncomputable section
namespace IsLocalRing
open Algebra IsLocalRing
open scoped _root_.TensorProduct

/- Auxiliary algebra for the three `K2-018` locators and pinned source above:
an étale algebra over any domain is reduced, without a field or characteristic restriction. -/

/- Auxiliary algebra for the three `K2-018` locators and pinned source above:
a standard smooth algebra over any domain is reduced, by its étale polynomial presentation. -/

/- Auxiliary algebra for the three `K2-018` locators and pinned source above:
a smooth algebra over any domain is reduced. Localizations supply the proof; reducedness
is a conclusion, not an input. -/

/-- Auxiliary local algebra for the three `K2-018` locators and pinned source above:
Krull intersection factors a nonzero element as a power of a chosen maximal-ideal generator
times a unit. This step uses Noetherianity and locality, without assuming a domain. -/
lemma exists_unit_mul_pow_of_principal_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (t : R) (ht : maximalIdeal R = Ideal.span {t}) {x : R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (a : R), IsUnit a ∧ x = t ^ n * a := by
  classical
  have hex : ∃ n : ℕ, x ∉ maximalIdeal R ^ n := by
    by_contra! h
    have hm : x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at hm
    exact hx hm
  have hnz : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    simp [h] at this
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hnz
  have hxmem : x ∈ maximalIdeal R ^ n := by
    exact not_not.mp (Nat.find_min hex (by omega))
  have hxnot : x ∉ maximalIdeal R ^ (n + 1) := by
    simpa [hn] using Nat.find_spec hex
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxmem
  obtain ⟨a, ha⟩ := hxmem
  refine ⟨n, a, ?_, ha⟩
  by_contra han
  apply hxnot
  rw [ha, pow_succ]
  apply Ideal.mul_mem_mul
  · rw [ht]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton t)) n
  · exact han

/-- Auxiliary local algebra for the three `K2-018` locators and pinned source above:
a reduced Noetherian local ring with principal maximal ideal is a domain. -/
lemma local_isDomain_of_reduced_principal_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    (hm : (maximalIdeal R).IsPrincipal) : IsDomain R := by
  obtain ⟨t, ht⟩ := hm
  by_cases ht0 : t = 0
  · have hf : IsField R := isField_iff_maximalIdeal_eq.mpr (by simpa [ht0] using ht)
    let := hf.toField
    infer_instance
  have ht_pow (n : ℕ) : t ^ n ≠ 0 := by
    intro h
    exact ht0 (IsNilpotent.eq_zero ⟨n, h⟩)
  suffices NoZeroDivisors R from NoZeroDivisors.to_isDomain _
  refine ⟨?_⟩
  intro x y hxy
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  exfalso
  obtain ⟨n, a, ha, rfl⟩ := exists_unit_mul_pow_of_principal_maximalIdeal R t ht hx
  obtain ⟨m, b, hb, rfl⟩ := exists_unit_mul_pow_of_principal_maximalIdeal R t ht hy
  apply ht_pow (n + m)
  have h : t ^ (n + m) * (a * b) = 0 := by
    simpa only [pow_add, mul_mul_mul_comm] using hxy
  exact (ha.mul hb).mul_left_eq_zero.mp h

/-- Auxiliary local algebra for the three `K2-018` locators and pinned source above:
cotangent dimension at most one and reducedness make a Noetherian local ring a domain.
The intended smooth-curve consumer derives both conditions from its actual geometry. -/
lemma isDomain_of_isReduced_of_finrank_cotangentSpace_le_one
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    (h : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1) : IsDomain R :=
  local_isDomain_of_reduced_principal_maximalIdeal R
    (finrank_cotangentSpace_le_one_iff.mp h)

end IsLocalRing
