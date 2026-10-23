/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Trivial lines in prime-characteristic p-group representations

A nonzero finite-dimensional Fp representation of a p-group has a nonzero
invariant vector, by the actual fixed-point cardinality congruence. Its span
is a genuine trivial subrepresentation of dimension one, and quotienting
strictly decreases dimension. No semisimplicity or invertible group order is used.
-/

@[expose] public noncomputable section

universe g v

namespace Representation

variable (p : ℕ) [Fact p.Prime] {G : Type g} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V] [Nontrivial V]

/-- The native fixed-point congruence supplies an actual nonzero invariant vector. -/
theorem exists_ne_zero_invariant_of_isPGroup
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ρ g x = x := by
  let : MulAction G V := {
    smul g x := ρ g x
    one_smul x := congrArg (fun f : Module.End (ZMod p) V => f x) ρ.map_one
    mul_smul g h x := congrArg (fun f : Module.End (ZMod p) V => f x) (ρ.map_mul g h) }
  have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  let : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out)))
  have hdiv : p ∣ Nat.card V := by
    rw [hcard]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
  have hzero : (0 : V) ∈ MulAction.fixedPoints G V := by
    intro g
    exact map_zero (ρ g)
  obtain ⟨x, hx, h0x⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdiv hzero
  exact ⟨x, Ne.symm h0x, hx⟩

/-- A genuine trivial line exists and the actual quotient has smaller dimension. -/
theorem exists_trivial_line_of_isPGroup
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ W : Subrepresentation ρ,
      Module.finrank (ZMod p) W.toSubmodule = 1 ∧
      W.toRepresentation.IsTrivial ∧
      Module.finrank (ZMod p) (V ⧸ W.toSubmodule) < Module.finrank (ZMod p) V := by
  obtain ⟨x, hx, hfix⟩ := exists_ne_zero_invariant_of_isPGroup p ρ hG
  have hline (g : G) (y : V) (hy : y ∈ Submodule.span (ZMod p) {x}) : ρ g y = y := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hfix]
  let W : Subrepresentation ρ := {
    toSubmodule := Submodule.span (ZMod p) {x}
    apply_mem_toSubmodule g y hy := by rw [hline g y hy]; exact hy }
  have hdim : Module.finrank (ZMod p) W.toSubmodule = 1 :=
    finrank_span_singleton hx
  refine ⟨W, hdim, ?_, ?_⟩
  · constructor
    intro g
    ext y
    exact hline g y y.property
  · have h := Submodule.finrank_quotient_add_finrank W.toSubmodule
    rw [hdim] at h
    omega

end Representation
