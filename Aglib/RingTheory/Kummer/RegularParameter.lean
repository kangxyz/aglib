/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.Uniformizer
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Mathlib.RingTheory.Flat.Basic

/-! # Regularity of the literal root algebra of a regular parameter

Over a Noetherian local ring, adjoining a positive-order root of a
nonzerodivisor with regular local quotient gives a regular local ring. The
proof uses the literal monic root algebra, its original root, and the original
parameter quotient. Neither invertibility of the order nor Henselianity is
needed. This is root-algebra regularity, not a tame-chart existence theorem.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Algebra.Kummer

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (f : R) (hf : f ∈ maximalIdeal R) (N : ℕ) (hN : 0 < N)

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)

include hf hN in
/-- A root of an element of the maximal ideal gives a local algebra, with no
Henselianity or regularity assumption. -/
theorem parameterRoot_isLocalRing : IsLocalRing T := by
  let : Module.Finite R T := root_finite N hN f
  have hfspan : Ideal.span {f} ≤ maximalIdeal R :=
    Ideal.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hf)
  have hfproper : (Ideal.span {f} : Ideal R) ≠ ⊤ :=
    ne_top_of_le_ne_top (inferInstance : (maximalIdeal R).IsMaximal).ne_top hfspan
  let : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hfproper
  let : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let J : Ideal T := Ideal.span {θ}
  let Q := T ⧸ J
  let : IsLocalRing Q := (rootQuotientEquiv N hN f).symm.toRingEquiv.isLocalRing
  let q : T →+* Q := Ideal.Quotient.mk J
  let m₀ : Ideal T := (maximalIdeal Q).comap q
  have hm₀ : m₀.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm
  let : m.IsMaximal := hm
  have hmunder : m.under R = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)
  have hfmem : algebraMap R T f ∈ m := by
    change f ∈ m.under R
    rwa [hmunder]
  have hθmem : θ ∈ m := by
    apply (inferInstance : m.IsPrime).mem_of_pow_mem N
    rwa [root_pow]
  have hJm : J ≤ m := Ideal.span_le.mpr (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hθmem)
  have hker : RingHom.ker q ≤ m := by
    intro x hx
    apply hJm
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hmQ : (m.map q).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  have heq : m.map q = maximalIdeal Q := IsLocalRing.eq_maximalIdeal hmQ
  calc
    m = (m.map q).comap q := (Ideal.comap_map_mk hJm).symm
    _ = m₀ := congrArg (Ideal.comap q) heq

include hN in
omit [IsLocalRing R] in
/-- The original root is a nonzerodivisor when the original parameter is one,
by monic freeness and its exact power equation. -/
theorem parameterRoot_root_regular (hreg : IsSMulRegular R f) : IsSMulRegular T θ := by
  let : Module.Free R T := (Polynomial.monic_X_pow_sub_C f (Nat.ne_of_gt hN)).free_adjoinRoot
  have hpow : IsSMulRegular T (algebraMap R T f) := hreg.of_flat
  rw [← root_pow N f] at hpow
  exact (IsSMulRegular.pow_iff hN).mp hpow

include hf hN in
/-- A positive-order root of a regular parameter with regular local quotient
is itself regular local, on the literal polynomial quotient. -/
theorem parameterRoot_isRegularLocalRing [IsNoetherianRing R]
    (hreg : IsSMulRegular R f) [IsRegularLocalRing (R ⧸ Ideal.span {f})] :
    IsRegularLocalRing T := by
  let : IsLocalRing T := parameterRoot_isLocalRing R f hf N hN
  let : Module.Finite R T := root_finite N hN f
  let : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  let : IsRegularLocalRing (T ⧸ Ideal.span {θ}) :=
    IsRegularLocalRing.of_ringEquiv (rootQuotientEquiv N hN f).symm.toRingEquiv
  exact IsRegularLocalRing.of_quotient_span_singleton T θ
    (parameterRoot_root_regular R f N hN hreg)

end Algebra.Kummer
