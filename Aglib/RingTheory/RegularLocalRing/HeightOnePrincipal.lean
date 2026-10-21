/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Aglib.RingTheory.RegularLocalRing.Parameters
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Principal prime ideals in regular local rings of dimension at most two

In dimension two every prime distinct from the maximal ideal is principal,
including the zero ideal. A first parameter outside the prime gives a regular
one-dimensional quotient. Its principal image lifts to a generator of the
original prime by Nakayama's lemma. No factoriality hypothesis is used.

The height-one specialization uses the actual Krull dimension and ideal height.
For a nonzero prime the principal generator supplies a basis of the actual ideal
module, with its usual inclusion into the ring.
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing Module

namespace IsLocalRing

/-- A nonmaximal prime in a Noetherian local ring misses a minimal generator of
the maximal ideal. The element also lies outside the square of that ideal. -/
theorem exists_parameter_not_mem_prime (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : Ideal R) [hpprime : p.IsPrime] (hp : p ≠ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ p ∧ x ∉ maximalIdeal R ^ 2 := by
  have hnot : ¬ maximalIdeal R ≤ p ⊔ maximalIdeal R ^ 2 := by
    intro hle
    have hm : maximalIdeal R ≤ p :=
      Submodule.le_of_le_smul_of_le_jacobson_bot
        (maximalIdeal R).fg_of_isNoetherianRing
        (I := maximalIdeal R)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top])
        (by simpa only [smul_eq_mul, pow_two] using hle)
    exact hp (le_antisymm (le_maximalIdeal hpprime.ne_top) hm)
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  exact ⟨x, hxm, fun hxp ↦ hx (Submodule.mem_sup_left hxp),
    fun hx2 ↦ hx (Submodule.mem_sup_right hx2)⟩

end IsLocalRing

namespace IsRegularLocalRing

/-- A regular local ring of dimension at most one is a principal ideal ring.
The domain property is derived from regularity. -/
theorem isPrincipalIdealRing_of_regularLocal_dimension_le_one (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  let : IsDomain R := isDomain_of_regularLocal R
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hc : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    exact_mod_cast he.trans_le hd
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 6 1).mp hc

/-- Every nonmaximal prime in a two-dimensional regular local ring is principal.
The zero ideal is included, and no factorization or ideal-freeness hypothesis is
assumed. -/
theorem isPrincipal_of_prime_ne_maximalIdeal_of_dimension_two (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R = 2)
    (p : Ideal R) [hpprime : p.IsPrime] (hp : p ≠ maximalIdeal R) : p.IsPrincipal := by
  classical
  obtain ⟨x, hxm, hxp, hx2⟩ := IsLocalRing.exists_parameter_not_mem_prime R p hp
  obtain ⟨hQ, hdQ⟩ := regularLocal_quotient_parameter R 1 (by simpa using hd) x hxm hx2
  let : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hQ
  let : IsPrincipalIdealRing (R ⧸ Ideal.span {x}) :=
    isPrincipalIdealRing_of_regularLocal_dimension_le_one _ (by simpa using hdQ.le)
  let q := Ideal.Quotient.mk (Ideal.span {x})
  obtain ⟨b, hbp, hb⟩ :=
    (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp
      (Submodule.IsPrincipal.generator_mem (p.map q))
  have hmap : p.map q = Ideal.span {q b} := by
    rw [hb]
    exact (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hle : p ≤ Ideal.span {b} ⊔ Ideal.span {x} • p := by
    intro a ha
    have hqa : q a ∈ Ideal.span {q b} := hmap ▸ Ideal.mem_map_of_mem q ha
    obtain ⟨cQ, hcQ⟩ := Ideal.mem_span_singleton'.mp hqa
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cQ
    have hdiff : a - c * b ∈ Ideal.span {x} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (a - c * b) = 0
      rw [map_sub, map_mul, sub_eq_zero]
      exact hcQ.symm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hdiff
    have hdp : d ∈ p :=
      (hpprime.mem_or_mem (hd ▸ p.sub_mem ha (p.mul_mem_left c hbp))).resolve_left hxp
    have hdsmul : a - c * b ∈ Ideal.span {x} • p := by
      rw [hd]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hdp
    rw [← sub_add_cancel a (c * b)]
    exact (Ideal.span {b} ⊔ Ideal.span {x} • p).add_mem
      (Submodule.mem_sup_right hdsmul)
      (Submodule.mem_sup_left
        ((Ideal.span {b}).mul_mem_left c (Ideal.mem_span_singleton_self b)))
  have hp_le : p ≤ Ideal.span {b} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot p.fg_of_isNoetherianRing
      (I := Ideal.span {x})
      (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
        exact (Ideal.span_singleton_le_iff_mem _).mpr hxm)
      hle
  exact ⟨b, le_antisymm hp_le ((Ideal.span_singleton_le_iff_mem p).mpr hbp)⟩

/-- Every height-one prime of a regular local ring of dimension at most two is
principal, with the dimension-one and dimension-zero cases included. -/
theorem isPrincipal_of_height_eq_one_of_dimension_le_two (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R ≤ 2)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) : p.IsPrincipal := by
  have hn : (maximalIdeal R).spanFinrank ≤ 2 := by
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal.trans_le hd
  have hcases : (maximalIdeal R).spanFinrank ≤ 1 ∨ (maximalIdeal R).spanFinrank = 2 := by
    omega
  rcases hcases with hsmall | htwo
  · let : IsPrincipalIdealRing R :=
      isPrincipalIdealRing_of_regularLocal_dimension_le_one R (by
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
        exact_mod_cast hsmall)
    infer_instance
  · have hd2 : ringKrullDim R = 2 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, htwo]
      rfl
    apply isPrincipal_of_prime_ne_maximalIdeal_of_dimension_two R hd2 p
    intro hpm
    have hheight := maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [← hpm, hp, hd2] at hheight
    norm_num at hheight

/-- A nonzero nonmaximal prime in a two-dimensional regular local ring has a
singleton basis as the actual ideal module. -/
def primeIdealBasisOfDimensionTwo (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 2) (p : Ideal R) [p.IsPrime]
    (hpm : p ≠ maximalIdeal R) (hp : p ≠ ⊥) : Basis PUnit.{u + 1} R p := by
  let : p.IsPrincipal := isPrincipal_of_prime_ne_maximalIdeal_of_dimension_two R hd p hpm
  let a := Submodule.IsPrincipal.generator p
  have ha : p = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator p).symm
  have ha0 : a ≠ 0 := by
    intro hzero
    exact hp (by rw [ha, hzero, Ideal.span_singleton_zero])
  exact Ideal.regularPrincipalIdealBasis p a
    (isSMulRegular_of_regularLocal_ne_zero R a ha0) ha

/-- A height-one prime in dimension at most two has a singleton basis as its
actual ideal module. Its nonvanishing follows from regular-local domainness. -/
def heightOneIdealBasisOfDimensionLETwo (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R ≤ 2) (p : Ideal R) [p.IsPrime]
    (hp : p.height = 1) : Basis PUnit.{u + 1} R p := by
  let : IsDomain R := isDomain_of_regularLocal R
  let : p.IsPrincipal := isPrincipal_of_height_eq_one_of_dimension_le_two R hd p hp
  let a := Submodule.IsPrincipal.generator p
  have ha : p = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator p).symm
  have ha0 : a ≠ 0 := by
    intro hzero
    exact (Ideal.ne_bot_of_height_eq_one hp) (by rw [ha, hzero, Ideal.span_singleton_zero])
  exact Ideal.regularPrincipalIdealBasis p a
    (isSMulRegular_of_regularLocal_ne_zero R a ha0) ha

end IsRegularLocalRing
