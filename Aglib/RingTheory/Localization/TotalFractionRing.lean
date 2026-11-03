/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian total quotient rings of reduced Noetherian rings

A maximal ideal of a Noetherian total quotient ring is associated. In a
reduced ring its annihilator witness shows that no smaller prime exists.
Thus the total quotient ring is zero-dimensional and Artinian. This concerns
the actual total quotient ring, not a generic fibre of a different algebra.
-/

@[expose] public noncomputable section

universe u v

namespace IsFractionRing

/-- A reduced Noetherian ring which is its own total quotient ring has
Krull dimension zero. -/
theorem krullDimLE_zero_of_isReduced
    (F : Type u) [CommRing F] [IsNoetherianRing F] [IsReduced F]
    [IsFractionRing F F] : Ring.KrullDimLE 0 F := by
  apply Ring.KrullDimLE.mk₀
  intro p hp
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
  let : m.IsMaximal := hm
  have hass : IsAssociatedPrime m F :=
    Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing F m
  obtain ⟨_, x, hmx⟩ := isAssociatedPrime_iff.mp hass
  have hmem (a : F) : a ∈ m ↔ a * x = 0 := by
    rw [hmx]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hx0 : x ≠ 0 := by
    intro hx
    apply hm.ne_top
    rw [hmx, hx, Submodule.colon_singleton_zero]
  have hxm : x ∉ m := by
    intro hx
    apply hx0
    exact IsReduced.eq_zero x ⟨2, by simpa only [pow_two] using (hmem x).mp hx⟩
  have hxp : x ∉ p := fun hx => hxm (hpm hx)
  have hmp : m ≤ p := by
    intro a ha
    have hmul : a * x ∈ p := by
      rw [(hmem a).mp ha]
      exact p.zero_mem
    exact (hp.mem_or_mem hmul).resolve_right hxp
  have hpm_eq : p = m := le_antisymm hpm hmp
  exact hpm_eq.symm ▸ hm

/-- The supplied genuine total quotient ring of a reduced Noetherian ring
is Artinian, retaining its original coefficient algebra. -/
theorem isArtinianRing_of_isReduced
    (R : Type u) (F : Type v) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    [CommRing F] [Algebra R F] [IsFractionRing R F] : IsArtinianRing F := by
  let : IsNoetherianRing F :=
    IsLocalization.isNoetherianRing (nonZeroDivisors R) F inferInstance
  let e : F ≃ₐ[R] FractionRing R :=
    IsLocalization.algEquiv (nonZeroDivisors R) F (FractionRing R)
  let : IsReduced F := isReduced_of_injective e e.injective
  let : IsFractionRing F F := IsFractionRing.idem R F
  let : Ring.KrullDimLE 0 F := krullDimLE_zero_of_isReduced F
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

end IsFractionRing

/-- In particular, the native `FractionRing R` is Artinian for a reduced
Noetherian ring R. No domain hypothesis is necessary. -/
theorem FractionRing.isArtinianRing_of_isReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] :
    IsArtinianRing (FractionRing R) :=
  IsFractionRing.isArtinianRing_of_isReduced R (FractionRing R)
