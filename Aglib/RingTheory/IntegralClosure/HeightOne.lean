/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Tactic.Ring

/-!
# Height-one obstructions to integral fractions

In a normal Noetherian local domain, a fraction outside the ring whose product with the
maximal ideal lies in the ring forces that maximal ideal to be principal. This is the
local determinant-trick input for codimension-one reconstruction.

The determinant argument refines the proof of
`maximalIdeal_isPrincipal_of_isDedekindDomain` in Mathlib's
`RingTheory/DiscreteValuationRing/TFAE.lean`: the fraction-multiplier hypothesis replaces
the dimension-one assumption used there to construct the fraction.
-/

@[expose] public section

noncomputable section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonintegral fraction multiplying the maximal ideal into the ring forces the maximal
ideal of a normal Noetherian local domain to be principal. -/
theorem maximalIdeal_isPrincipal_of_fraction (x : K)
    (hx : x ∉ Set.range (algebraMap R K))
    (hmul : ∀ r ∈ maximalIdeal R, x * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    (maximalIdeal R).IsPrincipal := by
  classical
  by_cases hm : maximalIdeal R = ⊥
  · rw [hm]
    infer_instance
  let N := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hN : N ≠ ⊥ := by
    obtain ⟨r, hr, hr0⟩ := (Submodule.ne_bot_iff _).mp hm
    rw [Submodule.ne_bot_iff]
    exact ⟨algebraMap R K r, ⟨r, hr, rfl⟩, by simpa using (IsFractionRing.injective R K).ne hr0⟩
  by_cases hstable : ∀ y ∈ N, x * y ∈ N
  · have hint : IsIntegral R x := isIntegral_of_smul_mem_submodule N hN
      ((IsNoetherian.noetherian _).map _) x hstable
    exact (hx (IsIntegrallyClosed.algebraMap_eq_of_integral hint)).elim
  · have htop : (N.map (DistribSMul.toLinearMap R K x)).comap
        (Algebra.linearMap R K) = ⊤ := by
      contrapose! hstable with hproper
      rintro z ⟨r, hr, rfl⟩
      obtain ⟨a, ha⟩ := hmul r hr
      exact ⟨a, le_maximalIdeal hproper ⟨_, ⟨r, hr, rfl⟩, ha.symm⟩, ha⟩
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ maximalIdeal R, x * algebraMap R K y = 1 := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
      obtain ⟨_, ⟨y, hy, rfl⟩, he⟩ := htop
      exact ⟨y, hy, by simpa using he⟩
    refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
    · intro r hr
      obtain ⟨a, ha⟩ := hmul r hr
      apply Ideal.mem_span_singleton.mpr
      refine ⟨a, (IsFractionRing.injective R K) ?_⟩
      rw [map_mul, ha]
      calc
        algebraMap R K r = (x * algebraMap R K y) * algebraMap R K r := by
          rw [hxy, one_mul]
        _ = algebraMap R K y * (x * algebraMap R K r) := by ring
    · exact (Ideal.span_singleton_le_iff_mem _).mpr hy

/-- Such a fraction can only occur in local dimension at most one. -/
theorem maximalIdeal_height_le_one_of_fraction (x : K)
    (hx : x ∉ Set.range (algebraMap R K))
    (hmul : ∀ r ∈ maximalIdeal R, x * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    (maximalIdeal R).height ≤ 1 := by
  let : (maximalIdeal R).IsPrincipal := maximalIdeal_isPrincipal_of_fraction K x hx hmul
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (maximalIdeal R) (maximalIdeal R)
    (by simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff])

end IsLocalRing
