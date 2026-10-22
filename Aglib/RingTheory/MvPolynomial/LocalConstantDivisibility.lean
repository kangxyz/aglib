/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Recovering divisibility of a constant from a local point

When the linear coefficients and nonlinear correction vanish modulo a generator of the
source maximal ideal, a point over a local target forces the constant to vanish as well.
The source residue field embeds in the target residue field through the actual local map.
Neither separability nor regularity of the generator is needed for this step.
-/

@[expose] public section

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A map from a local ring with principal maximal ideal is local when the chosen
generator maps into the target maximal ideal. In particular this applies to compatible
uniformizers of discrete valuation rings. -/
theorem isLocalHom_of_maximalIdeal_eq_span (ψ : R →+* S) (p : R)
    (hp : maximalIdeal R = Ideal.span {p}) (hψp : ψ p ∈ maximalIdeal S) :
    IsLocalHom ψ := by
  apply ((local_hom_TFAE ψ).out 1 4).mpr
  rw [hp]
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl : x = p := Set.mem_singleton_iff.mp hx
  exact hψp

end IsLocalRing

namespace MvPolynomial

variable {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ]
variable [IsLocalRing R] [IsLocalRing S]

/-- A vanishing point forces the constant of an affine-linear polynomial with a scaled
remainder to be divisible by the generator of the source maximal ideal, provided all
linear coefficients are already divisible. The target need not be a DVR. -/
theorem dvd_constant_of_local_eval₂Hom_eq_zero
    (ψ : R →+* S) [IsLocalHom ψ] (p c : R) (a : σ → R)
    (g Q : MvPolynomial σ R) (z : σ → S)
    (hp : IsLocalRing.maximalIdeal R = Ideal.span {p})
    (ha : ∀ j, a j ∈ Ideal.span {p})
    (hg : g = C c + (∑ j, C (a j) * X j) + C p * Q)
    (hpoint : eval₂Hom ψ z g = 0) : p ∣ c := by
  have hpR : p ∈ IsLocalRing.maximalIdeal R := by
    rw [hp]
    exact Ideal.subset_span (Set.mem_singleton p)
  have hpzero : IsLocalRing.residue S (ψ p) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (map_nonunit ψ p hpR)
  have hazero : ∀ j, IsLocalRing.residue S (ψ (a j)) = 0 := by
    intro j
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply map_nonunit ψ
    rw [hp]
    exact ha j
  have hcS : IsLocalRing.residue S (ψ c) = 0 := by
    have h := congrArg (IsLocalRing.residue S) hpoint
    simpa only [hg, map_add, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X',
      hazero, hpzero, zero_mul, Finset.sum_const_zero, add_zero, map_zero] using h
  have hcR : IsLocalRing.residue R c = 0 := by
    apply (IsLocalRing.ResidueField.map ψ).injective
    simpa only [IsLocalRing.ResidueField.map_residue, map_zero] using hcS
  apply Ideal.mem_span_singleton.mp
  rw [← hp]
  exact (IsLocalRing.residue_eq_zero_iff _).mp hcR

end MvPolynomial
