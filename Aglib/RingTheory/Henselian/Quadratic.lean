/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ComputeDegree

/-!
# Quadratic roots in a Henselian local ring

Relocated unchanged declarations from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original namespaces and explicit
source and hypothesis boundaries are retained.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Henselian/Quadratic.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9fa643e9feb45caee10585279d6e34dc8457c2b1b4487ee773566e7226fdab2f`.
-/

@[expose] public section

noncomputable section
open Polynomial IsLocalRing
universe u

namespace HenselianLocalRing

variable {R : Type u} [CommRing R]

/-- The local Henselian structure follows from actual maximal-ideal adic
completeness, using mathlib's proved complete-ring Hensel theorem. -/
theorem of_isAdicComplete [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a ha hd :=
    HenselianRing.is_henselian f hf a ha (hd.map (Ideal.Quotient.mk (maximalIdeal R)))

/-- A quadratic with unit linear coefficient and vanishing residue constant
has an actual root in the maximal ideal. No leading coefficient is inverted.
The proof reduces to the monic Hensel lemma already proved in mathlib. -/
theorem exists_quadratic_root_mem_maximalIdeal [HenselianLocalRing R]
    (a b c : R) (hb : IsUnit b) (hc : c ∈ maximalIdeal R) :
    ∃ x : R, a * x ^ 2 + b * x + c = 0 ∧ x ∈ maximalIdeal R := by
  let f : R[X] := X ^ 2 - C b * X + C (a * c)
  have hf : f.Monic := by dsimp [f]; monicity!
  have hfb : f.eval b ∈ maximalIdeal R := by
    have he : f.eval b = a * c := by simp [f]; ring
    rw [he]
    exact (maximalIdeal R).mul_mem_left a hc
  have hdfb : f.derivative.eval b = b := by
    simp [f, derivative_pow, derivative_mul]
    ring
  obtain ⟨z, hz, hzb⟩ := HenselianLocalRing.is_henselian f hf b hfb (by rw [hdfb]; exact hb)
  have hrzb : residue R z = residue R b := by
    have := (residue_eq_zero_iff _).mpr hzb
    simpa only [map_sub, sub_eq_zero] using this
  have hzu : IsUnit z := (residue_ne_zero_iff_isUnit z).mp
    (by rw [hrzb]; exact (residue_ne_zero_iff_isUnit b).mpr hb)
  obtain ⟨v, rfl⟩ := hzu
  have hz' : (v : R) ^ 2 - b * v + a * c = 0 := by
    simpa [Polynomial.IsRoot, f] using hz
  refine ⟨-c * ↑v⁻¹, ?_, ?_⟩
  · have hi : (v : R) * ↑v⁻¹ = 1 := v.mul_inv
    linear_combination c * (↑v⁻¹ : R) ^ 2 * hz' -
      c * ((v : R) * ↑v⁻¹ - b * ↑v⁻¹ + 1) * hi
  · exact (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).neg_mem hc)

end HenselianLocalRing

namespace IsLocalRing

variable {R : Type u} [CommRing R]

/-- A unit remains a unit after addition of an element of the maximal ideal. -/
theorem isUnit_add_of_mem_maximalIdeal [IsLocalRing R] (a b : R)
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_add, (residue_eq_zero_iff _).mpr hb, add_zero] using
    (residue_ne_zero_iff_isUnit _).mpr ha

end IsLocalRing
