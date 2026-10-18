/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRCartierLength

/-!
# Consumers of actual DVR Cartier lengths

Unit multiples and repeated powers have their full normalized multiplicity.
The infinite order of zero is explicitly excluded by the production API.
-/

@[expose] public noncomputable section

namespace AglibTest.DVRCartierLength

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The literal scalar may be any unit multiple of any uniformizer power. -/
theorem unitMultiplePower (u : Rˣ) (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length R (R ⧸ Ideal.ofList [(u : R) * ϖ ^ n]) = (n : ℕ∞) := by
  rw [length_quotient_ofList_eq_addVal _ (mul_ne_zero u.ne_zero (pow_ne_zero n hϖ.ne_zero)),
    addVal_def' u hϖ]

/-- A double zero has length two, not the length of its reduction. -/
theorem doubleUniformizer (ϖ : R) (hϖ : Irreducible ϖ) :
    Module.length R (R ⧸ Ideal.ofList [ϖ ^ 2]) = (2 : ℕ∞) := by
  rw [length_quotient_ofList_eq_addVal _ (pow_ne_zero 2 hϖ.ne_zero), hϖ.addVal_pow]
  rfl

/-- No toNat conversion is needed to establish finiteness. -/
theorem actualFiniteLength (t : R) (ht : t ≠ 0) :
    Module.length R (R ⧸ Ideal.ofList [t]) ≠ ⊤ := by
  rw [length_quotient_ofList_eq_addVal t ht]
  exact addVal_eq_top_iff.not.mpr ht

open Lean in
run_cmd do
  for name in #[``length_quotient_span_eq_addVal, ``length_quotient_ofList_eq_addVal,
      ``unitMultiplePower, ``doubleUniformizer, ``actualFiniteLength] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual DVR Cartier lengths use only standard foundations."

end AglibTest.DVRCartierLength
