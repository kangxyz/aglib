/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormRestrictionKernel

/-!
# Actual finite-field restriction-kernel consumers

The hypotheses require finite separability, not characteristic zero. No
canonical transfer or norm is supplied. The degree-one test is the only
injectivity assertion; arbitrary degree gives its precise torsion bound.
-/

@[expose] public noncomputable section

namespace AglibTest.PolynomialNormRestrictionKernel

open MilnorK.K2

variable (k E : Type*) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- The auxiliary map is constructed from the actual finite field extension. -/
theorem actual_degree_retraction :
    ∃ T : MilnorK.K2.Group E →ₗ[ℤ] MilnorK.K2.Group k,
      ∀ x : MilnorK.K2.Group k, T (map (algebraMap k E) x) = (Module.finrank k E : ℤ) • x :=
  exists_degree_retraction k E

/-- Only the original extension degree is asserted to kill the restriction kernel. -/
theorem actual_kernel_degree (x : MilnorK.K2.Group k) (hx : map (algebraMap k E) x = 0) :
    (Module.finrank k E : ℤ) • x = 0 :=
  finrank_smul_eq_zero_of_map_eq_zero k E x hx

/-- A residue ramification annihilator may be any integer, including zero or negative. -/
theorem actual_torsion_bound (e : ℤ) (x : MilnorK.K2.Group k)
    (hx : e • map (algebraMap k E) x = 0) :
    (e * (Module.finrank k E : ℤ)) • x = 0 :=
  mul_finrank_smul_eq_zero_of_smul_map_eq_zero k E e x hx

/-- Degree one specializes the proved kernel bound to actual injectivity. -/
theorem degree_one_injective (h : Module.finrank k E = 1) :
    Function.Injective (map (algebraMap k E)) := by
  intro x y hxy
  have hz : map (algebraMap k E) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hzero := finrank_smul_eq_zero_of_map_eq_zero k E (x - y) hz
  simpa only [h, Nat.cast_one, one_smul, sub_eq_zero] using hzero

/-- The same result applies to finite extensions in residue characteristic zero. -/
theorem residue_characteristic_zero {F L : Type*} [Field F] [Field L] [CharZero F]
    [Algebra F L] [FiniteDimensional F L] (x : MilnorK.K2.Group F)
    (hx : map (algebraMap F L) x = 0) : (Module.finrank F L : ℤ) • x = 0 :=
  finrank_smul_eq_zero_of_map_eq_zero F L x hx

open Lean in
run_cmd do
  for name in #[``exists_degree_retraction, ``finrank_smul_eq_zero_of_map_eq_zero,
      ``mul_finrank_smul_eq_zero_of_smul_map_eq_zero,
      ``actual_degree_retraction, ``actual_kernel_degree, ``actual_torsion_bound,
      ``degree_one_injective, ``residue_characteristic_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite separable K2 restriction annihilators use only standard foundations."

end AglibTest.PolynomialNormRestrictionKernel
