/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Swapping regular pairs

For two ambient regular scalars on a module, regularity modulo the first scalar
implies regularity in the opposite order. Over a domain, properness of the pair
and regularity modulo the first scalar supply regularity of the second scalar.
Neither result requires localness or Noetherianity. The intended consumer is the
one-pole raw chart and gluing construction for rational surface singularities.
-/

@[expose] public noncomputable section

open scoped Pointwise

universe u v

namespace IsSMulRegular

/-- Two ambient regular scalars can be swapped in a regular pair on any module. -/
theorem quotSMulTop_swap {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {x y : R}
    (hx : IsSMulRegular M x) (hy : IsSMulRegular M y)
    (hxy : IsSMulRegular (QuotSMulTop x M) y) :
    IsSMulRegular (QuotSMulTop y M) x := by
  rw [hx.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul, inf_comm, smul_comm]
  exact (hy.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul _).mp hxy

/-- A proper regular pair over a domain is regular in the opposite order. -/
theorem proper_pair_swap_of_isDomain {R : Type u} [CommRing R] [IsDomain R]
    (x y : R) (hx : IsSMulRegular R x)
    (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
    (hproper : Ideal.span {x, y} ≠ ⊤) :
    IsSMulRegular R y ∧ IsSMulRegular (R ⧸ Ideal.span {y}) x := by
  have hxproper : Ideal.span {x} ≠ (⊤ : Ideal R) := by
    intro htop
    apply hproper
    apply top_unique
    rw [← htop]
    exact Ideal.span_mono (by simp)
  let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxproper
  have hy0 : y ≠ 0 := by
    intro hzero
    subst y
    exact IsSMulRegular.not_zero hy
  have hy' : IsSMulRegular R y := IsSMulRegular.of_ne_zero hy0
  have hquot (r : R) : r • (⊤ : Submodule R R) = Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let ex : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
    Submodule.quotEquivOfEq _ _ (hquot x)
  let ey : QuotSMulTop y R ≃ₗ[R] R ⧸ Ideal.span {y} :=
    Submodule.quotEquivOfEq _ _ (hquot y)
  exact ⟨hy', (ey.isSMulRegular_congr x).mp
    (hx.quotSMulTop_swap hy' ((ex.isSMulRegular_congr y).mpr hy))⟩

end IsSMulRegular
