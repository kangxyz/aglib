/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Tensor
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Principal quotient as the actual cokernel of multiplication and cyclic tensor criterion

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 157–179.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra
variable {R : Type*} [CommRing R]
open Module.Flat
section PrincipalQuotient
variable {S : Type*} [CommRing S] [Algebra R S]

/-- The actual multiplication map has the principal-ideal quotient as cokernel. -/
theorem mulLeft_quotient_exact (a : S) :
    Function.Exact (LinearMap.mulLeft R a)
      (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap := by
  intro x
  change Ideal.Quotient.mk (Ideal.span {a}) x = 0 ↔ ∃ y, a * y = x
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simp only [dvd_def, eq_comm]

/-- A principal equation on a flat algebra is regular with flat quotient exactly
when its multiplication map stays injective after every cyclic base change.
This criterion is valid over arbitrary, possibly non-Noetherian rings. -/
theorem regular_and_flat_principal_quotient_iff [Module.Flat R S] (a : S) :
    (IsSMulRegular S a ∧ Module.Flat R (S ⧸ Ideal.span {a})) ↔
      ∀ I : Ideal R, Function.Injective ((LinearMap.mulLeft R a).lTensor (R ⧸ I)) :=
  injective_and_flat_iff_lTensor_quotient_injective (LinearMap.mulLeft R a)
    (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap (mulLeft_quotient_exact a)
    (Ideal.Quotient.mkₐ_surjective R _)

end PrincipalQuotient

end Algebra
