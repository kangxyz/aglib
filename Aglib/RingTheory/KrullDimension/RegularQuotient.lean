/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Dimension drop for regular kernel elements

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open LinearMap
open scoped nonZeroDivisors

section
namespace RingHom

/-- A regular element in the kernel of a quotient of a dimension-at-most-one ring
makes the quotient zero-dimensional. No Noetherian hypothesis is required. -/
theorem quotient_krullDimLE_zero_of_regular_kernel_element
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hdim : ringKrullDim R ≤ 1)
    (a : R) (ha : IsSMulRegular R a) (hazero : f a = 0) : Ring.KrullDimLE 0 S := by
  have hreg : a ∈ R⁰ := mem_nonZeroDivisors_iff_left.mpr fun r hr ↦
    ha (by simpa only [smul_eq_mul, mul_zero] using hr)
  have hdrop := (ringKrullDim_succ_le_of_surjective f hf hreg hazero).trans hdim
  rw [Ring.krullDimLE_iff]
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  simpa using hdrop

/-- The corresponding Noetherian quotient is Artinian. -/
theorem quotient_isArtinianRing_of_regular_kernel_element
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (hf : Function.Surjective f) (hdim : ringKrullDim R ≤ 1)
    (a : R) (ha : IsSMulRegular R a) (hazero : f a = 0) : IsArtinianRing S := by
  let : IsNoetherianRing S := isNoetherianRing_of_surjective R S f hf
  exact isArtinianRing_iff_krullDimLE_zero.mpr
    (_root_.RingHom.quotient_krullDimLE_zero_of_regular_kernel_element f hf hdim a ha hazero)

end RingHom
end
