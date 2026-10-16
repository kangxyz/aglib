/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases and regular generators of actual principal ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open LinearMap
open Module

section
namespace Ideal

/-- A nonzero ideal in a principal domain has an actual singleton basis. -/
def principalIdealBasis {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (I : Ideal R) (hI : I ≠ ⊥) : Basis PUnit.{u + 1} R I := by
  let a := Submodule.IsPrincipal.generator I
  have ha : I = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator I).symm
  have hane : a ≠ 0 := by
    intro h
    apply hI
    rw [ha, h, Ideal.span_singleton_zero]
  exact (Basis.singleton PUnit R).map
    ((LinearEquiv.toSpanNonzeroSingleton R R a hane).trans
      (LinearEquiv.ofEq _ _ ha.symm))

/-- A regular principal generator supplies an actual singleton basis, even
over nonreduced rings or the zero ring. -/
def regularPrincipalIdealBasis {R : Type u} [CommRing R] (I : Ideal R)
    (a : R) (ha : IsSMulRegular R a) (hI : I = Ideal.span {a}) :
    Basis PUnit.{u + 1} R I := by
  let aI : I := ⟨a, hI ▸ Ideal.mem_span_singleton_self a⟩
  let f := LinearMap.toSpanSingleton R I aI
  have hi : Function.Injective f := by
    intro x y hxy
    apply ha
    simpa only [f, aI, LinearMap.toSpanSingleton_apply, Submodule.coe_smul_of_tower,
      smul_eq_mul, mul_comm] using congrArg Subtype.val hxy
  have hs : Function.Surjective f := by
    intro x
    have hx : x.val ∈ Ideal.span {a} := by rw [← hI]; exact x.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨r, Subtype.ext hr⟩
  exact (Basis.singleton PUnit R).map (LinearEquiv.ofBijective f ⟨hi, hs⟩)

/-- A rank-one presentation of an ideal supplies an actual regular principal generator. -/
theorem ideal_exists_regular_generator {R : Type u} [CommRing R]
    (I : Ideal R) (e : I ≃ₗ[R] R) :
    ∃ a : R, IsSMulRegular R a ∧ I = Ideal.span {a} := by
  let a : I := e.symm 1
  have he (r : R) : e.symm r = r • a := by
    dsimp [a]
    rw [← map_smul, smul_eq_mul, mul_one]
  refine ⟨a.val, ?_, ?_⟩
  · intro r s hrs
    apply e.symm.injective
    rw [he, he]
    apply Subtype.ext
    simpa only [Submodule.coe_smul_of_tower, smul_eq_mul, mul_comm] using hrs
  · apply le_antisymm
    · intro x hx
      rw [Ideal.mem_span_singleton']
      refine ⟨e ⟨x, hx⟩, ?_⟩
      have hh := congrArg Subtype.val (he (e ⟨x, hx⟩))
      simpa using hh.symm
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a.property)

end Ideal
end
