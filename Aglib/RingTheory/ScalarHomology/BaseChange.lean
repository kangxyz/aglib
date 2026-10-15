/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.ScalarHomology.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Scalar homology under coefficient change

Flat scalar extension preserves the actual scalar kernel. Scalar cokernels commute with
arbitrary commutative scalar extension, without flatness. Restriction equivalences retain the
specified compatible scalar actions and scalar tower.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.LocalLength.PrincipalEulerScalarTransport` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`f3aef136d6013533d3a6e295159d993b7c0b3f74e1079bb8a7635f13a88e5fd4`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.

The two lower principal-submodule/cokernel helpers are transferred from
`R5Lab.KTheory.Grayson.Cycle.PrincipalFaceCokernel`:140–169 at the same revision,
source SHA-256 `3899115099799263e12a0de1fdd0cfb9e975e356e2ebedd14e5ed955641f5058`. No
application interfaces are transferred.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
open _root_.TensorProduct
universe u v w
variable {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
variable (M : Type w) [AddCommGroup M] [Module A M]

/-- Flat scalar extension preserves the actual scalar kernel. -/
def scalarKernelBaseChangeEquiv (B : Type*) [CommRing B] [Algebra A B]
    [Module.Flat A B] (t : A) :
    B ⊗[A] ScalarKernel M t ≃ₗ[B]
      ScalarKernel (B ⊗[A] M) (algebraMap A B t) := by
  let f := LinearMap.lsmul A M t
  let e := LinearMap.tensorKerEquiv B B f
  have hf : AlgebraTensorModule.lTensor B B f =
      LinearMap.lsmul B (B ⊗[A] M) (algebraMap A B t) := by
    apply LinearMap.ext
    intro x
    induction x using _root_.TensorProduct.inductionOn with
    | tmul b m =>
      change b ⊗ₜ[A] (t • m) = (algebraMap A B t) • (b ⊗ₜ[A] m)
      rw [_root_.TensorProduct.tmul_smul, algebraMap_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hf] at e
  exact e

variable [Module D M] [IsScalarTower A D M]

/-- Changing to the quotient scalar ring preserves the underlying scalar kernel. -/
def scalarKernelRestrictionEquiv (t : A) :
    ScalarKernel M t ≃ₗ[A] ScalarKernel M (algebraMap A D t) where
  toFun x := ⟨x.val, by
    simpa only [LinearMap.mem_ker, LinearMap.lsmul_apply, algebraMap_smul] using x.property⟩
  invFun x := ⟨x.val, by
    simpa only [LinearMap.mem_ker, LinearMap.lsmul_apply, algebraMap_smul] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Changing to the quotient scalar ring preserves the underlying scalar cokernel. -/
def scalarCokernelRestrictionEquiv (t : A) :
    ScalarCokernel M t ≃ₗ[A] ScalarCokernel M (algebraMap A D t) := by
  let f := LinearMap.lsmul D M (algebraMap A D t)
  have hf : LinearMap.lsmul A M t = f.restrictScalars A := by
    ext m
    exact (algebraMap_smul D t m).symm
  have hr : LinearMap.range (LinearMap.lsmul A M t) =
      (LinearMap.range f).restrictScalars A := by
    rw [hf, LinearMap.range_restrictScalars]
  exact (Submodule.quotEquivOfEq _ _ hr).trans
    (Submodule.Quotient.restrictScalarsEquiv A (LinearMap.range f))

end Module

namespace Module
universe u v w
variable {A : Type u} [CommRing A]
variable (N : Type w) [AddCommGroup N] [Module A N]

open scoped Pointwise in
/-- The principal ideal acting on N is the range of scalar multiplication by its generator.

Supporting helper for the module's explicit original principal-face/local-coefficient
source mapping. -/
theorem principalSubmodule_eq_range (t : A) :
    (Ideal.span ({t} : Set A)) • (⊤ : Submodule A N) =
      LinearMap.range (LinearMap.lsmul A N t) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext n
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp [LinearMap.mem_range]

/-- Quotient by a scalar commutes with arbitrary scalar extension; this is right exactness,
with no flatness assumption.

Source mapping: supporting local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded generic subset: principal quotients commute with arbitrary commutative scalar
extension A -> C, with no flatness premise. -/
def principalCokernelBaseChangeEquiv (C : Type*) [CommRing C] [Algebra A C] (t : A) :
    C ⊗[A] (N ⧸ LinearMap.range (LinearMap.lsmul A N t)) ≃ₗ[C]
      ((C ⊗[A] N) ⧸ LinearMap.range
        (LinearMap.lsmul C (C ⊗[A] N) (algebraMap A C t))) := by
  let I : Ideal A := Ideal.span ({t} : Set A)
  have hsrc : LinearMap.range (LinearMap.lsmul A N t) = I • ⊤ :=
    (principalSubmodule_eq_range N t).symm
  have htgt : I.map (algebraMap A C) • (⊤ : Submodule C (C ⊗[A] N)) =
      LinearMap.range (LinearMap.lsmul C (C ⊗[A] N) (algebraMap A C t)) := by
    change (Ideal.span ({t} : Set A)).map (algebraMap A C) • _ = _
    rw [Ideal.map_span, Set.image_singleton]
    exact principalSubmodule_eq_range _ _
  exact ((Submodule.quotEquivOfEq _ _ hsrc).baseChange A C _ _).trans
    ((_root_.TensorProduct.tensorQuotMapSMulEquivTensorQuot N C I).symm.trans
      (Submodule.quotEquivOfEq _ _ htgt))

end Module
