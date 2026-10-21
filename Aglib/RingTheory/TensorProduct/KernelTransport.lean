/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.TransferInstance

/-! # Actual scalar laws on a tensor-kernel module transported along its original inclusion -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.TensorProduct
universe u v w x y z
variable {A : Type u} {B : Type v} {S : Type w}
  [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
  {M : Type x} {N : Type y} {P : Type z}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module B M] [Module B N] [Module S N]
  [Module (B ⊗[A] S) N] [Module (B ⊗[A] S) P]
  (q : N →ₗ[B ⊗[A] S] P) (e : M ≃+ q.ker) (i : M →ₗ[B] N)
  (he : ∀ x, (e x : N) = i x)

/-- Transport of the actual tensor-kernel module to its original additive coordinates. -/
@[instance_reducible]
def kernelTransportModule : Module (B ⊗[A] S) M := e.module (B ⊗[A] S)

/-- The associated scalar action is restriction along the original right tensor inclusion. -/
@[instance_reducible]
def kernelTransportScalarModule : Module S M := by
  letI := kernelTransportModule q e
  exact Module.compHom M (includeRight : S →ₐ[A] B ⊗[A] S).toRingHom

include he in
omit [Module S N] in
theorem kernelTransportModule_inclusion (t : B ⊗[A] S) (x : M) :
    letI := kernelTransportModule q e
    i (t • x) = t • i x := by
  let := kernelTransportModule q e
  have h := congrArg (fun z : q.ker => (z : N)) ((e.linearEquiv (B ⊗[A] S)).map_smul t x)
  change (e (t • x) : N) = t • (e x : N) at h
  simpa only [he] using h

variable (htmul : ∀ (b : B) (s : S) (x : N), (b ⊗ₜ[A] s) • x = b • s • x)

include he htmul in
theorem kernelTransportScalarModule_inclusion (s : S) (x : M) :
    letI := kernelTransportScalarModule q e
    i (s • x) = s • i x := by
  let := kernelTransportModule q e
  let := kernelTransportScalarModule q e
  change i (((1 : B) ⊗ₜ[A] s) • x) = _
  rw [kernelTransportModule_inclusion q e i he, htmul, one_smul]

include he htmul in
/-- The transported tensor action retains the original coordinate action. -/
theorem kernelTransportModule_tmul_smul (hi : Function.Injective i)
    (b : B) (s : S) (x : M) :
    letI := kernelTransportModule q e
    letI := kernelTransportScalarModule q e
    (b ⊗ₜ[A] s) • x = b • s • x := by
  let := kernelTransportModule q e
  let := kernelTransportScalarModule q e
  apply hi
  rw [kernelTransportModule_inclusion q e i he, htmul, map_smul,
    kernelTransportScalarModule_inclusion q e i he htmul]

include he htmul in
/-- An actual scalar square on the original inclusion determines the
transported scalar action, without comparing implementation-specific instances. -/
theorem kernelTransportScalarModule_smul_eq (hi : Function.Injective i)
    (s : S) (x y : M) (hy : i y = s • i x) :
    letI := kernelTransportScalarModule q e
    s • x = y := by
  let := kernelTransportScalarModule q e
  apply hi
  rw [kernelTransportScalarModule_inclusion q e i he htmul, hy]

end Algebra.TensorProduct
