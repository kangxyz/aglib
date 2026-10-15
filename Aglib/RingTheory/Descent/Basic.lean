/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Etale.Descent

/-! Explicit effective descent of commutative algebras in coaction form.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.FaithfullyFlatAlgebraDescent` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`3426f90de31fb5831c17c911468f6553022fed0c2fdb4a5651e119e21009d7ca`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.TensorProduct

namespace Algebra.Descent

universe u v w
variable (R : Type u) (S : Type v) (B : Type w)
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- The counit multiplies the scalar into the algebra element. -/
def counit : S ⊗[R] B →ₐ[S] B :=
  AlgHom.liftEquiv R S B B (AlgHom.id R B)

@[simp] lemma counit_tmul (s : S) (b : B) : counit R S B (s ⊗ₜ[R] b) = s • b := rfl

/-- Algebra descent data in coaction form: multiplicative coaction, counit,
and the cocycle equation written as coassociativity. -/
structure Datum where
  /-- The S-algebra coaction from B to S ⊗[R] B. -/
  coaction : B →ₐ[S] S ⊗[R] B
  counit_coaction : (counit R S B).comp coaction = AlgHom.id S B
  coassoc :
    (Algebra.TensorProduct.map (AlgHom.id S S) (coaction.restrictScalars R)).comp coaction =
    (Algebra.TensorProduct.map (AlgHom.id S S)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)).comp coaction

variable {R S B}
namespace Datum
variable (D : Datum R S B)

/-- The descended algebra is the actual equalizer subalgebra. -/
def invariants : Subalgebra R B :=
  AlgHom.equalizer (D.coaction.restrictScalars R) Algebra.TensorProduct.includeRight

@[simp] lemma mem_invariants (b : B) : b ∈ D.invariants ↔ D.coaction b = 1 ⊗ₜ[R] b := Iff.rfl

/-- The reconstruction map sends `s ⊗ a` to `s * a`. -/
def baseChange : S ⊗[R] D.invariants →ₐ[S] B :=
  AlgHom.liftEquiv R S D.invariants B D.invariants.val

@[simp] lemma baseChange_tmul (s : S) (a : D.invariants) :
    D.baseChange (s ⊗ₜ[R] a) = s • (a : B) := rfl

/-- The R-linear tensor extension of the inclusion of the invariant subalgebra into B. -/
def tensorInclusion : S ⊗[R] D.invariants →ₗ[R] S ⊗[R] B :=
  D.invariants.val.toLinearMap.lTensor S

@[simp] lemma tensorInclusion_tmul (s : S) (a : D.invariants) :
    D.tensorInclusion (s ⊗ₜ[R] a) = s ⊗ₜ[R] (a : B) := rfl

lemma coaction_baseChange (z : S ⊗[R] D.invariants) :
    D.coaction (D.baseChange z) = D.tensorInclusion z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul s a =>
    rw [baseChange_tmul, map_smul, (D.mem_invariants a).1 a.property]
    simp [_root_.TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

lemma counit_tensorInclusion (z : S ⊗[R] D.invariants) :
    counit R S B (D.tensorInclusion z) = D.baseChange z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy => simp [hx, hy]

/-- The R-linear difference between the coaction and the canonical right tensor inclusion. -/
def difference : B →ₗ[R] S ⊗[R] B :=
  (D.coaction.restrictScalars R).toLinearMap -
    (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toLinearMap

lemma exact_invariants_difference : Function.Exact D.invariants.val.toLinearMap D.difference := by
  intro b
  constructor
  · intro hb
    exact ⟨⟨b, by simpa [difference, sub_eq_zero] using hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    change D.coaction a - (1 ⊗ₜ[R] (a : B)) = 0
    exact sub_eq_zero.mpr ((D.mem_invariants a).1 a.property)

lemma difference_tensor_coaction (b : B) :
    D.difference.lTensor S (D.coaction b) = 0 := by
  rw [difference, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
  exact congrArg (fun f : B →ₐ[S] S ⊗[R] (S ⊗[R] B) => f b) D.coassoc

lemma baseChange_injective [Module.Flat R S] : Function.Injective D.baseChange := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap D.invariants.val.toLinearMap
    Subtype.val_injective
  change D.tensorInclusion x = D.tensorInclusion y
  rw [← D.coaction_baseChange x, ← D.coaction_baseChange y, h]

lemma baseChange_surjective [Module.Flat R S] : Function.Surjective D.baseChange := by
  intro b
  obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact S D.exact_invariants_difference (D.coaction b)).1
    (D.difference_tensor_coaction b)
  refine ⟨z, ?_⟩
  change D.tensorInclusion z = D.coaction b at hz
  rw [← D.counit_tensorInclusion z, hz]
  exact congrArg (fun f : B →ₐ[S] B => f b) D.counit_coaction

/-- Effective reconstruction from the equalizer. Flatness suffices for this
direction; faithful flatness is needed for recovering a base algebra and for
descending its properties. -/
def baseChangeEquiv [Module.Flat R S] : S ⊗[R] D.invariants ≃ₐ[S] B :=
  AlgEquiv.ofBijective D.baseChange ⟨D.baseChange_injective, D.baseChange_surjective⟩

@[simp] lemma baseChangeEquiv_tmul [Module.Flat R S] (s : S) (a : D.invariants) :
    D.baseChangeEquiv (s ⊗ₜ[R] a) = s • (a : B) := rfl

end Datum
end Algebra.Descent
