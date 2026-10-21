/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The tensor algebra action associated to commuting scalar actions -/

@[expose] public noncomputable section

open scoped TensorProduct
universe u v w z z'
namespace Algebra.TensorProduct
variable (A : Type u) (B : Type v) (S : Type w) (N : Type z)
  [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
  [AddCommGroup N] [Module A N] [Module B N] [Module S N]
  [IsScalarTower A B N] [IsScalarTower A S N] [SMulCommClass B S N]

/-- The original commuting representations induce the canonical tensor representation. -/
def commutingActionHom : B ⊗[A] S →ₐ[A] Module.End A N :=
  lift (Algebra.lsmul A A N : B →ₐ[A] Module.End A N)
    (Algebra.lsmul A A N : S →ₐ[A] Module.End A N) fun b s => by
      ext x
      exact smul_comm b s x

/-- No new action is chosen: restriction of scalars along the canonical representation. -/
@[instance_reducible]
def commutingModule : Module (B ⊗[A] S) N :=
  Module.compHom N (commutingActionHom A B S N).toRingHom

lemma commutingModule_tmul_smul (b : B) (s : S) (x : N) :
    let := commutingModule A B S N
    (b ⊗ₜ[A] s) • x = b • s • x := rfl

/-- The tensor action retains the original affine-coordinate scalar action. -/
lemma commutingModule_scalarTower_left :
    let := commutingModule A B S N
    IsScalarTower B (B ⊗[A] S) N := by
  let := commutingModule A B S N
  apply IsScalarTower.of_algebraMap_smul
  intro b x
  change b • ((1 : S) • x) = b • x
  rw [one_smul]

/-- The tensor action retains the original base scalar action. -/
lemma commutingModule_scalarTower_base :
    let := commutingModule A B S N
    IsScalarTower A (B ⊗[A] S) N := by
  let := commutingModule A B S N
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  change commutingActionHom A B S N (algebraMap A (B ⊗[A] S) a) x = a • x
  rw [AlgHom.commutes]
  rfl

variable {N} {P : Type z'} [AddCommGroup P] [Module A P] [Module B P] [Module S P]
  [IsScalarTower A B P] [IsScalarTower A S P] [SMulCommClass B S P]

/-- Intertwining the two original actions intertwines the tensor action.
This applies to restriction maps on affine charts without a localization-flatness premise. -/
lemma commutingActionHom_naturality (f : N →ₗ[A] P)
    (hb : ∀ (b : B) x, f (b • x) = b • f x)
    (hs : ∀ (s : S) x, f (s • x) = s • f x)
    (t : B ⊗[A] S) (x : N) :
    f (commutingActionHom A B S N t x) = commutingActionHom A B S P t (f x) := by
  induction t using TensorProduct.inductionOn with
  | tmul b s => exact (hb b (s • x)).trans (congrArg (b • ·) (hs s x))
  | add t u ht hu => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht hu

end Algebra.TensorProduct
