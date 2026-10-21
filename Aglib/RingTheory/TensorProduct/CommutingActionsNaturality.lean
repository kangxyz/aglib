/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.CommutingActions

/-! # Naturality of commuting tensor actions under coordinate-ring restriction -/

@[expose] public noncomputable section

open scoped TensorProduct
universe u v v' w z z'
namespace Algebra.TensorProduct
variable (A : Type u) {B : Type v} {C : Type v'} (S : Type w)
  [CommRing A] [CommRing B] [CommRing C] [CommRing S]
  [Algebra A B] [Algebra A C] [Algebra A S]
  {N : Type z} {P : Type z'} [AddCommGroup N] [AddCommGroup P]
  [Module A N] [Module B N] [Module S N]
  [Module A P] [Module C P] [Module S P]
  [IsScalarTower A B N] [IsScalarTower A S N] [SMulCommClass B S N]
  [IsScalarTower A C P] [IsScalarTower A S P] [SMulCommClass C S P]

/-- A coordinate-semilinear restriction commuting with the original S action
intertwines the canonical tensor actions via the original coordinate-ring map. -/
lemma commutingActionHom_map_naturality (g : B →ₐ[A] C) (f : N →ₗ[A] P)
    (hb : ∀ (b : B) x, f (b • x) = g b • f x)
    (hs : ∀ (s : S) x, f (s • x) = s • f x)
    (t : B ⊗[A] S) (x : N) :
    f (commutingActionHom A B S N t x) =
      commutingActionHom A C S P (map g (AlgHom.id A S) t) (f x) := by
  induction t using TensorProduct.inductionOn with
  | tmul b s => exact (hb b (s • x)).trans (congrArg (g b • ·) (hs s x))
  | add t u ht hu => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht hu

/-- The same naturality stated literally for the induced module actions. -/
lemma commutingModule_map_smul (g : B →ₐ[A] C) (f : N →ₗ[A] P)
    (hb : ∀ (b : B) x, f (b • x) = g b • f x)
    (hs : ∀ (s : S) x, f (s • x) = s • f x)
    (t : B ⊗[A] S) (x : N) :
    let := commutingModule A B S N
    let := commutingModule A C S P
    f (t • x) = map g (AlgHom.id A S) t • f x :=
  commutingActionHom_map_naturality A S g f hb hs t x

end Algebra.TensorProduct
