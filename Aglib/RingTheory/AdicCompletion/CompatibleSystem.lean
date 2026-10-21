/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.NatTower
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Compatible finite module systems

This algebraic interface uses the actual native inverse diagram and its native
compatible-section submodule. The original successor is required to be
surjective with the precise ideal-multiple kernel. In particular, the canonical
reduction equivalence records the original transition map.

The indexing includes the zero stage. Ring and coefficient universes are
independent. No effectivity, completeness, or Noetherianity is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)

/-- Finite coefficients with the original adic quotient transition at every stage. -/
structure IsCompatibleSystem : Prop where
  finite : ∀ n : ℕ, Module.Finite R (F.obj (op n))
  annihilated : ∀ (n : ℕ) (a : ↥(I ^ n)) (x : F.obj (op n)), (a : R) • x = 0
  surjective : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)
  ker_transition : ∀ n : ℕ,
    (F.map (homOfLE (Nat.le_succ n)).op).hom.ker =
      (I ^ n) • (⊤ : Submodule R (F.obj (op (n + 1))))

namespace IsCompatibleSystem

variable {I F} (hF : IsCompatibleSystem I F)

include hF

/-- The original successor transition identifies its target with the canonical quotient. -/
def reductionEquiv (n : ℕ) :
    (F.obj (op (n + 1)) ⧸ ((I ^ n) • (⊤ : Submodule R (F.obj (op (n + 1)))))) ≃ₗ[R]
      F.obj (op n) :=
  (Submodule.quotEquivOfEq _ _ (hF.ker_transition n).symm).trans
    ((F.map (homOfLE (Nat.le_succ n)).op).hom.quotKerEquivOfSurjective (hF.surjective n))

@[simp]
theorem reductionEquiv_mk (n : ℕ) (x : F.obj (op (n + 1))) :
    hF.reductionEquiv n (Submodule.Quotient.mk x) =
      F.map (homOfLE (Nat.le_succ n)).op x := by
  simp [reductionEquiv]

/-- The native compatible-section module projects onto every original term. -/
theorem sectionsEval_surjective (n : ℕ) :
    Function.Surjective (ModuleCat.sectionsEval F n) :=
  ModuleCat.sectionsEval_surjective F hF.surjective n

/-- The zero stage is zero, with the unshifted indexing of formal functions. -/
theorem zero_eq (x : F.obj (op 0)) : x = 0 := by
  have h := hF.annihilated 0 ⟨1, by simp⟩ x
  simpa only [one_smul] using h

end IsCompatibleSystem

end AdicCompletion
