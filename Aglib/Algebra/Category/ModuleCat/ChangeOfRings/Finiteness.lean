/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite and projective native scalar extension

The actual extension-of-scalars functor preserves finite modules and projective
modules for every homomorphism of commutative rings. Scalar, coefficient-ring and module
universes remain independent. No complex, derived or flatness hypothesis is
involved.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]

/-- A finite module remains finite after an arbitrary ring base change. -/
theorem finite_extendScalars (φ : R →+* S) (M : ModuleCat.{v} R)
    [Module.Finite R M] : Module.Finite S ((extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance

/-- A projective module remains projective after an arbitrary ring base change. -/
theorem projective_extendScalars (φ : R →+* S) (M : ModuleCat.{v} R)
    [Module.Projective R M] : Module.Projective S ((extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Projective S (S ⊗[R] M)
  infer_instance

end ModuleCat
