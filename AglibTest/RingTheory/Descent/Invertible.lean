/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Descent.Invertible

/-! Focused consumer of faithfully flat descent of invertibility (plan row F5). The predicate is
Mathlib's `Module.Invertible` (bijective contraction `Mᵛ ⊗ M → A`) and the base change is the
ordinary tensor product `B ⊗[A] M`. -/

@[expose] public section

open TensorProduct

example (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M] [Module.Invertible B (B ⊗[A] M)] : Module.Invertible A M :=
  Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat A B M

example (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M] :
    Module.Invertible B (B ⊗[A] M) ↔ Module.Invertible A M :=
  Module.Invertible.iff_invertible_tensorProduct_of_faithfullyFlat A B M

/--
info: 'Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
