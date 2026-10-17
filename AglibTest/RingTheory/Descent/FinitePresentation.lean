/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Descent.FinitePresentation

/-! Focused consumer of faithfully flat descent of finite presentation for modules. The
hypotheses are Mathlib's `Module.FaithfullyFlat` and `Module.FinitePresentation`. -/

@[expose] public section

open TensorProduct

example (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M :=
  Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A B M

/--
info: 'Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
