/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic

/-! # The original quotient ring on the associated graded algebra

The explicit native constructor avoids repeated parent-structure inference
through the Rees subalgebra when specializing generic ring theorems.
-/

@[expose] public noncomputable section

namespace Ideal

universe u
variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The native quotient commutative ring, with its original operations. -/
instance associatedGradedCommRing : CommRing I.associatedGraded :=
  Ideal.Quotient.commRing I.associatedGradedIdeal

end Ideal
