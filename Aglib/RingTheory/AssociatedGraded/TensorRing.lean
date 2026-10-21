/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Native tensor rings with an associated-graded factor

Specifying the original quotient factor before elaborating the native tensor
ring constructor avoids ambiguous parent-structure inference. The ring is
Mathlib's original algebra tensor ring, with no replacement multiplication.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open scoped TensorProduct
namespace Ideal

variable {A : Type u} [CommRing A] (I : Ideal A)
  (B : Type v) [CommRing B] [Algebra A B]

/-- The native commutative ring on an external associated-graded tensor algebra. -/
instance associatedGradedTensorCommRing : CommRing (B ⊗[A] I.associatedGraded) :=
  Algebra.TensorProduct.instCommRing (R := A) (A := B) (B := I.associatedGraded)

end Ideal
