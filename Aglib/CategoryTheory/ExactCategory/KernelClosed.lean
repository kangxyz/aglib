/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Kernel closure for a selected exact structure

For a conflation, membership of its middle and last objects implies membership
of its first object. This requires both objects; arbitrary admissible-subobject
closure is not assumed.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Resolution/Finite.lean`.
SHA-256: `7bc6a09717c5db9e40eda8c01c9561ae85be53800006a856c7b89f3facbe6225`.
Selected source lines: 187–191.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Kernel closure for the selected conflations. Both the middle
and quotient are required to be resolving objects. This is weaker than closure
under arbitrary admissible subobjects in the ambient exact category. -/
class IsKernelClosed (P : ObjectProperty C) : Prop where
  prop_kernel : ∀ {S : ShortComplex C}, E.conflation S → P S.X₂ → P S.X₃ → P S.X₁

end CategoryTheory.ExactCategory.ExactStructure
