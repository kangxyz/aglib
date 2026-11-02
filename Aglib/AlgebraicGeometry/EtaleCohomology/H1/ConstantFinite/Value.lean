/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Coefficient
public import Mathlib.Algebra.Group.Shrink

/-! # Native finite constant values and their actual small-value iso

The finite native value is retained through an actual additive isomorphism
from the existing lifted constant-value construction. This is the shared
universe bridge; it does not replace the sheaf or its cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u

/-- A finite value in the native sheaf universe is actually isomorphic to the
standard lifted value of a small finite additive group. -/
theorem exists_small_finiteValueIso (A : AddCommGrpCat.{u + 1}) [Finite A] :
    ∃ (B : Type u) (_ : AddCommGroup B) (_ : Finite B),
      Nonempty (value B ≅ A) := by
  let := Fintype.ofFinite A
  have : Small.{u} A := Small.mk'
    ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  let B := Shrink.{u} A
  have : Finite B := Finite.of_equiv A (equivShrink A)
  exact ⟨B, inferInstance, inferInstance,
    ⟨AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
