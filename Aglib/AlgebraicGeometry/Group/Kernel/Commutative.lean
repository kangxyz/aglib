/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.CategoryTheory.Monoidal.CommMonObjOfMono

/-! The original kernel of a commutative group is commutative. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

attribute [local instance] Over.cartesianMonoidalCategory

/-- The original kernel inherits commutativity through its actual inclusion. -/
theorem isCommMonObj_group {S : Scheme.{u}} {G E : Grp (Over S)}
    [IsCommMonObj G.X] (p : G ⟶ E) : IsCommMonObj (group p).X := by
  let : Mono (inclusion p).hom.hom := (square p).mono_fst_of_mono
  exact IsCommMonObj.of_mono (inclusion p).hom.hom

end AlgebraicGeometry.Scheme.Group.Kernel
