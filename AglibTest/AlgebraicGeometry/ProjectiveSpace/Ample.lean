/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Ample

/-! The projective ample supplier keeps the original scheme and line bundle. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

example {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R) [IsHProjective p] :
    ∃ L : Scheme.Modules.Invertible.LineBundle X, L.IsAmple :=
  IsHProjective.exists_isAmple p

example (k : Type u) [Field k] :
    (ProjectiveSpace.twistingLineBundle k (ULift.{u} (Fin 1)) 1).IsAmple :=
  ProjectiveSpace.twistingLineBundle_one_isAmple k _

end
