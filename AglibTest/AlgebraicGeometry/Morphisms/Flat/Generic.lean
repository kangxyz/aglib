/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Flat.Generic

/-! Flatness uses the original structure sheaf and actual scheme morphism. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.relativeFlat f (SheafOfModules.unit X.ringCatSheaf) ↔ Flat f :=
  Scheme.Modules.relativeFlat_unit_iff_flat f

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] [Surjective f] :
    ∃ W : X.Opens, Nonempty W ∧ Flat (W.ι ≫ f) :=
  Scheme.exists_nonempty_source_open_flat_of_isIntegral f

end
