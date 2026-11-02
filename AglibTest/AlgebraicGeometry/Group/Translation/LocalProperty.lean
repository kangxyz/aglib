/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Translation.LocalProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Flatness is a second consumer of the same actual translation cover. -/

@[expose] public noncomputable section


open CategoryTheory AlgebraicGeometry

universe u

example {k : Type u} [Field k] [IsAlgClosed k]
    (G H : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom]
    (f : G ⟶ H) (W : G.X.left.Opens) (hW : Nonempty W)
    [Flat (W.ι ≫ f.hom.hom.left)] : Flat f.hom.hom.left := by
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  exact Scheme.Group.Translation.property_of_nonempty_open (@Flat.{u}) G H f W hW inferInstance

end
