/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Original subgroup kernels in a surjective square

Native subgroup image/preimage identities interchange the two directions of
a commuting square. The original homomorphisms and their literal kernels
are retained, with independent universes and no lifted carrier models.
-/

@[expose] public section

universe uA uB uC uD

namespace AddMonoidHom

/-- In a commuting square, a surjective top map and surjectivity on its
relation kernels identify the image of the other source kernel with the
other target kernel. The proof assembles native subgroup lattice identities. -/
theorem map_ker_eq_of_surjective_square
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [AddGroup A] [AddGroup B] [AddGroup C] [AddGroup D]
    (c : A →+ B) (d : C →+ D) (f : A →+ C) (g : B →+ D)
    (hc : Function.Surjective c) (hcomm : g.comp c = d.comp f)
    (hker : c.ker.map f = d.ker) : f.ker.map c = g.ker := by
  calc
    f.ker.map c = (c.ker ⊔ f.ker).map c := by
      rw [AddSubgroup.map_sup, AddSubgroup.map_ker_self, bot_sup_eq]
    _ = ((c.ker.map f).comap f).map c := by rw [AddSubgroup.comap_map_eq]
    _ = (d.ker.comap f).map c := by rw [hker]
    _ = (g.ker.comap c).map c := by rw [comap_ker, comap_ker, hcomm]
    _ = g.ker := AddSubgroup.map_comap_eq_self_of_surjective hc g.ker

end AddMonoidHom
