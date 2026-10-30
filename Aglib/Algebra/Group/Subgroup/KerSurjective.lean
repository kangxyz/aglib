/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Surjectivity of a homomorphism restricted to a kernel

A surjection `r` remains surjective on `ker d` if `d` maps `ker r` onto its codomain.
The correction is constructed inside the proof; no selected section enters the interface.
-/

@[expose] public section

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Surjectivity on a kernel follows by correcting a lift inside the other kernel. -/
theorem surjective_comp_ker_subtype (r : A →+ B) (d : A →+ C)
    (hr : Function.Surjective r) (hd : Function.Surjective (d.comp r.ker.subtype)) :
    Function.Surjective (r.comp d.ker.subtype) := by
  intro b
  obtain ⟨a, ha⟩ := hr b
  obtain ⟨c, hc⟩ := hd (d a)
  have hc' : d (c : A) = d a := hc
  refine ⟨⟨a - c, ?_⟩, ?_⟩
  · change d (a - c) = 0
    rw [map_sub, hc', sub_self]
  · change r (a - c) = b
    rw [map_sub, c.property, sub_zero, ha]

end AddMonoidHom
