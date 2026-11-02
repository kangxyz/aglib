/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Exact.Basic

/-!
# Finiteness of the middle additive group of an exact pair

The original kernel of the second map is the actual range of the first.
Finite outer groups therefore give finite kernel and range, and the pinned
kernel-range finiteness criterion gives the original middle group.
No scalar ring, surjective second map or replacement group is introduced.
-/

@[expose] public section

universe u v w

namespace AddMonoidHom

/-- An exact pair of original additive homomorphisms has finite middle group
when its two outer groups are finite. No surjectivity hypothesis is needed. -/
theorem finite_of_exact
    {A : Type u} {B : Type v} {C : Type w}
    [AddGroup A] [AddGroup B] [AddGroup C] [Finite A] [Finite C]
    (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g) : Finite B := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · have hker : g.ker = f.range := by
      ext b
      exact hfg b
    rw [hker]
    exact Finite.of_surjective f.rangeRestrict (by
      intro b
      obtain ⟨a, ha⟩ := b.property
      exact ⟨a, Subtype.ext ha⟩)
  · infer_instance

end AddMonoidHom
