/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.PGroup.FixedPoint
public import Mathlib.Algebra.Group.Action.Hom

/-! # Fixed points from a p-group permutation image

The acting group itself need not be a p-group. Only its actual permutation
image is used, which is the form supplied by finite Galois monodromy.
-/

@[expose] public noncomputable section

namespace MonoidHom

universe g v

/-- A p-group permutation image fixing zero on a nontrivial finite p-torsion
abelian group gives a nonzero point fixed by every original group element. -/
theorem exists_ne_zero_fixedPoint_of_isPGroup_range
    {p : ℕ} [Fact p.Prime] {G : Type g} [Group G]
    {V : Type v} [AddCommGroup V] [Finite V] [Nontrivial V]
    (ρ : G →* Equiv.Perm V) (hρ : IsPGroup p ρ.range)
    (hzero : ∀ g : G, ρ g 0 = 0) (hV : ∀ x : V, p • x = 0) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ρ g x = x := by
  let : MulAction ρ.range V := MulAction.compHom V ρ.range.subtype
  have hz : ∀ g : ρ.range, g • (0 : V) = 0 := by
    rintro ⟨g, σ, rfl⟩
    exact hzero σ
  obtain ⟨x, hx, hfix⟩ := hρ.exists_ne_zero_fixedPoint_of_annihilated hz hV
  exact ⟨x, hx, fun g => hfix (ρ.rangeRestrict g)⟩

end MonoidHom
