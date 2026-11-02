/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Separation.Basic

/-! # An omitted original point supplies a closed boundary after base change

Surjectivity of the actual projection preserves nonemptiness of the complement.
Compactness of the target scheme then supplies a closed point in that same
complement. Neither rationality of the original boundary point nor separable
closedness of its residue field is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A surjective commuting square preserves a nonempty boundary, and compactness
produces an actual closed point outside the original target open immersion. -/
theorem exists_closedPoint_outside_of_surjective_square
    {U X V Y : Scheme.{u}} (j : U ⟶ X) (j' : V ⟶ Y) [IsOpenImmersion j']
    (a : Y ⟶ X) [Surjective a] (b : V ⟶ U) (h : j' ≫ a = b ≫ j)
    [CompactSpace Y] (hx : ∃ x : X, x ∉ Set.range j) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ∉ Set.range j' := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := a.surjective x
  have hy' : y ∉ Set.range j' := by
    rintro ⟨v, hv⟩
    have hv' : a (j' v) = j (b v) := congrArg (fun f : V ⟶ X => f v) h
    exact hx ⟨b v, hv'.symm.trans ((congrArg a hv).trans hy)⟩
  have hc : IsClosed ((Set.range j')ᶜ : Set Y) := j'.opensRange.isOpen.isClosed_compl
  obtain ⟨y', hy', hc'⟩ := hc.exists_closed_singleton ⟨y, hy'⟩
  exact ⟨y', hc', hy'⟩

end AlgebraicGeometry.Scheme
