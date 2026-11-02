/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
# Constructibility by Noetherian induction

A subset of a Noetherian space is constructible if every irreducible closed subset
has a nonempty relatively open part contained either in the subset or its complement.
No generic points, sobriety, or scheme structure are needed.
-/

@[expose] public section

open Topology

namespace TopologicalSpace.NoetherianSpace

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- A set is constructible if its membership is constant on some nonempty relatively
open part of every irreducible closed subset of a Noetherian space. -/
theorem isConstructible_of_isIrreducible {s : Set X}
    (H : ∀ Z : Set X, IsClosed Z → IsIrreducible Z →
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧
        (U ∩ Z ⊆ s ∨ U ∩ Z ⊆ sᶜ)) :
    IsConstructible s := by
  suffices hZ : ∀ Z : Closeds X, IsConstructible (s ∩ (Z : Set X)) by
    simpa only [Closeds.coe_top, Set.inter_univ] using hZ ⊤
  intro Z
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  rcases eq_or_ne Z ⊥ with rfl | h₀
  · simp
  by_cases h₁ : IsPreirreducible (Z : Set X)
  · obtain ⟨U, hU, ⟨x₀, hx₀U, hx₀Z⟩, hconst⟩ :=
      H Z Z.isClosed ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
    let W : Closeds X := ⟨Uᶜ, hU.isClosed_compl⟩
    have hlt : Z ⊓ W < Z := inf_lt_left.2 fun hZW => hZW hx₀Z hx₀U
    have hlocal : IsConstructible (s ∩ (U ∩ (Z : Set X))) := by
      rcases hconst with hin | hout
      · have heq : s ∩ (U ∩ (Z : Set X)) = U ∩ (Z : Set X) :=
          Set.inter_eq_right.mpr hin
        rw [heq]
        exact ((NoetherianSpace.isCompact U).isConstructible hU).inter
          ((NoetherianSpace.isCompact (Z : Set X)ᶜ).isConstructible
            Z.isClosed.isOpen_compl).of_compl
      · have heq : s ∩ (U ∩ (Z : Set X)) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro x ⟨hxs, hx⟩
          exact hout hx hxs
        rw [heq]
        exact IsConstructible.empty
    have heq : s ∩ (Z : Set X) =
        (s ∩ (U ∩ (Z : Set X))) ∪ (s ∩ ((Z ⊓ W : Closeds X) : Set X)) := by
      ext x
      change (x ∈ s ∧ x ∈ Z) ↔
        (x ∈ s ∧ x ∈ U ∧ x ∈ Z) ∨ (x ∈ s ∧ x ∈ Z ∧ x ∉ U)
      constructor
      · rintro ⟨hxs, hxZ⟩
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxs, hxU, hxZ⟩
        · exact Or.inr ⟨hxs, hxZ, hxU⟩
      · rintro (hx | hx)
        · exact ⟨hx.1, hx.2.2⟩
        · exact ⟨hx.1, hx.2.1⟩
    rw [heq]
    exact hlocal.union (ih (Z ⊓ W) hlt)
  · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
    obtain ⟨z₁, z₂, hz₁, hz₂, hsub, hz₁', hz₂'⟩ := h₁
    lift z₁ to Closeds X using hz₁
    lift z₂ to Closeds X using hz₂
    have heq : s ∩ (Z : Set X) =
        (s ∩ ((Z ⊓ z₁ : Closeds X) : Set X)) ∪
          (s ∩ ((Z ⊓ z₂ : Closeds X) : Set X)) := by
      ext x
      change (x ∈ s ∧ x ∈ Z) ↔
        (x ∈ s ∧ x ∈ Z ∧ x ∈ z₁) ∨ (x ∈ s ∧ x ∈ Z ∧ x ∈ z₂)
      constructor
      · rintro ⟨hxs, hxZ⟩
        rcases hsub hxZ with hx₁ | hx₂
        · exact Or.inl ⟨hxs, hxZ, hx₁⟩
        · exact Or.inr ⟨hxs, hxZ, hx₂⟩
      · rintro (hx | hx) <;> exact ⟨hx.1, hx.2.1⟩
    rw [heq]
    exact (ih (Z ⊓ z₁) (inf_lt_left.2 hz₁')).union
      (ih (Z ⊓ z₂) (inf_lt_left.2 hz₂'))

end TopologicalSpace.NoetherianSpace
