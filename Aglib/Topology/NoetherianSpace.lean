/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.NoetherianSpace

/-!
# Local constancy and Noetherian induction on Noetherian spaces

On a Noetherian space, any family `g i` of locally constant functions, indexed by an arbitrary
type, is jointly locally constant: `x ↦ (i ↦ g i x)` is locally constant
(`TopologicalSpace.NoetherianSpace.isLocallyConstant_pi`). The set of points where some `g i`
differs from its value at `x` is open, hence compact, so finitely many `g i` already cut out the
fibre through `x`. Without the Noetherian hypothesis this fails (an unformalized remark): the
coordinate functions of the Cantor space `ℕ → Bool` are locally constant, but the identity is not.

This is the topological step from local constancy of every value `χ(F_s(m))` to local constancy
of the Hilbert polynomial over a Noetherian base (Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, proof of Thm 4.3, (A), pp. 20–21).

`TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible` is the Noetherian induction of
the same proof: if every irreducible closed subset `Z` meets an open `U` with `h '' (U ∩ Z)`
finite, then `h` has finite range. A minimal closed `Z` with infinite image would be irreducible,
and `Z \ U` is a smaller closed subset.
-/

@[expose] public section

namespace TopologicalSpace.NoetherianSpace

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- **Families of locally constant functions on a Noetherian space are jointly locally
constant.** -/
theorem isLocallyConstant_pi {I : Type*} {Y : I → Type*} {g : ∀ i, X → Y i}
    (hg : ∀ i, IsLocallyConstant (g i)) : IsLocallyConstant (fun x i => g i x) := by
  classical
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro x
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact {y | ∃ i, g i y ≠ g i x}).elim_finite_subcover
    (fun i => {y | g i y ≠ g i x}) (fun i => ((hg i).isClosed_fiber (g i x)).isOpen_compl)
    (fun y ⟨i, hi⟩ => Set.mem_iUnion.mpr ⟨i, hi⟩)
  have he : (fun y i => g i y) ⁻¹' {fun i => g i x} = ⋂ i ∈ t, {y | g i y = g i x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h i _ => congrFun h i, fun h => funext fun j => ?_⟩
    by_contra hj
    obtain ⟨i, hi, hne⟩ := Set.mem_iUnion₂.mp (ht ⟨j, hj⟩)
    exact hne (h i hi)
  rw [he]
  exact isOpen_biInter_finset fun i _ => (hg i).isOpen_fiber (g i x)

/-- **Noetherian induction for finite images**: if every irreducible closed subset `Z` meets an
open `U` with `h '' (U ∩ Z)` finite, then `h` has finite range. -/
theorem finite_range_of_isIrreducible {β : Type*} (h : X → β)
    (H : ∀ Z : Set X, IsClosed Z → IsIrreducible Z →
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ (h '' (U ∩ Z)).Finite) :
    (Set.range h).Finite := by
  suffices hZ : ∀ Z : Closeds X, (h '' (Z : Set X)).Finite by
    simpa only [Closeds.coe_top, Set.image_univ] using hZ ⊤
  intro Z
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  rcases eq_or_ne Z ⊥ with rfl | h₀
  · simp
  by_cases h₁ : IsPreirreducible (Z : Set X)
  · obtain ⟨U, hU, ⟨x₀, hx₀U, hx₀Z⟩, hfin⟩ := H Z Z.isClosed ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
    let W : Closeds X := ⟨Uᶜ, hU.isClosed_compl⟩
    have hlt : Z ⊓ W < Z := inf_lt_left.2 fun hZW => hZW hx₀Z hx₀U
    refine (hfin.union (ih (Z ⊓ W) hlt)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨x, ⟨hxU, hx⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hxU⟩, rfl⟩
  · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
    obtain ⟨z₁, z₂, hz₁, hz₂, hsub, hz₁', hz₂'⟩ := h₁
    lift z₁ to Closeds X using hz₁
    lift z₂ to Closeds X using hz₂
    refine ((ih (Z ⊓ z₁) (inf_lt_left.2 hz₁')).union
      (ih (Z ⊓ z₂) (inf_lt_left.2 hz₂'))).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hsub hx with hx₁ | hx₂
    · exact Or.inl ⟨x, ⟨hx, hx₁⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hx₂⟩, rfl⟩

end TopologicalSpace.NoetherianSpace
