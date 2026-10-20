/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Homomorphisms determined by cofinite translated values


Source: `R5Lab.Aglib.GroupTheory.Hom.Cofinite`.
Packet SHA-256:
`d972df58304b0777e572b2051d877166fc5bc5704aeb799edff8abbed579957f`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace MonoidHom
universe u v

/-- An infinite group contains a point and its prescribed translate outside any
finite forbidden set. -/
theorem exists_mem_and_mul_mem_of_finite_compl
    {G : Type u} [Group G] [Infinite G] (S : Set G) (hS : Sᶜ.Finite) (x : G) :
    ∃ y, y ∈ S ∧ x * y ∈ S := by
  have hpre : ((fun y : G => x * y) ⁻¹' Sᶜ).Finite :=
    hS.preimage (mul_right_injective x).injOn
  obtain ⟨y, hy⟩ := (hS.union hpre).exists_notMem
  refine ⟨y, ?_⟩
  simpa only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] using hy

/-- A translated group homomorphism that agrees with a group homomorphism on a
cofinite set of an infinite group has trivial translation and agrees everywhere.
The target need not be commutative. -/
theorem translated_hom_eq_of_cofinite
    {G : Type u} {H : Type v} [Group G] [Infinite G] [Group H]
    (c : H) (Ghom Phom : G →* H) (S : Set G) (hS : Sᶜ.Finite)
    (h : ∀ x ∈ S, c * Ghom x = Phom x) : c = 1 ∧ Ghom = Phom := by
  have hconj : ∀ x, c * Ghom x = Phom x * c := by
    intro x
    obtain ⟨y, hy, hxy⟩ := exists_mem_and_mul_mem_of_finite_compl S hS x
    apply mul_right_cancel (b := Ghom y)
    calc
      (c * Ghom x) * Ghom y = c * Ghom (x * y) := by rw [map_mul, mul_assoc]
      _ = Phom (x * y) := h _ hxy
      _ = (Phom x * c) * Ghom y := by rw [map_mul, ← h y hy, mul_assoc]
  obtain ⟨x, hx⟩ := (Set.infinite_of_finite_compl hS).nonempty
  have hc : c = 1 := by
    have he : Phom x * c = Phom x * 1 := by rw [← hconj x, h x hx, mul_one]
    exact mul_left_cancel he
  refine ⟨hc, ?_⟩
  ext x
  simpa [hc] using hconj x

end MonoidHom
