/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness from lifted relations

A module `M` is flat if every finite relation `∑ fᵢ xᵢ = 0` in `M` lifts, through a linear map
from one module of a family of flat modules, to a relation among preimages of the `xᵢ`
(`Module.Flat.of_forall_exists_lift_relation`). The lifted relation is trivial by the equational
criterion for flatness (Stacks Project, Tag 00HK; Mathlib's
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`), and its image trivializes the original
relation (`Module.Flat.of_forall_isTrivialRelation`). The consumer is the flatness of chart
sections in Nitsure's Lemma 3.2, `AlgebraicGeometry/Cohomology/Projective/FlatOfSections`.
-/

@[expose] public section

namespace Module.Flat

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Flatness from lifted relations.** If every finite relation `∑ fᵢ xᵢ = 0` in `M` lifts,
through a linear map from one module of a family of flat modules, to a relation among preimages
of the `xᵢ`, then `M` is flat. The lifted relation is trivial by the equational criterion
([Stacks, Tag 00HK]), and its image trivializes the original one. -/
theorem of_forall_exists_lift_relation {κ : Type*} {E : κ → Type*} [∀ k, AddCommGroup (E k)]
    [∀ k, Module R (E k)] (hE : ∀ k, Module.Flat R (E k)) (g : ∀ k, E k →ₗ[R] M)
    (h : ∀ {l : ℕ} (f : Fin l → R) (x : Fin l → M), ∑ i, f i • x i = 0 →
      ∃ (k : κ) (y : Fin l → E k), (∀ i, g k (y i) = x i) ∧ ∑ i, f i • y i = 0) :
    Module.Flat R M := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  obtain ⟨k, y, hy, hrel⟩ := h f x hfx
  have := hE k
  obtain ⟨k', a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k', a, fun j => g k (z j), fun i => ?_, ha⟩
  rw [← hy i, hz i, map_sum]
  exact Finset.sum_congr rfl fun j _ => (g k).map_smul _ _

end Module.Flat
