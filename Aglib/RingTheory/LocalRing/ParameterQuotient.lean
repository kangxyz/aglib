/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fintype.Card
/-!
# Quotienting a regular local ring by a first minimal generator

A nonzero cotangent vector extends to a basis. Lifting that basis and using
Nakayama gives a minimal generating family containing the specified
parameter. Removing its image in the quotient decreases the generator
bound by one. Krull's height inequality then proves quotient regularity and
the exact dimension drop, without first assuming that the ring is a domain.

## Extraction basis

Transferred from `Quillen.Algebra.RegularLocal.ParameterQuotient` at source revision
`83629578a3d70787d41ec631f5234af8758716af`, SHA-256
`848871057c33da3a84886d133b551c6c063b184f723f36db1409937abb1bfd8a`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open IsLocalRing Module

namespace IsLocalRing
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A first minimal generator belongs to a generating family of the maximal
ideal of cardinality at most the cotangent dimension. -/
theorem exists_generators_containing_parameter (x : R) (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ s : Finset R, x ∈ s ∧ Ideal.span (s : Set R) = maximalIdeal R ∧
      s.card ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  let m := maximalIdeal R
  let v : CotangentSpace R := m.toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := fun h => hx2 ((m.toCotangent_eq_zero ⟨x, hx⟩).mp h)
  have hs : LinearIndepOn (ResidueField R) id ({v} : Set (CotangentSpace R)) :=
    (linearIndepOn_singleton_iff (ResidueField R)).mpr hv
  let I := hs.extend (Set.subset_univ {v})
  let b : Basis I (ResidueField R) (CotangentSpace R) := Basis.extend hs
  have : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  let i₀ : I := ⟨v, (Basis.subset_extend hs) (Set.mem_singleton v)⟩
  choose g hg using fun i : I => m.toCotangent_surjective (b i)
  let g' : I → m := Function.update g i₀ ⟨x, hx⟩
  have hg' (i : I) : m.toCotangent (g' i) = b i := by
    by_cases hi : i = i₀
    · subst i
      rw [show g' i₀ = ⟨x, hx⟩ by simp [g']]
      exact (Basis.extend_apply_self hs i₀).symm
    · simp [g', hi, hg i]
  have himage : m.toCotangent '' Set.range g' = Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext hg'
  have hspan : Submodule.span R (Set.range g') = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp (himage ▸ b.span_eq)
  let f : I → R := fun i => (g' i).val
  have hgens : Ideal.span (Set.range f) = m := by
    have he := congrArg (Submodule.map m.subtype) hspan
    change Submodule.span R (Set.range (m.subtype ∘ g')) = m
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      using he
  let s := Finset.univ.image f
  refine ⟨s, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, by simp [f, g']⟩
  · simpa [s] using hgens
  · exact (Finset.card_image_le).trans (by simp [Module.finrank_eq_card_basis b])

/-- Killing a first minimal generator decreases the maximal-ideal generator
bound by one. This statement does not require regularity. -/
theorem spanFinrank_maximalIdeal_quotient_parameter_le
    (d : ℕ) (hd : Module.finrank (ResidueField R) (CotangentSpace R) ≤ d + 1)
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ d := by
  classical
  obtain ⟨s, hxs, hs, hcard⟩ := exists_generators_containing_parameter R x hx hx2
  let q := Ideal.Quotient.mk (Ideal.span {x})
  let t := (s.erase x).image q
  have hs' : Ideal.span (s : Set R) = Ideal.span {x} ⊔ Ideal.span (s.erase x : Set R) := by
    nth_rw 1 [← Finset.insert_erase hxs]
    rw [Finset.coe_insert, Ideal.span_insert]
  have ht : Ideal.span (t : Set (R ⧸ Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) := by
    have he := map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
    rw [← hs, hs', Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span] at he
    simpa [t, q] using he
  rw [← ht]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet t)).trans
  rw [Set.ncard_coe_finset]
  have herase := Finset.card_erase_add_one hxs
  have htcard : t.card ≤ (s.erase x).card := Finset.card_image_le
  omega

end IsLocalRing

