/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.EtaleConstructibleRefinement
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Reduced

/-! # Actual reduced refinements of finite partitions

Each original part is replaced by its native nilradical closed subscheme.
The labels and original images are unchanged, and the reduction inclusions
supply actual refinement maps. Finite affine etale structural maps then have
reduced sources, while all prescribed original constructible preimages
remain clopen in those whole sources.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u v

private theorem nilradical_subscheme_reduced (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme := by
  apply IdealSheafData.subscheme_reduced_of_radical
  rw [← IdealSheafData.vanishingIdeal_support, support_nilradical,
    IdealSheafData.vanishingIdeal_top]

private theorem nilradical_subscheme_surjective (X : Scheme.{u}) :
    Function.Surjective X.nilradical.subschemeι := by
  apply Set.range_eq_univ.mp
  rw [IdealSheafData.range_subschemeι, support_nilradical]
  rfl

private theorem range_nilradical_subscheme_comp {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Set.range (Y.nilradical.subschemeι ≫ f) = Set.range f := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (nilradical_subscheme_surjective Y).range_eq, Set.image_univ]

namespace FiniteLocallyClosedPartition

variable {X : Scheme.{u}}

/-- Reduce every actual stratum, preserving its finite label and its
original image in the base. -/
def reduce (p : FiniteLocallyClosedPartition X) : FiniteLocallyClosedPartition X where
  count := p.count
  stratum i := (p.stratum i).nilradical.subscheme
  inclusion i := (p.stratum i).nilradical.subschemeι ≫ p.inclusion i
  immersion i := by
    have := p.immersion i
    infer_instance
  constructible_range i := by
    rw [range_nilradical_subscheme_comp]
    exact p.constructible_range i
  disjoint := by
    intro i j hij
    rw [range_nilradical_subscheme_comp, range_nilradical_subscheme_comp]
    exact p.disjoint hij
  covers x := by
    obtain ⟨i, y, hy⟩ := p.covers x
    obtain ⟨z, hz⟩ := nilradical_subscheme_surjective (p.stratum i) y
    exact ⟨i, z, by simpa only [Scheme.Hom.comp_apply, hz] using hy⟩

/-- The native nilradical inclusions are the actual refinement maps. -/
def reductionRefinement (p : FiniteLocallyClosedPartition X) : p.reduce.Refinement p where
  indexMap := id
  map i := (p.stratum i).nilradical.subschemeι
  comm _ := rfl

/-- Every stratum of the actual reduction is reduced, even over an
arbitrary non-Noetherian base. -/
theorem reduce_stratum_isReduced (p : FiniteLocallyClosedPartition X) (i : Fin p.count) :
    IsReduced (p.reduce.stratum i) :=
  nilradical_subscheme_reduced (p.stratum i)

/-- Reduction preserves each original stratum image, not merely their union. -/
@[simp]
theorem range_reduce_inclusion (p : FiniteLocallyClosedPartition X) (i : Fin p.count) :
    Set.range (p.reduce.inclusion i) = Set.range (p.inclusion i) :=
  range_nilradical_subscheme_comp (p.inclusion i)

end FiniteLocallyClosedPartition

/-- A finite family of constructible subsets of an affine etale source
admits a partition with reduced parts and reduced whole pulled-back
sources, finite structural maps, and clopen original subset preimages. -/
theorem exists_reduced_finite_clopen_partition_of_isAffineHom_of_etale
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f]
    {ι : Type v} [Finite ι] (s : ι → Set Y) (hs : ∀ i, Topology.IsConstructible (s i)) :
    ∃ p : FiniteLocallyClosedPartition X,
      (∀ k, IsReduced (p.stratum k)) ∧
      (∀ k, IsFinite (pullback.snd f (p.inclusion k))) ∧
      (∀ k, IsReduced (pullback f (p.inclusion k))) ∧
      ∀ i k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i) := by
  obtain ⟨p, hp, hclopen⟩ :=
    exists_finite_clopen_partition_of_isAffineHom_of_etale f s hs
  have hfinite := p.reductionRefinement.isFinite_pullback_snd f hp
  refine ⟨p.reduce, p.reduce_stratum_isReduced, hfinite, ?_, ?_⟩
  · intro k
    have := p.reduce_stratum_isReduced k
    have := hfinite k
    exact Etale.finite_isReduced (pullback.snd f (p.reduce.inclusion k))
  · intro i
    exact p.reductionRefinement.isClopen_preimage f (s i) (hclopen i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
