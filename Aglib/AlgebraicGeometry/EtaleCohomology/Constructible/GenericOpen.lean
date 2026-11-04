/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic

/-!
# The original generic stratum is a dense open

A dense immersion into a reduced scheme is open. Applied to the stratum
containing the generic point, this keeps the actual source and inclusion of
the original finite locally closed partition. No coefficient or locus model
is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

/-- A dense original immersion into a reduced scheme is an open immersion.
The coborder is only an auxiliary target for proving the closed factor invertible. -/
theorem isOpenImmersion_of_immersion_denseRange
    {S X : Scheme.{u}} [IsReduced X] (f : S ⟶ X) [IsImmersion f]
    (hf : DenseRange f) : IsOpenImmersion f := by
  have hc : closure (Set.range f) = Set.univ := dense_iff_closure_eq.mp hf
  have hr : (f.coborderRange : Set X) = Set.range f := by
    change coborder (Set.range f) = Set.range f
    rw [coborder_eq_union_closure_compl, hc, Set.compl_univ, Set.union_empty]
  let : Surjective f.liftCoborder := ⟨by
    intro y
    have hy : y.val ∈ Set.range f := by
      rw [← hr]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply f.coborderRange.ι.isOpenEmbedding.injective
    change (f.liftCoborder ≫ f.coborderRange.ι) x = y.val
    rw [f.liftCoborder_ι]
    exact hx⟩
  let : IsIso f.liftCoborder := isIso_of_isClosedImmersion_of_surjective f.liftCoborder
  have h : IsOpenImmersion (f.liftCoborder ≫ f.coborderRange.ι) := inferInstance
  simpa only [f.liftCoborder_ι] using h

namespace FiniteLocallyClosedPartition

/-- A stratum containing the original generic point has dense range. -/
theorem denseRange_inclusion_of_genericPoint_mem
    {X : Scheme.{u}} [IsIntegral X] (t : FiniteLocallyClosedPartition X)
    (a : Fin t.count) (ha : genericPoint X ∈ Set.range (t.inclusion a)) :
    DenseRange (t.inclusion a) := by
  have hη : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq, genericPoint_closure]
  exact hη.mono (Set.singleton_subset_iff.mpr ha)

/-- The given partition has an actual nonempty dense open stratum. Its source
and inclusion are retained, together with membership of the original generic point. -/
theorem exists_generic_open_stratum
    {X : Scheme.{u}} [IsIntegral X] (t : FiniteLocallyClosedPartition X) :
    ∃ a : Fin t.count, genericPoint X ∈ Set.range (t.inclusion a) ∧
      IsOpenImmersion (t.inclusion a) ∧ DenseRange (t.inclusion a) ∧
        Nonempty (t.stratum a) := by
  obtain ⟨a, y, hy⟩ := t.covers (genericPoint X)
  have ha : genericPoint X ∈ Set.range (t.inclusion a) := ⟨y, hy⟩
  have hd := t.denseRange_inclusion_of_genericPoint_mem a ha
  let : IsImmersion (t.inclusion a) := t.immersion a
  exact ⟨a, ha, isOpenImmersion_of_immersion_denseRange (t.inclusion a) hd, hd, ⟨y⟩⟩

end FiniteLocallyClosedPartition

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
