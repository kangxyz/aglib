/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact images in directed unions of open subschemes

A morphism whose compact image lies in a directed union of opens factors through one of the
actual open subschemes. The factor is Mathlib's native `IsOpenImmersion.lift`; both its triangle
with the original morphism and its cartesian square with the identity of the source are retained.
The current consumer is a quasi-compact part of a Picard stratum covered by increasing levels.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- A compact image contained in a directed union of opens factors through a single member,
with its original morphism and its actual cartesian square unchanged. -/
theorem exists_lift_opens_of_isCompact_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type v} [Nonempty I] (U : I → Y.Opens) (hU : Directed (· ≤ ·) U)
    (hcompact : IsCompact (Set.range f))
    (hcover : Set.range f ⊆ (⨆ i, U i : Y.Opens)) :
    ∃ (i : I) (g : X ⟶ (U i).toScheme),
      g ≫ (U i).ι = f ∧ IsPullback g (𝟙 X) (U i).ι f := by
  obtain ⟨i, hi⟩ := hcompact.elim_directed_cover (fun i => (U i : Set Y))
    (fun i => (U i).isOpen) (fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hy)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩) hU
  have hrange : Set.range f ⊆ Set.range (U i).ι := by
    simpa only [Scheme.Opens.range_ι] using hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι f hrange,
    IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.isPullback_lift_id f (U i).ι hrange⟩

/-- In particular, a morphism from a quasi-compact scheme into a directed union of opens
factors through one open, with the whole scheme factorization retained. -/
theorem exists_lift_opens_of_compactSpace {X Y : Scheme.{u}} [CompactSpace X] (f : X ⟶ Y)
    {I : Type v} [Nonempty I] (U : I → Y.Opens) (hU : Directed (· ≤ ·) U)
    (hcover : Set.range f ⊆ (⨆ i, U i : Y.Opens)) :
    ∃ (i : I) (g : X ⟶ (U i).toScheme),
      g ≫ (U i).ι = f ∧ IsPullback g (𝟙 X) (U i).ι f :=
  f.exists_lift_opens_of_isCompact_range U hU (isCompact_range f.continuous) hcover

end AlgebraicGeometry.Scheme.Hom
