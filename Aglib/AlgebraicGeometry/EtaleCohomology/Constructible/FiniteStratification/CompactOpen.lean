/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual open-complement partitions

A constructible open and its reduced closed complement form an actual finite
locally closed partition. A quasi-compact open immersion becomes finite on
these two strata. This is a geometric base case for finite-etale stratification;
it does not assert the corresponding construction for arbitrary etale maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

namespace FiniteLocallyClosedPartition

variable {X : Scheme.{u}}

/-- The open itself and the actual reduced closed complement. -/
def openComplementStratum (U : X.Opens) : Bool → Scheme.{u}
  | false => U.toScheme
  | true => (IdealSheafData.vanishingIdeal U.compl).subscheme

/-- The original open and closed inclusions into the same base. -/
def openComplementInclusion (U : X.Opens) : ∀ b, openComplementStratum U b ⟶ X
  | false => U.ι
  | true => (IdealSheafData.vanishingIdeal U.compl).subschemeι

@[simp]
theorem range_openComplementInclusion_false (U : X.Opens) :
    Set.range (openComplementInclusion U false) = U :=
  U.range_ι

@[simp]
theorem range_openComplementInclusion_true (U : X.Opens) :
    Set.range (openComplementInclusion U true) = (U : Set X)ᶜ := by
  change Set.range (IdealSheafData.vanishingIdeal U.compl).subschemeι = _
  exact (IdealSheafData.range_subschemeι _).trans
    (IdealSheafData.coe_support_vanishingIdeal _)

/-- The actual two-stratum partition associated with a constructible open.
The closed complement retains its reduced induced scheme structure. -/
def openComplement (U : X.Opens) (hU : Topology.IsConstructible (U : Set X)) :
    FiniteLocallyClosedPartition X :=
  ofFintype (openComplementStratum U) (openComplementInclusion U)
    (by
      intro b
      cases b
      · change IsImmersion U.ι
        infer_instance
      · change IsImmersion (IdealSheafData.vanishingIdeal U.compl).subschemeι
        infer_instance)
    (by
      intro b
      cases b
      · simpa only [range_openComplementInclusion_false] using hU
      · simpa only [range_openComplementInclusion_true] using hU.compl)
    (by
      intro a b hab
      cases a <;> cases b
      · exact False.elim (hab rfl)
      · simpa only [range_openComplementInclusion_false,
          range_openComplementInclusion_true] using disjoint_compl_right
      · simpa only [range_openComplementInclusion_false,
          range_openComplementInclusion_true] using disjoint_compl_left
      · exact False.elim (hab rfl))
    (by
      intro x
      by_cases hx : x ∈ U
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
      · have hx' : x ∈ Set.range (openComplementInclusion U true) := by
          rw [range_openComplementInclusion_true]
          exact hx
        obtain ⟨y, hy⟩ := hx'
        exact ⟨true, y, hy⟩)

end FiniteLocallyClosedPartition

/-- A constructible open immersion becomes finite on the actual open and
reduced closed-complement strata. No Noetherian hypothesis is required. -/
theorem exists_finitePartition_of_isOpenImmersion
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : Topology.IsConstructible (Set.range f)) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i, IsFinite (pullback.snd f (p.inclusion i)) := by
  have hU : Topology.IsConstructible (f.opensRange : Set X) := hf
  refine ⟨FiniteLocallyClosedPartition.openComplement f.opensRange hU, ?_⟩
  suffices ∀ b : Bool, IsFinite (pullback.snd f
      (FiniteLocallyClosedPartition.openComplementInclusion f.opensRange b)) by
    intro i
    exact this ((Fintype.equivFin Bool).symm i)
  intro b
  cases b
  · change IsFinite (pullback.snd f f.opensRange.ι)
    have : Surjective (pullback.snd f f.opensRange.ι) := ⟨by
      intro y
      change y ∈ Set.range (pullback.snd f f.opensRange.ι)
      rw [Scheme.Pullback.range_snd]
      exact y.property⟩
    have : IsIso (pullback.snd f f.opensRange.ι) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
    infer_instance
  · change IsFinite (pullback.snd f
      (IdealSheafData.vanishingIdeal f.opensRange.compl).subschemeι)
    have : IsEmpty ↑(pullback f
        (IdealSheafData.vanishingIdeal f.opensRange.compl).subschemeι) :=
      Scheme.isEmpty_pullback_iff.mpr (by
        rw [IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
        exact disjoint_compl_right)
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
