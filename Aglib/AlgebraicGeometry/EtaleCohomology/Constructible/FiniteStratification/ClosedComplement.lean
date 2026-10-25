/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Assembling actual partitions across a closed complement

On a Noetherian base every immersion has constructible range. This permits
an actual partition of a closed complement to be joined to its original open
immersion. A surjective closed immersion also transports the same strata to
the ambient scheme. These constructions preserve the actual component maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- Every actual immersion into a Noetherian scheme has constructible range. -/
theorem isConstructible_range_of_noetherian {Y X : Scheme.{u}}
    [IsNoetherian X] (f : Y ⟶ X) [IsImmersion f] :
    Topology.IsConstructible (Set.range f) := by
  obtain ⟨U, Z, hU, hZ, hrange⟩ := f.isLocallyClosed_range
  rw [hrange]
  exact ((NoetherianSpace.isCompact U).isConstructible hU).inter
    (by simpa only [compl_compl] using
      ((NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).compl)

namespace FiniteLocallyClosedPartition

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The given open source and each original closed-complement stratum. -/
def attachOpenStratum {S : Scheme.{u}} (j : S ⟶ X) [IsOpenImmersion j]
    (p : FiniteLocallyClosedPartition
      (IdealSheafData.vanishingIdeal j.opensRange.compl).subscheme) :
    Option (Fin p.count) → Scheme.{u}
  | none => S
  | some i => p.stratum i

/-- The actual component maps for adjoining the given open immersion. -/
def attachOpenInclusion {S : Scheme.{u}} (j : S ⟶ X) [IsOpenImmersion j]
    (p : FiniteLocallyClosedPartition
      (IdealSheafData.vanishingIdeal j.opensRange.compl).subscheme) :
    ∀ i, attachOpenStratum j p i ⟶ X
  | none => j
  | some i => p.inclusion i ≫
      (IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι

/-- Join the given original open immersion to a partition of its actual
reduced closed complement. -/
def attachOpen {S : Scheme.{u}} (j : S ⟶ X) [IsOpenImmersion j]
    (p : FiniteLocallyClosedPartition
      (IdealSheafData.vanishingIdeal j.opensRange.compl).subscheme) :
    FiniteLocallyClosedPartition X := by
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  let T := attachOpenStratum j p
  let a := attachOpenInclusion j p
  have ha (i) : IsImmersion (a i) := by
    cases i with
    | none => exact inferInstanceAs (IsImmersion j)
    | some i =>
      have := p.immersion i
      exact inferInstanceAs (IsImmersion (p.inclusion i ≫ I.subschemeι))
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  refine ofFintype T a ha (fun i => ?_) ?_ ?_
  · have := ha i
    exact isConstructible_range_of_noetherian (a i)
  · intro i k hik
    cases i with
    | none =>
      cases k with
      | none => exact False.elim (hik rfl)
      | some k =>
        apply Set.disjoint_left.mpr
        rintro x hx ⟨z, rfl⟩
        have hz : I.subschemeι (p.inclusion k z) ∈ Set.range I.subschemeι :=
          ⟨p.inclusion k z, rfl⟩
        rw [hI] at hz
        exact hz hx
    | some i =>
      cases k with
      | none =>
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ hx
        have hz : I.subschemeι (p.inclusion i z) ∈ Set.range I.subschemeι :=
          ⟨p.inclusion i z, rfl⟩
        rw [hI] at hz
        exact hz hx
      | some k =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        have heq : p.inclusion k z = p.inclusion i y :=
          I.subschemeι.isClosedEmbedding.injective hz
        exact Set.disjoint_left.mp (p.disjoint (fun h => hik (congrArg some h)))
          ⟨y, rfl⟩ ⟨z, heq⟩
  · intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨y, hy⟩ := hx
      exact ⟨none, y, hy⟩
    · obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := hI ▸ hx
      obtain ⟨i, y, hy⟩ := p.covers z
      refine ⟨some i, y, ?_⟩
      change I.subschemeι (p.inclusion i y) = I.subschemeι z
      exact congrArg I.subschemeι hy

/-- Transport actual strata along a surjective closed immersion. In
particular, a partition of the reduction partitions the original base. -/
def alongSurjectiveClosed {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] [Surjective j] (p : FiniteLocallyClosedPartition Y) :
    FiniteLocallyClosedPartition X where
  count := p.count
  stratum := p.stratum
  inclusion i := p.inclusion i ≫ j
  immersion i := by
    have := p.immersion i
    infer_instance
  constructible_range i := by
    have := p.immersion i
    exact isConstructible_range_of_noetherian (p.inclusion i ≫ j)
  disjoint := by
    intro i k hik
    apply Set.disjoint_left.mpr
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    have heq : p.inclusion k z = p.inclusion i y := j.isClosedEmbedding.injective hz
    exact Set.disjoint_left.mp (p.disjoint hik) ⟨y, rfl⟩ ⟨z, heq⟩
  covers x := by
    obtain ⟨z, rfl⟩ := j.surjective x
    obtain ⟨i, y, hy⟩ := p.covers z
    exact ⟨i, y, by simp only [Scheme.Hom.comp_apply, hy]⟩

end FiniteLocallyClosedPartition

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
