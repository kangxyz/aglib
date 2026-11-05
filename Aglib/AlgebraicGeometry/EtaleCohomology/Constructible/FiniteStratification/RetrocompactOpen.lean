/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.OpenGluing

/-! # Partitions on a retrocompact open with its actual closed complement -/

@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
universe u

/-- The original open strata and the actual closed complement. -/
def extendOpenStratum {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (p : FiniteLocallyClosedPartition U) : Option (Fin p.count) → Scheme.{u}
  | none => (IdealSheafData.vanishingIdeal j.opensRange.compl).subscheme
  | some i => p.stratum i

/-- Original component maps of the retrocompact-open partition. -/
def extendOpenInclusion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (p : FiniteLocallyClosedPartition U) : ∀ i, extendOpenStratum j p i ⟶ X
  | none => (IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι
  | some i => p.inclusion i ≫ j

/-- Retain every original open stratum and adjoin the actual closed complement.
Constructibility follows from retrocompactness, not Noetherianity. -/
def extendOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hretro : IsRetrocompact (Set.range j)) (p : FiniteLocallyClosedPartition U) :
    FiniteLocallyClosedPartition X := by
  classical
  let I := IdealSheafData.vanishingIdeal j.opensRange.compl
  let T := extendOpenStratum j p
  let a := extendOpenInclusion j p
  have hI : Set.range I.subschemeι = (Set.range j)ᶜ :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have ha (i) : IsImmersion (a i) := by
    cases i with
    | none => exact inferInstanceAs (IsImmersion I.subschemeι)
    | some i =>
      have := p.immersion i
      exact inferInstanceAs (IsImmersion (p.inclusion i ≫ j))
  refine ofFintype T a ha (fun i => ?_) ?_ ?_
  · cases i with
    | none =>
      change Topology.IsConstructible (Set.range I.subschemeι)
      rw [hI]
      exact (hretro.isConstructible j.isOpenEmbedding.isOpen_range).compl
    | some i =>
      change Topology.IsConstructible (Set.range (j ∘ p.inclusion i))
      rw [Set.range_comp]
      exact (p.constructible_range i).image_of_isOpenEmbedding j.isOpenEmbedding hretro
  · intro i k hik
    cases i with
    | none =>
      cases k with
      | none => exact False.elim (hik rfl)
      | some k =>
        apply Set.disjoint_left.mpr
        rintro x hx ⟨y, rfl⟩
        change j (p.inclusion k y) ∈ Set.range I.subschemeι at hx
        rw [hI] at hx
        exact hx ⟨p.inclusion k y, rfl⟩
    | some i =>
      cases k with
      | none =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ hx
        change j (p.inclusion i y) ∈ Set.range I.subschemeι at hx
        rw [hI] at hx
        exact hx ⟨p.inclusion i y, rfl⟩
      | some k =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        have heq : p.inclusion k z = p.inclusion i y :=
          j.isOpenEmbedding.injective hz
        exact Set.disjoint_left.mp (p.disjoint (fun h => hik (congrArg some h)))
          ⟨y, rfl⟩ ⟨z, heq⟩
  · intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hx
      obtain ⟨i, z, hz⟩ := p.covers y
      exact ⟨some i, z, congrArg j hz⟩
    · obtain ⟨z, hz⟩ : x ∈ Set.range I.subschemeι := hI ▸ hx
      exact ⟨none, z, hz⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
