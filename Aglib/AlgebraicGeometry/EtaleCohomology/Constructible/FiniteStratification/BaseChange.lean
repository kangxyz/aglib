/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions

/-! # Actual finite partitions under quasi-compact base change

The new strata are the literal scheme pullbacks of the original immersions.
Over a compact base, a quasi-compact map from a quasi-separated scheme pulls
constructible sets back to constructible sets. A given original cartesian
square transports finiteness on those same actual strata.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition

universe u

variable {X₀ X : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X]

/-- Pull the actual strata and immersions back along the original map.
The finite labels do not change. -/
def baseChange (p : FiniteLocallyClosedPartition X₀) (g : X ⟶ X₀) [QuasiCompact g] :
    FiniteLocallyClosedPartition X where
  count := p.count
  stratum i := pullback (p.inclusion i) g
  inclusion i := pullback.snd (p.inclusion i) g
  immersion i := by
    have := p.immersion i
    infer_instance
  constructible_range i := by
    rw [Scheme.Pullback.range_snd]
    apply (p.constructible_range i).preimage g.continuous
    intro s hs hretro
    exact (g.isSpectralMap.2 hs hretro.isCompact).isRetrocompact
      (hs.preimage g.continuous)
  disjoint := by
    intro i j hij
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (p.disjoint hij) hxi hxj
  covers x := by
    obtain ⟨i, y, hy⟩ := p.covers (g x)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz⟩

/-- Finiteness of the original structural maps survives the actual pulled-
back partition, through the specified original cartesian square. -/
theorem finite_baseChange {U₀ U : Scheme.{u}}
    (f₀ : U₀ ⟶ X₀) (f : U ⟶ X) (a : U ⟶ U₀) (g : X ⟶ X₀)
    [QuasiCompact g] (H : IsPullback a f f₀ g)
    (p : FiniteLocallyClosedPartition X₀)
    (hp : ∀ i, IsFinite (pullback.snd f₀ (p.inclusion i))) :
    ∀ i, IsFinite (pullback.snd f ((p.baseChange g).inclusion i)) := by
  intro i
  let q : pullback (p.inclusion i) g ⟶ X := pullback.snd (p.inclusion i) g
  let r : pullback (p.inclusion i) g ⟶ p.stratum i := pullback.fst (p.inclusion i) g
  have hfinite : IsFinite (pullback.snd (pullback.snd f₀ g) q) := by
    apply (isFinite_pullback_snd_comp_iff f₀ g q).mp
    rw [show q ≫ g = r ≫ p.inclusion i from pullback.condition.symm]
    apply (isFinite_pullback_snd_comp_iff f₀ (p.inclusion i) r).mpr
    have := hp i
    infer_instance
  let e₀ : Over.mk f ≅ Over.mk (pullback.snd f₀ g) :=
    Over.isoMk H.isoPullback H.isoPullback_hom_snd
  let e := (Over.pullback q).mapIso e₀
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have heq : e.hom.left ≫ pullback.snd (pullback.snd f₀ g) q =
      pullback.snd f q := e.hom.w
  change IsFinite (pullback.snd f q)
  rw [← heq]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
